"""Pre-game availability from the official NBA injury report + player impact values.

For each (game, team) we take the LAST report version published before tip-off (falling back to the
latest version of the previous day when a team had not yet submitted), map each listed player to
their stats.nba.com id (direct id, else normalised name match within the team), and attach the
player's impact value and typical minute share. Questionable players are kept as a separate bucket so
the model and the Monte Carlo scenarios can treat them as "maybe".
"""
from __future__ import annotations

import logging
import re
import unicodedata

import numpy as np
import pandas as pd

from nba_quant.config import PARQUET_DIR

log = logging.getLogger(__name__)

OUT_STATUSES = {"Out", "Doubtful"}
Q_STATUSES = {"Questionable"}
PROB_STATUSES = {"Probable", "Available"}
MIN_HALF_LIFE = 5.0
ROTATION_MIN = 10.0
REPLACEMENT = -1.5


def norm_name(s: str) -> str:
    s = unicodedata.normalize("NFKD", str(s)).encode("ascii", "ignore").decode()
    s = re.sub(r"[^a-z ]", "", s.lower())
    s = re.sub(r"\b(jr|sr|ii|iii|iv)\b", "", s)
    return re.sub(r"\s+", " ", s).strip()


def typical_minutes(players: pd.DataFrame) -> pd.DataFrame:
    """Pre-game EWMA of minutes per player-team (shifted; zero for DNP rows), plus prior-season mean."""
    p = players.sort_values(["player_id", "game_date", "game_id"])[["game_id", "season", "game_date", "team", "player_id", "player_name", "min", "starter"]].copy()
    grp = p.groupby(["player_id", "team", "season"], sort=False)
    p["typ_min"] = grp["min"].transform(lambda s: s.shift(1).ewm(halflife=MIN_HALF_LIFE, min_periods=1).mean())
    p["typ_start"] = grp["starter"].transform(lambda s: s.shift(1).astype(float).ewm(halflife=MIN_HALF_LIFE, min_periods=1).mean())
    prev = p.groupby(["player_id", "season"])["min"].mean().groupby(level=0).shift(1)
    prev_map = prev.to_dict()
    fallback = pd.Series([prev_map.get((pid, s), np.nan) for pid, s in zip(p["player_id"], p["season"])], index=p.index)
    p["typ_min"] = p["typ_min"].fillna(fallback).fillna(0.0)
    p["n_prev_games"] = grp.cumcount()
    return p


def pregame_report(games: pd.DataFrame, injuries: pd.DataFrame) -> pd.DataFrame:
    """Latest submitted injury-report version per (game, team) before tip-off."""
    inj = injuries[injuries["game_id"].notna()].copy()
    g = games.set_index("game_id")
    tip = pd.to_datetime(g["start_time_utc"], utc=True).dt.tz_convert("America/New_York").dt.tz_localize(None)
    inj["tip_et"] = inj["game_id"].map(tip)
    # when the tip time is unknown use end of game day
    inj["tip_et"] = inj["tip_et"].fillna(pd.to_datetime(inj["game_date"]) + pd.Timedelta(hours=23, minutes=59))
    inj = inj[inj["report_datetime"] <= inj["tip_et"]]
    submitted = inj[inj["submitted"]]
    last_version = submitted.groupby(["game_id", "team"])["report_datetime"].max().rename("last_report")
    inj = submitted.merge(last_version, left_on=["game_id", "team"], right_index=True)
    inj = inj[inj["report_datetime"] == inj["last_report"]]
    return inj[["game_id", "game_date", "team", "player_id", "player_name", "status", "reason", "reason_category", "last_report"]]


def attach_players(report: pd.DataFrame, typ: pd.DataFrame, values: pd.DataFrame, games: pd.DataFrame) -> pd.DataFrame:
    """Join each report line to the player's typical minutes (that game) and impact value (that season)."""
    typ = typ.copy()
    typ["name_key"] = typ["player_name"].map(norm_name)
    rep = report.copy()
    rep["name_key"] = rep["player_name"].map(norm_name)
    # id match first
    key_cols = ["game_id", "team", "player_id"]
    t_id = typ.dropna(subset=["player_id"])[key_cols + ["typ_min", "typ_start", "season"]]
    m1 = rep.merge(t_id, on=key_cols, how="left")
    # name fallback for unmatched ids
    miss = m1["typ_min"].isna()
    if miss.any():
        t_nm = typ[["game_id", "team", "name_key", "player_id", "typ_min", "typ_start", "season"]].drop_duplicates(["game_id", "team", "name_key"])
        fix = m1.loc[miss, ["game_id", "team", "name_key"]].merge(t_nm, on=["game_id", "team", "name_key"], how="left")
        for c in ["typ_min", "typ_start", "season"]:
            m1.loc[miss, c] = fix[c].to_numpy()
        m1.loc[miss & m1["player_id"].isna(), "player_id"] = fix["player_id"].to_numpy()[m1.loc[miss, "player_id"].isna().to_numpy()]
    m1["season"] = m1["season"].fillna(m1["game_id"].map(games.set_index("game_id")["season"]))
    v = values.rename(columns={"asof_season": "season"})[["season", "player_id", "value", "value_off", "value_def"]]
    m1 = m1.merge(v, on=["season", "player_id"], how="left")
    m1["value"] = m1["value"].fillna(REPLACEMENT)
    m1["typ_min"] = m1["typ_min"].fillna(0.0)
    m1["share"] = m1["typ_min"] / 48.0
    m1["value_above_repl"] = (m1["value"] - REPLACEMENT) * m1["share"]
    return m1


def availability_features(att: pd.DataFrame) -> pd.DataFrame:
    """Aggregate the attached report lines into per (game, team) features."""
    rot = att[att["typ_min"] >= ROTATION_MIN]
    out_mask = rot["status"].isin(OUT_STATUSES)
    q_mask = rot["status"].isin(Q_STATUSES)
    feats = rot.assign(out_val=np.where(out_mask, rot["value_above_repl"], 0.0),
                       q_val=np.where(q_mask, rot["value_above_repl"], 0.0),
                       out_min=np.where(out_mask, rot["typ_min"], 0.0),
                       q_min=np.where(q_mask, rot["typ_min"], 0.0),
                       out_n=out_mask.astype(int), q_n=q_mask.astype(int),
                       out_star=np.where(out_mask, rot["value"], -99.0))
    agg = feats.groupby(["game_id", "team"]).agg(out_val=("out_val", "sum"), q_val=("q_val", "sum"), out_min=("out_min", "sum"),
                                                 q_min=("q_min", "sum"), out_n=("out_n", "sum"), q_n=("q_n", "sum"),
                                                 out_star=("out_star", "max"))
    agg["out_star"] = agg["out_star"].replace(-99, np.nan)
    return agg.reset_index()


def actual_missing(typ: pd.DataFrame, values: pd.DataFrame) -> pd.DataFrame:
    """Post-hoc: rotation players (typical >=10 min) who did not play; used for calibration only."""
    t = typ[(typ["typ_min"] >= ROTATION_MIN) & (typ["min"] <= 0)].copy()
    v = values.rename(columns={"asof_season": "season"})[["season", "player_id", "value"]]
    t = t.merge(v, on=["season", "player_id"], how="left")
    t["value"] = t["value"].fillna(REPLACEMENT)
    t["val_missing"] = (t["value"] - REPLACEMENT) * t["typ_min"] / 48.0
    return t.groupby(["game_id", "team"]).agg(actual_missing_val=("val_missing", "sum"), actual_missing_n=("player_id", "size")).reset_index()


def build(write: bool = True):
    games = pd.read_parquet(PARQUET_DIR / "games.parquet")
    players = pd.read_parquet(PARQUET_DIR / "players.parquet")
    injuries = pd.read_parquet(PARQUET_DIR / "injuries.parquet")
    values = pd.read_parquet(PARQUET_DIR / "player_values.parquet")
    typ = typical_minutes(players)
    rep = pregame_report(games, injuries)
    att = attach_players(rep, typ, values, games)
    feats = availability_features(att)
    act = actual_missing(typ, values)
    # questionable -> played rate, by season (for scenario weighting)
    played = players[["game_id", "player_id", "min"]].rename(columns={"min": "min_played"})
    q = att[att["status"].isin(Q_STATUSES | OUT_STATUSES | PROB_STATUSES)].merge(played, on=["game_id", "player_id"], how="left")
    q["played"] = q["min_played"].fillna(0) > 0
    rates = q.groupby("status")["played"].agg(["mean", "size"]).rename(columns={"mean": "play_rate", "size": "n"})
    log.info("play rates by status:\n%s", rates.round(3))
    if write:
        att.to_parquet(PARQUET_DIR / "pregame_injury_lines.parquet", index=False, compression="zstd")
        feats.to_parquet(PARQUET_DIR / "availability_features.parquet", index=False)
        act.to_parquet(PARQUET_DIR / "actual_missing.parquet", index=False)
        typ[["game_id", "season", "game_date", "team", "player_id", "player_name", "min", "typ_min", "typ_start", "n_prev_games"]].to_parquet(
            PARQUET_DIR / "player_typical_minutes.parquet", index=False, compression="zstd")
        rates.to_json(PARQUET_DIR / "status_play_rates.json")
    return att, feats, act, rates


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    pd.set_option("display.width", 220); pd.set_option("display.max_columns", 40)
    att, feats, act, rates = build()
    print(feats.describe().round(2).T)
    print(att[att.game_id == att.game_id.max()][["team", "player_name", "status", "reason", "typ_min", "value", "value_above_repl"]].to_string())

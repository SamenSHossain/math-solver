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
    p["typ_min_post"] = grp["min"].transform(lambda s: s.ewm(halflife=MIN_HALF_LIFE, min_periods=1).mean())
    p["typ_start_post"] = grp["starter"].transform(lambda s: s.astype(float).ewm(halflife=MIN_HALF_LIFE, min_periods=1).mean())
    p["n_prev_games"] = grp.cumcount()
    return p


def latest_typical(typ: pd.DataFrame) -> pd.DataFrame:
    """Each player's current (post latest game) typical minutes with his latest team."""
    last = typ.sort_values(["game_date", "game_id"]).groupby("player_id").tail(1)
    out = last[["player_id", "player_name", "team", "season", "typ_min_post", "typ_start_post", "game_date"]].rename(
        columns={"typ_min_post": "typ_min", "typ_start_post": "typ_start", "game_date": "last_game_date"})
    return out


def load_overrides(path=None) -> pd.DataFrame:
    """Manual injury overrides (data/injuries_override.csv): game_date, team, player_name, status, reason, source."""
    from nba_quant.config import DATA_DIR
    path = path or DATA_DIR / "injuries_override.csv"
    if not path.exists():
        return pd.DataFrame(columns=["game_date", "team", "player_name", "status", "reason", "source"])
    o = pd.read_csv(path, dtype=str).fillna("")
    o["game_date"] = pd.to_datetime(o["game_date"]).dt.date.astype(str)
    o["status"] = o["status"].str.title()
    return o


def upcoming_report(games: pd.DataFrame, injuries: pd.DataFrame, through_date: str, overrides: pd.DataFrame | None = None) -> pd.DataFrame:
    """Latest available report lines for scheduled games (any version, since tip-off has not happened),
    with manual overrides layered on top (override wins; new names are added)."""
    up = games[(~games["completed"]) & (games["game_date"] <= through_date)]
    inj = injuries[injuries["game_id"].isin(up["game_id"]) & injuries["submitted"]]
    last_version = inj.groupby(["game_id", "team"])["report_datetime"].max().rename("last_report")
    inj = inj.merge(last_version, left_on=["game_id", "team"], right_index=True)
    inj = inj[inj["report_datetime"] == inj["last_report"]][["game_id", "game_date", "team", "player_id", "player_name", "status", "reason", "reason_category", "last_report"]].copy()
    inj["source"] = "official_report"
    if overrides is not None and len(overrides):
        o = overrides.merge(up[["game_id", "game_date", "home_team", "away_team"]], on="game_date", how="inner")
        o = o[(o["team"] == o["home_team"]) | (o["team"] == o["away_team"])]
        o = o[["game_id", "game_date", "team", "player_name", "status", "reason", "source"]].copy()
        o["player_id"] = np.nan; o["reason_category"] = "override"; o["last_report"] = pd.NaT
        key = ["game_id", "team"]
        o["name_key"] = o["player_name"].map(norm_name); inj["name_key"] = inj["player_name"].map(norm_name)
        inj = inj[~inj.set_index(key + ["name_key"]).index.isin(o.set_index(key + ["name_key"]).index)]
        inj = pd.concat([inj.drop(columns=["name_key"]), o.drop(columns=["name_key"])], ignore_index=True)
    return inj


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
    # upcoming games (no box score yet): use each player's latest typical-minutes state with that team
    miss = m1["typ_min"].isna()
    if miss.any():
        lt = latest_typical(typ)
        lt["name_key"] = lt["player_name"].map(norm_name)
        by_id = lt.dropna(subset=["player_id"]).drop_duplicates("player_id").set_index("player_id")
        by_nm = lt.drop_duplicates(["team", "name_key"]).set_index(["team", "name_key"])
        for i in m1.index[miss]:
            pid = m1.at[i, "player_id"]
            row = None
            if pid == pid and pid in by_id.index and by_id.at[pid, "team"] == m1.at[i, "team"]:
                row = by_id.loc[pid]
            elif (m1.at[i, "team"], m1.at[i, "name_key"]) in by_nm.index:
                row = by_nm.loc[(m1.at[i, "team"], m1.at[i, "name_key"])]
                m1.at[i, "player_id"] = row["player_id"]
            if row is not None:
                m1.at[i, "typ_min"] = row["typ_min"]; m1.at[i, "typ_start"] = row["typ_start"]
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


def build(write: bool = True, through_date: str | None = None):
    games = pd.read_parquet(PARQUET_DIR / "games.parquet")
    players = pd.read_parquet(PARQUET_DIR / "players.parquet")
    injuries = pd.read_parquet(PARQUET_DIR / "injuries.parquet")
    values = pd.read_parquet(PARQUET_DIR / "player_values.parquet")
    typ = typical_minutes(players)
    rep = pregame_report(games, injuries)
    through = through_date or str(pd.Timestamp.today().date())
    rep_up = upcoming_report(games, injuries, through, load_overrides())
    # for upcoming games use the current (in-season) values; map them onto the current season label
    cur = pd.read_parquet(PARQUET_DIR / "player_values_current.parquet")
    cur["asof_season"] = int(games["season"].max())
    vals = pd.concat([values[values["asof_season"] < int(games["season"].max())], cur[values.columns.intersection(cur.columns)]], ignore_index=True)
    rep = rep[~rep["game_id"].isin(rep_up["game_id"])]   # upcoming games come only from the upcoming path
    att = attach_players(pd.concat([rep, rep_up], ignore_index=True), typ, vals, games)
    att = att.drop_duplicates(["game_id", "team", "name_key"])
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

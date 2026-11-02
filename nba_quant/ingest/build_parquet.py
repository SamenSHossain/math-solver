"""Build the canonical parquet data lake from the raw mirror downloads.

Outputs (data/parquet/):
  games.parquet         one row per game (regular season, play-in, playoffs, NBA Cup final)
  teams.parquet         one row per team-game: box score + opponent box + derived efficiency
  players.parquet       one row per player-game (box score, minutes, starter flag, DNP reason)
  lineups.parquet       five-man lineups per team-season (minutes, possessions, ratings, four factors)
  team_seasons.parquet  team-season aggregates (advanced/base/misc/scoring/opponent, wide)
  injuries.parquet      every version of the official NBA injury report, normalised
  MANIFEST.json         row counts, columns, build timestamp

Season label convention everywhere: END year (2026 == 2025-26).
"""
from __future__ import annotations

import json
import logging
import re
from datetime import datetime, timezone

import numpy as np
import pandas as pd
import pyarrow.parquet as pq

from nba_quant.config import ALL_SEASONS, NBA_TEAM_IDS, PARQUET_DIR, normalize_tricode
from nba_quant.ingest import sdv_mirror as M

log = logging.getLogger(__name__)

SEASON_TYPE_MAP = {"1": "preseason", "2": "regular", "3": "allstar", "4": "playoffs", "5": "playin", "6": "cupfinal"}
ESPN_SEASON_TYPE = {1: "preseason", 2: "regular", 3: "playoffs", 5: "playin"}


# ----------------------------------------------------------------------------- helpers
def _read(asset: M.Asset, season: int, columns: list[str] | None = None) -> pd.DataFrame:
    path = asset.local_path(season)
    if not path.exists():
        raise FileNotFoundError(f"missing raw asset {path}; run sdv_mirror.download_many first")
    df = pq.read_table(path, columns=columns).to_pandas()
    df["season"] = season
    return df


def _concat(asset: M.Asset, seasons, columns=None) -> pd.DataFrame:
    frames = []
    for s in seasons:
        try:
            frames.append(_read(asset, s, columns))
        except FileNotFoundError as exc:
            log.warning(str(exc))
    return pd.concat(frames, ignore_index=True) if frames else pd.DataFrame()


def minutes_to_float(x) -> float:
    """'33:15' -> 33.25 ; '240:00' -> 240.0 ; 'PT33M15.00S' -> 33.25 ; NaN -> 0."""
    if x is None or (isinstance(x, float) and np.isnan(x)):
        return 0.0
    s = str(x)
    m = re.match(r"PT(\d+)M([\d.]+)S", s)
    if m:
        return int(m.group(1)) + float(m.group(2)) / 60
    if ":" in s:
        mm, ss = s.split(":")[:2]
        return float(mm) + float(ss) / 60
    try:
        return float(s)
    except ValueError:
        return 0.0


def season_type_from_game_id(game_id: str) -> str:
    return SEASON_TYPE_MAP.get(str(game_id)[2], "other")


# ----------------------------------------------------------------------------- games
def load_nba_schedule(seasons) -> pd.DataFrame:
    sch = _concat(M.NBA_SCHEDULE, seasons)
    sch["game_id"] = sch["game_id"].astype(str).str.zfill(10)
    sch["season_type"] = sch["game_id"].map(season_type_from_game_id)
    sch["game_date"] = pd.to_datetime(sch["game_date"]).dt.date.astype(str)
    sch = sch.rename(columns={"home_team_abbreviation": "home_team", "away_team_abbreviation": "away_team",
                              "home_pts": "home_score", "away_pts": "away_score"})
    sch["home_team"] = sch["home_team"].map(normalize_tricode)
    sch["away_team"] = sch["away_team"].map(normalize_tricode)
    # drop preseason/all-star; keep regular, play-in, playoffs, cup final
    sch = sch[sch["season_type"].isin(["regular", "playin", "playoffs", "cupfinal"])]
    return sch.drop_duplicates("game_id")


def load_espn_schedule(seasons) -> pd.DataFrame:
    cols = ["game_id", "season", "season_type", "game_date", "game_date_time", "date", "status_type_name",
            "status_type_completed", "neutral_site", "attendance", "venue_full_name", "venue_address_city",
            "venue_address_state", "home_abbreviation", "away_abbreviation", "home_score", "away_score",
            "broadcast_name", "notes_headline"]
    frames = []
    for s in seasons:
        df = _read(M.ESPN_SCHEDULE, s)
        df = df[[c for c in cols if c in df.columns]]
        frames.append(df)
    e = pd.concat(frames, ignore_index=True)
    e = e.rename(columns={"game_id": "espn_game_id", "home_abbreviation": "home_team", "away_abbreviation": "away_team",
                          "home_score": "espn_home_score", "away_score": "espn_away_score", "date": "start_time_utc"})
    e["espn_game_id"] = e["espn_game_id"].astype(str)
    e["home_team"] = e["home_team"].map(normalize_tricode)
    e["away_team"] = e["away_team"].map(normalize_tricode)
    e["game_date"] = pd.to_datetime(e["game_date"]).dt.date.astype(str)
    e["espn_season_type"] = e["season_type"].map(ESPN_SEASON_TYPE)
    e["start_time_utc"] = pd.to_datetime(e["start_time_utc"], utc=True, errors="coerce")
    return e.drop(columns=["season_type"]).drop_duplicates("espn_game_id")


def pbp_game_level(seasons) -> pd.DataFrame:
    """Per-game facts from ESPN play-by-play: market spread and number of periods."""
    cols = ["game_id", "home_team_spread", "game_spread", "home_favorite", "game_spread_available", "period_number"]
    out = []
    for s in seasons:
        path = M.ESPN_PBP.local_path(s)
        if not path.exists():
            log.warning("no pbp for %s", s)
            continue
        df = pq.read_table(path, columns=cols).to_pandas()
        g = df.groupby("game_id").agg(home_exp_margin_market=("home_team_spread", "first"),
                                      spread_available=("game_spread_available", "first"),
                                      periods=("period_number", "max"))
        g.index = g.index.astype(str)
        out.append(g)
    res = pd.concat(out)
    res.loc[~res["spread_available"].astype(bool), "home_exp_margin_market"] = np.nan
    res["home_spread_market"] = -res["home_exp_margin_market"]  # conventional: negative = home favoured
    res["overtime_periods"] = (res["periods"].fillna(4) - 4).clip(lower=0).astype(int)
    return res.drop(columns=["spread_available", "periods"]).rename_axis("espn_game_id").reset_index()


def build_games(seasons=ALL_SEASONS) -> pd.DataFrame:
    nba = load_nba_schedule(seasons)
    espn = load_espn_schedule(seasons)
    key = ["game_date", "home_team", "away_team"]
    merged = nba.merge(espn.drop(columns=["season"]), on=key, how="left", suffixes=("", "_espn"))
    # ESPN occasionally stamps a late tip on the next UTC day; retry unmatched on date +/- 1
    miss = merged["espn_game_id"].isna()
    if miss.any():
        e2 = espn.copy()
        for shift in (-1, 1):
            e2s = e2.copy()
            e2s["game_date"] = (pd.to_datetime(e2s["game_date"]) + pd.Timedelta(days=shift)).dt.date.astype(str)
            fix = merged.loc[miss, ["game_id"] + key].merge(e2s.drop(columns=["season"]), on=key, how="inner")
            if len(fix):
                fix = fix.set_index("game_id")
                for c in fix.columns:
                    if c in merged.columns and c not in key:
                        merged.loc[merged["game_id"].isin(fix.index), c] = merged.loc[merged["game_id"].isin(fix.index), "game_id"].map(fix[c])
                miss = merged["espn_game_id"].isna()
    pbp = pbp_game_level(seasons)
    merged = merged.merge(pbp, on="espn_game_id", how="left")
    merged["home_win"] = np.where(merged["home_score"].notna(), (merged["home_score"] > merged["away_score"]).astype(float), np.nan)
    merged["margin"] = merged["home_score"] - merged["away_score"]
    merged["total"] = merged["home_score"] + merged["away_score"]
    merged["completed"] = merged["home_score"].notna()
    merged["playoffs"] = merged["season_type"].eq("playoffs")
    merged["neutral_site"] = merged["neutral_site"].fillna(False).astype(bool)
    cols = ["game_id", "espn_game_id", "season", "season_type", "playoffs", "game_date", "start_time_utc", "completed",
            "home_team", "away_team", "home_team_id", "away_team_id", "home_score", "away_score", "home_win", "margin",
            "total", "overtime_periods", "home_exp_margin_market", "home_spread_market", "neutral_site", "venue_full_name",
            "venue_address_city", "venue_address_state", "attendance", "broadcast_name", "status_type_name", "notes_headline"]
    games = merged[cols].sort_values(["game_date", "game_id"]).reset_index(drop=True)
    games["game_number_season"] = games.groupby("season").cumcount() + 1
    log.info("games: %d rows, %d unmatched to ESPN", len(games), games["espn_game_id"].isna().sum())
    return games


# ----------------------------------------------------------------------------- teams
BOX_RENAME = {
    "field_goals_made": "fgm", "field_goals_attempted": "fga", "three_pointers_made": "fg3m",
    "three_pointers_attempted": "fg3a", "free_throws_made": "ftm", "free_throws_attempted": "fta",
    "rebounds_offensive": "oreb", "rebounds_defensive": "dreb", "rebounds_total": "reb", "assists": "ast",
    "steals": "stl", "blocks": "blk", "turnovers": "tov", "fouls_personal": "pf", "points": "pts",
    "plus_minus_points": "plus_minus",
}
BOX_COLS = ["fgm", "fga", "fg3m", "fg3a", "ftm", "fta", "oreb", "dreb", "reb", "ast", "stl", "blk", "tov", "pf", "pts"]


def possessions(t: pd.DataFrame, o: pd.DataFrame) -> pd.Series:
    """Basketball-Reference possession estimate averaged over both teams."""
    def one(a, b):
        orb_share = a["oreb"] / (a["oreb"] + b["dreb"]).replace(0, np.nan)
        return a["fga"] + 0.4 * a["fta"] - 1.07 * orb_share.fillna(0) * (a["fga"] - a["fgm"]) + a["tov"]
    return 0.5 * (one(t, o) + one(o, t))


def build_teams(games: pd.DataFrame, seasons=ALL_SEASONS) -> pd.DataFrame:
    tb = _concat(M.NBA_TEAM_BOX, seasons)
    tb["game_id"] = tb["game_id"].astype(str).str.zfill(10)
    tb = tb.rename(columns=BOX_RENAME)
    tb["team"] = tb["team_id"].map(NBA_TEAM_IDS).fillna(tb["team_tricode"].map(normalize_tricode))
    tb["minutes"] = tb["minutes"].map(minutes_to_float)
    tb = tb[tb["game_id"].isin(games["game_id"])]
    keep = ["game_id", "season", "team", "team_id", "side", "minutes"] + BOX_COLS + ["plus_minus"]
    tb = tb[keep].drop_duplicates(["game_id", "team_id"])
    opp = tb[["game_id", "team", "team_id"] + BOX_COLS].rename(columns={"team": "opponent", "team_id": "opponent_id"})
    opp = opp.rename(columns={c: f"opp_{c}" for c in BOX_COLS})
    t = tb.merge(opp, on="game_id")
    t = t[t["team_id"] != t["opponent_id"]]
    o = t[[f"opp_{c}" for c in BOX_COLS]].rename(columns=lambda c: c[4:])
    t["poss"] = possessions(t[BOX_COLS], o)
    t["pace"] = 48 * t["poss"] / (t["minutes"] / 5).replace(0, np.nan)
    t["off_rtg"] = 100 * t["pts"] / t["poss"]
    t["def_rtg"] = 100 * t["opp_pts"] / t["poss"]
    t["net_rtg"] = t["off_rtg"] - t["def_rtg"]
    t["efg"] = (t["fgm"] + 0.5 * t["fg3m"]) / t["fga"]
    t["ts"] = t["pts"] / (2 * (t["fga"] + 0.44 * t["fta"]))
    t["tov_pct"] = t["tov"] / t["poss"]
    t["oreb_pct"] = t["oreb"] / (t["oreb"] + t["opp_dreb"])
    t["dreb_pct"] = t["dreb"] / (t["dreb"] + t["opp_oreb"])
    t["ftr"] = t["fta"] / t["fga"]
    t["fg3a_rate"] = t["fg3a"] / t["fga"]
    t["fg3_pct"] = t["fg3m"] / t["fg3a"].replace(0, np.nan)
    t["fg2_pct"] = (t["fgm"] - t["fg3m"]) / (t["fga"] - t["fg3a"]).replace(0, np.nan)
    t["ft_pct"] = t["ftm"] / t["fta"].replace(0, np.nan)
    t["ast_pct"] = t["ast"] / t["fgm"].replace(0, np.nan)
    t["opp_efg"] = (t["opp_fgm"] + 0.5 * t["opp_fg3m"]) / t["opp_fga"]
    t["opp_tov_pct"] = t["opp_tov"] / t["poss"]
    t["opp_ftr"] = t["opp_fta"] / t["opp_fga"]
    t["opp_fg3a_rate"] = t["opp_fg3a"] / t["opp_fga"]
    t["opp_fg3_pct"] = t["opp_fg3m"] / t["opp_fg3a"].replace(0, np.nan)
    g = games.set_index("game_id")
    t["game_date"] = t["game_id"].map(g["game_date"])
    t["season_type"] = t["game_id"].map(g["season_type"])
    t["espn_game_id"] = t["game_id"].map(g["espn_game_id"])
    t["home"] = t["side"].eq("home")
    t["win"] = (t["pts"] > t["opp_pts"]).astype(int)
    t["margin"] = t["pts"] - t["opp_pts"]
    t["overtime_periods"] = t["game_id"].map(g["overtime_periods"]).fillna(0).astype(int)
    # rest / schedule context
    t = t.sort_values(["team", "game_date", "game_id"])
    t["prev_game_date"] = t.groupby(["team", "season"])["game_date"].shift(1)
    t["rest_days"] = (pd.to_datetime(t["game_date"]) - pd.to_datetime(t["prev_game_date"])).dt.days - 1
    t["back_to_back"] = t["rest_days"].eq(0)
    t["team_game_no"] = t.groupby(["team", "season"]).cumcount() + 1
    d = pd.to_datetime(t["game_date"])
    t["games_last_7d"] = 0
    for (team, season), idx in t.groupby(["team", "season"]).groups.items():
        dd = d.loc[idx]
        vals = np.searchsorted(dd.values, dd.values, side="right") - np.searchsorted(dd.values, (dd - pd.Timedelta(days=7)).values, side="left")
        t.loc[idx, "games_last_7d"] = vals - 1
    # ESPN extras (fast-break points, paint points, lead changes) via crosswalk
    espn_cols = ["game_id", "team_abbreviation", "fast_break_points", "points_in_paint", "largest_lead", "lead_changes",
                 "turnover_points", "team_turnovers", "flagrant_fouls", "technical_fouls"]
    eb = pd.concat([_read(M.ESPN_TEAM_BOX, s).reindex(columns=espn_cols) for s in seasons
                    if M.ESPN_TEAM_BOX.local_path(s).exists()])
    eb = eb.rename(columns={"game_id": "espn_game_id", "team_abbreviation": "team"})
    eb["espn_game_id"] = eb["espn_game_id"].astype(str)
    eb["team"] = eb["team"].map(normalize_tricode)
    for c in ["fast_break_points", "points_in_paint", "largest_lead", "lead_changes", "turnover_points"]:
        eb[c] = pd.to_numeric(eb[c], errors="coerce")
    t = t.merge(eb.drop_duplicates(["espn_game_id", "team"]), on=["espn_game_id", "team"], how="left")
    order = ["game_id", "espn_game_id", "season", "season_type", "game_date", "team", "team_id", "opponent", "opponent_id",
             "home", "win", "margin", "minutes", "overtime_periods", "rest_days", "back_to_back", "games_last_7d",
             "team_game_no", "poss", "pace", "off_rtg", "def_rtg", "net_rtg", "efg", "ts", "tov_pct", "oreb_pct",
             "dreb_pct", "ftr", "fg3a_rate", "fg3_pct", "fg2_pct", "ft_pct", "ast_pct", "opp_efg", "opp_tov_pct",
             "opp_ftr", "opp_fg3a_rate", "opp_fg3_pct"] + BOX_COLS + ["plus_minus"] + [f"opp_{c}" for c in BOX_COLS] + [
             "fast_break_points", "points_in_paint", "largest_lead", "lead_changes", "turnover_points"]
    return t[order].sort_values(["game_date", "game_id", "home"]).reset_index(drop=True)


# ----------------------------------------------------------------------------- players
def build_players(games: pd.DataFrame, seasons=ALL_SEASONS) -> pd.DataFrame:
    pb = _concat(M.NBA_PLAYER_BOX, seasons)
    pb["game_id"] = pb["game_id"].astype(str).str.zfill(10)
    pb = pb[pb["game_id"].isin(games["game_id"])]
    pb = pb.rename(columns=BOX_RENAME)
    pb["team"] = pb["team_id"].map(NBA_TEAM_IDS).fillna(pb["team_tricode"].map(normalize_tricode))
    pb["player_name"] = (pb["first_name"].fillna("") + " " + pb["family_name"].fillna("")).str.strip()
    pb["min"] = pb["minutes"].map(minutes_to_float)
    pb["starter"] = pb["position"].fillna("").str.len().gt(0)
    pb["played"] = pb["min"] > 0
    pb["dnp_reason"] = pb["comment"].fillna("").str.strip()
    pb["dnp"] = ~pb["played"]
    pb["dnp_injury"] = pb["dnp_reason"].str.contains(r"injur|ill|sore|strain|sprain|concussion|surgery|fracture|tear|manage|recovery|health", case=False, regex=True)
    g = games.set_index("game_id")
    pb["game_date"] = pb["game_id"].map(g["game_date"])
    pb["season_type"] = pb["game_id"].map(g["season_type"])
    pb["home"] = pb["side"].eq("home")
    home_team = pb["game_id"].map(g["home_team"])
    away_team = pb["game_id"].map(g["away_team"])
    pb["opponent"] = np.where(pb["home"], away_team, home_team)
    pb["team_pts"] = np.where(pb["home"], pb["game_id"].map(g["home_score"]), pb["game_id"].map(g["away_score"]))
    pb["opp_pts"] = np.where(pb["home"], pb["game_id"].map(g["away_score"]), pb["game_id"].map(g["home_score"]))
    pb["win"] = (pb["team_pts"] > pb["opp_pts"]).astype(int)
    pb["ts"] = pb["pts"] / (2 * (pb["fga"] + 0.44 * pb["fta"])).replace(0, np.nan)
    pb["efg"] = (pb["fgm"] + 0.5 * pb["fg3m"]) / pb["fga"].replace(0, np.nan)
    # usage proxy: share of team FGA+0.44FTA+TOV while on the floor
    team_tot = pb.groupby(["game_id", "team_id"]).agg(t_fga=("fga", "sum"), t_fta=("fta", "sum"), t_tov=("tov", "sum"), t_min=("min", "sum"))
    pb = pb.merge(team_tot, left_on=["game_id", "team_id"], right_index=True, how="left")
    denom = (pb["t_fga"] + 0.44 * pb["t_fta"] + pb["t_tov"]) * (pb["min"] / pb["t_min"].replace(0, np.nan))
    pb["usage"] = ((pb["fga"] + 0.44 * pb["fta"] + pb["tov"]) / denom.replace(0, np.nan)).where(pb["min"] > 0)
    pb["min_share"] = pb["min"] / pb["t_min"].replace(0, np.nan)
    cols = ["game_id", "season", "season_type", "game_date", "team", "team_id", "opponent", "home", "win", "person_id",
            "player_name", "position", "jersey_num", "starter", "played", "dnp", "dnp_reason", "dnp_injury", "min",
            "min_share"] + BOX_COLS + ["plus_minus", "ts", "efg", "usage"]
    out = pb[cols].rename(columns={"person_id": "player_id"})
    return out.sort_values(["game_date", "game_id", "team", "starter"], ascending=[True, True, True, False]).reset_index(drop=True)


# ----------------------------------------------------------------------------- lineups
def _wide_by_measure(df: pd.DataFrame, keys: list[str]) -> pd.DataFrame:
    """Rows are split by measure_type with each type filling its own columns: collapse to one row."""
    df = df.drop(columns=[c for c in df.columns if c.endswith("_rank")], errors="ignore")
    num = df.drop(columns=["measure_type"]).groupby(keys, dropna=False).first()
    return num.reset_index()


def build_lineups(seasons=ALL_SEASONS) -> pd.DataFrame:
    li = _concat(M.NBA_LINEUPS, seasons)
    li = li[li["per_mode"].eq("totals")]
    keys = ["season", "season_type", "team_id", "group_id"]
    w = _wide_by_measure(li, keys)
    w["team"] = w["team_id"].map(NBA_TEAM_IDS).fillna(w["team_abbreviation"].map(normalize_tricode))
    ids = w["group_id"].str.strip("-").str.split("-", expand=True)
    for i in range(5):
        w[f"player{i+1}_id"] = pd.to_numeric(ids[i], errors="coerce").astype("Int64")
    w["player_ids"] = w["group_id"].str.strip("-").str.replace("-", ",")
    w = w.rename(columns={"group_name": "lineup_name", "min": "minutes"})
    drop = ["group_set", "per_mode", "team_abbreviation", "sum_time_played"]
    w = w.drop(columns=[c for c in drop if c in w.columns])
    first = ["season", "season_type", "team", "team_id", "group_id", "lineup_name", "player_ids",
             "player1_id", "player2_id", "player3_id", "player4_id", "player5_id", "gp", "w", "l", "minutes", "poss",
             "off_rating", "def_rating", "net_rating", "pace", "efg_pct", "ts_pct", "tm_tov_pct", "oreb_pct", "dreb_pct",
             "fta_rate", "opp_efg_pct", "opp_fta_rate", "opp_tov_pct", "opp_oreb_pct", "plus_minus", "pts", "opp_pts"]
    rest = [c for c in w.columns if c not in first]
    w = w[[c for c in first if c in w.columns] + rest]
    return w.sort_values(["season", "team", "minutes"], ascending=[True, True, False]).reset_index(drop=True)


def build_team_seasons(seasons=ALL_SEASONS) -> pd.DataFrame:
    ts = _concat(M.NBA_TEAM_SEASON, seasons)
    ts = ts[ts["per_mode"].eq("totals")]
    keys = ["season", "season_type", "team_id"]
    w = _wide_by_measure(ts, keys)
    w["team"] = w["team_id"].map(NBA_TEAM_IDS)
    w = w.drop(columns=[c for c in ["per_mode"] if c in w.columns])
    cols = ["season", "season_type", "team", "team_id", "team_name"] + [c for c in w.columns if c not in ["season", "season_type", "team", "team_id", "team_name"]]
    return w[cols].sort_values(["season", "team"]).reset_index(drop=True)


# ----------------------------------------------------------------------------- injuries
def build_injuries(seasons=ALL_SEASONS) -> pd.DataFrame:
    inj = _concat(M.NBA_INJURY_REPORT, seasons)
    inj["team"] = inj["team_id"].map(NBA_TEAM_IDS)
    inj["game_id"] = inj["game_id"].astype("string").str.zfill(10)
    inj["game_date"] = pd.to_datetime(inj["game_date"]).dt.date.astype(str)
    inj["report_datetime"] = pd.to_datetime(inj["report_datetime"])
    inj["player_name"] = inj["report_player_name"].fillna("")
    # "Last, First" -> "First Last"
    swap = inj["player_name"].str.contains(",")
    inj.loc[swap, "player_name"] = inj.loc[swap, "player_name"].str.split(",").map(lambda p: (p[1].strip() + " " + p[0].strip()) if len(p) == 2 else ",".join(p))
    inj["status"] = inj["current_status"].fillna("").str.title()
    inj["reason"] = inj["reason"].fillna("")
    inj["reason_category"] = np.select(
        [inj["reason"].str.startswith("Injury/Illness"), inj["reason"].str.startswith("G League"),
         inj["reason"].str.contains("Personal"), inj["reason"].str.contains("Suspension"),
         inj["reason"].str.contains("Rest"), inj["reason"].eq("NOT YET SUBMITTED")],
        ["injury", "gleague", "personal", "suspension", "rest", "not_submitted"], default="other")
    inj["submitted"] = ~inj["reason"].eq("NOT YET SUBMITTED")
    cols = ["season", "report_datetime", "game_date", "game_id", "report_matchup", "team", "team_id", "player_name",
            "person_id", "status", "previous_status", "reason", "reason_category", "submitted", "match_method"]
    out = inj[cols].rename(columns={"person_id": "player_id"})
    return out.sort_values(["report_datetime", "game_date", "team"]).reset_index(drop=True)


# ----------------------------------------------------------------------------- orchestration
def build_all(seasons=ALL_SEASONS, write: bool = True) -> dict[str, pd.DataFrame]:
    games = build_games(seasons)
    out = {
        "games": games,
        "teams": build_teams(games, seasons),
        "players": build_players(games, seasons),
        "lineups": build_lineups(seasons),
        "team_seasons": build_team_seasons(seasons),
        "injuries": build_injuries(seasons),
    }
    if write:
        PARQUET_DIR.mkdir(parents=True, exist_ok=True)
        manifest = {"built_at_utc": datetime.now(timezone.utc).isoformat(), "seasons": list(seasons), "tables": {}}
        for name, df in out.items():
            path = PARQUET_DIR / f"{name}.parquet"
            df.to_parquet(path, index=False, compression="zstd")
            manifest["tables"][name] = {"rows": int(len(df)), "columns": list(map(str, df.columns)),
                                        "bytes": path.stat().st_size,
                                        "max_game_date": str(df["game_date"].max()) if "game_date" in df else None}
            log.info("wrote %s (%d rows, %.1f MB)", path.name, len(df), path.stat().st_size / 1e6)
        (PARQUET_DIR / "MANIFEST.json").write_text(json.dumps(manifest, indent=2))
    return out


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    build_all()

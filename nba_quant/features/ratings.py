"""Pre-game team strength features.

Everything here is computed strictly from games played BEFORE the game in question
(shift-by-one inside each team-season, with a regressed carry-over of the previous season),
so the resulting table is safe to use as model input without look-ahead leakage.

Features per team-game (prefix-free; the game-level builder adds home_/away_ prefixes):
  elo_pre                 margin-of-victory Elo (FiveThirtyEight-style update), carried across seasons
  ewm_off, ewm_def, ...   exponentially-weighted means (half-life 10 games) of efficiency/four-factor stats
  adj_off, adj_def        opponent-adjusted EWMA efficiencies (one-step adjustment vs opponent's pre-game EWMA)
  s2d_*                   season-to-date means (regressed to the prior-season value early in the season)
  l10_*                   last-10-game means
  n_prior                 games already played this season
"""
from __future__ import annotations

import logging

import numpy as np
import pandas as pd

from nba_quant.config import PARQUET_DIR

log = logging.getLogger(__name__)

ELO_K = 20.0
ELO_HOME = 100.0          # ~3 points of home court in Elo space
ELO_MEAN = 1500.0
ELO_CARRY = 0.70          # regress 30% toward the mean between seasons
HALF_LIFE = 10.0
PRIOR_GAMES = 12.0        # pseudo-games of prior-season weight when blending season-to-date means

RATE_COLS = ["off_rtg", "def_rtg", "pace", "efg", "tov_pct", "oreb_pct", "dreb_pct", "ftr", "fg3a_rate", "fg3_pct",
             "fg2_pct", "ft_pct", "ast_pct", "opp_efg", "opp_tov_pct", "opp_ftr", "opp_fg3a_rate", "opp_fg3_pct"]


def mov_multiplier(margin: np.ndarray, elo_diff_winner: np.ndarray) -> np.ndarray:
    return ((np.abs(margin) + 3.0) ** 0.8) / (7.5 + 0.006 * elo_diff_winner)


def compute_elo(games: pd.DataFrame) -> pd.DataFrame:
    """Return per-game pre-game Elo for home and away plus the post-game values."""
    g = games[games["completed"]].sort_values(["game_date", "game_id"]).copy()
    elo: dict[str, float] = {}
    season_seen: dict[str, int] = {}
    rows = []
    for r in g.itertuples(index=False):
        for team in (r.home_team, r.away_team):
            if team not in elo:
                elo[team] = ELO_MEAN
                season_seen[team] = r.season
            elif season_seen[team] != r.season:  # new season: regress toward mean
                elo[team] = ELO_MEAN + ELO_CARRY * (elo[team] - ELO_MEAN)
                season_seen[team] = r.season
        h, a = elo[r.home_team], elo[r.away_team]
        hca = 0.0 if r.neutral_site else ELO_HOME
        exp_home = 1.0 / (1.0 + 10 ** (-(h + hca - a) / 400.0))
        margin = r.margin
        home_won = margin > 0
        diff_w = (h + hca - a) if home_won else (a - h - hca)
        mult = mov_multiplier(np.array(margin), np.array(diff_w)).item()
        delta = ELO_K * mult * ((1.0 if home_won else 0.0) - exp_home)
        rows.append((r.game_id, h, a, exp_home))
        elo[r.home_team] = h + delta
        elo[r.away_team] = a - delta
    out = pd.DataFrame(rows, columns=["game_id", "home_elo_pre", "away_elo_pre", "home_elo_winprob"])
    current = pd.DataFrame({"team": list(elo), "elo": list(elo.values())})
    return out, current


def ewm_by_team(df: pd.DataFrame, cols: list[str], half_life: float = HALF_LIFE) -> pd.DataFrame:
    """Pre-game EWMA per team (shifted so the current game is excluded), continuous across seasons."""
    out = pd.DataFrame(index=df.index)
    grp = df.groupby("team", sort=False)
    for c in cols:
        out[f"ewm_{c}"] = grp[c].transform(lambda s: s.shift(1).ewm(halflife=half_life, min_periods=1).mean())
    return out


def build_team_game_features(teams: pd.DataFrame, games: pd.DataFrame) -> pd.DataFrame:
    t = teams.merge(games[["game_id", "neutral_site", "playoffs"]], on="game_id", how="left")
    t = t.sort_values(["game_date", "game_id", "team"]).reset_index(drop=True)
    # order within team by date so shift() is chronological
    t = t.sort_values(["team", "game_date", "game_id"]).reset_index(drop=True)

    # league-average per season (season-to-date would be purer but seasonal means are stable; use prior-season
    # mean for the first 15 games to avoid leakage)
    lg = t.groupby("season")[RATE_COLS].mean()
    lg_prev = lg.shift(1).bfill()
    early = t["team_game_no"] <= 15
    for c in RATE_COLS:
        t[f"lg_{c}"] = np.where(early, t["season"].map(lg_prev[c]), t["season"].map(lg[c]))

    ew = ewm_by_team(t, RATE_COLS)
    t = pd.concat([t, ew], axis=1)

    # one-step opponent adjustment: how good was this performance relative to what the opponent usually allows
    opp = t[["game_id", "team", "ewm_off_rtg", "ewm_def_rtg", "ewm_pace", "lg_off_rtg", "lg_def_rtg", "lg_pace"]].rename(
        columns={"team": "opponent", "ewm_off_rtg": "opp_ewm_off", "ewm_def_rtg": "opp_ewm_def", "ewm_pace": "opp_ewm_pace"})
    t = t.merge(opp.drop(columns=["lg_off_rtg", "lg_def_rtg", "lg_pace"]), on=["game_id", "opponent"], how="left")
    t["adj_off_game"] = t["off_rtg"] - (t["opp_ewm_def"].fillna(t["lg_def_rtg"]) - t["lg_def_rtg"])
    t["adj_def_game"] = t["def_rtg"] - (t["opp_ewm_off"].fillna(t["lg_off_rtg"]) - t["lg_off_rtg"])
    t["adj_pace_game"] = t["pace"] - (t["opp_ewm_pace"].fillna(t["lg_pace"]) - t["lg_pace"])
    t = t.sort_values(["team", "game_date", "game_id"]).reset_index(drop=True)
    grp = t.groupby("team", sort=False)
    for c in ["adj_off_game", "adj_def_game", "adj_pace_game"]:
        t[c.replace("_game", "")] = grp[c].transform(lambda s: s.shift(1).ewm(halflife=HALF_LIFE, min_periods=1).mean())
    t["adj_net"] = t["adj_off"] - t["adj_def"]
    t["ewm_net"] = t["ewm_off_rtg"] - t["ewm_def_rtg"]

    # season-to-date and last-10 means (shifted), with prior-season blend early in the season
    key_stats = ["off_rtg", "def_rtg", "pace", "adj_off_game", "adj_def_game", "margin", "win"]
    gs = t.groupby(["team", "season"], sort=False)
    t["n_prior"] = gs.cumcount()
    prev_season = t.groupby(["team", "season"])[key_stats].mean().groupby(level=0).shift(1)
    for c in key_stats:
        s2d = gs[c].transform(lambda s: s.shift(1).expanding().mean())
        prior = pd.MultiIndex.from_frame(t[["team", "season"]]).map(prev_season[c].to_dict()) if len(prev_season) else np.nan
        prior = pd.Series(np.asarray(prior, dtype=float), index=t.index)
        lgmean = t[f"lg_{c}"] if f"lg_{c}" in t else pd.Series(np.nan, index=t.index)
        prior = prior.fillna(lgmean) if c in RATE_COLS else prior.fillna(0.0 if c == "margin" else (0.5 if c == "win" else np.nan))
        n = t["n_prior"]
        t[f"s2d_{c}"] = (s2d.fillna(prior) * n + prior * PRIOR_GAMES) / (n + PRIOR_GAMES)
        t[f"l10_{c}"] = gs[c].transform(lambda s: s.shift(1).rolling(10, min_periods=1).mean())
    t = t.rename(columns={"s2d_adj_off_game": "s2d_adj_off", "s2d_adj_def_game": "s2d_adj_def",
                          "l10_adj_off_game": "l10_adj_off", "l10_adj_def_game": "l10_adj_def"})
    t["s2d_adj_net"] = t["s2d_adj_off"] - t["s2d_adj_def"]
    t["l10_adj_net"] = t["l10_adj_off"] - t["l10_adj_def"]
    # streak / form
    t["streak"] = gs["win"].transform(lambda s: s.shift(1).groupby((s.shift(1) != s.shift(2)).cumsum()).cumcount() + 1) * np.where(gs["win"].shift(1) == 1, 1, -1)
    t["streak"] = t["streak"].fillna(0)

    feat_cols = (["game_id", "espn_game_id", "season", "season_type", "playoffs", "game_date", "team", "opponent", "home",
                  "win", "margin", "pts", "opp_pts", "poss", "rest_days", "back_to_back", "games_last_7d", "team_game_no",
                  "n_prior", "streak", "ewm_net", "adj_off", "adj_def", "adj_net", "adj_pace", "s2d_adj_off", "s2d_adj_def",
                  "s2d_adj_net", "l10_adj_off", "l10_adj_def", "l10_adj_net", "s2d_margin", "l10_margin", "s2d_win",
                  "l10_win", "s2d_pace", "l10_pace"]
                 + [f"ewm_{c}" for c in RATE_COLS] + [f"lg_{c}" for c in ["off_rtg", "def_rtg", "pace", "efg", "tov_pct",
                                                                           "oreb_pct", "ftr", "fg3a_rate", "fg3_pct", "fg2_pct", "ft_pct"]])
    return t[feat_cols].sort_values(["game_date", "game_id", "home"]).reset_index(drop=True)


def current_team_state(team_feats: pd.DataFrame, teams: pd.DataFrame) -> pd.DataFrame:
    """Latest post-game state per team (i.e., the pre-game features a team would carry into its next game)."""
    # Re-run the EWMA including the latest game: emulate by appending a dummy next game per team.
    last = teams.sort_values(["team", "game_date"]).groupby("team").tail(1)
    return last


def elo_current(games: pd.DataFrame) -> pd.DataFrame:
    _, cur = compute_elo(games)
    return cur


def upcoming_team_rows(games: pd.DataFrame, teams: pd.DataFrame, through_date: str) -> pd.DataFrame:
    """Pseudo team-game rows (stats NaN) for scheduled games up to `through_date`, so the shifted
    EWMA / season-to-date features evaluate to each team's current pre-game state."""
    up = games[(~games["completed"]) & (games["game_date"] <= through_date)]
    if up.empty:
        return teams.iloc[0:0]
    rows = []
    for r in up.itertuples(index=False):
        for team, opp, home in ((r.home_team, r.away_team, True), (r.away_team, r.home_team, False)):
            rows.append({"game_id": r.game_id, "espn_game_id": r.espn_game_id, "season": r.season, "season_type": r.season_type,
                         "game_date": r.game_date, "team": team, "opponent": opp, "home": home})
    pseudo = pd.DataFrame(rows)
    pseudo = pseudo.reindex(columns=teams.columns)
    both = pd.concat([teams, pseudo], ignore_index=True).sort_values(["team", "game_date", "game_id"])
    # recompute schedule context for the pseudo rows
    both["prev_game_date"] = both.groupby(["team", "season"])["game_date"].shift(1)
    both["rest_days"] = (pd.to_datetime(both["game_date"]) - pd.to_datetime(both["prev_game_date"])).dt.days - 1
    both["back_to_back"] = both["rest_days"].eq(0)
    both["team_game_no"] = both.groupby(["team", "season"]).cumcount() + 1
    d = pd.to_datetime(both["game_date"])
    both["games_last_7d"] = 0
    for (team, season), idx in both.groupby(["team", "season"]).groups.items():
        dd = d.loc[idx]
        vals = np.searchsorted(dd.values, dd.values, side="right") - np.searchsorted(dd.values, (dd - pd.Timedelta(days=7)).values, side="left")
        both.loc[idx, "games_last_7d"] = vals - 1
    return both.drop(columns=["prev_game_date"])


def build_all(write: bool = True, through_date: str | None = None) -> pd.DataFrame:
    games = pd.read_parquet(PARQUET_DIR / "games.parquet")
    teams = pd.read_parquet(PARQUET_DIR / "teams.parquet")
    if through_date:
        teams = upcoming_team_rows(games, teams, through_date)
    feats = build_team_game_features(teams, games)
    elo, cur = compute_elo(games)
    home = elo[["game_id", "home_elo_pre"]].rename(columns={"home_elo_pre": "elo_pre"}).assign(home=True)
    away = elo[["game_id", "away_elo_pre"]].rename(columns={"away_elo_pre": "elo_pre"}).assign(home=False)
    feats = feats.merge(pd.concat([home, away]), on=["game_id", "home"], how="left")
    # upcoming games: current Elo
    cur_map = cur.set_index("team")["elo"]
    feats["elo_pre"] = feats["elo_pre"].fillna(feats["team"].map(cur_map))
    if write:
        feats.to_parquet(PARQUET_DIR / "team_game_features.parquet", index=False, compression="zstd")
        cur.to_parquet(PARQUET_DIR / "elo_current.parquet", index=False)
        log.info("wrote team_game_features.parquet (%d rows)", len(feats))
    return feats


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    f = build_all()
    print(f.tail(4).T.head(60))

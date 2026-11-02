"""Game-level feature matrix for the win-probability / spread / total models.

One row per game (completed games for training; scheduled games through `through_date` for
prediction). Every feature is known before tip-off:
  * team strength: MOV-Elo, opponent-adjusted EWMA efficiencies, season-to-date / last-10 form
  * schedule: rest days, back-to-back, games in last 7 days, games into season, streak
  * shot profile (for totals): 3PA rate, eFG, TOV, OREB, FT rate, opponent versions
  * availability (official injury report, last version before tip): value of rotation players
    Out/Doubtful, Questionable bucket, counts, best missing player
  * coaching: composite indices and simulator primitives for the head coach of each side
  * market reference (ESPN closing spread) kept as a column, NOT used by the market-free model
"""
from __future__ import annotations

import logging
from datetime import date

import numpy as np
import pandas as pd

from nba_quant.config import PARQUET_DIR
from nba_quant.features import ratings

log = logging.getLogger(__name__)

SIDE_FEATURES = ["elo_pre", "adj_off", "adj_def", "adj_net", "adj_pace", "ewm_net", "s2d_adj_net", "l10_adj_net", "s2d_win",
                 "l10_margin", "s2d_margin", "ewm_efg", "ewm_tov_pct", "ewm_oreb_pct", "ewm_ftr", "ewm_fg3a_rate", "ewm_fg3_pct",
                 "ewm_fg2_pct", "ewm_ft_pct", "ewm_opp_efg", "ewm_opp_tov_pct", "ewm_opp_fg3a_rate", "ewm_opp_ftr", "ewm_dreb_pct",
                 "rest_days", "back_to_back", "games_last_7d", "n_prior", "streak",
                 "out_val", "q_val", "out_n", "q_n", "out_star", "out_min",
                 "coach_overall", "coach_strategy", "coach_rotation", "coach_endgame", "coach_pace", "coach_three", "coach_foul_up3",
                 "coach_clutch", "coach_star_load"]
LEAGUE_COLS = ["lg_off_rtg", "lg_def_rtg", "lg_pace", "lg_efg", "lg_tov_pct", "lg_oreb_pct", "lg_ftr", "lg_fg3a_rate", "lg_fg3_pct",
               "lg_fg2_pct", "lg_ft_pct"]


def coach_lookup() -> tuple[pd.DataFrame, pd.DataFrame]:
    coaches = pd.read_parquet(PARQUET_DIR / "coaches.parquet")
    attr = pd.read_parquet(PARQUET_DIR / "coach_game_attribution.parquet")
    cols = {"overall_coaching_score": "coach_overall", "strategy_index": "coach_strategy", "rotation_index": "coach_rotation",
            "endgame_index": "coach_endgame", "sim_pace_score": "coach_pace", "sim_three_score": "coach_three",
            "sim_foul_up3_score": "coach_foul_up3", "sim_clutch_score": "coach_clutch", "star_load_index": "coach_star_load"}
    c = coaches[["slug", "coach", "team"] + list(cols)].rename(columns=cols)
    return c, attr


def attach_coaches(tgf: pd.DataFrame, games: pd.DataFrame) -> pd.DataFrame:
    c, attr = coach_lookup()
    by_slug = c.set_index("slug")
    cur_by_team = c.drop_duplicates("team").set_index("team")   # current head coach per team (for upcoming games)
    t = tgf.merge(attr[["game_id", "team", "slug"]], on=["game_id", "team"], how="left")
    # upcoming / unattributed games -> current coach
    miss = t["slug"].isna()
    t.loc[miss, "slug"] = t.loc[miss, "team"].map(cur_by_team["slug"])
    feat_cols = [c_ for c_ in c.columns if c_.startswith("coach_")]
    for col in feat_cols:
        t[col] = t["slug"].map(by_slug[col])
    t["coach_name"] = t["slug"].map(by_slug["coach"])
    return t


def build(through_date: str | None = None, write: bool = True) -> pd.DataFrame:
    through_date = through_date or str(date.today())
    games = pd.read_parquet(PARQUET_DIR / "games.parquet")
    tgf = ratings.build_all(write=False, through_date=through_date)
    avail = pd.read_parquet(PARQUET_DIR / "availability_features.parquet")
    tgf = tgf.merge(avail, on=["game_id", "team"], how="left")
    for c in ["out_val", "q_val", "out_n", "q_n", "out_min", "q_min"]:
        tgf[c] = tgf[c].fillna(0.0)
    tgf["out_star"] = tgf["out_star"].fillna(-3.0)   # no notable absence
    tgf["rest_days"] = tgf["rest_days"].fillna(3).clip(upper=7)
    tgf["back_to_back"] = tgf["back_to_back"].fillna(False).astype(int)
    tgf = attach_coaches(tgf, games)

    home = tgf[tgf["home"]].set_index("game_id")
    away = tgf[~tgf["home"]].set_index("game_id")
    g = games.set_index("game_id")
    idx = home.index.intersection(away.index)
    base = g.loc[idx, ["espn_game_id", "season", "season_type", "playoffs", "game_date", "start_time_utc", "completed", "home_team", "away_team",
                       "home_score", "away_score", "home_win", "margin", "total", "home_exp_margin_market", "home_spread_market", "neutral_site"]].copy()
    for col in SIDE_FEATURES:
        base[f"home_{col}"] = home.loc[idx, col].astype(float)
        base[f"away_{col}"] = away.loc[idx, col].astype(float)
    for col in LEAGUE_COLS:
        base[col] = home.loc[idx, col].astype(float)
    base["home_coach"] = home.loc[idx, "coach_name"]; base["away_coach"] = away.loc[idx, "coach_name"]
    # differences & sums
    for col in ["elo_pre", "adj_net", "s2d_adj_net", "l10_adj_net", "ewm_net", "s2d_win", "l10_margin", "rest_days", "games_last_7d",
                "out_val", "q_val", "coach_overall", "coach_strategy", "coach_endgame", "streak"]:
        base[f"diff_{col}"] = base[f"home_{col}"] - base[f"away_{col}"]
    base["sum_adj_pace"] = base["home_adj_pace"] + base["away_adj_pace"]
    base["sum_off"] = base["home_adj_off"] + base["away_adj_off"]
    base["sum_def"] = base["home_adj_def"] + base["away_adj_def"]
    base["sum_fg3a_rate"] = base["home_ewm_fg3a_rate"] + base["away_ewm_fg3a_rate"]
    base["exp_total_naive"] = (base["home_adj_off"] + base["away_adj_def"] - base["lg_off_rtg"] + base["away_adj_off"] + base["home_adj_def"] - base["lg_off_rtg"]) * base["sum_adj_pace"] / 2 / 100 * 1.0
    base["exp_total_naive"] = ((base["home_adj_off"] + base["away_adj_def"]) / 2 + (base["away_adj_off"] + base["home_adj_def"]) / 2) * (base["sum_adj_pace"] - base["lg_pace"]) / 100
    base["exp_margin_naive"] = ((base["home_adj_off"] - base["away_adj_def"]) + (base["away_adj_def"] - base["home_adj_def"]) ) / 2  # placeholder, refined below
    base["exp_margin_naive"] = ((base["home_adj_net"] - base["away_adj_net"]) / 2) * (base["sum_adj_pace"] - base["lg_pace"]) / 100
    base["playoffs"] = base["playoffs"].astype(int); base["neutral_site"] = base["neutral_site"].astype(int)
    base = base.reset_index().sort_values(["game_date", "game_id"]).reset_index(drop=True)
    if write:
        base.to_parquet(PARQUET_DIR / "game_features.parquet", index=False, compression="zstd")
        log.info("wrote game_features.parquet (%d rows; %d completed, %d upcoming)", len(base), base["completed"].sum(), (~base["completed"]).sum())
    return base


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    pd.set_option("display.width", 250); pd.set_option("display.max_columns", 50)
    f = build()
    up = f[~f["completed"]]
    print(up[["game_date", "away_team", "home_team", "home_elo_pre", "away_elo_pre", "home_adj_net", "away_adj_net", "home_out_val", "away_out_val",
              "home_q_val", "away_q_val", "home_rest_days", "away_rest_days", "home_coach", "away_coach", "exp_margin_naive", "exp_total_naive"]].round(2).to_string())
    print(f[f.completed][["home_win", "margin", "total", "diff_elo_pre", "diff_adj_net", "home_out_val", "exp_margin_naive"]].corr().round(3))

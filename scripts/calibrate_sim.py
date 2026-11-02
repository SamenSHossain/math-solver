"""Calibrate the Monte Carlo simulator against five seasons of actual results.

Empirical targets: sd of (actual margin - market expected margin), overtime rate, share of games
decided by <= 3 points. The sim is run on a random sample of historical games using only pre-game
team profiles (no market input) for a grid of restoring-force values.
"""
from __future__ import annotations

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import numpy as np
import pandas as pd

from nba_quant.config import PARQUET_DIR
from nba_quant.sim.possession import LeagueAverages, profile_from_row, simulate

games = pd.read_parquet(PARQUET_DIR / "games.parquet")
tgf = pd.read_parquet(PARQUET_DIR / "team_game_features.parquet")
done = games[games["completed"] & (games["season_type"] == "regular")]
res = done["margin"] - done["home_exp_margin_market"]
print(f"EMPIRICAL  n={len(done)}  sd(margin-market)={res.std():.2f}  sd(margin)={done['margin'].std():.2f}  "
      f"sd(total)={done['total'].std():.2f}  OT rate={(done['overtime_periods']>0).mean():.3f}  "
      f"P(|margin|<=3)={(done['margin'].abs()<=3).mean():.3f}  mean home margin={done['margin'].mean():.2f}")
by = done.groupby("season").agg(sd_res=("margin", lambda s: (s - done.loc[s.index, "home_exp_margin_market"]).std()),
                                ot=("overtime_periods", lambda s: (s > 0).mean()), tot_sd=("total", "std"), hca=("margin", "mean"))
print(by.round(3))

rng = np.random.default_rng(0)
sample = done[done["season"].isin([2024, 2025, 2026])].sample(240, random_state=1)
home_rows = tgf[tgf["home"]].set_index("game_id")
away_rows = tgf[~tgf["home"]].set_index("game_id")
lg_by_season = {s: LeagueAverages(off_rtg=float(tgf.loc[tgf.season == s, "lg_off_rtg"].iloc[-1]), pace=float(tgf.loc[tgf.season == s, "lg_pace"].iloc[-1]),
                                  fg3a_rate=float(tgf.loc[tgf.season == s, "lg_fg3a_rate"].iloc[-1]), fg3_pct=float(tgf.loc[tgf.season == s, "lg_fg3_pct"].iloc[-1]),
                                  fg2_pct=float(tgf.loc[tgf.season == s, "lg_fg2_pct"].iloc[-1]), ftr=float(tgf.loc[tgf.season == s, "lg_ftr"].iloc[-1]),
                                  ft_pct=float(tgf.loc[tgf.season == s, "lg_ft_pct"].iloc[-1]), tov_pct=float(tgf.loc[tgf.season == s, "lg_tov_pct"].iloc[-1]),
                                  oreb_pct=float(tgf.loc[tgf.season == s, "lg_oreb_pct"].iloc[-1]), home_court=float(by.loc[s, "hca"]))
                for s in [2024, 2025, 2026]}
kappas = [float(k) for k in sys.argv[1:]] or [0.0, 0.002, 0.0035, 0.005, 0.007]
for kappa in kappas:
    sim_sd, sim_tot_sd, ot, close, resid, resid_tot, mean_poss, act_poss = [], [], [], [], [], [], [], []
    for g in sample.itertuples():
        if g.game_id not in home_rows.index or g.game_id not in away_rows.index:
            continue
        lg = lg_by_season[g.season]
        h = profile_from_row(g.home_team, home_rows.loc[g.game_id], lg)
        a = profile_from_row(g.away_team, away_rows.loc[g.game_id], lg)
        r = simulate(h, a, lg, n_sims=3000, seed=int(rng.integers(1e9)), kappa=kappa)
        sim_sd.append(r["margin_sd"]); sim_tot_sd.append(r["total_sd"]); ot.append(r["ot_rate"])
        close.append(float((np.abs(r["margin_samples"]) <= 3).mean()))
        resid.append(g.margin - r["mean_margin"]); resid_tot.append(g.total - r["mean_total"])
        mean_poss.append(r["expected_poss"])
    print(f"kappa={kappa:.4f}  sim margin sd={np.mean(sim_sd):.2f}  realised resid sd={np.std(resid):.2f}  sim total sd={np.mean(sim_tot_sd):.2f}  "
          f"realised total resid sd={np.std(resid_tot):.2f}  mean total resid={np.mean(resid_tot):+.2f}  mean margin resid={np.mean(resid):+.2f}  "
          f"OT={np.mean(ot):.3f}  P(|m|<=3)={np.mean(close):.3f}  n={len(resid)}")

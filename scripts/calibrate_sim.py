"""Calibrate the Monte Carlo simulator against actual results (batched, fast).

Targets: realised residual sd of margin (actual - sim mean) should equal the sim's own margin sd;
share of games decided by <= 3; overtime rate; realised total residual sd vs sim total sd.
Usage: python scripts/calibrate_sim.py [n_games] [kappa_end,form_sd ...]
"""
from __future__ import annotations

import sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import numpy as np
import pandas as pd

from nba_quant.config import PARQUET_DIR
from nba_quant.sim.possession import league_from_row, profile_from_row, simulate_batch

games = pd.read_parquet(PARQUET_DIR / "games.parquet")
tgf = pd.read_parquet(PARQUET_DIR / "team_game_features.parquet")
done = games[games["completed"] & (games["season_type"] == "regular")]
res = done["margin"] - done["home_exp_margin_market"]
print(f"EMPIRICAL n={len(done)} sd(margin-market)={res.std():.2f} OT={(done['overtime_periods']>0).mean():.3f} "
      f"P(|m|<=3)={(done['margin'].abs()<=3).mean():.3f} P(|m|<=1)={(done['margin'].abs()<=1).mean():.3f} home margin={done['margin'].mean():.2f} total sd={done['total'].std():.2f}")
hca = done.groupby("season")["margin"].mean()
n_games = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
configs = [tuple(map(float, a.split(","))) for a in sys.argv[2:]] or [(0.0045, 0.03), (0.003, 0.03), (0.006, 0.03), (0.0045, 0.02), (0.0045, 0.04)]
sample = done[(done["season"] >= 2023) & (done["game_number_season"] > 150)].sample(n_games, random_state=1)
home_rows = tgf[tgf["home"]].set_index("game_id"); away_rows = tgf[~tgf["home"]].set_index("game_id")
sample = sample[sample["game_id"].isin(home_rows.index) & sample["game_id"].isin(away_rows.index)]
homes, aways, lgs = [], [], []
for g in sample.itertuples():
    lg = league_from_row(home_rows.loc[g.game_id], home_court=float(hca.loc[g.season]))
    homes.append(profile_from_row(g.home_team, home_rows.loc[g.game_id], lg))
    aways.append(profile_from_row(g.away_team, away_rows.loc[g.game_id], lg))
    lgs.append(lg)
for kappa_end, form_sd in configs:
    t0 = time.time()
    out = simulate_batch(homes, aways, lgs, n_sims=300, seed=11, kappa_end=kappa_end, form_sd=form_sd, return_samples=True)
    mm = np.array([o["mean_margin"] for o in out]); mt = np.array([o["mean_total"] for o in out])
    sd_m = np.mean([o["margin_sd"] for o in out]); sd_t = np.mean([o["total_sd"] for o in out])
    ot = np.mean([o["ot_rate"] for o in out])
    close3 = np.mean([(np.abs(o["margin_samples"]) <= 3).mean() for o in out]); close1 = np.mean([(np.abs(o["margin_samples"]) <= 1).mean() for o in out])
    wp = np.array([o["home_win_prob"] for o in out]); y = (sample["margin"] > 0).to_numpy().astype(float)
    ll = -np.mean(y * np.log(np.clip(wp, 1e-6, 1)) + (1 - y) * np.log(np.clip(1 - wp, 1e-6, 1)))
    rm = sample["margin"].to_numpy() - mm; rt = sample["total"].to_numpy() - mt
    print(f"kappa_end={kappa_end:.4f} form_sd={form_sd:.3f} | sim margin sd={sd_m:.2f} realised resid sd={rm.std():.2f} bias={rm.mean():+.2f} | "
          f"sim total sd={sd_t:.2f} realised={rt.std():.2f} bias={rt.mean():+.2f} | OT={ot:.3f} P(|m|<=3)={close3:.3f} P(|m|<=1)={close1:.3f} | "
          f"logloss={ll:.4f} MAE margin={np.abs(rm).mean():.2f} | {time.time()-t0:.0f}s")

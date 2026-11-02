"""Simulate every completed game from its pre-game team profiles (no market, no injuries) in batches and
store sim_home_wp / sim_margin / sim_total as model features (data/parquet/sim_features.parquet)."""
from __future__ import annotations

import sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import numpy as np
import pandas as pd

from nba_quant.config import PARQUET_DIR
from nba_quant.sim.possession import league_from_row, profile_from_row, simulate_batch

N_SIMS = int(sys.argv[1]) if len(sys.argv) > 1 else 300
CHUNK = 400
games = pd.read_parquet(PARQUET_DIR / "games.parquet")
tgf = pd.read_parquet(PARQUET_DIR / "team_game_features.parquet")
done = games[games["completed"]].sort_values(["game_date", "game_id"])
hca = done[done["season_type"] == "regular"].groupby("season")["margin"].mean()
home_rows = tgf[tgf["home"]].set_index("game_id"); away_rows = tgf[~tgf["home"]].set_index("game_id")
done = done[done["game_id"].isin(home_rows.index) & done["game_id"].isin(away_rows.index)]
rows = []
t0 = time.time()
ids = done["game_id"].tolist()
for start in range(0, len(ids), CHUNK):
    chunk = done.iloc[start:start + CHUNK]
    homes, aways, lgs, neutral = [], [], [], []
    for g in chunk.itertuples():
        # prior-season home court for the current season (unknown in-season)
        hc = float(hca.get(g.season, hca.iloc[-1])) if g.season in hca.index and g.season < hca.index.max() else float(hca.iloc[-2]) if len(hca) > 1 else 2.0
        lg = league_from_row(home_rows.loc[g.game_id], home_court=hc)
        homes.append(profile_from_row(g.home_team, home_rows.loc[g.game_id], lg))
        aways.append(profile_from_row(g.away_team, away_rows.loc[g.game_id], lg))
        lgs.append(lg); neutral.append(bool(g.neutral_site))
    out = simulate_batch(homes, aways, lgs, n_sims=N_SIMS, seed=1000 + start, neutral=neutral)
    for g, o in zip(chunk.itertuples(), out):
        rows.append({"game_id": g.game_id, "sim_home_wp": o["home_win_prob"], "sim_margin": o["mean_margin"], "sim_total": o["mean_total"],
                     "sim_margin_sd": o["margin_sd"], "sim_total_sd": o["total_sd"], "sim_ot_rate": o["ot_rate"]})
    print(f"{start + len(chunk)}/{len(ids)} games  {time.time() - t0:.0f}s", flush=True)
df = pd.DataFrame(rows)
df.to_parquet(PARQUET_DIR / "sim_features.parquet", index=False)
m = done.set_index("game_id").loc[df["game_id"]]
print("done; corr(sim_margin, margin)=", np.corrcoef(df["sim_margin"], m["margin"])[0, 1].round(3), " MAE margin=", np.abs(df["sim_margin"] - m["margin"].to_numpy()).mean().round(2),
      " MAE total=", np.abs(df["sim_total"] - m["total"].to_numpy()).mean().round(2))

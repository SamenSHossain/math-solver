"""Injury-scenario Monte Carlo for a slate of games.

For each game we build TeamProfiles from the pre-game feature row (ratings, shot profile, pace),
attach the head coach's simulator primitives (pace / three-point tilt / foul-up-3 / clutch), and apply
an availability adjustment derived from the official injury report:

    net adjustment (pts/100) = -K * sum_over_missing (value_i - replacement) * typical_share_i

with K = margin_per_out_val from models/calibration.json (estimated on five seasons of games).
Players listed Out/Doubtful are removed in every scenario. Each Questionable player is a binary
switch: we enumerate all in/out combinations (up to 4 switches per game; extra low-impact names are
folded into the expected case), simulate every scenario, and also report the probability-weighted
"expected" distribution using the historical play rate of Questionable listings (~57%).
"""
from __future__ import annotations

import itertools
import json
import logging

import numpy as np
import pandas as pd

from nba_quant.config import MODEL_DIR, PARQUET_DIR
from nba_quant.features.injuries import OUT_STATUSES, Q_STATUSES, REPLACEMENT, ROTATION_MIN
from nba_quant.sim.possession import LeagueAverages, TeamProfile, league_from_row, profile_from_row, simulate_batch

log = logging.getLogger(__name__)
MAX_SWITCHES = 4


def load_calibration() -> dict:
    p = MODEL_DIR / "calibration.json"
    if p.exists():
        return json.loads(p.read_text())
    return {"margin_per_out_val": 1.0}


def play_rates() -> dict:
    p = PARQUET_DIR / "status_play_rates.json"
    if p.exists():
        d = json.loads(p.read_text())
        return {k: float(v) for k, v in d.get("play_rate", {}).items()}
    return {"Questionable": 0.57, "Probable": 0.88, "Doubtful": 0.02, "Available": 0.85, "Out": 0.0}


def game_injury_lines(game_id: str, lines: pd.DataFrame) -> pd.DataFrame:
    l = lines[(lines["game_id"] == game_id) & (lines["typ_min"] >= ROTATION_MIN)].copy()
    l["impact"] = (l["value"] - REPLACEMENT) * l["typ_min"] / 48.0
    return l.sort_values("impact", ascending=False)


def team_profile(row: pd.Series, side: str, lg: LeagueAverages, coach_row: pd.Series | None) -> TeamProfile:
    pref = f"{side}_"
    sub = {k[len(pref):]: v for k, v in row.items() if k.startswith(pref)}
    prof = profile_from_row(row[f"{side}_team"], pd.Series(sub), lg)
    if coach_row is not None:
        prof.coach_pace = float(coach_row.get("sim_pace_score", 50)); prof.coach_three = float(coach_row.get("sim_three_score", 50))
        prof.coach_foul_up3 = float(coach_row.get("sim_foul_up3_score", 50)); prof.coach_clutch = float(coach_row.get("sim_clutch_score", 50))
    # rest: back-to-back teams play ~1 point worse (second night), long layoffs slightly worse too
    b2b = float(row.get(f"{side}_back_to_back", 0) or 0)
    prof.off_adjust = -0.6 * b2b; prof.def_adjust = -0.6 * b2b
    return prof


def scenarios_for_game(row: pd.Series, lines: pd.DataFrame, coaches: pd.DataFrame, n_sims: int = 5000, seed: int = 7,
                       k_avail: float | None = None, rates: dict | None = None, center: tuple[float, float] | None = None) -> dict:
    """Run all injury scenarios for one game.

    center=(margin, total): shift every scenario so the probability-weighted mixture mean matches the
    given margin/total (used to centre the simulation on the trained model's point estimates while
    keeping the simulated shape and the scenario deltas).
    """
    k_avail = abs(k_avail) if k_avail is not None else abs(load_calibration().get("margin_per_out_val", 1.0))
    rates = rates or play_rates()
    lg = league_from_row(row, home_court=2.2)
    coach_idx = coaches.set_index("team")
    profs = {}
    for side in ("home", "away"):
        team = row[f"{side}_team"]
        crow = coach_idx.loc[team] if team in coach_idx.index else None
        profs[side] = team_profile(row, side, lg, crow)
    gl = game_injury_lines(row["game_id"], lines)
    out_lines = gl[gl["status"].isin(OUT_STATUSES)]
    q_lines = gl[gl["status"].isin(Q_STATUSES | {"Probable"})]
    fixed = {side: float(out_lines[out_lines["team"] == row[f"{side}_team"]]["impact"].sum()) for side in ("home", "away")}
    # switches: questionable / probable rotation players, largest impact first
    q_lines = q_lines.sort_values("impact", ascending=False)
    switches = q_lines.head(MAX_SWITCHES)
    folded = q_lines.iloc[MAX_SWITCHES:]
    fold_exp = {side: float(sum((1 - rates.get(s, 0.57)) * imp for s, imp, t in zip(folded["status"], folded["impact"], folded["team"]) if t == row[f"{side}_team"]))
                for side in ("home", "away")}
    combos = list(itertools.product([1, 0], repeat=len(switches)))  # 1 = plays
    homes, aways, labels, probs = [], [], [], []
    for combo in combos:
        miss = {"home": fixed["home"] + fold_exp["home"], "away": fixed["away"] + fold_exp["away"]}
        p = 1.0; desc = []
        for plays, (_, sw) in zip(combo, switches.iterrows()):
            side = "home" if sw["team"] == row["home_team"] else "away"
            pr = rates.get(sw["status"], 0.57)
            if plays:
                p *= pr; desc.append(f"{sw['player_name']} IN")
            else:
                p *= (1 - pr); miss[side] += sw["impact"]; desc.append(f"{sw['player_name']} OUT")
        h = TeamProfile(**{**profs["home"].__dict__}); a = TeamProfile(**{**profs["away"].__dict__})
        h.availability_net_adjust = -k_avail * miss["home"]; a.availability_net_adjust = -k_avail * miss["away"]
        homes.append(h); aways.append(a); labels.append(", ".join(desc) if desc else "all listed players as reported"); probs.append(p)
    probs = np.array(probs); probs = probs / probs.sum()
    neutral = [bool(row.get("neutral_site", 0))] * len(homes)
    shift_m = shift_t = 0.0
    if center is not None:
        pass1 = simulate_batch(homes, aways, lg, n_sims=min(n_sims, 2000), seed=seed + 1, neutral=neutral)
        exp_m1 = float(sum(p * r["mean_margin"] for p, r in zip(probs, pass1))); exp_t1 = float(sum(p * r["mean_total"] for p, r in zip(probs, pass1)))
        shift_m, shift_t = center[0] - exp_m1, center[1] - exp_t1
        poss = pass1[0]["expected_poss"]
        for h, a in zip(homes, aways):   # points -> points per 100 possessions on each offence
            h.off_adjust += (shift_t / 2 + shift_m / 2) * 100.0 / poss
            a.off_adjust += (shift_t / 2 - shift_m / 2) * 100.0 / poss
    res = simulate_batch(homes, aways, lg, n_sims=n_sims, seed=seed, neutral=neutral, return_samples=True)
    # probability-weighted mixture of samples
    all_m = np.concatenate([r["margin_samples"] for r in res]); all_t = np.concatenate([r["total_samples"] for r in res])
    w = np.concatenate([np.full(n_sims, p / n_sims) for p in probs])
    exp_wp = float(np.sum(w * (all_m > 0))); exp_margin = float(np.sum(w * all_m)); exp_total = float(np.sum(w * all_t))
    # resample for a weighted mixture sample (for cover / over probabilities)
    rng = np.random.default_rng(seed)
    pick = rng.choice(len(all_m), size=min(len(all_m), 20000), p=w)
    scen = [{"label": lab, "probability": float(p), "home_win_prob": r["home_win_prob"], "mean_margin": r["mean_margin"], "mean_total": r["mean_total"],
             "margin_sd": r["margin_sd"], "total_sd": r["total_sd"], "ot_rate": r["ot_rate"], "home_mean": r["home_mean"], "away_mean": r["away_mean"],
             "home_avail_adjust": h.availability_net_adjust, "away_avail_adjust": a.availability_net_adjust}
            for lab, p, r, h, a in zip(labels, probs, res, homes, aways)]
    return {"game_id": row["game_id"], "home": row["home_team"], "away": row["away_team"], "game_date": str(row["game_date"]),
            "k_avail": k_avail, "center": center, "center_shift": {"margin": shift_m, "total": shift_t}, "out_lines": out_lines[["team", "player_name", "status", "reason", "typ_min", "value", "impact"]].to_dict("records"),
            "switch_lines": switches[["team", "player_name", "status", "reason", "typ_min", "value", "impact"]].to_dict("records"),
            "scenarios": scen, "expected": {"home_win_prob": exp_wp, "mean_margin": exp_margin, "mean_total": exp_total},
            "mixture_margin_samples": all_m[pick], "mixture_total_samples": all_t[pick],
            "profiles": {"home": profs["home"].__dict__, "away": profs["away"].__dict__}}


def run_slate(through_date: str, n_sims: int = 5000) -> list[dict]:
    gf = pd.read_parquet(PARQUET_DIR / "game_features.parquet")
    lines = pd.read_parquet(PARQUET_DIR / "pregame_injury_lines.parquet")
    coaches = pd.read_parquet(PARQUET_DIR / "coaches.parquet")
    slate = gf[(~gf["completed"]) & (gf["game_date"] <= through_date)]
    out = []
    for _, row in slate.iterrows():
        out.append(scenarios_for_game(row, lines, coaches, n_sims=n_sims))
    return out


if __name__ == "__main__":
    import sys
    logging.basicConfig(level=logging.INFO)
    date = sys.argv[1] if len(sys.argv) > 1 else "2026-11-02"
    res = run_slate(date, n_sims=3000)
    for r in res:
        print(f"\n{r['away']} @ {r['home']}  expected: home wp {r['expected']['home_win_prob']:.3f} margin {r['expected']['mean_margin']:+.1f} total {r['expected']['mean_total']:.1f}  (k={r['k_avail']:.2f})")
        for s in r["scenarios"]:
            print(f"   p={s['probability']:.2f} {s['label'][:70]:70s} wp={s['home_win_prob']:.3f} margin={s['mean_margin']:+.1f} total={s['mean_total']:.1f} adj=({s['home_avail_adjust']:+.1f},{s['away_avail_adjust']:+.1f})")

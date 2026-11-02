"""Slate predictions: XGBoost point estimates + injury-scenario Monte Carlo + Kelly sizing.

For every scheduled game through `date`:
  1. XGBoost win probability, margin and total from the pre-game feature row (injury report included).
  2. Monte Carlo scenarios (Out/Doubtful removed; each Questionable player in/out), centred on the
     XGBoost margin/total, giving the full score distribution, cover/over probabilities for any line,
     overtime rate and per-scenario deltas.
  3. Consensus = average of the XGBoost win probability and the scenario-weighted Monte Carlo win
     probability; predicted score from the centred distribution.
  4. If a lines file exists (data/lines/lines_<date>.csv: game_id or away/home, home_ml, away_ml,
     spread_home, spread_odds, total, total_odds) Kelly stakes are computed for the whole slate.
Outputs: data/predictions/predictions_<date>.json (+ latest.json) and predictions_<date>.parquet.
"""
from __future__ import annotations

import json
import logging
import shutil
from datetime import date, datetime, timezone

import numpy as np
import pandas as pd
from xgboost import XGBClassifier, XGBRegressor

from nba_quant.betting.kelly import Bet, american_to_decimal, portfolio_kelly
from nba_quant.config import DATA_DIR, MODEL_DIR, PARQUET_DIR, PRED_DIR, TEAM_NAMES
from nba_quant.sim.scenarios import scenarios_for_game

log = logging.getLogger(__name__)


def load_models():
    feats = json.loads((MODEL_DIR / "features.json").read_text())
    win = XGBClassifier(); win.load_model(MODEL_DIR / "xgb_win.json")
    margin = XGBRegressor(); margin.load_model(MODEL_DIR / "xgb_margin.json")
    total = XGBRegressor(); total.load_model(MODEL_DIR / "xgb_total.json")
    return feats, win, margin, total


def load_lines(day: str) -> pd.DataFrame | None:
    p = DATA_DIR / "lines" / f"lines_{day}.csv"
    if not p.exists():
        return None
    return pd.read_csv(p)


def hist(samples: np.ndarray, lo: int, hi: int, step: int = 1) -> dict:
    edges = np.arange(lo, hi + step, step)
    counts, _ = np.histogram(samples, bins=edges)
    return {"edges": edges.tolist(), "counts": counts.tolist()}


def predict_slate(day: str, n_sims: int = 10000) -> dict:
    feats, m_win, m_margin, m_total = load_models()
    gf = pd.read_parquet(PARQUET_DIR / "game_features.parquet")
    sim_feats = [f for f in feats if f.startswith("sim_")]
    if sim_feats:  # the live rows have no pre-computed sim features -> fill after a ratings-only sim below
        for f in sim_feats:
            if f not in gf:
                gf[f] = np.nan
    slate = gf[(~gf["completed"]) & (gf["game_date"] <= day)].copy()
    if slate.empty:
        log.warning("no scheduled games through %s", day)
        return {"date": day, "games": []}
    lines = pd.read_parquet(PARQUET_DIR / "pregame_injury_lines.parquet")
    coaches = pd.read_parquet(PARQUET_DIR / "coaches.parquet").set_index("team")
    if sim_feats:  # ratings-only simulation as the sim_* inputs
        from nba_quant.sim.possession import league_from_row, profile_from_row, simulate_batch
        homes, aways, lgs = [], [], []
        for _, r in slate.iterrows():
            lg = league_from_row(r, home_court=2.2)
            homes.append(profile_from_row(r["home_team"], pd.Series({k[5:]: v for k, v in r.items() if k.startswith("home_")}), lg))
            aways.append(profile_from_row(r["away_team"], pd.Series({k[5:]: v for k, v in r.items() if k.startswith("away_")}), lg))
            lgs.append(lg)
        rs = simulate_batch(homes, aways, lgs, n_sims=2000, seed=5)
        slate["sim_home_wp"] = [x["home_win_prob"] for x in rs]; slate["sim_margin"] = [x["mean_margin"] for x in rs]; slate["sim_total"] = [x["mean_total"] for x in rs]
    X = slate[feats].astype(float)
    slate["xgb_home_wp"] = np.clip(m_win.predict_proba(X)[:, 1], 0.02, 0.98)
    slate["xgb_margin"] = m_margin.predict(X); slate["xgb_total"] = m_total.predict(X)
    games = []
    for _, row in slate.iterrows():
        sc = scenarios_for_game(row, lines, coaches.reset_index(), n_sims=n_sims, seed=11, center=(float(row["xgb_margin"]), float(row["xgb_total"])))
        mm = sc["mixture_margin_samples"]; tt = sc["mixture_total_samples"]
        mc_wp = float((mm > 0).mean())
        consensus_wp = 0.5 * float(row["xgb_home_wp"]) + 0.5 * mc_wp
        pred_margin = float(np.mean(mm)); pred_total = float(np.mean(tt))
        home_pts = (pred_total + pred_margin) / 2; away_pts = (pred_total - pred_margin) / 2
        hc = coaches.loc[row["home_team"]] if row["home_team"] in coaches.index else None
        ac = coaches.loc[row["away_team"]] if row["away_team"] in coaches.index else None
        g = {
            "game_id": row["game_id"], "espn_game_id": row.get("espn_game_id"), "game_date": str(row["game_date"]),
            "tip_utc": str(row["start_time_utc"]) if pd.notna(row.get("start_time_utc")) else None,
            "home": row["home_team"], "away": row["away_team"], "home_name": TEAM_NAMES.get(row["home_team"]), "away_name": TEAM_NAMES.get(row["away_team"]),
            "home_coach": row.get("home_coach"), "away_coach": row.get("away_coach"),
            "xgb_home_wp": float(row["xgb_home_wp"]), "xgb_margin": float(row["xgb_margin"]), "xgb_total": float(row["xgb_total"]),
            "sim_ratings_only": {"home_wp": float(row.get("sim_home_wp", np.nan)), "margin": float(row.get("sim_margin", np.nan)), "total": float(row.get("sim_total", np.nan))},
            "mc_home_wp": mc_wp, "consensus_home_wp": consensus_wp, "pred_margin": pred_margin, "pred_total": pred_total,
            "pred_home_pts": home_pts, "pred_away_pts": away_pts,
            "likeliest_winner": row["home_team"] if consensus_wp >= 0.5 else row["away_team"],
            "pred_spread_home": -round(pred_margin * 2) / 2,   # conventional sign, half-point grid
            "margin_quantiles": {str(q): float(np.quantile(mm, q)) for q in (0.05, 0.25, 0.5, 0.75, 0.95)},
            "total_quantiles": {str(q): float(np.quantile(tt, q)) for q in (0.05, 0.25, 0.5, 0.75, 0.95)},
            "margin_sd": float(np.std(mm)), "total_sd": float(np.std(tt)),
            "ot_rate": float(np.mean([s["ot_rate"] * s["probability"] for s in sc["scenarios"]]) / max(sum(s["probability"] for s in sc["scenarios"]), 1e-9)),
            "margin_hist": hist(mm, -45, 46), "total_hist": hist(tt, 170, 290, 2),
            "scenarios": sc["scenarios"], "out_lines": sc["out_lines"], "switch_lines": sc["switch_lines"], "center_shift": sc["center_shift"], "k_avail": sc["k_avail"],
            "features": {k: (None if pd.isna(row[k]) else float(row[k])) for k in ["home_elo_pre", "away_elo_pre", "home_adj_net", "away_adj_net", "home_adj_pace", "away_adj_pace",
                                                                                  "home_rest_days", "away_rest_days", "home_back_to_back", "away_back_to_back", "home_out_val", "away_out_val",
                                                                                  "home_q_val", "away_q_val", "home_n_prior", "away_n_prior", "home_ewm_fg3a_rate", "away_ewm_fg3a_rate"]},
            "market_home_exp_margin": None if pd.isna(row.get("home_exp_margin_market")) else float(row["home_exp_margin_market"]),
            "coaching": {"home": None if hc is None else {k: float(hc[k]) for k in ["overall_coaching_score", "strategy_index", "rotation_index", "endgame_index", "offense_index", "defense_index"]},
                         "away": None if ac is None else {k: float(ac[k]) for k in ["overall_coaching_score", "strategy_index", "rotation_index", "endgame_index", "offense_index", "defense_index"]}},
            "_margin_samples": mm, "_total_samples": tt,
        }
        games.append(g)
    return {"date": day, "generated_at_utc": datetime.now(timezone.utc).isoformat(), "n_sims": n_sims, "games": games}


def kelly_for_slate(pred: dict, lines: pd.DataFrame | None, bankroll_fraction: float = 0.25, cap_per_bet: float = 0.05, cap_total: float = 0.20) -> pd.DataFrame:
    if lines is None or lines.empty:
        return pd.DataFrame()
    bets = []
    for g in pred["games"]:
        sel = lines[(lines.get("home", pd.Series(dtype=str)) == g["home"]) & (lines.get("away", pd.Series(dtype=str)) == g["away"])] if "home" in lines else lines[lines["game_id"].astype(str) == g["game_id"]]
        if sel.empty:
            continue
        l = sel.iloc[0]
        mm, tt = g["_margin_samples"], g["_total_samples"]
        p_home = g["consensus_home_wp"]
        if pd.notna(l.get("home_ml")):
            bets.append(Bet(f"{g['away']}@{g['home']} {g['home']} ML", p_home, american_to_decimal(l["home_ml"])))
        if pd.notna(l.get("away_ml")):
            bets.append(Bet(f"{g['away']}@{g['home']} {g['away']} ML", 1 - p_home, american_to_decimal(l["away_ml"])))
        if pd.notna(l.get("spread_home")):
            o = american_to_decimal(l.get("spread_odds", -110) if pd.notna(l.get("spread_odds")) else -110)
            cov = float((mm + l["spread_home"] > 0).mean()); push = float((mm + l["spread_home"] == 0).mean())
            bets.append(Bet(f"{g['away']}@{g['home']} {g['home']} {l['spread_home']:+g}", cov, o, push))
            bets.append(Bet(f"{g['away']}@{g['home']} {g['away']} {-l['spread_home']:+g}", max(0.0, 1 - cov - push), o, push))
        if pd.notna(l.get("total")):
            o = american_to_decimal(l.get("total_odds", -110) if pd.notna(l.get("total_odds")) else -110)
            over = float((tt > l["total"]).mean()); push = float((tt == l["total"]).mean())
            bets.append(Bet(f"{g['away']}@{g['home']} Over {l['total']}", over, o, push))
            bets.append(Bet(f"{g['away']}@{g['home']} Under {l['total']}", max(0.0, 1 - over - push), o, push))
    # keep only the better side of each two-way market before portfolio sizing
    df_all = pd.DataFrame([{"label": b.label, "prob": b.prob, "odds": b.decimal_odds, "edge": b.prob * (b.decimal_odds - 1) - (1 - b.prob - b.push_prob)} for b in bets])
    keep = [b for b in bets if b.prob * (b.decimal_odds - 1) - (1 - b.prob - b.push_prob) > 0]
    pk = portfolio_kelly(keep, fraction=bankroll_fraction, cap_per_bet=cap_per_bet, cap_total=cap_total) if keep else pd.DataFrame()
    return pk


def main(day: str | None = None, n_sims: int = 10000) -> dict:
    day = day or str(date.today())
    pred = predict_slate(day, n_sims=n_sims)
    lines = load_lines(day)
    kelly = kelly_for_slate(pred, lines)
    PRED_DIR.mkdir(parents=True, exist_ok=True)
    rows = []
    for g in pred["games"]:
        rows.append({k: v for k, v in g.items() if not isinstance(v, (dict, list, np.ndarray))})
    table = pd.DataFrame(rows)
    table.to_parquet(PRED_DIR / f"predictions_{day}.parquet", index=False)
    out = {**pred, "games": [{k: v for k, v in g.items() if not k.startswith("_")} for g in pred["games"]],
           "kelly": kelly.to_dict("records") if len(kelly) else [], "lines_available": lines is not None}
    (PRED_DIR / f"predictions_{day}.json").write_text(json.dumps(out, indent=1, default=float))
    shutil.copy(PRED_DIR / f"predictions_{day}.json", PRED_DIR / "latest.json")
    log.info("wrote predictions for %s (%d games)", day, len(pred["games"]))
    return out


if __name__ == "__main__":
    import sys
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    d = sys.argv[1] if len(sys.argv) > 1 else None
    out = main(d, n_sims=int(sys.argv[2]) if len(sys.argv) > 2 else 10000)
    pd.set_option("display.width", 250)
    t = pd.DataFrame(out["games"])[["away", "home", "xgb_home_wp", "mc_home_wp", "consensus_home_wp", "likeliest_winner", "pred_away_pts", "pred_home_pts", "pred_spread_home", "pred_total", "xgb_total", "margin_sd", "ot_rate"]]
    print(t.round(3).to_string())

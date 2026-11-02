"""Train and evaluate the XGBoost win-probability, spread (margin) and total models.

Walk-forward evaluation: for each test season S in {2024, 2025, 2026, 2027} fit on every completed
game from seasons < S and score season S. Baselines: Elo win probability, the ESPN market spread
(win prob via a normal(0, 13.45) margin model), season-mean total. Final models are refit on all
completed games and saved to models/ together with the feature list, walk-forward metrics and the
availability calibration used by the simulator.
"""
from __future__ import annotations

import json
import logging
from datetime import datetime, timezone

import numpy as np
import pandas as pd
from scipy.stats import norm
from sklearn.metrics import brier_score_loss, log_loss, mean_absolute_error, roc_auc_score
from xgboost import XGBClassifier, XGBRegressor

from nba_quant.config import MODEL_DIR, PARQUET_DIR

log = logging.getLogger(__name__)
MARKET_SD = 13.45
TEST_SEASONS = [2024, 2025, 2026, 2027]

BASE_FEATURES = [
    "diff_elo_pre", "home_elo_pre", "away_elo_pre",
    "home_adj_off", "home_adj_def", "away_adj_off", "away_adj_def", "home_adj_pace", "away_adj_pace",
    "diff_adj_net", "diff_s2d_adj_net", "diff_l10_adj_net", "diff_ewm_net", "diff_s2d_win", "diff_l10_margin",
    "home_s2d_margin", "away_s2d_margin",
    "home_ewm_efg", "away_ewm_efg", "home_ewm_tov_pct", "away_ewm_tov_pct", "home_ewm_oreb_pct", "away_ewm_oreb_pct",
    "home_ewm_ftr", "away_ewm_ftr", "home_ewm_fg3a_rate", "away_ewm_fg3a_rate", "home_ewm_fg3_pct", "away_ewm_fg3_pct",
    "home_ewm_fg2_pct", "away_ewm_fg2_pct", "home_ewm_ft_pct", "away_ewm_ft_pct",
    "home_ewm_opp_efg", "away_ewm_opp_efg", "home_ewm_opp_tov_pct", "away_ewm_opp_tov_pct",
    "home_ewm_opp_fg3a_rate", "away_ewm_opp_fg3a_rate", "home_ewm_opp_ftr", "away_ewm_opp_ftr", "home_ewm_dreb_pct", "away_ewm_dreb_pct",
    "home_rest_days", "away_rest_days", "diff_rest_days", "home_back_to_back", "away_back_to_back", "home_games_last_7d", "away_games_last_7d",
    "home_n_prior", "away_n_prior", "home_streak", "away_streak",
    "home_out_val", "away_out_val", "diff_out_val", "home_q_val", "away_q_val", "diff_q_val", "home_out_n", "away_out_n",
    "home_q_n", "away_q_n", "home_out_star", "away_out_star", "home_out_min", "away_out_min",
    "home_coach_overall", "away_coach_overall", "diff_coach_overall", "home_coach_strategy", "away_coach_strategy",
    "home_coach_rotation", "away_coach_rotation", "home_coach_endgame", "away_coach_endgame", "diff_coach_endgame",
    "home_coach_pace", "away_coach_pace", "home_coach_three", "away_coach_three", "home_coach_star_load", "away_coach_star_load",
    "playoffs", "neutral_site", "sum_adj_pace", "sum_off", "sum_def", "sum_fg3a_rate", "exp_total_naive", "exp_margin_naive",
    "lg_off_rtg", "lg_pace",
]
SIM_FEATURES = ["sim_home_wp", "sim_margin", "sim_total"]

PARAMS_CLF = dict(n_estimators=1500, learning_rate=0.015, max_depth=3, subsample=0.8, colsample_bytree=0.6, min_child_weight=25,
                  reg_lambda=8.0, reg_alpha=0.5, gamma=0.2, objective="binary:logistic", eval_metric="logloss", n_jobs=8, random_state=42)
PARAMS_REG = dict(n_estimators=1500, learning_rate=0.015, max_depth=3, subsample=0.8, colsample_bytree=0.6, min_child_weight=25,
                  reg_lambda=8.0, reg_alpha=0.5, gamma=0.2, objective="reg:squarederror", eval_metric="mae", n_jobs=8, random_state=42)


def load_training_frame() -> tuple[pd.DataFrame, list[str]]:
    gf = pd.read_parquet(PARQUET_DIR / "game_features.parquet")
    feats = list(BASE_FEATURES)
    sim_path = PARQUET_DIR / "sim_features.parquet"
    if sim_path.exists():
        sim = pd.read_parquet(sim_path)
        gf = gf.merge(sim[["game_id"] + SIM_FEATURES], on="game_id", how="left")
        feats += SIM_FEATURES
        log.info("merged sim features (%d games)", sim["game_id"].nunique())
    for c in feats:
        if c not in gf:
            gf[c] = np.nan
        gf[c] = gf[c].astype(float)
    return gf, feats


def _fit_with_es(model, X, y, X_val, y_val):
    model.set_params(early_stopping_rounds=100)
    model.fit(X, y, eval_set=[(X_val, y_val)], verbose=False)
    best = int(model.best_iteration) + 1 if getattr(model, "best_iteration", None) is not None else model.n_estimators
    return model, best


def fit_models(train: pd.DataFrame, feats: list[str], n_rounds: dict | None = None):
    train = train.sort_values(["game_date", "game_id"])
    cut = int(len(train) * 0.85)
    tr, va = train.iloc[:cut], train.iloc[cut:]
    out, rounds = {}, {}
    for name, target, cls, params in (("win", "home_win", XGBClassifier, PARAMS_CLF), ("margin", "margin", XGBRegressor, PARAMS_REG),
                                      ("total", "total", XGBRegressor, PARAMS_REG)):
        if n_rounds and name in n_rounds:
            m = cls(**{**params, "n_estimators": n_rounds[name]})
            m.fit(train[feats], train[target], verbose=False)
            best = n_rounds[name]
        else:
            m, best = _fit_with_es(cls(**params), tr[feats], tr[target], va[feats], va[target])
            m = cls(**{**params, "n_estimators": best})
            m.fit(train[feats], train[target], verbose=False)
        out[name] = m; rounds[name] = best
    return out, rounds


def evaluate(test: pd.DataFrame, models: dict, feats: list[str]) -> dict:
    p = np.clip(models["win"].predict_proba(test[feats])[:, 1], 1e-4, 1 - 1e-4)
    m_hat = models["margin"].predict(test[feats]); t_hat = models["total"].predict(test[feats])
    y = test["home_win"].astype(int).to_numpy()
    res = {"n": int(len(test)),
           "logloss": float(log_loss(y, p)), "brier": float(brier_score_loss(y, p)), "accuracy": float(((p > 0.5) == y).mean()),
           "auc": float(roc_auc_score(y, p)) if len(np.unique(y)) > 1 else np.nan,
           "margin_mae": float(mean_absolute_error(test["margin"], m_hat)), "margin_rmse": float(np.sqrt(np.mean((test["margin"] - m_hat) ** 2))),
           "total_mae": float(mean_absolute_error(test["total"], t_hat)), "total_rmse": float(np.sqrt(np.mean((test["total"] - t_hat) ** 2))),
           "pick_accuracy_from_margin": float(((m_hat > 0) == (test["margin"] > 0)).mean())}
    # baselines
    elo_p = 1 / (1 + 10 ** (-(test["diff_elo_pre"] + 100 * (1 - test["neutral_site"])) / 400))
    res["elo_logloss"] = float(log_loss(y, np.clip(elo_p, 1e-4, 1 - 1e-4))); res["elo_accuracy"] = float(((elo_p > 0.5) == y).mean())
    mk = test.dropna(subset=["home_exp_margin_market"])
    if len(mk):
        pm = np.clip(norm.cdf(mk["home_exp_margin_market"] / MARKET_SD), 1e-4, 1 - 1e-4)
        ym = mk["home_win"].astype(int)
        res["market_n"] = int(len(mk)); res["market_logloss"] = float(log_loss(ym, pm)); res["market_accuracy"] = float(((pm > 0.5) == ym).mean())
        res["market_margin_mae"] = float(mean_absolute_error(mk["margin"], mk["home_exp_margin_market"]))
        pmod = np.clip(models["win"].predict_proba(mk[feats])[:, 1], 1e-4, 1 - 1e-4)
        res["model_logloss_on_market_games"] = float(log_loss(ym, pmod))
        res["model_margin_mae_on_market_games"] = float(mean_absolute_error(mk["margin"], models["margin"].predict(mk[feats])))
        # agreement / beat-the-closing-line style check: how often model side vs spread wins
        mm = models["margin"].predict(mk[feats])
        side = np.sign(mm - mk["home_exp_margin_market"])
        cover = np.sign(mk["margin"] - mk["home_exp_margin_market"])
        decided = cover != 0
        res["ats_win_rate_all_games"] = float((side[decided] == cover[decided]).mean())
        edge = np.abs(mm - mk["home_exp_margin_market"]) >= 3
        if (edge & decided).sum() > 20:
            res["ats_win_rate_edge3plus"] = float((side[edge & decided] == cover[edge & decided]).mean()); res["ats_n_edge3plus"] = int((edge & decided).sum())
    res["total_mae_seasonmean_baseline"] = float(mean_absolute_error(test["total"], np.full(len(test), test["total"].mean())))
    # calibration bins
    bins = pd.cut(p, [0, 0.3, 0.4, 0.5, 0.6, 0.7, 1.0])
    cal = pd.DataFrame({"p": p, "y": y}).groupby(bins, observed=True).agg(pred=("p", "mean"), actual=("y", "mean"), n=("y", "size"))
    res["calibration"] = {str(k): {"pred": round(float(v.pred), 3), "actual": round(float(v.actual), 3), "n": int(v.n)} for k, v in cal.iterrows()}
    return res


def availability_calibration(df: pd.DataFrame) -> dict:
    """Points of margin per unit of out_val (used by the simulator's availability adjustment)."""
    d = df.dropna(subset=["margin", "exp_margin_naive", "diff_out_val"]).copy()
    X = np.column_stack([np.ones(len(d)), d["diff_elo_pre"], d["diff_adj_net"], d["diff_out_val"], d["diff_q_val"]])
    beta, *_ = np.linalg.lstsq(X, d["margin"].to_numpy(), rcond=None)
    return {"intercept_home_adv": float(beta[0]), "per_elo_point": float(beta[1]), "per_adj_net": float(beta[2]),
            "margin_per_out_val": float(beta[3]), "margin_per_q_val": float(beta[4]), "n": int(len(d))}


def walk_forward(gf: pd.DataFrame, feats: list[str]) -> dict:
    done = gf[gf["completed"]].copy()
    results = {}
    for s in TEST_SEASONS:
        train = done[done["season"] < s]; test = done[done["season"] == s]
        if len(test) < 50:
            continue
        models, rounds = fit_models(train, feats)
        r = evaluate(test, models, feats)
        r_reg = evaluate(test[test["playoffs"] == 0], models, feats)
        r["rounds"] = rounds; r["regular_season_only"] = {k: v for k, v in r_reg.items() if k in ("n", "logloss", "brier", "accuracy", "margin_mae", "total_mae", "market_logloss", "market_margin_mae", "elo_logloss")}
        results[str(s)] = r
        log.info("season %s: n=%d logloss=%.4f (elo %.4f, market %s) acc=%.3f margin MAE=%.2f (market %s) total MAE=%.2f", s, r["n"], r["logloss"], r["elo_logloss"],
                 f"{r.get('market_logloss', float('nan')):.4f}", r["accuracy"], r["margin_mae"], f"{r.get('market_margin_mae', float('nan')):.2f}", r["total_mae"])
    return results


def train_final(gf: pd.DataFrame, feats: list[str], rounds_hint: dict | None = None):
    done = gf[gf["completed"]]
    models, rounds = fit_models(done, feats, n_rounds=rounds_hint)
    MODEL_DIR.mkdir(exist_ok=True, parents=True)
    for name, m in models.items():
        m.save_model(MODEL_DIR / f"xgb_{name}.json")
    imp = {name: dict(sorted(zip(feats, map(float, m.feature_importances_)), key=lambda kv: -kv[1])[:25]) for name, m in models.items()}
    return models, rounds, imp


def main():
    gf, feats = load_training_frame()
    wf = walk_forward(gf, feats)
    # use the median best-iteration across folds for the final refit
    rounds_hint = {k: int(np.median([wf[s]["rounds"][k] for s in wf])) for k in ("win", "margin", "total")}
    models, rounds, imp = train_final(gf, feats, rounds_hint)
    cal = availability_calibration(gf[gf["completed"]])
    meta = {"trained_at_utc": datetime.now(timezone.utc).isoformat(), "features": feats, "n_train": int(gf["completed"].sum()),
            "seasons": sorted(map(int, gf.loc[gf["completed"], "season"].unique())), "rounds": rounds, "walk_forward": wf,
            "feature_importance_top25": imp, "availability_calibration": cal, "market_sd": MARKET_SD}
    (MODEL_DIR / "metrics.json").write_text(json.dumps(meta, indent=2, default=float))
    (MODEL_DIR / "features.json").write_text(json.dumps(feats))
    (MODEL_DIR / "calibration.json").write_text(json.dumps(cal, indent=2))
    log.info("saved models; availability calibration %s", cal)
    return meta


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    meta = main()
    for s, r in meta["walk_forward"].items():
        print(s, {k: (round(v, 4) if isinstance(v, float) else v) for k, v in r.items() if k not in ("calibration", "regular_season_only", "rounds")})
        print("   calibration:", r["calibration"])
    print("top win features:", list(meta["feature_importance_top25"]["win"].items())[:12])
    print("top total features:", list(meta["feature_importance_top25"]["total"].items())[:10])

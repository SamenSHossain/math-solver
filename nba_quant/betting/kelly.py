"""Kelly-criterion bet sizing as a percentage of a portfolio (bankroll).

Single bet:   f* = (b p - q) / b   with b = decimal odds - 1, p = model probability, q = 1 - p.
Fractional Kelly (default 1/4) is strongly recommended: model probabilities are estimates, and the
growth-rate penalty for over-betting is far steeper than for under-betting.

Multiple simultaneous bets (a slate): the single-bet fractions are not additive. `portfolio_kelly`
maximises the expected log growth E[log(1 + sum_i f_i * R_i)] over the joint outcome distribution,
assuming independence between games (exact enumeration up to 14 bets, Monte Carlo beyond), subject to
per-bet caps and a total exposure cap. Correlated legs (same-game spread + total) should be entered
as one combined position or left out.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product

import numpy as np
import pandas as pd
from scipy.optimize import minimize


def american_to_decimal(odds: float) -> float:
    odds = float(odds)
    return 1 + odds / 100 if odds > 0 else 1 + 100 / abs(odds)


def decimal_to_american(dec: float) -> float:
    return round((dec - 1) * 100) if dec >= 2 else round(-100 / (dec - 1))


def implied_probability(decimal_odds: float) -> float:
    return 1.0 / decimal_odds


def remove_vig(dec_a: float, dec_b: float) -> tuple[float, float]:
    """Fair probabilities for a two-way market (multiplicative de-vig)."""
    pa, pb = 1 / dec_a, 1 / dec_b
    s = pa + pb
    return pa / s, pb / s


def kelly_fraction(p: float, decimal_odds: float) -> float:
    """Full-Kelly fraction of bankroll (0 if no edge)."""
    b = decimal_odds - 1.0
    if b <= 0:
        return 0.0
    f = (b * p - (1 - p)) / b
    return max(0.0, float(f))


def edge(p: float, decimal_odds: float) -> float:
    """Expected profit per unit staked."""
    return p * (decimal_odds - 1) - (1 - p)


@dataclass
class Bet:
    label: str
    prob: float             # model probability the bet wins
    decimal_odds: float
    push_prob: float = 0.0  # probability of a push (stake returned), e.g. integer spreads/totals

    @property
    def b(self) -> float:
        return self.decimal_odds - 1.0


def size_single(bet: Bet, fraction: float = 0.25, cap: float = 0.05) -> dict:
    win, push = bet.prob, bet.push_prob
    lose = max(0.0, 1 - win - push)
    b = bet.b
    f_full = max(0.0, (b * win - lose) / b) if b > 0 else 0.0
    ev = win * b - lose
    return dict(label=bet.label, prob=win, push_prob=push, decimal_odds=bet.decimal_odds,
                american_odds=decimal_to_american(bet.decimal_odds), implied_prob=1 / bet.decimal_odds,
                edge=ev, kelly_full=f_full, kelly_fractional=min(cap, fraction * f_full),
                growth_full=(win * np.log1p(f_full * b) + lose * np.log1p(-f_full) if 0 < f_full < 1 else 0.0))


def _outcome_matrix(bets: list[Bet], rng: np.random.Generator, max_exact: int = 14, n_mc: int = 20000):
    n = len(bets)
    probs = np.array([[b.prob, b.push_prob, max(0.0, 1 - b.prob - b.push_prob)] for b in bets])
    if n <= max_exact:
        states = np.array(list(product([0, 1, 2], repeat=n)))  # 0 win, 1 push, 2 lose
        w = np.prod(probs[np.arange(n)[None, :], states], axis=1)
        keep = w > 1e-9
        states, w = states[keep], w[keep] / w[keep].sum()
    else:
        u = rng.random((n_mc, n))
        states = np.where(u < probs[:, 0], 0, np.where(u < probs[:, 0] + probs[:, 1], 1, 2))
        w = np.full(len(states), 1.0 / len(states))
    bvec = np.array([b.b for b in bets])
    returns = np.where(states == 0, bvec, np.where(states == 1, 0.0, -1.0))  # per unit stake
    return returns, w


def portfolio_kelly(bets: list[Bet], fraction: float = 0.25, cap_per_bet: float = 0.05, cap_total: float = 0.20,
                    seed: int = 0) -> pd.DataFrame:
    """Simultaneous Kelly allocation (fraction of bankroll per bet) for an independent slate."""
    bets = [b for b in bets if b.b > 0]
    if not bets:
        return pd.DataFrame()
    rng = np.random.default_rng(seed)
    R, w = _outcome_matrix(bets, rng)
    n = len(bets)

    def neg_growth(f):
        wealth = 1.0 + R @ f
        if np.any(wealth <= 1e-9):
            return 1e6
        return -float(np.sum(w * np.log(wealth)))

    f0 = np.array([min(cap_per_bet, kelly_fraction(b.prob, b.decimal_odds) * 0.5) for b in bets])
    cons = [{"type": "ineq", "fun": lambda f: cap_total / max(fraction, 1e-9) - f.sum()}]
    res = minimize(neg_growth, f0, method="SLSQP", bounds=[(0.0, min(0.5, cap_per_bet / max(fraction, 1e-9)))] * n, constraints=cons,
                   options={"maxiter": 500, "ftol": 1e-10})
    f_full = np.clip(res.x, 0, None) if res.success else f0
    rows = []
    for b, ff in zip(bets, f_full):
        single = size_single(b, fraction=fraction, cap=cap_per_bet)
        rows.append({**single, "portfolio_full": float(ff), "portfolio_pct": float(min(cap_per_bet, fraction * ff))})
    out = pd.DataFrame(rows)
    out["portfolio_pct"] = out["portfolio_pct"].where(out["edge"] > 0, 0.0)
    total = out["portfolio_pct"].sum()
    if total > cap_total:
        out["portfolio_pct"] *= cap_total / total
    out.attrs["expected_log_growth_full"] = -neg_growth(f_full)
    out.attrs["expected_log_growth_scaled"] = -neg_growth(out["portfolio_pct"].to_numpy())
    return out


def bets_from_prediction(pred: dict, lines: dict, fraction_push=None) -> list[Bet]:
    """Build Bet objects from a game prediction dict and a lines dict.

    pred keys: home, away, p_home (win prob), p_home_cover(spread)->callable or precomputed probs via
    'cover_prob' and 'over_prob' entries; lines: {'home_ml': -150, 'away_ml': +130, 'spread_home': -3.5,
    'spread_odds': -110, 'total': 228.5, 'total_odds': -110}
    """
    bets = []
    if lines.get("home_ml") is not None:
        bets.append(Bet(f"{pred['home']} ML", pred["p_home"], american_to_decimal(lines["home_ml"])))
    if lines.get("away_ml") is not None:
        bets.append(Bet(f"{pred['away']} ML", 1 - pred["p_home"], american_to_decimal(lines["away_ml"])))
    if lines.get("spread_home") is not None and "cover_prob" in pred:
        p_cov, p_push = pred["cover_prob"], pred.get("cover_push", 0.0)
        o = american_to_decimal(lines.get("spread_odds", -110))
        bets.append(Bet(f"{pred['home']} {lines['spread_home']:+g}", p_cov, o, p_push))
        bets.append(Bet(f"{pred['away']} {-lines['spread_home']:+g}", max(0.0, 1 - p_cov - p_push), o, p_push))
    if lines.get("total") is not None and "over_prob" in pred:
        p_over, p_push = pred["over_prob"], pred.get("total_push", 0.0)
        o = american_to_decimal(lines.get("total_odds", -110))
        bets.append(Bet(f"Over {lines['total']}", p_over, o, p_push))
        bets.append(Bet(f"Under {lines['total']}", max(0.0, 1 - p_over - p_push), o, p_push))
    return bets


if __name__ == "__main__":
    slate = [Bet("BOS ML", 0.62, american_to_decimal(-150)), Bet("DEN -4.5", 0.56, american_to_decimal(-110)),
             Bet("Over 228.5 OKC/CLE", 0.53, american_to_decimal(-110)), Bet("MIA ML", 0.41, american_to_decimal(+180))]
    pd.set_option("display.width", 200)
    df = portfolio_kelly(slate, fraction=0.25)
    print(df[["label", "prob", "american_odds", "implied_prob", "edge", "kelly_full", "kelly_fractional", "portfolio_full", "portfolio_pct"]].round(4).to_string())
    print("expected log growth (scaled):", round(df.attrs["expected_log_growth_scaled"], 5))

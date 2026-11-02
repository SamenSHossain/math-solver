"""Possession-level Monte Carlo game simulator.

Design (see docs/METHODOLOGY.md for the research background):
  * Possessions per team ~ Normal(mean = league pace + (home pace dev) + (away pace dev) + coaching pace
    tilt, sd = PACE_SD), identical for both teams (+/-1 for the first/last possession).
  * Each possession is a chain of "plays": turnover | free-throw trip | 3PA | 2PA; a missed shot (or
    missed last FT) is rebounded by the offence with the matchup offensive-rebound rate and the chain
    continues ("second chance" with lower efficiency).
  * Shooting percentages are rescaled so that the expected points per possession equals the matchup
    target: league avg + (team adjusted offence - lg) + (opponent adjusted defence - lg) + home court
    + rest + availability adjustment. The shot profile therefore shapes the VARIANCE (3PA-heavy teams
    are higher variance) while the ratings pin the MEAN.
  * End-game dynamics (last ~12 possessions): trailing teams shift toward 3PA when down 4-12; in the
    final possessions a team trailing by 3-9 intentionally fouls (extra free-throw possessions for the
    leader, quick possessions for the trailer); a team leading by exactly 3 on the final defensive
    possession fouls with a coach-specific probability; leading teams milk the clock (fewer
    possessions). Clutch coaching quality tilts efficiency in close late-game possessions.
  * Ties go to overtime (about 10 possessions per team), repeated until decided.
All draws are vectorised across simulations with numpy.
"""
from __future__ import annotations

from dataclasses import dataclass, field, asdict

import numpy as np

PACE_SD = 3.6          # residual sd of game possessions after accounting for both teams' tendencies
OT_POSS = 10           # possessions per team in a five-minute overtime
AND1_RATE = 0.065      # share of made 2PA that draw an and-one free throw
TRIP_3FT_RATE = 0.06   # share of FT trips that are three-shot fouls
SECOND_CHANCE_EFF = 0.95  # multiplier on shooting after an offensive rebound (putbacks are efficient but rushed)
ENDGAME_POSS = 12      # possessions (per team) considered "end game"
CLUTCH_MARGIN = 5
CLUTCH_PPP_PER_SCORE = 0.030  # points per possession tilt at coaching clutch score 100 vs 0 (+/-0.015 at the extremes)
RESTORE_KAPPA = 0.0035  # within-game mean reversion: PPP change per point of lead (leaders coast, trailers press)
PACE_TRAIL_BOOST = 0.0  # reserved: extra possessions when trailing (kept 0; pace handled via n_poss)


@dataclass
class TeamProfile:
    name: str
    off_rtg: float           # adjusted offensive rating (pts / 100 poss)
    def_rtg: float           # adjusted defensive rating (pts allowed / 100 poss)
    pace: float              # possessions per 48 minutes
    fg3a_rate: float         # 3PA / FGA
    fg3_pct: float
    fg2_pct: float
    ftr: float               # FTA / FGA
    ft_pct: float
    tov_pct: float           # TOV / possession
    oreb_pct: float          # offensive rebound share of own misses
    dreb_pct: float          # defensive rebound share of opponent misses
    opp_fg3a_rate: float     # allowed 3PA/FGA
    opp_fg3_pct: float
    opp_tov_pct: float       # forced turnovers / possession
    opp_ftr: float           # fouls: opponent FTA/FGA allowed
    # coaching tendency scores (0-100, 50 = league average); None -> neutral
    coach_pace: float | None = None
    coach_three: float | None = None
    coach_foul_up3: float | None = None
    coach_clutch: float | None = None
    coach_late_shrink: float | None = None
    # situational adjustments in points per 100 possessions (applied to this team's offence / defence)
    off_adjust: float = 0.0
    def_adjust: float = 0.0
    availability_net_adjust: float = 0.0   # from injuries: negative when key players are out
    extra: dict = field(default_factory=dict)


@dataclass
class LeagueAverages:
    off_rtg: float = 114.5
    pace: float = 99.0
    fg3a_rate: float = 0.40
    fg3_pct: float = 0.362
    fg2_pct: float = 0.546
    ftr: float = 0.26
    ft_pct: float = 0.78
    tov_pct: float = 0.137
    oreb_pct: float = 0.245
    home_court: float = 2.4   # expected home margin, points


def _clip(x, lo, hi):
    return float(np.clip(x, lo, hi))


def matchup_rates(off: TeamProfile, deff: TeamProfile, lg: LeagueAverages, is_home: bool, context: dict) -> dict:
    """Blend an offence with a defence (additive deviations from league average)."""
    coach_three = 0.0 if off.coach_three is None else (off.coach_three - 50) / 50 * 0.02
    fg3a_rate = _clip(off.fg3a_rate + (deff.opp_fg3a_rate - lg.fg3a_rate) + coach_three, 0.15, 0.65)
    fg3 = _clip(off.fg3_pct + (deff.opp_fg3_pct - lg.fg3_pct) * 0.5, 0.25, 0.48)   # opponent 3pt% is mostly noise: half weight
    fg2 = _clip(off.fg2_pct, 0.42, 0.65)
    ftr = _clip(off.ftr + (deff.opp_ftr - lg.ftr), 0.12, 0.45)
    tov = _clip(off.tov_pct + (deff.opp_tov_pct - lg.tov_pct), 0.07, 0.22)
    oreb = _clip(off.oreb_pct + ((1 - deff.dreb_pct) - lg.oreb_pct), 0.12, 0.40)
    hca = lg.home_court if is_home else -lg.home_court
    target_rtg = (lg.off_rtg + (off.off_rtg - lg.off_rtg) + (deff.def_rtg - lg.off_rtg)
                  + hca / 2 + off.off_adjust - deff.def_adjust + off.availability_net_adjust / 2 - deff.availability_net_adjust / 2)
    target_rtg += context.get("off_rtg_shift", 0.0)
    return dict(fg3a_rate=fg3a_rate, fg3=fg3, fg2=fg2, ftr=ftr, tov=tov, oreb=oreb, ft=_clip(off.ft_pct, 0.65, 0.9),
                target_ppp=target_rtg / 100.0)


def play_probabilities(r: dict) -> dict:
    """Convert per-possession rates into per-play probabilities and solve the shooting scale for the target PPP."""
    # expected plays per possession: FGA per poss ~ (1 - tov) * plays... derive from rates per FGA
    # Per non-turnover play: trip share from FTr (two FTs per trip), rest are field goal attempts.
    trips_per_fga = r["ftr"] / 2.0 * (1 - AND1_RATE * (1 - r["fg3a_rate"]) * r["fg2"])  # and-ones are not separate trips
    p_tov = r["tov"]
    p_trip = (1 - p_tov) * trips_per_fga / (1 + trips_per_fga)
    p_fga = (1 - p_tov) - p_trip
    p_3 = p_fga * r["fg3a_rate"]
    p_2 = p_fga * (1 - r["fg3a_rate"])

    def expected_ppp(scale: float) -> float:
        fg3 = min(r["fg3"] * scale, 0.75); fg2 = min(r["fg2"] * scale, 0.9); ft = r["ft"]
        pts_play = p_3 * 3 * fg3 + p_2 * (2 * fg2 + AND1_RATE * fg2 * ft) + p_trip * (2 * ft + TRIP_3FT_RATE * ft)
        miss_play = p_3 * (1 - fg3) + p_2 * (1 - fg2) + p_trip * (1 - ft) * 0.5
        plays = 1.0 / (1.0 - miss_play * r["oreb"] * 0.98)
        # second-chance plays are slightly less efficient
        return pts_play * (1 + (plays - 1) * SECOND_CHANCE_EFF)

    lo, hi = 0.6, 1.6
    for _ in range(40):
        mid = 0.5 * (lo + hi)
        if expected_ppp(mid) < r["target_ppp"]:
            lo = mid
        else:
            hi = mid
    scale = 0.5 * (lo + hi)
    return dict(p_tov=p_tov, p_trip=p_trip, p_3=p_3, p_2=p_2, fg3=min(r["fg3"] * scale, 0.75), fg2=min(r["fg2"] * scale, 0.9),
                ft=r["ft"], oreb=r["oreb"], scale=scale, expected_ppp=expected_ppp(scale))


def _possession_points(rng, n, pp: dict, mask, three_shift=0.0, eff_shift=0.0):
    """Vectorised points for one possession for `n` sims (only where mask is True).

    eff_shift is a (scalar or per-sim) multiplicative tilt on shooting percentages, expressed as a
    fraction of PPP; three_shift moves attempt share from 2PA to 3PA.
    """
    pts = np.zeros(n)
    alive = mask.copy()
    eff = 1.0 + np.asarray(eff_shift) / max(pp["expected_ppp"], 0.5)   # PPP tilt -> shooting-% tilt
    fg3 = np.minimum(pp["fg3"] * eff, 0.8); fg2 = np.minimum(pp["fg2"] * eff, 0.9); ft = pp["ft"]
    p3 = pp["p_3"] + three_shift * (pp["p_3"] + pp["p_2"])
    p2 = pp["p_2"] - three_shift * (pp["p_3"] + pp["p_2"])
    cum_tov = pp["p_tov"]; cum_trip = cum_tov + pp["p_trip"]; cum_3 = cum_trip + p3
    for k in range(5):  # at most 5 plays per possession
        if not alive.any():
            break
        u = rng.random(n)
        tov = alive & (u < cum_tov)
        trip = alive & (u >= cum_tov) & (u < cum_trip)
        three = alive & (u >= cum_trip) & (u < cum_3)
        two = alive & (u >= cum_3)
        shoot_eff = 1.0 if k == 0 else SECOND_CHANCE_EFF
        made3 = three & (rng.random(n) < fg3 * shoot_eff)
        made2 = two & (rng.random(n) < fg2 * shoot_eff)
        and1 = made2 & (rng.random(n) < AND1_RATE) & (rng.random(n) < ft)
        ft1 = trip & (rng.random(n) < ft)
        ft2 = trip & (rng.random(n) < ft)
        ft3 = trip & (rng.random(n) < TRIP_3FT_RATE) & (rng.random(n) < ft)
        pts += 3 * made3 + 2 * made2 + and1 + ft1 + ft2 + ft3
        missed_shot = (three & ~made3) | (two & ~made2) | (trip & ~ft2 & ~ft3)
        oreb = missed_shot & (rng.random(n) < pp["oreb"])
        alive = oreb  # possession continues only after an offensive rebound
        # turnovers / makes / defensive rebounds end the possession
        _ = tov
    return pts


def simulate(home: TeamProfile, away: TeamProfile, lg: LeagueAverages | None = None, n_sims: int = 20000,
             seed: int | None = 7, context: dict | None = None, kappa: float | None = None) -> dict:
    lg = lg or LeagueAverages()
    context = context or {}
    kappa = RESTORE_KAPPA if kappa is None else kappa
    rng = np.random.default_rng(seed)
    rh = matchup_rates(home, away, lg, True, context.get("home", {}))
    ra = matchup_rates(away, home, lg, False, context.get("away", {}))
    ph, pa = play_probabilities(rh), play_probabilities(ra)
    coach_pace = 0.0
    for t in (home, away):
        if t.coach_pace is not None:
            coach_pace += (t.coach_pace - 50) / 50 * 1.0
    mean_poss = lg.pace + (home.pace - lg.pace) + (away.pace - lg.pace) + coach_pace + context.get("pace_shift", 0.0)
    n_poss = np.clip(np.round(rng.normal(mean_poss, PACE_SD, n_sims)), 80, 125).astype(int)
    max_poss = int(n_poss.max())
    hs = np.zeros(n_sims); as_ = np.zeros(n_sims)
    foul_h = 0.5 if home.coach_foul_up3 is None else home.coach_foul_up3 / 100
    foul_a = 0.5 if away.coach_foul_up3 is None else away.coach_foul_up3 / 100
    clutch_h = 0.0 if home.coach_clutch is None else (home.coach_clutch - 50) / 50 * CLUTCH_PPP_PER_SCORE / 2
    clutch_a = 0.0 if away.coach_clutch is None else (away.coach_clutch - 50) / 50 * CLUTCH_PPP_PER_SCORE / 2
    # home team starts with the ball in half the sims
    home_first = rng.random(n_sims) < 0.5
    for i in range(max_poss):
        active = i < n_poss
        remaining = n_poss - i  # possessions left for each team including this one
        endgame = active & (remaining <= ENDGAME_POSS)
        margin_h = hs - as_
        close = np.abs(margin_h) <= CLUTCH_MARGIN
        for who in (0, 1):
            # the team that won the opening tip has the ball on the first half-possession (who == 0)
            offence_home = home_first if who == 0 else ~home_first
            mask_home = active & offence_home
            mask_away = active & ~offence_home
            # --- end-game behaviour ------------------------------------------------------
            # trailing team down 4-12 hunts threes; leading team up >6 milks clock (skip some possessions)
            margin_h = hs - as_
            trail_home = margin_h < 0; trail_away = margin_h > 0
            shift_h = np.where(endgame & trail_home & (margin_h >= -12) & (margin_h <= -4), 0.18, 0.0)
            shift_a = np.where(endgame & trail_away & (margin_h <= 12) & (margin_h >= 4), 0.18, 0.0)
            late_lead_h = endgame & (remaining <= 4) & (margin_h > 6)
            late_lead_a = endgame & (remaining <= 4) & (margin_h < -6)
            skip = (mask_home & late_lead_h & (rng.random(n_sims) < 0.35)) | (mask_away & late_lead_a & (rng.random(n_sims) < 0.35))
            # intentional fouling: final 3 possessions, trailing by 3-9 -> leader shoots two free throws
            foul_sit_h_def = mask_away & (remaining <= 3) & (margin_h <= -3) & (margin_h >= -9)   # home trails, away has ball
            foul_sit_a_def = mask_home & (remaining <= 3) & (margin_h >= 3) & (margin_h <= 9)     # away trails, home has ball
            # foul up three on the final defensive possession
            up3_h = mask_away & (remaining <= 1) & (margin_h == 3) & (rng.random(n_sims) < foul_h)
            up3_a = mask_home & (remaining <= 1) & (margin_h == -3) & (rng.random(n_sims) < foul_a)
            # restoring force (leaders coast / trailers press) + clutch coaching tilt in close end-game possessions
            eff_h = -kappa * margin_h + np.where(endgame & close, clutch_h - clutch_a, 0.0)
            eff_a = kappa * margin_h - np.where(endgame & close, clutch_h - clutch_a, 0.0)
            # --- home offence ------------------------------------------------------------
            m = mask_home & ~skip
            ft_only = foul_sit_a_def | up3_a
            normal = m & ~ft_only
            pts = np.zeros(n_sims)
            if normal.any():
                for sh in np.unique(shift_h[normal]):
                    sub = normal & (shift_h == sh)
                    pts += _possession_points(rng, n_sims, ph, sub, three_shift=sh, eff_shift=eff_h)
            fts = m & ft_only
            if fts.any():
                pts += fts * ((rng.random(n_sims) < ph["ft"]).astype(float) + (rng.random(n_sims) < ph["ft"]).astype(float))
            hs += pts
            # --- away offence ------------------------------------------------------------
            m = mask_away & ~skip
            ft_only = foul_sit_h_def | up3_h
            normal = m & ~ft_only
            pts = np.zeros(n_sims)
            if normal.any():
                for sh in np.unique(shift_a[normal]):
                    sub = normal & (shift_a == sh)
                    pts += _possession_points(rng, n_sims, pa, sub, three_shift=sh, eff_shift=eff_a)
            fts = m & ft_only
            if fts.any():
                pts += fts * ((rng.random(n_sims) < pa["ft"]).astype(float) + (rng.random(n_sims) < pa["ft"]).astype(float))
            as_ += pts
    # overtime
    tied = hs == as_
    ot_count = np.zeros(n_sims, dtype=int)
    rounds = 0
    while tied.any() and rounds < 6:
        rounds += 1
        ot_count[tied] += 1
        for _ in range(OT_POSS):
            hs += _possession_points(rng, n_sims, ph, tied)
            as_ += _possession_points(rng, n_sims, pa, tied)
        tied = hs == as_
    # coin flip for the (rare) still-tied sims
    if tied.any():
        flip = rng.random(n_sims) < 0.5
        hs += tied & flip; as_ += tied & ~flip
    margin = hs - as_
    total = hs + as_
    return dict(
        home=home.name, away=away.name, n_sims=n_sims,
        home_win_prob=float((margin > 0).mean()),
        mean_margin=float(margin.mean()), median_margin=float(np.median(margin)),
        mean_total=float(total.mean()), median_total=float(np.median(total)),
        home_mean=float(hs.mean()), away_mean=float(as_.mean()),
        margin_sd=float(margin.std()), total_sd=float(total.std()),
        ot_rate=float((ot_count > 0).mean()),
        margin_quantiles={q: float(np.quantile(margin, q)) for q in (0.05, 0.25, 0.5, 0.75, 0.95)},
        total_quantiles={q: float(np.quantile(total, q)) for q in (0.05, 0.25, 0.5, 0.75, 0.95)},
        expected_poss=float(mean_poss), ppp_home=ph["expected_ppp"], ppp_away=pa["expected_ppp"],
        shooting_scale=(ph["scale"], pa["scale"]),
        margin_samples=margin, total_samples=total, home_samples=hs, away_samples=as_,
    )


def cover_probability(result: dict, home_spread: float) -> float:
    """P(home covers a conventional spread, e.g. -4.5 means home must win by 5+)."""
    m = result["margin_samples"]
    return float((m + home_spread > 0).mean() + 0.5 * (m + home_spread == 0).mean())


def over_probability(result: dict, total_line: float) -> float:
    t = result["total_samples"]
    return float((t > total_line).mean() + 0.5 * (t == total_line).mean())


def profile_from_row(name: str, row, lg: LeagueAverages) -> TeamProfile:
    """Build a TeamProfile from a team_game_features-style row (ewm_* / adj_* columns)."""
    g = lambda k, d: float(row[k]) if k in row and row[k] == row[k] else d
    return TeamProfile(
        name=name, off_rtg=g("adj_off", lg.off_rtg), def_rtg=g("adj_def", lg.off_rtg), pace=g("adj_pace", lg.pace),
        fg3a_rate=g("ewm_fg3a_rate", lg.fg3a_rate), fg3_pct=g("ewm_fg3_pct", lg.fg3_pct), fg2_pct=g("ewm_fg2_pct", lg.fg2_pct),
        ftr=g("ewm_ftr", lg.ftr), ft_pct=g("ewm_ft_pct", lg.ft_pct), tov_pct=g("ewm_tov_pct", lg.tov_pct),
        oreb_pct=g("ewm_oreb_pct", lg.oreb_pct), dreb_pct=g("ewm_dreb_pct", 1 - lg.oreb_pct),
        opp_fg3a_rate=g("ewm_opp_fg3a_rate", lg.fg3a_rate), opp_fg3_pct=g("ewm_opp_fg3_pct", lg.fg3_pct),
        opp_tov_pct=g("ewm_opp_tov_pct", lg.tov_pct), opp_ftr=g("ewm_opp_ftr", lg.ftr),
    )


if __name__ == "__main__":
    lg = LeagueAverages()
    h = TeamProfile("BOS", 120.0, 110.0, 97.0, 0.50, 0.37, 0.56, 0.24, 0.80, 0.12, 0.22, 0.75, 0.40, 0.36, 0.14, 0.25, coach_three=85, coach_clutch=70)
    a = TeamProfile("ORL", 111.0, 109.0, 98.5, 0.33, 0.33, 0.55, 0.30, 0.76, 0.15, 0.27, 0.74, 0.37, 0.355, 0.15, 0.27, coach_pace=55, coach_foul_up3=70)
    import time; t0 = time.time()
    r = simulate(h, a, lg, n_sims=20000)
    print(f"{time.time()-t0:.2f}s", {k: (round(v, 3) if isinstance(v, float) else v) for k, v in r.items() if not k.endswith("samples") and not isinstance(v, dict)})
    print("margin q", {k: round(v, 1) for k, v in r["margin_quantiles"].items()}, "total q", {k: round(v, 1) for k, v in r["total_quantiles"].items()})
    print("P(BOS -6.5)", round(cover_probability(r, -6.5), 3), "P(over 228.5)", round(over_probability(r, 228.5), 3))

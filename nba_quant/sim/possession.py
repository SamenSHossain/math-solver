"""Possession-level Monte Carlo game simulator (batched / vectorised).

Design (research background in docs/METHODOLOGY.md):
  * Possessions per team ~ Normal(mean = league pace + home pace deviation + away pace deviation +
    coaching pace tilt, sd = PACE_SD), identical for both teams (alternating half-possessions).
  * A possession is a chain of plays: turnover | free-throw trip | 3PA | 2PA. A missed shot (or a
    missed final free throw) is rebounded by the offence with the matchup offensive-rebound rate and
    the chain continues as a (slightly less efficient) second chance.
  * Shooting percentages are rescaled so the expected points per possession equals the matchup
    target: league average + (team adjusted offence - lg) + (opponent adjusted defence - lg) + home
    court + situational adjustments (rest, availability). The shot profile shapes the VARIANCE
    (3PA-heavy teams are higher variance) while the ratings pin the MEAN.
  * Pre-game "form" noise: each team's efficiency is shifted by N(0, FORM_SD) per simulated game,
    capturing day-to-day strength variation (minutes distribution, matchup fit, motivation).
  * End-game dynamics (last ENDGAME_POSS possessions): leaders coast and trailers press (restoring
    force), trailing teams hunt threes (down 4-12), tie-hunting threes when down exactly three on the
    final possession, intentional fouling by a team trailing 3-9 in the final three possessions, a
    team up exactly three on the final defensive possession fouls with a coach-specific probability,
    leaders milk the clock. Clutch coaching quality tilts efficiency in close late possessions.
  * Ties go to overtime (OT_POSS possessions per team), repeated until decided.

`simulate_batch` runs G games x S sims in one vectorised pass (parameters per column); `simulate`
is the single-game convenience wrapper that also returns the raw samples.
"""
from __future__ import annotations

from dataclasses import dataclass, field

import numpy as np

PACE_SD = 2.6            # residual sd of game possessions given both teams' tendencies (calibrated: total sd)
PACE_BIAS = -0.9         # calibrated possession offset (end-game foul cycles add ~2 pts otherwise)
FORM_SD = 0.030          # pre-game efficiency noise per team, points per possession (~3 pts/100)
OT_POSS = 10             # possessions per team in a five-minute overtime
AND1_RATE = 0.065        # share of made 2PA that draw an and-one free throw
TRIP_3FT_RATE = 0.06     # share of FT trips that are three-shot fouls
SECOND_CHANCE_EFF = 0.95 # multiplier on shooting after an offensive rebound
ENDGAME_POSS = 12        # possessions (per team) considered "end game"
CLUTCH_MARGIN = 5
CLUTCH_PPP_PER_SCORE = 0.030  # PPP tilt between a clutch score of 100 and 0 (+/-0.015 at the extremes)
KAPPA_GAME = 0.0008      # game-long restoring force: PPP change per point of lead
KAPPA_END = 0.0045       # additional end-game restoring force (coasting / pressing)
FOUL_CYCLES = 2          # late foul-to-extend cycles available to a team trailing by 1-9


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
    opp_ftr: float           # opponent FTA/FGA allowed (fouling)
    # coaching tendency scores (0-100, 50 = league average); None -> neutral
    coach_pace: float | None = None
    coach_three: float | None = None
    coach_foul_up3: float | None = None
    coach_clutch: float | None = None
    # situational adjustments, points per 100 possessions
    off_adjust: float = 0.0            # e.g. rest, travel
    def_adjust: float = 0.0            # positive = better defence (fewer points allowed)
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
    home_court: float = 2.2   # expected home margin, points


def _clip(x, lo, hi):
    return float(np.clip(x, lo, hi))


def matchup_rates(off: TeamProfile, deff: TeamProfile, lg: LeagueAverages, is_home: bool, neutral: bool = False) -> dict:
    """Blend an offence with a defence (additive deviations from league average)."""
    coach_three = 0.0 if off.coach_three is None else (off.coach_three - 50) / 50 * 0.02
    fg3a_rate = _clip(off.fg3a_rate + (deff.opp_fg3a_rate - lg.fg3a_rate) + coach_three, 0.15, 0.65)
    fg3 = _clip(off.fg3_pct + (deff.opp_fg3_pct - lg.fg3_pct) * 0.5, 0.25, 0.48)   # opponent 3pt% is mostly noise
    fg2 = _clip(off.fg2_pct, 0.42, 0.65)
    ftr = _clip(off.ftr + (deff.opp_ftr - lg.ftr), 0.12, 0.45)
    tov = _clip(off.tov_pct + (deff.opp_tov_pct - lg.tov_pct), 0.07, 0.22)
    oreb = _clip(off.oreb_pct + ((1 - deff.dreb_pct) - lg.oreb_pct), 0.12, 0.40)
    hca = 0.0 if neutral else (lg.home_court if is_home else -lg.home_court)
    target_rtg = (lg.off_rtg + (off.off_rtg - lg.off_rtg) + (deff.def_rtg - lg.off_rtg)
                  + hca / 2 + off.off_adjust - deff.def_adjust + off.availability_net_adjust / 2 - deff.availability_net_adjust / 2)
    return dict(fg3a_rate=fg3a_rate, fg3=fg3, fg2=fg2, ftr=ftr, tov=tov, oreb=oreb, ft=_clip(off.ft_pct, 0.65, 0.9),
                target_ppp=target_rtg / 100.0)


def play_probabilities(r: dict) -> dict:
    """Per-play probabilities from per-possession rates; solve the shooting scale that hits the target PPP."""
    trips_per_fga = r["ftr"] / 2.0 * (1 - AND1_RATE * (1 - r["fg3a_rate"]) * r["fg2"])
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


def _possession_points(rng, n, pp: dict, mask, three_shift, eff_shift):
    """Vectorised points for one possession (all arrays of length n; pp values are arrays or scalars).

    eff_shift: additive PPP tilt (per column) converted to a multiplicative shooting-% tilt.
    three_shift: share of field-goal attempts moved from 2PA to 3PA (negative moves toward 2PA).
    """
    pts = np.zeros(n)
    alive = mask.copy()
    eff = 1.0 + np.asarray(eff_shift) / np.maximum(pp["expected_ppp"], 0.5)
    fg3 = np.minimum(pp["fg3"] * eff, 0.8); fg2 = np.minimum(pp["fg2"] * eff, 0.9); ft = pp["ft"]
    p_fga = pp["p_3"] + pp["p_2"]
    p3 = np.clip(pp["p_3"] + three_shift * p_fga, 0.0, p_fga)
    cum_tov = pp["p_tov"]; cum_trip = cum_tov + pp["p_trip"]; cum_3 = cum_trip + p3
    for k in range(5):  # at most 5 plays per possession
        if not alive.any():
            break
        u = rng.random(n)
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
        missed = (three & ~made3) | (two & ~made2) | (trip & ~ft2 & ~ft3)
        alive = missed & (rng.random(n) < pp["oreb"])  # offensive rebound keeps the possession alive
    return pts


def _expand(pp: dict, S: int) -> dict:
    return {k: np.repeat(np.asarray(v, dtype=float), S) for k, v in pp.items()}


def simulate_batch(homes: list[TeamProfile], aways: list[TeamProfile], lgs: list[LeagueAverages] | LeagueAverages,
                   n_sims: int = 2000, seed: int | None = 7, neutral: list[bool] | None = None,
                   kappa_game: float = KAPPA_GAME, kappa_end: float = KAPPA_END, form_sd: float = FORM_SD,
                   return_samples: bool = False) -> list[dict]:
    """Simulate G games with S sims each in one vectorised pass. Returns one summary dict per game."""
    G = len(homes)
    S = n_sims
    N = G * S
    if not isinstance(lgs, list):
        lgs = [lgs] * G
    neutral = neutral or [False] * G
    rng = np.random.default_rng(seed)
    ph_list, pa_list, mean_poss, foul_h, foul_a, clutch_h, clutch_a = [], [], [], [], [], [], []
    for h, a, lg, nt in zip(homes, aways, lgs, neutral):
        ph_list.append(play_probabilities(matchup_rates(h, a, lg, True, nt)))
        pa_list.append(play_probabilities(matchup_rates(a, h, lg, False, nt)))
        cp = sum(((t.coach_pace - 50) / 50 * 1.0) for t in (h, a) if t.coach_pace is not None)
        mean_poss.append(lg.pace + (h.pace - lg.pace) + (a.pace - lg.pace) + cp + PACE_BIAS)
        foul_h.append(0.5 if h.coach_foul_up3 is None else h.coach_foul_up3 / 100)
        foul_a.append(0.5 if a.coach_foul_up3 is None else a.coach_foul_up3 / 100)
        clutch_h.append(0.0 if h.coach_clutch is None else (h.coach_clutch - 50) / 50 * CLUTCH_PPP_PER_SCORE / 2)
        clutch_a.append(0.0 if a.coach_clutch is None else (a.coach_clutch - 50) / 50 * CLUTCH_PPP_PER_SCORE / 2)
    keys = ["p_tov", "p_trip", "p_3", "p_2", "fg3", "fg2", "ft", "oreb", "expected_ppp"]
    ph = _expand({k: [d[k] for d in ph_list] for k in keys}, S)
    pa = _expand({k: [d[k] for d in pa_list] for k in keys}, S)
    mean_poss_c = np.repeat(np.asarray(mean_poss), S)
    foul_h_c = np.repeat(np.asarray(foul_h), S); foul_a_c = np.repeat(np.asarray(foul_a), S)
    clutch_c = np.repeat(np.asarray(clutch_h) - np.asarray(clutch_a), S)
    n_poss = np.clip(np.round(rng.normal(mean_poss_c, PACE_SD)), 80, 125).astype(int)
    form_h = rng.normal(0.0, form_sd, N); form_a = rng.normal(0.0, form_sd, N)
    hs = np.zeros(N); as_ = np.zeros(N)
    home_first = rng.random(N) < 0.5
    max_poss = int(n_poss.max())
    for i in range(max_poss):
        active = i < n_poss
        remaining = n_poss - i
        endgame = active & (remaining <= ENDGAME_POSS)
        for who in (0, 1):
            offence_home = home_first if who == 0 else ~home_first
            mask_home = active & offence_home
            mask_away = active & ~offence_home
            margin_h = hs - as_
            close = np.abs(margin_h) <= CLUTCH_MARGIN
            # shot-selection shifts for the trailing team
            shift_h = np.zeros(N); shift_a = np.zeros(N)
            down_h = -margin_h; down_a = margin_h
            for shift, down in ((shift_h, down_h), (shift_a, down_a)):
                shift[endgame & (down >= 4) & (down <= 12)] = 0.18
                shift[endgame & (remaining <= 2) & (down >= 4) & (down <= 6)] = 0.40
                shift[active & (remaining <= 1) & (down == 3)] = 0.80          # need a three to tie
                shift[active & (remaining <= 1) & (down >= 1) & (down <= 2)] = -0.15  # drive for the tie / lead
                shift[active & (remaining <= 1) & (down >= -2) & (down <= 0)] = -0.10  # protect a small lead: safer twos
            # leaders milk the clock late (possession lost to the shot clock / fewer possessions)
            late_lead_h = endgame & (remaining <= 4) & (margin_h > 6)
            late_lead_a = endgame & (remaining <= 4) & (margin_h < -6)
            skip = ((mask_home & late_lead_h) | (mask_away & late_lead_a)) & (rng.random(N) < 0.35)
            # intentional fouling: final three possessions, trailing by 3-9 -> leader shoots two free throws
            foul_sit_home_trails = np.zeros(N, dtype=bool)   # handled by the end-game extension phase
            foul_sit_away_trails = np.zeros(N, dtype=bool)
            # foul up three on the final defensive possession
            up3_h = np.zeros(N, dtype=bool); up3_a = np.zeros(N, dtype=bool)  # handled by the extension phase
            kappa = kappa_game + np.where(endgame, kappa_end, 0.0)
            eff_h = -kappa * margin_h + np.where(endgame & close, clutch_c, 0.0) + form_h
            eff_a = kappa * margin_h - np.where(endgame & close, clutch_c, 0.0) + form_a
            # home offence
            m = mask_home & ~skip
            ft_only = foul_sit_away_trails | up3_a
            normal = m & ~ft_only
            if normal.any():
                hs += _possession_points(rng, N, ph, normal, shift_h, eff_h)
            fts = m & ft_only
            if fts.any():
                hs += fts * ((rng.random(N) < ph["ft"]).astype(float) + (rng.random(N) < ph["ft"]).astype(float))
            # away offence
            m = mask_away & ~skip
            ft_only = foul_sit_home_trails | up3_h
            normal = m & ~ft_only
            if normal.any():
                as_ += _possession_points(rng, N, pa, normal, shift_a, eff_a)
            fts = m & ft_only
            if fts.any():
                as_ += fts * ((rng.random(N) < pa["ft"]).astype(float) + (rng.random(N) < pa["ft"]).astype(float))
    # end-game extension: a team trailing by 1-9 fouls to get the ball back; each cycle = leader free
    # throws + a rushed trailer possession (threes when down 3+). Up to FOUL_CYCLES cycles.
    for cyc in range(FOUL_CYCLES):
        margin_h = hs - as_
        trail_h = (margin_h <= -1) & (margin_h >= -9)
        trail_a = (margin_h >= 1) & (margin_h <= 9)
        last = cyc == FOUL_CYCLES - 1
        # leader free throws (home leads -> home shoots; a leader up exactly 3 on the last cycle may instead be
        # fouled only if the trailer chooses to foul; we model that the trailer always fouls here)
        hs += trail_a * ((rng.random(N) < ph["ft"]).astype(float) + (rng.random(N) < ph["ft"]).astype(float))
        as_ += trail_h * ((rng.random(N) < pa["ft"]).astype(float) + (rng.random(N) < pa["ft"]).astype(float))
        margin_h = hs - as_
        trail_h = (margin_h <= -1) & (margin_h >= -9)
        trail_a = (margin_h >= 1) & (margin_h <= 9)
        down_h = -margin_h; down_a = margin_h
        shift_h = np.where(down_h >= 3, 0.75, -0.15); shift_a = np.where(down_a >= 3, 0.75, -0.15)
        # leader up exactly three fouls before the shot with coach-specific probability -> trailer gets two FTs instead
        up3_a_fouls = trail_h & (down_h == 3) & (rng.random(N) < foul_a_c)
        up3_h_fouls = trail_a & (down_a == 3) & (rng.random(N) < foul_h_c)
        hs += (trail_h & ~up3_a_fouls) * 0 + _possession_points(rng, N, ph, trail_h & ~up3_a_fouls, shift_h, form_h - 0.08)
        hs += up3_a_fouls * ((rng.random(N) < ph["ft"]).astype(float) + (rng.random(N) < ph["ft"]).astype(float))
        as_ += _possession_points(rng, N, pa, trail_a & ~up3_h_fouls, shift_a, form_a - 0.08)
        as_ += up3_h_fouls * ((rng.random(N) < pa["ft"]).astype(float) + (rng.random(N) < pa["ft"]).astype(float))
    # overtime
    tied = hs == as_
    ot_count = np.zeros(N, dtype=int)
    rounds = 0
    zero = np.zeros(N)
    while tied.any() and rounds < 6:
        rounds += 1
        ot_count[tied] += 1
        for _ in range(OT_POSS):
            hs += _possession_points(rng, N, ph, tied, zero, form_h)
            as_ += _possession_points(rng, N, pa, tied, zero, form_a)
        tied = hs == as_
    if tied.any():
        flip = rng.random(N) < 0.5
        hs += tied & flip; as_ += tied & ~flip
    margin = (hs - as_).reshape(G, S)
    total = (hs + as_).reshape(G, S)
    hsr = hs.reshape(G, S); asr = as_.reshape(G, S); otr = ot_count.reshape(G, S)
    out = []
    for g in range(G):
        d = dict(home=homes[g].name, away=aways[g].name, n_sims=S,
                 home_win_prob=float((margin[g] > 0).mean()),
                 mean_margin=float(margin[g].mean()), median_margin=float(np.median(margin[g])),
                 mean_total=float(total[g].mean()), median_total=float(np.median(total[g])),
                 home_mean=float(hsr[g].mean()), away_mean=float(asr[g].mean()),
                 margin_sd=float(margin[g].std()), total_sd=float(total[g].std()),
                 ot_rate=float((otr[g] > 0).mean()),
                 margin_quantiles={q: float(np.quantile(margin[g], q)) for q in (0.05, 0.25, 0.5, 0.75, 0.95)},
                 total_quantiles={q: float(np.quantile(total[g], q)) for q in (0.05, 0.25, 0.5, 0.75, 0.95)},
                 expected_poss=float(mean_poss[g]), ppp_home=float(ph_list[g]["expected_ppp"]), ppp_away=float(pa_list[g]["expected_ppp"]))
        if return_samples:
            d.update(margin_samples=margin[g], total_samples=total[g], home_samples=hsr[g], away_samples=asr[g])
        out.append(d)
    return out


def simulate(home: TeamProfile, away: TeamProfile, lg: LeagueAverages | None = None, n_sims: int = 20000,
             seed: int | None = 7, neutral: bool = False, **kw) -> dict:
    return simulate_batch([home], [away], lg or LeagueAverages(), n_sims=n_sims, seed=seed, neutral=[neutral],
                          return_samples=True, **kw)[0]


def cover_probability(result: dict, home_spread: float) -> tuple[float, float]:
    """(P(home covers), P(push)) for a conventional spread, e.g. -4.5 means home must win by 5+."""
    m = result["margin_samples"]
    return float((m + home_spread > 0).mean()), float((m + home_spread == 0).mean())


def over_probability(result: dict, total_line: float) -> tuple[float, float]:
    t = result["total_samples"]
    return float((t > total_line).mean()), float((t == total_line).mean())


def profile_from_row(name: str, row, lg: LeagueAverages) -> TeamProfile:
    """Build a TeamProfile from a team_game_features-style row (ewm_* / adj_* columns)."""
    def g(k, d):
        try:
            v = row[k]
        except (KeyError, IndexError):
            return d
        return float(v) if v == v else d
    return TeamProfile(
        name=name, off_rtg=g("adj_off", lg.off_rtg), def_rtg=g("adj_def", lg.off_rtg), pace=g("adj_pace", lg.pace),
        fg3a_rate=g("ewm_fg3a_rate", lg.fg3a_rate), fg3_pct=g("ewm_fg3_pct", lg.fg3_pct), fg2_pct=g("ewm_fg2_pct", lg.fg2_pct),
        ftr=g("ewm_ftr", lg.ftr), ft_pct=g("ewm_ft_pct", lg.ft_pct), tov_pct=g("ewm_tov_pct", lg.tov_pct),
        oreb_pct=g("ewm_oreb_pct", lg.oreb_pct), dreb_pct=g("ewm_dreb_pct", 1 - lg.oreb_pct),
        opp_fg3a_rate=g("ewm_opp_fg3a_rate", lg.fg3a_rate), opp_fg3_pct=g("ewm_opp_fg3_pct", lg.fg3_pct),
        opp_tov_pct=g("ewm_opp_tov_pct", lg.tov_pct), opp_ftr=g("ewm_opp_ftr", lg.ftr),
    )


def league_from_row(row, home_court: float = 2.2) -> LeagueAverages:
    def g(k, d):
        try:
            v = row[k]
        except (KeyError, IndexError):
            return d
        return float(v) if v == v else d
    return LeagueAverages(off_rtg=g("lg_off_rtg", 114.5), pace=g("lg_pace", 99.0), fg3a_rate=g("lg_fg3a_rate", 0.40),
                          fg3_pct=g("lg_fg3_pct", 0.362), fg2_pct=g("lg_fg2_pct", 0.546), ftr=g("lg_ftr", 0.26),
                          ft_pct=g("lg_ft_pct", 0.78), tov_pct=g("lg_tov_pct", 0.137), oreb_pct=g("lg_oreb_pct", 0.245),
                          home_court=home_court)


if __name__ == "__main__":
    import time
    lg = LeagueAverages()
    h = TeamProfile("BOS", 120.0, 110.0, 97.0, 0.50, 0.37, 0.56, 0.24, 0.80, 0.12, 0.22, 0.75, 0.40, 0.36, 0.14, 0.25, coach_three=85, coach_clutch=70)
    a = TeamProfile("ORL", 111.0, 109.0, 98.5, 0.33, 0.33, 0.55, 0.30, 0.76, 0.15, 0.27, 0.74, 0.37, 0.355, 0.15, 0.27, coach_pace=55, coach_foul_up3=70)
    t0 = time.time(); r = simulate(h, a, lg, n_sims=20000)
    print(f"single {time.time()-t0:.2f}s", {k: (round(v, 3) if isinstance(v, float) else v) for k, v in r.items() if not k.endswith("samples") and not isinstance(v, dict)})
    print("margin q", {k: round(v, 1) for k, v in r["margin_quantiles"].items()}, "| P(BOS -6.5)", cover_probability(r, -6.5), "| P(over 228.5)", over_probability(r, 228.5))
    t0 = time.time(); rs = simulate_batch([h] * 300, [a] * 300, lg, n_sims=1000)
    print(f"batch 300 games x 1000 sims: {time.time()-t0:.1f}s; mean wp {np.mean([x['home_win_prob'] for x in rs]):.3f}")

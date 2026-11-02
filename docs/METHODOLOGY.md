# Methodology

## 1. Data lake

Season labels use the END year (2027 = 2026-27). Sources are the sportsdataverse mirrors of ESPN and stats.nba.com data, downloaded per season as parquet from GitHub releases (`nba_quant/ingest/sdv_mirror.py`). The lake (`nba_quant/ingest/build_parquet.py`) joins NBA and ESPN game ids on date + home/away tri-code (ESPN codes normalised: GS→GSW, NY→NYK, NO→NOP, SA→SAS, UTAH→UTA, WSH→WAS) and keeps regular season, play-in, NBA Cup final and playoff games.

Possessions use the Basketball-Reference estimate averaged over both teams:
`0.5 * [(FGA + 0.4 FTA − 1.07 (ORB/(ORB+OppDRB)) (FGA − FGM) + TOV) + (same for the opponent)]`.
Pace = 48 · possessions / (team minutes / 5), so overtime games are normalised.

## 2. Pre-game team strength (`features/ratings.py`)

Everything is computed with a one-game shift inside each team's chronology, so a row only sees earlier games.

- **MOV Elo** (FiveThirtyEight-style): K = 20, home court 100 Elo, margin multiplier `((|m|+3)^0.8)/(7.5+0.006·Δ)`, 30% regression to the mean between seasons.
- **EWMA efficiencies** (half-life 10 games, continuous across seasons) of offensive/defensive rating, pace, eFG%, TOV%, ORB%, DRB%, FT rate, 3PA rate, 3P%, 2P%, FT%, assist share, and opponent-allowed versions.
- **One-step opponent adjustment**: a game's offensive rating is adjusted by how good the opponent's defence had been (its own pre-game EWMA relative to league average); the adjusted series is then EWMA'd (`adj_off`, `adj_def`, `adj_pace`).
- **Season-to-date blends**: expanding means blended with the prior-season mean using 12 pseudo-games, plus last-10 means, streaks, rest days, back-to-back flags, games in the last seven days.
- For scheduled games the same code runs on pseudo rows (stats NaN) so the shifted features evaluate to each team's current state.

## 3. Player impact and availability (`features/player_impact.py`, `features/injuries.py`)

Two regularised estimates per season (regular season only), blended across seasons with a 0.7 decay and shrinkage toward a replacement level of −1.5 points per 100 possessions:

1. **Lineup ridge**: five-man lineup net rating (relative to league) regressed on its five players, weighted by possessions, ridge λ = 2,500 possessions, prior that moves off replacement level after ~1,000 possessions.
2. **Minutes-weighted APM**: home margin per 100 possessions (minus the season's home-court mean) = Σ(min/48 · β) over home players − the same for away players, ridge toward the lineup estimate (λ = 40 game-equivalents).

Values for season S use only seasons < S (leakage-free); the live values also use the in-progress season. Values are deliberately compressed (top players ≈ +3 per 100); the effect on outcomes is calibrated empirically in `model/train.py` (`margin_per_out_val`, currently ≈ −1.15 points of home margin per unit of `diff_out_val`).

**Availability**: for each (game, team) the last official injury-report version published before tip-off is used (fallback: the latest version). Listed players are matched by stats.nba.com id, then normalised name within the team. Each rotation player (typical minutes ≥ 10, where typical minutes is an EWMA with half-life 5 games including zero-minute inactive games) contributes `(value − replacement) × typical_minutes/48` to `out_val` (Out/Doubtful) or `q_val` (Questionable). Historical play rates by listing: Questionable 57%, Probable 88%, Doubtful 2%, Available 85%, Out 0%.

## 4. Coaching tendencies (`coaching/metrics.py`, `coaching/scores.py`, `data/research/`)

**Rubric** (29 dimensions, 0-100, 50 = average): rotation (depth, star minutes load, consistency, youth trust, load management, closing flexibility); offense (pace, three-point emphasis, ball movement, transition, offensive rebounding, paint/post, play-calling/ATO quality); defense (aggressiveness, perimeter priority, foul discipline, zone usage, scheme adaptability); end-game (timeout aggressiveness, foul up three, late lineup shrink, challenge quality, two-for-one awareness, risk appetite, clutch reputation); overall (adaptability, player development, analytics adoption, reputation).

**Research layer**: seven parallel research passes (web search only; the build environment cannot open ESPN, The Athletic, Reddit, YouTube, X or Substack pages directly, so evidence comes from search summaries that quote those sources) produced one JSON per coach with a score, confidence, evidence sentences and source URLs per dimension, plus records, scheme tags, quotes, strengths and criticisms. A tenure table (69 stints incl. interims, with dates) was researched separately. Unsourced dimensions are capped at 0.3 confidence.

**Data layer** (five seasons of ESPN play-by-play and box scores, regular season, attributed to coaches by tenure dates):
- timeouts per game; share of opponent 6-0+ runs answered with a timeout before the run ended; run size at the timeout;
- coach's challenges and overturn rate (shrunk toward the league rate);
- clutch games (within 5 in the last 5 minutes), clutch wins, clutch net points;
- foul-up-3: final-30-second defensive possessions with exactly a 3-point lead and whether the leader fouled before a shot (shrunk);
- late trailing shot selection (3PA share when down 1-9 in the last 3 minutes); 2-for-1 shots (26-36 s left in Q1-Q3); trailing-late fouls;
- rotation: players with 10+/20+ minutes, bench minute share, top-3 minutes, minute concentration, minutes-weighted age and share of minutes to players ≤ 23 (rosters), DNP-rest counts;
- scheme proxies: pace, 3PA rate, assist share, ORB%, fast-break and paint point shares, opponent 3PA rate, opponent FT rate, opponent turnover rate.

Each metric is z-scored across the 30 current coaches (weighted by games) and mapped to `50 + 20z` (clipped 2-98). **Fusion**: `final = (c·research + w·data)/(c + w)` with c = research confidence and w = min(1, games/82); dimensions without a data counterpart use the research score. Composite indices: rotation, offense, defense, end-game, strategy (end-game + ATO + scheme adaptability + analytics), and overall (0.35 strategy + 0.20 rotation + 0.25 reputation + 0.20 adaptability). Simulator primitives: pace score, three-point score, foul-up-3 score, clutch (end-game) index.

## 5. Possession Monte Carlo (`sim/possession.py`, `sim/scenarios.py`)

Background: possession-level simulators that loop shot/turnover/rebound events with offensive rebounds extending possessions (e.g. the StatSurge R simulation, the University of Iowa tournament simulator, the NCSU box-score simulator, Squared2020's possession models) and end-of-game research (fouling up three shows little or no advantage in NBA data — Winston; the 2003-23 Bayesian study; the TSN review; the Journal of Sports Analytics 2019 end-of-game tactics metric) informed the design:

- Possessions per team ~ Normal(league pace + both teams' pace deviations + coaching tilt − 0.9, sd 2.6), identical for both teams.
- Each possession is a chain of plays: turnover, free-throw trip (two shots; 6% three-shot fouls; 6.5% and-ones on made twos), 3PA or 2PA; a missed shot is rebounded by the offence with the matchup ORB rate and the chain continues at 95% efficiency.
- Matchup rates = team rate + (opponent allowed rate − league); shooting percentages are rescaled by bisection so expected points per possession equals the target rating (league + team offence deviation + opponent defence deviation + half the home court + adjustments). The shot profile therefore drives variance while ratings pin the mean.
- Pre-game form noise: N(0, 0.03) points per possession per team per simulated game.
- Dynamics: a restoring force (leaders coast, trailers press) of 0.0008 PPP per point all game plus 0.0045 in the last 12 possessions; trailing teams shift to threes when down 4-12 (stronger when down 4-6 with 2 possessions left), hunt a three when down exactly 3 on the final possession, drive when down 1-2; leaders up 7+ milk the clock in the last four possessions; two late foul-to-extend cycles (leader free throws, rushed trailer possession) for teams down 1-9; a leader up exactly three fouls with the coach's foul-up-3 probability; clutch coaching tilts PPP by up to ±0.015 in close late possessions; ties go to 10-possession overtimes.
- Calibration against 2022-23 → 2025-26 games (1,200-game samples): simulated margin sd 13.9 vs realised residual sd 14.1; total sd 19.2 vs 18.5; OT rate 5.9% vs 5.0%; P(|margin| ≤ 1) 3.6% vs 3.9%; P(|margin| ≤ 3) 11.4% vs 14.4% (the simulation under-produces 2-3 point finishes).
- Scenarios: Out/Doubtful rotation players removed everywhere; each Questionable/Probable player is a binary switch (≤ 4 per game, remainder folded into the expected case); every combination is simulated and weighted by the listing play rates. The probability-weighted mixture is centred on the XGBoost margin/total via an offence adjustment on both teams, so the simulation contributes shape, injury deltas, overtime and line probabilities while the trained model contributes the mean.

## 6. Models (`model/train.py`)

XGBoost classifier (home win) and regressors (margin, total): depth 3, learning rate 0.015, subsample 0.8, column subsample 0.6, min child weight 25, L2 = 8, early stopping on the last 15% of the training period, final refit with the median best iteration. ~105 pre-game features (Elo, adjusted efficiencies, form, shot profiles, rest, injuries, coaching, naive expectations, ratings-only simulator outputs). Walk-forward by season; see RESULTS.md. Market reference: ESPN spread → win probability via N(0, 13.45²).

## 7. Kelly sizing (`betting/kelly.py`)

Full Kelly `f* = (bp − q)/b`; fractional Kelly with per-bet cap; simultaneous-slate allocation that maximises `E[log(1 + Σ fᵢ Rᵢ)]` over the joint outcome distribution (independence across games; exact enumeration up to 14 bets, Monte Carlo beyond) with per-bet and total exposure caps. Pushes are modelled for integer lines. Because the model's edge over the market is small and noisy, the dashboard defaults to a 0.25 multiplier, 3% per-bet cap and 15% total exposure.

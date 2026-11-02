# NBA Quant — win probability, spread and total prediction stack

End-to-end research and prediction system for NBA games:

1. **Data lake (parquet)** — five full seasons (2021-22 → 2025-26) plus the live 2026-27 season of game, team, player and lineup data, the official NBA injury report (every published version), play-by-play, and ESPN closing spreads.
2. **Coaching tendency scores** — all 30 head coaches scored 0-100 on 29 rotation / offense / defense / end-game / overall dimensions, fusing web research (interviews, pressers, analysts, beat writers, Reddit/X/YouTube discussion) with play-by-play metrics mined over the last five seasons and attributed to each coach via a tenure table.
3. **Possession-level Monte Carlo** — a vectorised simulator (turnovers, free-throw trips, 2PA/3PA, offensive rebounds, end-game fouling/tie-hunting/coasting, overtime) calibrated to five seasons of actual margins, totals and overtime rates, run per game across every in/out combination of **Questionable** players.
4. **XGBoost models** — walk-forward-validated win probability, margin and total models built only from pre-game information (ratings, schedule, injury report, coaching, simulator outputs).
5. **Dashboard (MVP)** — Streamlit app: today's slate with likeliest winner and predicted score, per-game distributions and injury scenarios, coaching comparison, model diagnostics, and **Kelly-criterion bet sizing** as a percentage of bankroll.

> Honest baseline: the model beats margin-of-victory Elo in every test season and matches the market on straight-up picks (~69% in 2025-26), but it does **not** beat the closing spread (margin MAE 11.2 vs 10.9 for the market; ~50% ATS on 3+ point disagreements). Use fractional Kelly (≤ 0.25) and tight caps. See [docs/RESULTS.md](docs/RESULTS.md).

## Quick start

```bash
pip install -r requirements.txt && pip install -e .
python scripts/build_all.py --download-all          # first run: download mirrors, build everything (~15 min; the historical simulation is the slow step)
streamlit run nba_quant/dashboard/app.py
```

Daily refresh (pull the latest live-season data, rebuild features, keep saved models unless you want to retrain):

```bash
python scripts/build_all.py --refresh --skip-sim-features --skip-train --date 2026-11-03
```

Individual steps are also runnable as modules, e.g. `python -m nba_quant.model.predict 2026-11-02` or `python -m nba_quant.sim.scenarios 2026-11-02`.

## Data sources and network notes

All bulk data comes from the sportsdataverse GitHub release mirrors (`github.com/sportsdataverse/sportsdataverse-data`), which republish ESPN (daily in-season) and stats.nba.com data as per-season parquet assets. This was chosen because the build environment can only reach GitHub and PyPI; `stats.nba.com`, ESPN, Basketball-Reference and the NBA's injury-report PDFs are blocked there. The mirror carries the official injury report (updated nightly, 15-minute versions), so pre-game statuses are available for every historical game. For same-day updates that post after the nightly mirror run, add rows to `data/injuries_override.csv` (`game_date, team, player_name, status, reason, source`); today's file contains the 08:30 ET updates found via web search (Irving, Haliburton, Nembhard, Aldama, Lively, Pippen Jr., Diallo).

Two extra prior seasons (2019-20, 2020-21) are downloaded only to give the player-impact model a leakage-free prior for 2021-22.

## Outputs

| File | Rows | What |
|---|---:|---|
| `data/parquet/games.parquet` | 7.8k | one row per game: ids, teams, scores, margin/total, OT periods, ESPN closing spread, venue |
| `data/parquet/teams.parquet` | 13.4k | team-game box score + opponent box + possessions, ratings, four factors, rest context |
| `data/parquet/players.parquet` | 175k | player-game box scores incl. inactive players and DNP reasons |
| `data/parquet/lineups.parquet` | 24k | five-man lineups per team-season (minutes, possessions, ratings, four factors, scoring splits) |
| `data/parquet/injuries.parquet` | 1.2M | every official injury-report version, normalised |
| `data/parquet/coaches.parquet`, `data/research/coaching_scores.csv` | 30 | coaching tendency scores (research, data, final, composites) |
| `data/research/coaches/*.json`, `coach_tenures.json` | 30 + 69 stints | research profiles with evidence/sources; head-coaching tenures with dates |
| `data/parquet/game_features.parquet` | 6.7k | model feature matrix (completed + upcoming games) |
| `models/*.json`, `models/metrics.json` | | XGBoost models, walk-forward metrics, availability calibration |
| `data/predictions/predictions_<date>.json` | | slate predictions, scenarios, distributions, Kelly table (if lines provided) |

Full schemas: [docs/DATA_DICTIONARY.md](docs/DATA_DICTIONARY.md). Method details: [docs/METHODOLOGY.md](docs/METHODOLOGY.md). Coaching tables: [docs/COACHING_SCORES.md](docs/COACHING_SCORES.md).

## How a prediction is produced

```
mirror downloads ─► parquet lake ─► team ratings (Elo, EWMA, opp-adjusted) ─┐
                                 ├► player impact values (lineup ridge + minutes APM) ─► injury-report availability features
                                 ├► coaching metrics (pbp) + research JSON ─► coaching scores
                                 └► game feature matrix ─► XGBoost (win / margin / total)
                                                            │
possession Monte Carlo (ratings, shot profiles, coaching primitives, injuries) ◄─ centred on XGBoost margin/total
                                                            │
                               scenario-weighted distribution ─► win prob, spread, total, cover/over probs ─► Kelly sizing ─► dashboard
```

- **Win probability** shown on the dashboard = average of the XGBoost probability and the scenario-weighted Monte Carlo probability.
- **Spread / total / predicted score** come from the simulated distribution centred on the XGBoost point estimates (the simulation supplies the shape, the injury what-ifs, overtime, and cover/over probabilities for any line).
- **Injury scenarios**: Out/Doubtful rotation players are removed in every scenario; each Questionable/Probable player is a switch (all combinations up to four per game), weighted by the historical play rate of the listing (Questionable ≈ 57%, Probable ≈ 88%, Doubtful ≈ 2%).
- **Kelly**: enter the odds you can get; the dashboard shows edge, full Kelly, fractional Kelly and a simultaneous-slate allocation (expected-log-growth optimisation with per-bet and total caps). You can also drop a `data/lines/lines_<date>.csv` (`home, away, home_ml, away_ml, spread_home, spread_odds, total, total_odds`) and the prediction script sizes the slate automatically.

## Repository layout

```
nba_quant/
  config.py                 seasons, paths, team ids
  ingest/sdv_mirror.py      GitHub-release downloader (ESPN + NBA Stats mirrors)
  ingest/build_parquet.py   canonical parquet lake
  features/ratings.py       Elo, EWMA / opponent-adjusted efficiencies, schedule context (pre-game, leakage-free)
  features/player_impact.py lineup ridge + minutes-weighted APM player values
  features/injuries.py      official injury report → pre-game availability features (+ manual overrides)
  features/build_features.py game-level feature matrix (completed + upcoming games)
  coaching/metrics.py       play-by-play coaching metrics (timeouts vs runs, challenges, clutch, foul-up-3, 2-for-1, rotation)
  coaching/scores.py        research + data fusion → coaches.parquet
  sim/possession.py         batched possession Monte Carlo
  sim/scenarios.py          injury in/out scenario enumeration, model-centred
  model/train.py            walk-forward XGBoost training + evaluation
  model/predict.py          slate predictions + Kelly
  betting/kelly.py          Kelly criterion (single, fractional, portfolio)
  dashboard/app.py          Streamlit MVP
scripts/                    build_all.py, run_sim_features.py, calibrate_sim.py, write_docs.py
tests/                      pytest suite (parsing, possessions, Kelly, simulator invariants, leakage check)
docs/                       METHODOLOGY, RESULTS, COACHING_SCORES, DATA_DICTIONARY
```

## Limitations

- Research coverage is uneven: the web-search budget ran out part-way through the coaching research, so some coaches (Rajakovic, Ott, Bickerstaff, Mazzulla, Carlisle) have low-confidence research dimensions and most 2026-27 records were not verifiable; the data-driven metrics carry more weight for them. Confidence is stored per dimension and shown in the dashboard.
- Player values are regularised APM-style estimates with a compressed scale; the availability effect is calibrated empirically (≈1.15 points of margin per unit of missing value above replacement) rather than taken at face value.
- The ESPN spread in the data is whatever ESPN's feed carried (treated as a closing-line proxy); no market totals or moneylines are in the data, so total/moneyline edges are not benchmarked.
- Early-season ratings are blended with regressed prior-season values; roster turnover (trades, free agency) is only learned as games are played.

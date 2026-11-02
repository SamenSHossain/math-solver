# Model results (walk-forward)

Trained 2026-11-02T22:30:35 UTC on 6,697 completed games, seasons [2022, 2023, 2024, 2025, 2026, 2027]. Each test season is scored with models fit only on earlier seasons (regular season + playoffs). Market = ESPN closing spread converted to a win probability with a normal(0, 13.45) margin model.

| Test season | Games | Log loss | Elo log loss | Market log loss | Accuracy | Market accuracy | Margin MAE | Market margin MAE | Total MAE | Season-mean total MAE | ATS vs market (edge >= 3) | n |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2024 | 1319 | 0.6195 | 0.6252 | 0.5848 | 0.657 | 0.689 | 11.15 | 10.64 | 14.62 | 16.38 | 0.510 | 537 |
| 2025 | 1321 | 0.6117 | 0.6263 | 0.5862 | 0.665 | 0.691 | 11.12 | 10.64 | 14.56 | 15.86 | 0.490 | 508 |
| 2026 | 1322 | 0.5903 | 0.6116 | 0.5763 | 0.694 | 0.687 | 11.20 | 10.95 | 14.87 | 15.96 | 0.539 | 464 |
| 2027 | 92 | 0.6395 | 0.6645 | 0.5661 | 0.620 | 0.696 | 12.28 | 11.16 | 15.98 | 16.15 | 0.375 | 40 |

## Calibration (predicted vs actual home win rate)

- 2024: (0.0, 0.3]: pred 0.27 / actual 0.15 (n=71); (0.3, 0.4]: pred 0.35 / actual 0.29 (n=191); (0.4, 0.5]: pred 0.45 / actual 0.46 (n=190); (0.5, 0.6]: pred 0.55 / actual 0.54 (n=272); (0.6, 0.7]: pred 0.65 / actual 0.63 (n=312); (0.7, 1.0]: pred 0.75 / actual 0.80 (n=283)
- 2025: (0.0, 0.3]: pred 0.24 / actual 0.20 (n=151); (0.3, 0.4]: pred 0.35 / actual 0.32 (n=142); (0.4, 0.5]: pred 0.45 / actual 0.45 (n=183); (0.5, 0.6]: pred 0.55 / actual 0.48 (n=212); (0.6, 0.7]: pred 0.65 / actual 0.66 (n=268); (0.7, 1.0]: pred 0.78 / actual 0.78 (n=365)
- 2026: (0.0, 0.3]: pred 0.24 / actual 0.17 (n=143); (0.3, 0.4]: pred 0.35 / actual 0.28 (n=153); (0.4, 0.5]: pred 0.45 / actual 0.44 (n=181); (0.5, 0.6]: pred 0.55 / actual 0.58 (n=229); (0.6, 0.7]: pred 0.65 / actual 0.65 (n=247); (0.7, 1.0]: pred 0.80 / actual 0.79 (n=369)
- 2027: (0.0, 0.3]: pred 0.24 / actual 0.17 (n=12); (0.3, 0.4]: pred 0.34 / actual 0.50 (n=8); (0.4, 0.5]: pred 0.46 / actual 0.46 (n=13); (0.5, 0.6]: pred 0.57 / actual 0.54 (n=13); (0.6, 0.7]: pred 0.66 / actual 0.52 (n=21); (0.7, 1.0]: pred 0.79 / actual 0.72 (n=25)

## Interpretation

- The model beats margin-of-victory Elo on log loss in every season and matches the market on straight-up pick accuracy (0.69 vs 0.69 in 2025-26).
- It does **not** beat the closing spread: margin MAE is about 0.3-0.5 points worse than the market and the against-the-spread win rate on 3+ point disagreements is roughly 50%. Treat model edges as noisy; use fractional Kelly (<= 0.25) with tight caps, and prefer markets where the model has information the line may not fully price (late injury news, rest).
- Totals: MAE about 14.6-14.9 vs 15.9-16.4 for a season-mean baseline (no market total is available in the data).
- Availability calibration: -1.15 points of margin per unit of missing rotation value (value above replacement x minutes share); a star worth +3 per 100 possessions playing 34 minutes is about 3.5 points of spread.

## Top features

- **win**: diff_elo_pre (0.092), diff_s2d_win (0.064), diff_ewm_net (0.060), diff_adj_net (0.044), sim_home_wp (0.038), exp_margin_naive (0.035), sim_margin (0.025), diff_s2d_adj_net (0.016), home_s2d_margin (0.014), home_elo_pre (0.013)
- **margin**: exp_margin_naive (0.104), diff_adj_net (0.086), diff_elo_pre (0.082), diff_s2d_win (0.046), diff_ewm_net (0.046), sim_home_wp (0.033), sim_margin (0.032), diff_s2d_adj_net (0.016), diff_l10_margin (0.013), away_out_n (0.013)
- **total**: exp_total_naive (0.081), sim_total (0.066), sum_adj_pace (0.062), sum_def (0.020), sum_off (0.017), playoffs (0.016), home_adj_pace (0.015), away_games_last_7d (0.015), away_ewm_dreb_pct (0.014), home_ewm_efg (0.014)
"""Generate the data-driven documentation pages (coaching scores, results, data dictionary)."""
from __future__ import annotations

import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import pandas as pd

from nba_quant.config import MODEL_DIR, PARQUET_DIR, RESEARCH_DIR, ROOT

DOCS = ROOT / "docs"; DOCS.mkdir(exist_ok=True)

# ----------------------------------------------------------------------------- coaching scores
c = pd.read_parquet(PARQUET_DIR / "coaches.parquet").sort_values("overall_coaching_score", ascending=False)
lines = ["# Coaching tendency scores", "",
         "Scores are 0-100 with 50 = league-average head coach. `final` blends the research score (interviews, pressers, analysts, beat writers, "
         "Reddit/X/YouTube discussion found through web search) with a play-by-play metric score (five seasons of games attributed to the coach via "
         "the tenure table), weighted by research confidence and games coached. Six 2026-27 first-year coaches (Splitter, May, Mosley-NOP, Sweeney, Nori, "
         "Jenkins-MIL) carry little or no in-tenure data for their current team; Jenkins and Mosley inherit their prior-team metrics.", "",
         "Research coverage caveat: the web-search budget available during the research pass was exhausted part-way, so several coaches "
         "(notably Rajakovic, Ott, Bickerstaff, Mazzulla, Carlisle) have low-confidence research dimensions; their final scores lean on the data metrics. "
         "`research_confidence` is the mean per-dimension confidence (0-1).", "",
         "## Composite indices", "",
         "| Coach | Team | HC since | Games in data | Win% | Research conf | Overall | Strategy | Rotation | Star load | End-game | Offense | Defense |",
         "|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
for r in c.itertuples():
    lines.append(f"| {r.coach} | {r.team} | {r.head_coach_since} | {int(r.games_in_data)} | {r.win_pct_in_data:.3f} | {r.research_confidence:.2f} | "
                 f"{r.overall_coaching_score:.0f} | {r.strategy_index:.0f} | {r.rotation_index:.0f} | {r.star_load_index:.0f} | {r.endgame_index:.0f} | {r.offense_index:.0f} | {r.defense_index:.0f} |")
lines += ["", "## Dimension scores (final)", ""]
dims = [col for col in c.columns if col.startswith("score__")]
groups = sorted({d.split("__")[1].split(".")[0] for d in dims}, key=["rotation", "offense", "defense", "endgame", "overall"].index)
for g in groups:
    gd = [d for d in dims if d.split("__")[1].startswith(g + ".")]
    lines += [f"### {g}", "", "| Coach | " + " | ".join(d.split(".")[1] for d in gd) + " |", "|---|" + "---:|" * len(gd)]
    for _, r in c.iterrows():
        lines.append(f"| {r['coach']} ({r['team']}) | " + " | ".join(f"{r[d]:.0f}" for d in gd) + " |")
    lines.append("")
lines += ["## Scheme tags and notes", ""]
for r in c.itertuples():
    lines += [f"**{r.coach} ({r.team})** · defense: `{r.defense_scheme_tags}` · offense: `{r.offense_scheme_tags}`", f"- Strengths: {r.key_strengths}", f"- Criticisms: {r.key_criticisms}", ""]
lines += ["## Data-driven metrics per coach (career over 2021-22 .. today, regular season)", ""]
career = pd.read_parquet(PARQUET_DIR / "coach_career_metrics.parquet")
cur = c[["slug", "coach", "team"]].merge(career, on="slug")
cols = ["coach", "team", "games", "win_pct", "pace", "fg3a_rate", "ast_pct", "oreb_pct", "opp_fg3a_rate", "opp_ftr", "opp_tov_pct", "n_10min", "bench_min_share", "top3_min",
        "young_min_share", "to_total", "run_timeout_rate", "chal_count", "chal_rate", "foul_up3_opps", "foul_up3_rate", "two_for_one_shots", "clutch_games", "clutch_win_pct", "clutch_net_per_game", "late_trail_3pa_rate"]
lines.append("| " + " | ".join(cols) + " |"); lines.append("|" + "---|" * len(cols))
for r in cur[cols].itertuples(index=False):
    lines.append("| " + " | ".join(f"{v:.3f}" if isinstance(v, float) else str(v) for v in r) + " |")
lines += ["", "Metric definitions: `run_timeout_rate` = share of opponent 6-0+ runs answered with a timeout before the run ended; `chal_rate` = coach's-challenge "
          "overturn rate (shrunk, pseudo-count 10); `foul_up3_rate` = share of final-30-second, up-exactly-3 defensive possessions where the leader fouled before a shot "
          "(shrunk, pseudo-count 5); `two_for_one_shots` = shots per game taken with 26-36 s left in Q1-Q3; `clutch_*` = games within 5 in the last 5 minutes; "
          "`late_trail_3pa_rate` = 3PA share when trailing 1-9 in the last 3 minutes; `n_10min` = players with 10+ minutes per game; `young_min_share` = minutes to players aged 23 or younger."]
(DOCS / "COACHING_SCORES.md").write_text("\n".join(lines))

# ----------------------------------------------------------------------------- results
m = json.loads((MODEL_DIR / "metrics.json").read_text())
wf = m["walk_forward"]
r_lines = ["# Model results (walk-forward)", "", f"Trained {m['trained_at_utc'][:19]} UTC on {m['n_train']:,} completed games, seasons {m['seasons']}. "
           "Each test season is scored with models fit only on earlier seasons (regular season + playoffs). Market = ESPN closing spread "
           "converted to a win probability with a normal(0, 13.45) margin model.", "",
           "| Test season | Games | Log loss | Elo log loss | Market log loss | Accuracy | Market accuracy | Margin MAE | Market margin MAE | Total MAE | Season-mean total MAE | ATS vs market (edge >= 3) | n |",
           "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
for s, r in wf.items():
    r_lines.append(f"| {s} | {r['n']} | {r['logloss']:.4f} | {r['elo_logloss']:.4f} | {r.get('market_logloss', float('nan')):.4f} | {r['accuracy']:.3f} | {r.get('market_accuracy', float('nan')):.3f} | "
                   f"{r['margin_mae']:.2f} | {r.get('market_margin_mae', float('nan')):.2f} | {r['total_mae']:.2f} | {r['total_mae_seasonmean_baseline']:.2f} | "
                   f"{r.get('ats_win_rate_edge3plus', float('nan')):.3f} | {r.get('ats_n_edge3plus', 0)} |")
r_lines += ["", "## Calibration (predicted vs actual home win rate)", ""]
for s, r in wf.items():
    r_lines.append(f"- {s}: " + "; ".join(f"{b}: pred {v['pred']:.2f} / actual {v['actual']:.2f} (n={v['n']})" for b, v in r["calibration"].items()))
r_lines += ["", "## Interpretation", "",
            "- The model beats margin-of-victory Elo on log loss in every season and matches the market on straight-up pick accuracy (0.69 vs 0.69 in 2025-26).",
            "- It does **not** beat the closing spread: margin MAE is about 0.3-0.5 points worse than the market and the against-the-spread win rate on 3+ point disagreements is roughly 50%. "
            "Treat model edges as noisy; use fractional Kelly (<= 0.25) with tight caps, and prefer markets where the model has information the line may not fully price (late injury news, rest).",
            "- Totals: MAE about 14.6-14.9 vs 15.9-16.4 for a season-mean baseline (no market total is available in the data).",
            f"- Availability calibration: {m['availability_calibration']['margin_per_out_val']:.2f} points of margin per unit of missing rotation value (value above replacement x minutes share); "
            "a star worth +3 per 100 possessions playing 34 minutes is about 3.5 points of spread.", "",
            "## Top features", ""]
for name in ("win", "margin", "total"):
    r_lines.append(f"- **{name}**: " + ", ".join(f"{k} ({v:.3f})" for k, v in list(m["feature_importance_top25"][name].items())[:10]))
(DOCS / "RESULTS.md").write_text("\n".join(r_lines))

# ----------------------------------------------------------------------------- data dictionary
man = json.loads((PARQUET_DIR / "MANIFEST.json").read_text())
notes = {
    "games": "One row per game (regular season, play-in, NBA Cup final, playoffs; preseason excluded). Keys: `game_id` (stats.nba.com, 10-char string), `espn_game_id`. "
             "`margin` = home - away; `home_exp_margin_market` = ESPN spread as expected home margin (positive = home favoured); `home_spread_market` = conventional sign.",
    "teams": "One row per team-game: box score, opponent box score (`opp_*`), possessions (Basketball-Reference formula), pace, offensive/defensive rating, four factors, "
             "rest days / back-to-back / games in last 7 days, ESPN extras (fast-break points, paint points, lead changes).",
    "players": "One row per player-game including inactive players (`dnp`, `dnp_reason`, `dnp_injury`). `min_share` = share of team minutes; `usage` = usage-rate proxy.",
    "lineups": "Five-man lineups per team-season (regular season and playoffs) from stats.nba.com `leaguedashlineups`: minutes, possessions, off/def/net rating, four factors, scoring splits, opponent stats; "
               "player ids parsed into `player1_id..player5_id`.",
    "team_seasons": "Team-season aggregates (advanced, base, misc, scoring, opponent families folded wide).",
    "injuries": "Every published version of the official NBA injury report (2021-22 .. today): `report_datetime` (ET), `game_id`, `team`, `player_name`, `player_id`, `status`, `reason`, `reason_category`.",
}
d_lines = ["# Data dictionary", "", f"Built {man['built_at_utc'][:19]} UTC · seasons {man['seasons']} (END-year labels: 2027 = 2026-27). Sources: sportsdataverse GitHub release mirrors of ESPN "
           "(daily refresh in-season) and stats.nba.com data; see README for the refresh procedure.", ""]
for name, info in man["tables"].items():
    d_lines += [f"## `{name}.parquet`", "", f"{info['rows']:,} rows · {len(info['columns'])} columns · {info['bytes']/1e6:.1f} MB · last game date {info['max_game_date']}", "",
                notes.get(name, ""), "", "Columns: " + ", ".join(f"`{c}`" for c in info["columns"]), ""]
d_lines += ["## Derived tables", "",
            "- `team_game_features.parquet`: pre-game team state (Elo, EWMA / opponent-adjusted efficiencies, season-to-date blends, schedule context) per team-game.",
            "- `player_season_impact.parquet`, `player_values.parquet`, `player_values_current.parquet`: player impact values (points per 100 possessions on court vs average).",
            "- `coach_team_game_metrics.parquet`, `coach_season_metrics.parquet`, `coach_career_metrics.parquet`, `coach_game_attribution.parquet`, `coaches.parquet`: coaching metrics and scores.",
            "- `pregame_injury_lines.parquet`, `availability_features.parquet`, `player_typical_minutes.parquet`, `status_play_rates.json`: injury-report derived availability.",
            "- `game_features.parquet`: the model feature matrix (one row per game, completed + upcoming).",
            "- `sim_features.parquet`: ratings-only Monte Carlo outputs for every completed game (model inputs).", ""]
(DOCS / "DATA_DICTIONARY.md").write_text("\n".join(d_lines))
print("docs written:", [p.name for p in DOCS.glob("*.md")])

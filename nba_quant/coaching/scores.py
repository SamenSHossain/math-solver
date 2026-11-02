"""Coaching tendency scores: fuse qualitative research with tenure-attributed play-by-play metrics.

Inputs
  data/research/coaches/<slug>.json   research profiles (29 dimensions, 0-100, with confidence)
  data/research/coach_tenures.json    head-coaching stints with dates (interims included)
  data/parquet/coach_team_game_metrics.parquet   per team-game metrics mined from pbp/box scores

Method
  1. Attribute every team-game (2021-22 .. today) to the head coach via the tenure table.
  2. Aggregate per coach (regular season): rotation, scheme and end-game metrics, W-L, clutch record.
  3. Convert each data metric to a 0-100 score: 50 + 20 * z (z across the 30 current coaches'
     pooled coach-seasons, minutes-weighted), clipped to [2, 98]. Rates with small denominators
     (foul-up-3, challenges, clutch wins) are shrunk toward the league rate with a pseudo-count.
  4. Fuse: final = (c * research + w * data) / (c + w), c = research confidence (capped at 0.3 when
     unsourced), w = min(1, games_coached / 82) when a data counterpart exists, else research only.
  5. Composite indices: rotation_index, offense_index, defense_index, endgame (strategy) index,
     overall_coaching_score; the model and simulator consume the composites and a few primitives.
"""
from __future__ import annotations

import json
import logging
from datetime import date

import numpy as np
import pandas as pd

from nba_quant.config import PARQUET_DIR, RESEARCH_DIR, TEAM_NAMES

log = logging.getLogger(__name__)

DIMENSIONS = {
    "rotation": ["depth", "star_minutes_load", "consistency", "youth_trust", "load_management", "closing_flexibility"],
    "offense": ["pace", "three_point_emphasis", "ball_movement", "transition_emphasis", "offensive_rebounding", "paint_post_emphasis", "playcalling_ato_quality"],
    "defense": ["aggressiveness", "perimeter_priority", "foul_discipline", "zone_usage", "scheme_adaptability"],
    "endgame": ["timeout_aggressiveness", "foul_up_three", "late_lineup_shrink", "challenge_quality", "two_for_one_awareness", "risk_appetite", "clutch_reputation"],
    "overall": ["adaptability", "player_development", "analytics_adoption", "reputation"],
}
# data metric -> (dimension, sign)   (+1: higher metric = higher score)
DATA_MAP = {
    "n_10min": ("rotation.depth", +1), "bench_min_share": ("rotation.depth", +1),
    "top3_min": ("rotation.star_minutes_load", +1),
    "rotation_churn": ("rotation.consistency", -1),
    "young_min_share": ("rotation.youth_trust", +1), "age_wtd": ("rotation.youth_trust", -1),
    "n_dnp_rest": ("rotation.load_management", +1),
    "pace": ("offense.pace", +1), "fg3a_rate": ("offense.three_point_emphasis", +1),
    "ast_pct": ("offense.ball_movement", +1), "fb_share": ("offense.transition_emphasis", +1),
    "oreb_pct": ("offense.offensive_rebounding", +1), "paint_share": ("offense.paint_post_emphasis", +1),
    "opp_tov_pct": ("defense.aggressiveness", +1), "opp_fg3a_rate": ("defense.perimeter_priority", -1),
    "opp_ftr": ("defense.foul_discipline", -1),
    "run_timeout_rate": ("endgame.timeout_aggressiveness", +1), "to_total": ("endgame.timeout_aggressiveness", +1),
    "foul_up3_rate": ("endgame.foul_up_three", +1), "chal_rate": ("endgame.challenge_quality", +1),
    "two_for_one_shots": ("endgame.two_for_one_awareness", +1), "late_trail_3pa_rate": ("endgame.risk_appetite", +1),
    "clutch_net_per_game": ("endgame.clutch_reputation", +1), "clutch_win_pct": ("endgame.clutch_reputation", +1),
}


def load_research() -> dict[str, dict]:
    out = {}
    for f in sorted((RESEARCH_DIR / "coaches").glob("*.json")):
        d = json.loads(f.read_text())
        out[d["slug"]] = d
    return out


def load_tenures() -> pd.DataFrame:
    t = pd.DataFrame(json.loads((RESEARCH_DIR / "coach_tenures.json").read_text()))
    t["start_date"] = pd.to_datetime(t["start_date"])
    t["end_date"] = pd.to_datetime(t["end_date"]).fillna(pd.Timestamp(date.today()) + pd.Timedelta(days=1))
    t["slug"] = t["coach"].map(slugify)
    return t


def slugify(name: str) -> str:
    import re, unicodedata
    s = unicodedata.normalize("NFKD", name).encode("ascii", "ignore").decode().lower()
    s = re.sub(r"[^a-z ]", "", s)
    return "-".join(s.split())


def attribute_games(metrics: pd.DataFrame, tenures: pd.DataFrame) -> pd.DataFrame:
    m = metrics.copy()
    m["game_date"] = pd.to_datetime(m["game_date"])
    m["coach"] = None; m["slug"] = None; m["interim"] = False
    for r in tenures.itertuples(index=False):
        sel = (m["team"] == r.team) & (m["game_date"] >= r.start_date) & (m["game_date"] <= r.end_date)
        m.loc[sel, ["coach", "slug", "interim"]] = [r.coach, r.slug, bool(r.interim)]
    unattributed = m["coach"].isna().mean()
    if unattributed > 0:
        log.warning("%.1f%% of team-games not attributed to a coach", 100 * unattributed)
    return m


def coach_season_metrics(m: pd.DataFrame) -> pd.DataFrame:
    reg = m[(m["season_type"] == "regular") & m["slug"].notna()].copy()
    reg["clutch_net"] = reg["clutch_pts_for"] - reg["clutch_pts_against"]
    g = reg.groupby(["slug", "coach", "season", "team"])
    agg = g.agg(games=("game_id", "size"), wins=("win", "sum"), margin=("margin", "mean"),
                pace=("pace", "mean"), fg3a_rate=("fg3a_rate", "mean"), ast_pct=("ast_pct", "mean"), oreb_pct=("oreb_pct", "mean"),
                ftr=("ftr", "mean"), fb_share=("fb_share", "mean"), paint_share=("paint_share", "mean"),
                opp_fg3a_rate=("opp_fg3a_rate", "mean"), opp_ftr=("opp_ftr", "mean"), opp_tov_pct=("opp_tov_pct", "mean"),
                n_10min=("n_10min", "mean"), bench_min_share=("bench_min_share", "mean"), top3_min=("top3_min", "mean"),
                rotation_churn=("n_10min", "std"), young_min_share=("young_min_share", "mean"), age_wtd=("age_wtd", "mean"),
                n_dnp_rest=("n_dnp_rest", "mean"), to_total=("to_total", "mean"), to_q4_last3=("to_q4_last3", "mean"),
                runs6_against=("runs6_against", "sum"), runs6_timeout=("runs6_timeout", "sum"),
                chal_count=("chal_count", "sum"), chal_success=("chal_success", "sum"),
                clutch_games=("clutch_game", "sum"), clutch_wins=("clutch_win", "sum"), clutch_net=("clutch_net", "sum"),
                foul_up3_opps=("foul_up3_opps", "sum"), foul_up3_fouls=("foul_up3_fouls", "sum"),
                two_for_one_shots=("two_for_one_shots", "mean"), late_trail_fga=("late_trail_fga", "sum"), late_trail_fg3a=("late_trail_fg3a", "sum"),
                ot_games=("ot", "sum")).reset_index()
    agg["win_pct"] = agg["wins"] / agg["games"]
    return agg


def coach_career(cs: pd.DataFrame, min_games: int = 10) -> pd.DataFrame:
    """Minutes-weighted career aggregation over the last five seasons + current."""
    cs = cs[cs["games"] >= 1].copy()
    w = cs["games"]
    def wmean(col):
        return (cs[col] * w).groupby(cs["slug"]).sum() / w.groupby(cs["slug"]).sum()
    out = pd.DataFrame({"slug": sorted(cs["slug"].unique())}).set_index("slug")
    for col in ["pace", "fg3a_rate", "ast_pct", "oreb_pct", "ftr", "fb_share", "paint_share", "opp_fg3a_rate", "opp_ftr", "opp_tov_pct",
                "n_10min", "bench_min_share", "top3_min", "rotation_churn", "young_min_share", "age_wtd", "n_dnp_rest", "to_total", "to_q4_last3",
                "two_for_one_shots", "margin"]:
        out[col] = wmean(col)
    sums = cs.groupby("slug")[["games", "wins", "runs6_against", "runs6_timeout", "chal_count", "chal_success", "clutch_games", "clutch_wins",
                               "clutch_net", "foul_up3_opps", "foul_up3_fouls", "late_trail_fga", "late_trail_fg3a", "ot_games"]].sum()
    out = out.join(sums)
    lg_f3 = sums["foul_up3_fouls"].sum() / max(sums["foul_up3_opps"].sum(), 1)
    lg_ch = sums["chal_success"].sum() / max(sums["chal_count"].sum(), 1)
    lg_cw = sums["clutch_wins"].sum() / max(sums["clutch_games"].sum(), 1)
    out["win_pct"] = out["wins"] / out["games"]
    out["run_timeout_rate"] = out["runs6_timeout"] / out["runs6_against"].replace(0, np.nan)
    out["foul_up3_rate"] = (out["foul_up3_fouls"] + 5 * lg_f3) / (out["foul_up3_opps"] + 5)           # shrunk
    out["chal_rate"] = (out["chal_success"] + 10 * lg_ch) / (out["chal_count"] + 10)
    out["clutch_win_pct"] = (out["clutch_wins"] + 10 * lg_cw) / (out["clutch_games"] + 10)
    out["clutch_net_per_game"] = out["clutch_net"] / out["clutch_games"].replace(0, np.nan)
    out["late_trail_3pa_rate"] = out["late_trail_fg3a"] / out["late_trail_fga"].replace(0, np.nan)
    out["seasons"] = cs.groupby("slug")["season"].nunique()
    out["teams"] = cs.groupby("slug")["team"].agg(lambda s: "/".join(sorted(set(s))))
    return out.reset_index()


def z_to_score(series: pd.Series, weights: pd.Series | None = None) -> pd.Series:
    x = series.astype(float)
    if weights is not None and weights.sum() > 0:
        mu = np.average(x.fillna(x.mean()), weights=weights.fillna(0))
        sd = np.sqrt(np.average((x.fillna(mu) - mu) ** 2, weights=weights.fillna(0)))
    else:
        mu, sd = x.mean(), x.std()
    sd = sd if sd and sd > 1e-9 else 1.0
    return (50 + 20 * (x - mu) / sd).clip(2, 98)


def research_table(research: dict[str, dict]) -> pd.DataFrame:
    rows = []
    for slug, d in research.items():
        for grp, dims in DIMENSIONS.items():
            for dim in dims:
                v = d.get("scores", {}).get(grp, {}).get(dim)
                if not v:
                    continue
                conf = float(v.get("confidence", 0.3))
                if not v.get("sources"):
                    conf = min(conf, 0.3)
                rows.append({"slug": slug, "dimension": f"{grp}.{dim}", "research_score": float(v["score"]), "confidence": conf,
                             "evidence": " | ".join(v.get("evidence", [])[:2])})
    return pd.DataFrame(rows)


def build_scores(write: bool = True) -> pd.DataFrame:
    research = load_research()
    tenures = load_tenures()
    metrics = pd.read_parquet(PARQUET_DIR / "coach_team_game_metrics.parquet")
    attributed = attribute_games(metrics, tenures)
    cs = coach_season_metrics(attributed)
    career = coach_career(cs).set_index("slug")
    rt = research_table(research)
    current = tenures[tenures["end_date"] > pd.Timestamp(date.today())].drop_duplicates("team").set_index("slug")

    # data scores (z across current coaches, weighted by games)
    data_scores = {}
    cur_slugs = [s for s in current.index if s in career.index]
    base = career.loc[cur_slugs]
    for metric, (dim, sign) in DATA_MAP.items():
        if metric not in base:
            continue
        sc = z_to_score(sign * base[metric], weights=base["games"])
        data_scores.setdefault(dim, []).append(sc)
    data_dim = {dim: pd.concat(lst, axis=1).mean(axis=1) for dim, lst in data_scores.items()}

    rows = []
    for slug in research:
        prof = research[slug]
        team = prof.get("team")
        games = float(career["games"].get(slug, 0.0)) if slug in career.index else 0.0
        w_data = min(1.0, games / 82.0)
        rec = {"slug": slug, "coach": prof["coach"], "team": team, "team_name": TEAM_NAMES.get(team, prof.get("team_name")),
               "head_coach_since": prof.get("head_coach_since"), "games_in_data": games,
               "win_pct_in_data": float(career["win_pct"].get(slug, np.nan)) if slug in career.index else np.nan,
               "avg_margin_in_data": float(career["margin"].get(slug, np.nan)) if slug in career.index else np.nan,
               "seasons_in_data": int(career["seasons"].get(slug, 0)) if slug in career.index else 0,
               "teams_in_data": career["teams"].get(slug, "") if slug in career.index else "",
               "defense_scheme_tags": ",".join(prof.get("defense_scheme_tags", [])),
               "offense_scheme_tags": ",".join(prof.get("offense_scheme_tags", [])),
               "key_strengths": " | ".join(prof.get("key_strengths", [])[:3]),
               "key_criticisms": " | ".join(prof.get("key_criticisms", [])[:3])}
        r_sub = rt[rt["slug"] == slug].set_index("dimension")
        confs = []
        for grp, dims in DIMENSIONS.items():
            for dim in dims:
                key = f"{grp}.{dim}"
                rs = float(r_sub["research_score"].get(key, 50.0)); c = float(r_sub["confidence"].get(key, 0.2))
                ds = data_dim.get(key, pd.Series(dtype=float)).get(slug, np.nan)
                if ds == ds and w_data > 0:
                    final = (c * rs + w_data * ds) / (c + w_data)
                else:
                    final = rs
                rec[f"research__{key}"] = rs
                rec[f"data__{key}"] = ds
                rec[f"score__{key}"] = float(final)
                confs.append(c)
        rec["research_confidence"] = float(np.mean(confs))
        rec["data_weight"] = w_data
        # composites
        g = lambda k: rec[f"score__{k}"]
        rec["rotation_index"] = np.mean([g("rotation.depth"), g("rotation.consistency"), g("rotation.closing_flexibility"), g("rotation.youth_trust")])
        rec["star_load_index"] = g("rotation.star_minutes_load")
        rec["offense_index"] = np.mean([g("offense.ball_movement"), g("offense.playcalling_ato_quality"), g("offense.three_point_emphasis")])
        rec["defense_index"] = np.mean([g("defense.aggressiveness"), g("defense.scheme_adaptability"), g("defense.foul_discipline")])
        rec["endgame_index"] = np.mean([g("endgame.clutch_reputation"), g("endgame.challenge_quality"), g("endgame.two_for_one_awareness"),
                                        g("endgame.timeout_aggressiveness"), g("overall.adaptability")])
        rec["strategy_index"] = np.mean([rec["endgame_index"], g("offense.playcalling_ato_quality"), g("defense.scheme_adaptability"), g("overall.analytics_adoption")])
        rec["overall_coaching_score"] = (0.35 * rec["strategy_index"] + 0.20 * rec["rotation_index"] + 0.25 * g("overall.reputation")
                                         + 0.20 * g("overall.adaptability"))
        # simulator primitives
        rec["sim_pace_score"] = g("offense.pace"); rec["sim_three_score"] = g("offense.three_point_emphasis")
        rec["sim_foul_up3_score"] = g("endgame.foul_up_three"); rec["sim_clutch_score"] = rec["endgame_index"]
        rows.append(rec)
    coaches = pd.DataFrame(rows).sort_values("overall_coaching_score", ascending=False).reset_index(drop=True)
    if write:
        coaches.to_parquet(PARQUET_DIR / "coaches.parquet", index=False)
        cs.to_parquet(PARQUET_DIR / "coach_season_metrics.parquet", index=False)
        career.reset_index().to_parquet(PARQUET_DIR / "coach_career_metrics.parquet", index=False)
        flat_cols = ["coach", "team", "head_coach_since", "games_in_data", "win_pct_in_data", "research_confidence", "data_weight",
                     "rotation_index", "star_load_index", "offense_index", "defense_index", "endgame_index", "strategy_index",
                     "overall_coaching_score"] + [c for c in coaches.columns if c.startswith("score__")] + ["defense_scheme_tags", "offense_scheme_tags"]
        coaches[flat_cols].round(1).to_csv(RESEARCH_DIR / "coaching_scores.csv", index=False)
        attributed[["game_id", "team", "season", "game_date", "coach", "slug", "interim"]].to_parquet(PARQUET_DIR / "coach_game_attribution.parquet", index=False)
        log.info("wrote coaches.parquet (%d coaches)", len(coaches))
    return coaches


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    pd.set_option("display.width", 250); pd.set_option("display.max_columns", 40)
    c = build_scores()
    print(c[["coach", "team", "games_in_data", "win_pct_in_data", "research_confidence", "rotation_index", "offense_index", "defense_index",
             "endgame_index", "strategy_index", "overall_coaching_score"]].round(1).to_string())
    print(c[["coach", "score__endgame.foul_up_three", "data__endgame.foul_up_three", "score__endgame.challenge_quality", "data__endgame.challenge_quality",
             "score__rotation.depth", "data__rotation.depth", "score__offense.pace", "data__offense.pace"]].round(1).head(12).to_string())

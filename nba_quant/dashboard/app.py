"""Streamlit dashboard: NBA win probability, spread and total predictions with injury scenarios,
coaching tendency scores, model diagnostics and Kelly bet sizing.

    streamlit run nba_quant/dashboard/app.py
"""
from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import pandas as pd
import plotly.graph_objects as go
import streamlit as st

from nba_quant.betting.kelly import Bet, american_to_decimal, portfolio_kelly, size_single
from nba_quant.config import MODEL_DIR, PARQUET_DIR, PRED_DIR, TEAM_NAMES

st.set_page_config(page_title="NBA Quant Dashboard", layout="wide", page_icon="🏀")

PALETTE = {"home": "#2563eb", "away": "#f97316", "neutral": "#64748b", "good": "#16a34a", "bad": "#dc2626"}


@st.cache_data(show_spinner=False)
def load_predictions(path: str) -> dict:
    return json.loads(Path(path).read_text())


@st.cache_data(show_spinner=False)
def load_parquet(name: str) -> pd.DataFrame:
    return pd.read_parquet(PARQUET_DIR / name)


@st.cache_data(show_spinner=False)
def load_metrics() -> dict:
    p = MODEL_DIR / "metrics.json"
    return json.loads(p.read_text()) if p.exists() else {}


def pct(x: float) -> str:
    return f"{100 * x:.1f}%"


def gradient(styler, subset, cmap="RdYlGn", vmin=None, vmax=None):
    """Apply a background gradient when matplotlib is available (it is optional)."""
    try:
        import matplotlib  # noqa: F401
        return styler.background_gradient(subset=subset, cmap=cmap, vmin=vmin, vmax=vmax)
    except ImportError:
        return styler


def hist_fig(h: dict, title: str, color: str, vline: float | None = None, line_label: str = "") -> go.Figure:
    edges = np.array(h["edges"]); counts = np.array(h["counts"], dtype=float)
    centers = (edges[:-1] + edges[1:]) / 2
    fig = go.Figure(go.Bar(x=centers, y=counts / counts.sum(), marker_color=color, opacity=0.85, hovertemplate="%{x}: %{y:.1%}<extra></extra>"))
    if vline is not None:
        fig.add_vline(x=vline, line_dash="dash", line_color=PALETTE["neutral"], annotation_text=line_label, annotation_position="top")
    fig.update_layout(title=title, height=300, margin=dict(l=10, r=10, t=40, b=10), yaxis_tickformat=".0%", showlegend=False,
                      plot_bgcolor="rgba(0,0,0,0)", paper_bgcolor="rgba(0,0,0,0)")
    return fig


# ----------------------------------------------------------------------------- sidebar
pred_files = sorted(PRED_DIR.glob("predictions_*.json"))
st.sidebar.title("🏀 NBA Quant")
if not pred_files:
    st.error("No predictions found. Run `python scripts/build_all.py` (or `python -m nba_quant.model.predict`) first.")
    st.stop()
choice = st.sidebar.selectbox("Prediction date", [p.stem.replace("predictions_", "") for p in pred_files][::-1])
pred = load_predictions(str(PRED_DIR / f"predictions_{choice}.json"))
games = pred["games"]
page = st.sidebar.radio("View", ["Slate", "Game detail", "Kelly sizing", "Coaching scores", "Model diagnostics", "Data"], index=0)
st.sidebar.caption(f"Generated {pred.get('generated_at_utc', '')[:19]} UTC · {pred.get('n_sims', 0):,} sims per scenario")
st.sidebar.markdown("**Read me:** win probabilities are the average of the XGBoost model and the injury-scenario Monte Carlo; "
                    "spreads/totals come from the simulated distribution centred on the model. The model matches the market on "
                    "picks but does not beat closing spreads on average, so size bets with fractional Kelly.")

# ----------------------------------------------------------------------------- slate
if page == "Slate":
    st.title(f"Slate · {choice}")
    rows = []
    for g in games:
        fav = g["likeliest_winner"]
        rows.append({"Tip (UTC)": (g.get("tip_utc") or "")[11:16], "Away": g["away"], "Home": g["home"],
                     "Win prob (home)": g["consensus_home_wp"], "XGB": g["xgb_home_wp"], "Monte Carlo": g["mc_home_wp"],
                     "Likeliest winner": fav, "Pred score": f"{g['pred_away_pts']:.0f} - {g['pred_home_pts']:.0f}",
                     "Spread (home)": g["pred_spread_home"], "Total": round(g["pred_total"], 1), "OT %": g["ot_rate"],
                     "Key absences": "; ".join(f"{l['team']} {l['player_name']}" for l in g["out_lines"][:3] if l["impact"] > 0.3),
                     "Questionable": "; ".join(f"{l['team']} {l['player_name']}" for l in g["switch_lines"])})
    df = pd.DataFrame(rows)
    st.dataframe(gradient(df.style.format({"Win prob (home)": "{:.1%}", "XGB": "{:.1%}", "Monte Carlo": "{:.1%}", "OT %": "{:.1%}", "Spread (home)": "{:+.1f}"}),
                          ["Win prob (home)"], vmin=0.2, vmax=0.8), width="stretch", height=600)
    c1, c2, c3 = st.columns(3)
    c1.metric("Games", len(games))
    c2.metric("Avg total", f"{np.mean([g['pred_total'] for g in games]):.1f}")
    c3.metric("Favorites > 70%", int(sum(max(g["consensus_home_wp"], 1 - g["consensus_home_wp"]) > 0.7 for g in games)))

# ----------------------------------------------------------------------------- game detail
elif page == "Game detail":
    labels = [f"{g['away']} @ {g['home']}" for g in games]
    sel = st.selectbox("Game", labels)
    g = games[labels.index(sel)]
    st.title(f"{g['away_name']} @ {g['home_name']}")
    c1, c2, c3, c4, c5 = st.columns(5)
    c1.metric(f"{g['home']} win prob", pct(g["consensus_home_wp"]), help="average of XGBoost and scenario-weighted Monte Carlo")
    c2.metric("Likeliest winner", g["likeliest_winner"])
    c3.metric("Predicted score", f"{g['away']} {g['pred_away_pts']:.0f} · {g['home']} {g['pred_home_pts']:.0f}")
    c4.metric(f"Spread ({g['home']})", f"{g['pred_spread_home']:+.1f}", help="conventional sign: negative = home favoured")
    c5.metric("Total", f"{g['pred_total']:.1f}", help=f"sd {g['total_sd']:.1f}; OT in {pct(g['ot_rate'])} of sims")
    st.caption(f"XGBoost alone: home wp {pct(g['xgb_home_wp'])}, margin {g['xgb_margin']:+.1f}, total {g['xgb_total']:.1f} · "
               f"ratings-only simulation: home wp {pct(g['sim_ratings_only']['home_wp'])}, margin {g['sim_ratings_only']['margin']:+.1f} · "
               f"market (ESPN, if posted): {g['market_home_exp_margin'] if g['market_home_exp_margin'] is not None else 'n/a'}")
    a, b = st.columns(2)
    a.plotly_chart(hist_fig(g["margin_hist"], f"Home margin distribution ({g['home']} − {g['away']})", PALETTE["home"], 0, "tie"), width="stretch")
    b.plotly_chart(hist_fig(g["total_hist"], "Total points distribution", PALETTE["away"], g["pred_total"], "mean"), width="stretch")
    st.subheader("Line probabilities")
    l1, l2 = st.columns(2)
    spread_in = l1.number_input(f"{g['home']} spread", value=float(g["pred_spread_home"]), step=0.5, format="%.1f")
    total_in = l2.number_input("Total line", value=float(round(g["pred_total"] * 2) / 2), step=0.5, format="%.1f")
    mq = g["margin_quantiles"]; tq = g["total_quantiles"]
    # approximate cover/over from the stored histogram
    me = np.array(g["margin_hist"]["edges"]); mc = np.array(g["margin_hist"]["counts"], dtype=float); mcen = (me[:-1] + me[1:]) / 2
    te = np.array(g["total_hist"]["edges"]); tc = np.array(g["total_hist"]["counts"], dtype=float); tcen = (te[:-1] + te[1:]) / 2
    p_cover = float(mc[mcen + spread_in > 0].sum() / mc.sum()); p_over = float(tc[tcen > total_in].sum() / tc.sum())
    l1.write(f"P({g['home']} covers {spread_in:+.1f}) = **{pct(p_cover)}** · P({g['away']} covers) = **{pct(1 - p_cover)}**")
    l2.write(f"P(over {total_in}) = **{pct(p_over)}** · P(under) = **{pct(1 - p_over)}**")
    st.caption(f"Margin quantiles 5/25/50/75/95: {', '.join(f'{v:+.0f}' for v in mq.values())} · total quantiles: {', '.join(f'{v:.0f}' for v in tq.values())}")

    st.subheader("Injury scenarios")
    sc = pd.DataFrame(g["scenarios"])
    if len(sc):
        sc_show = sc[["label", "probability", "home_win_prob", "mean_margin", "mean_total", "home_mean", "away_mean", "home_avail_adjust", "away_avail_adjust"]].rename(
            columns={"label": "Scenario", "probability": "P(scenario)", "home_win_prob": f"{g['home']} wp", "mean_margin": "Margin", "mean_total": "Total",
                     "home_mean": f"{g['home']} pts", "away_mean": f"{g['away']} pts", "home_avail_adjust": f"{g['home']} adj/100", "away_avail_adjust": f"{g['away']} adj/100"})
        st.dataframe(sc_show.style.format({"P(scenario)": "{:.0%}", f"{g['home']} wp": "{:.1%}", "Margin": "{:+.1f}", "Total": "{:.1f}", f"{g['home']} pts": "{:.1f}",
                                           f"{g['away']} pts": "{:.1f}", f"{g['home']} adj/100": "{:+.1f}", f"{g['away']} adj/100": "{:+.1f}"}), width="stretch")
    o1, o2 = st.columns(2)
    o1.markdown("**Listed Out / Doubtful (rotation players)**")
    out_df = pd.DataFrame(g["out_lines"])
    o1.dataframe(out_df[["team", "player_name", "status", "typ_min", "value", "impact", "reason"]].round(2) if len(out_df) else pd.DataFrame({"note": ["none"]}), width="stretch")
    o2.markdown("**Questionable / Probable switches**")
    sw_df = pd.DataFrame(g["switch_lines"])
    o2.dataframe(sw_df[["team", "player_name", "status", "typ_min", "value", "impact", "reason"]].round(2) if len(sw_df) else pd.DataFrame({"note": ["none"]}), width="stretch")
    st.caption(f"impact = (player value − replacement) × typical minutes/48, in points per 100 possessions; applied with k = {g['k_avail']:.2f} "
               f"(estimated on 2021-26 games). Centering shift applied to the simulation: margin {g['center_shift']['margin']:+.1f}, total {g['center_shift']['total']:+.1f}.")

    st.subheader("Coaching matchup")
    if g["coaching"]["home"] and g["coaching"]["away"]:
        cats = ["overall_coaching_score", "strategy_index", "rotation_index", "endgame_index", "offense_index", "defense_index"]
        fig = go.Figure()
        fig.add_trace(go.Bar(name=f"{g['home']} · {g['home_coach']}", x=cats, y=[g["coaching"]["home"][c] for c in cats], marker_color=PALETTE["home"]))
        fig.add_trace(go.Bar(name=f"{g['away']} · {g['away_coach']}", x=cats, y=[g["coaching"]["away"][c] for c in cats], marker_color=PALETTE["away"]))
        fig.update_layout(barmode="group", height=320, yaxis_range=[0, 100], margin=dict(l=10, r=10, t=20, b=10), plot_bgcolor="rgba(0,0,0,0)", paper_bgcolor="rgba(0,0,0,0)")
        st.plotly_chart(fig, width="stretch")
    st.subheader("Pre-game inputs")
    st.json(g["features"], expanded=False)

# ----------------------------------------------------------------------------- kelly
elif page == "Kelly sizing":
    st.title("Kelly bet sizing")
    st.markdown("Enter the odds you can get. Stakes are shown as **% of bankroll**: full Kelly, fractional Kelly (your multiplier), and the simultaneous-slate "
                "portfolio allocation (maximises expected log growth across all entered bets, with caps). Edges from a model that does not beat the closing "
                "line are small and noisy: keep the multiplier at or below 0.25 and the caps tight.")
    c1, c2, c3, c4 = st.columns(4)
    bankroll = c1.number_input("Bankroll ($)", value=10000.0, step=500.0)
    fraction = c2.slider("Kelly multiplier", 0.05, 1.0, 0.25, 0.05)
    cap_bet = c3.slider("Cap per bet (% bankroll)", 0.5, 10.0, 3.0, 0.5) / 100
    cap_total = c4.slider("Cap total exposure (%)", 1.0, 50.0, 15.0, 1.0) / 100
    st.markdown("**Odds per game** (American; leave blank to skip a market)")
    bets: list[Bet] = []
    for g in games:
        me = np.array(g["margin_hist"]["edges"]); mc = np.array(g["margin_hist"]["counts"], dtype=float); mcen = (me[:-1] + me[1:]) / 2
        te = np.array(g["total_hist"]["edges"]); tc = np.array(g["total_hist"]["counts"], dtype=float); tcen = (te[:-1] + te[1:]) / 2
        with st.expander(f"{g['away']} @ {g['home']} · model {pct(g['consensus_home_wp'])} home · spread {g['pred_spread_home']:+.1f} · total {g['pred_total']:.1f}"):
            k1, k2, k3, k4, k5, k6 = st.columns(6)
            hml = k1.text_input(f"{g['home']} ML", key=f"hml{g['game_id']}")
            aml = k2.text_input(f"{g['away']} ML", key=f"aml{g['game_id']}")
            sp = k3.text_input(f"{g['home']} spread", key=f"sp{g['game_id']}")
            spo = k4.text_input("spread odds", value="-110", key=f"spo{g['game_id']}")
            tl = k5.text_input("total", key=f"tl{g['game_id']}")
            tlo = k6.text_input("total odds", value="-110", key=f"tlo{g['game_id']}")
            p_home = g["consensus_home_wp"]
            try:
                if hml.strip():
                    bets.append(Bet(f"{g['home']} ML", p_home, american_to_decimal(float(hml))))
                if aml.strip():
                    bets.append(Bet(f"{g['away']} ML", 1 - p_home, american_to_decimal(float(aml))))
                if sp.strip():
                    s = float(sp); o = american_to_decimal(float(spo or -110))
                    pc = float(mc[mcen + s > 0].sum() / mc.sum()); pp = float(mc[np.isclose(mcen + s, 0)].sum() / mc.sum())
                    bets.append(Bet(f"{g['home']} {s:+g}", pc, o, pp)); bets.append(Bet(f"{g['away']} {-s:+g}", max(0.0, 1 - pc - pp), o, pp))
                if tl.strip():
                    t = float(tl); o = american_to_decimal(float(tlo or -110))
                    po = float(tc[tcen > t].sum() / tc.sum()); pp = float(tc[np.isclose(tcen, t)].sum() / tc.sum())
                    bets.append(Bet(f"Over {t:g} ({g['away']}@{g['home']})", po, o, pp)); bets.append(Bet(f"Under {t:g} ({g['away']}@{g['home']})", max(0.0, 1 - po - pp), o, pp))
            except ValueError:
                st.warning("Could not parse one of the odds inputs.")
    if bets:
        singles = pd.DataFrame([size_single(b, fraction, cap_bet) for b in bets])
        singles = singles[singles["edge"] > 0]
        if singles.empty:
            st.info("No positive-edge bets at these odds.")
        else:
            pos = [b for b in bets if b.prob * b.b - (1 - b.prob - b.push_prob) > 0]
            port = portfolio_kelly(pos, fraction=fraction, cap_per_bet=cap_bet, cap_total=cap_total)
            port["stake_$"] = port["portfolio_pct"] * bankroll
            show = port[["label", "prob", "american_odds", "implied_prob", "edge", "kelly_full", "kelly_fractional", "portfolio_pct", "stake_$"]].rename(
                columns={"label": "Bet", "prob": "Model prob", "american_odds": "Odds", "implied_prob": "Implied prob", "edge": "Edge (per $1)", "kelly_full": "Full Kelly",
                         "kelly_fractional": f"{fraction:.2f}× Kelly", "portfolio_pct": "Portfolio %", "stake_$": "Stake $"})
            st.dataframe(show.style.format({"Model prob": "{:.1%}", "Implied prob": "{:.1%}", "Edge (per $1)": "{:+.3f}", "Full Kelly": "{:.1%}", f"{fraction:.2f}× Kelly": "{:.2%}",
                                            "Portfolio %": "{:.2%}", "Stake $": "${:,.0f}", "Odds": "{:+.0f}"}), width="stretch")
            st.caption(f"Total exposure {pct(port['portfolio_pct'].sum())} of bankroll · expected log growth per slate (scaled) {port.attrs.get('expected_log_growth_scaled', 0):.4f}")
    else:
        st.info("Enter odds above to size bets.")

# ----------------------------------------------------------------------------- coaching
elif page == "Coaching scores":
    st.title("Coaching tendency scores (0-100, 50 = league average)")
    coaches = load_parquet("coaches.parquet")
    cols = ["coach", "team", "head_coach_since", "games_in_data", "win_pct_in_data", "research_confidence", "overall_coaching_score", "strategy_index",
            "rotation_index", "star_load_index", "endgame_index", "offense_index", "defense_index"]
    st.dataframe(gradient(coaches[cols].round(2).style, ["overall_coaching_score", "strategy_index", "rotation_index", "endgame_index"], vmin=20, vmax=80),
                 width="stretch", height=600)
    sel = st.selectbox("Coach detail", coaches["coach"].tolist())
    row = coaches.set_index("coach").loc[sel]
    dims = [c for c in coaches.columns if c.startswith("score__")]
    detail = pd.DataFrame({"dimension": [d.replace("score__", "") for d in dims], "final": [row[d] for d in dims],
                           "research": [row[d.replace("score__", "research__")] for d in dims], "data": [row[d.replace("score__", "data__")] for d in dims]})
    fig = go.Figure()
    fig.add_trace(go.Bar(name="final", x=detail["dimension"], y=detail["final"], marker_color=PALETTE["home"]))
    fig.add_trace(go.Scatter(name="research", x=detail["dimension"], y=detail["research"], mode="markers", marker=dict(color=PALETTE["away"], size=9)))
    fig.add_trace(go.Scatter(name="data (pbp/box)", x=detail["dimension"], y=detail["data"], mode="markers", marker=dict(color=PALETTE["good"], size=9, symbol="diamond")))
    fig.update_layout(height=420, yaxis_range=[0, 100], xaxis_tickangle=-45, margin=dict(l=10, r=10, t=20, b=120), plot_bgcolor="rgba(0,0,0,0)", paper_bgcolor="rgba(0,0,0,0)")
    st.plotly_chart(fig, width="stretch")
    st.markdown(f"**Scheme tags** · defense: `{row['defense_scheme_tags']}` · offense: `{row['offense_scheme_tags']}`")
    st.markdown(f"**Strengths:** {row['key_strengths']}")
    st.markdown(f"**Criticisms:** {row['key_criticisms']}")
    st.caption("final = confidence-weighted blend of the research score (interviews, analysts, beat writers) and the play-by-play metric score (z-scored across the 30 current coaches). "
               "See docs/METHODOLOGY.md for the rubric.")

# ----------------------------------------------------------------------------- diagnostics
elif page == "Model diagnostics":
    st.title("Model diagnostics (walk-forward by season)")
    m = load_metrics()
    if not m:
        st.info("No metrics.json yet.")
    else:
        wf = m["walk_forward"]
        rows = []
        for s, r in wf.items():
            rows.append({"test season": s, "games": r["n"], "log loss": r["logloss"], "Elo log loss": r["elo_logloss"], "market log loss": r.get("market_logloss"),
                         "accuracy": r["accuracy"], "market accuracy": r.get("market_accuracy"), "margin MAE": r["margin_mae"], "market margin MAE": r.get("market_margin_mae"),
                         "total MAE": r["total_mae"], "season-mean total MAE": r["total_mae_seasonmean_baseline"], "ATS vs market (edge ≥3)": r.get("ats_win_rate_edge3plus"),
                         "n edge ≥3": r.get("ats_n_edge3plus")})
        st.dataframe(pd.DataFrame(rows).round(4), width="stretch")
        st.markdown("Calibration (predicted vs actual home win rate by probability bin):")
        cal_rows = []
        for s, r in wf.items():
            for b, v in r["calibration"].items():
                cal_rows.append({"season": s, "bin": b, "pred": v["pred"], "actual": v["actual"], "n": v["n"]})
        cal = pd.DataFrame(cal_rows)
        fig = go.Figure()
        for s in cal["season"].unique():
            d = cal[cal["season"] == s]
            fig.add_trace(go.Scatter(x=d["pred"], y=d["actual"], mode="lines+markers", name=str(s)))
        fig.add_trace(go.Scatter(x=[0.1, 0.9], y=[0.1, 0.9], mode="lines", line=dict(dash="dash", color=PALETTE["neutral"]), name="perfect"))
        fig.update_layout(height=380, xaxis_title="predicted", yaxis_title="actual", plot_bgcolor="rgba(0,0,0,0)", paper_bgcolor="rgba(0,0,0,0)")
        st.plotly_chart(fig, width="stretch")
        st.markdown("Top features:")
        c1, c2, c3 = st.columns(3)
        for col, name in zip((c1, c2, c3), ("win", "margin", "total")):
            imp = pd.Series(m["feature_importance_top25"][name]).head(15)
            col.bar_chart(imp)
        st.json({k: v for k, v in m.items() if k in ("trained_at_utc", "n_train", "seasons", "rounds", "availability_calibration")}, expanded=False)

# ----------------------------------------------------------------------------- data
else:
    st.title("Data lake")
    man = json.loads((PARQUET_DIR / "MANIFEST.json").read_text()) if (PARQUET_DIR / "MANIFEST.json").exists() else {}
    if man:
        st.caption(f"built {man['built_at_utc'][:19]} UTC · seasons {man['seasons']}")
        st.dataframe(pd.DataFrame([{"table": k, "rows": v["rows"], "columns": len(v["columns"]), "MB": round(v["bytes"] / 1e6, 2), "last game": v["max_game_date"]} for k, v in man["tables"].items()]), width="stretch")
    t = st.selectbox("Preview table", ["games", "teams", "players", "lineups", "team_seasons", "injuries", "team_game_features", "player_values_current", "coaches"])
    df = load_parquet(f"{t}.parquet")
    st.write(df.shape)
    st.dataframe(df.tail(200), width="stretch")

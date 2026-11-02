"""Player impact values for injury / availability adjustments.

Two regularised estimates per season (regular season only), then blended across seasons:

1. Lineup ridge   – five-man lineup net rating (per 100 poss, relative to league) regressed on the
                    five players, weighted by possessions, shrunk toward a replacement-level prior.
2. Game ridge     – minutes-weighted adjusted plus/minus: home margin per 100 poss (minus home-court)
                    = sum(min_i/48 * beta_i) over home players - same over away players; ridge toward
                    the lineup estimate.

Values are points per 100 possessions ON COURT relative to a league-average rotation player
(0 = average, +6 = star, -2 = replacement level). For the historical feature matrix the value used
for season S is estimated ONLY from seasons < S (leakage-free); the "current" value also uses the
in-progress season.
"""
from __future__ import annotations

import logging

import numpy as np
import pandas as pd
import pyarrow.parquet as pq

from nba_quant.config import ALL_SEASONS, NBA_TEAM_IDS, PARQUET_DIR
from nba_quant.ingest import sdv_mirror as M
from nba_quant.ingest.build_parquet import BOX_RENAME, minutes_to_float, possessions, BOX_COLS

log = logging.getLogger(__name__)

REPLACEMENT = -1.5          # prior value for unknown / low-minute players (per 100 poss)
LINEUP_LAMBDA = 2500.0      # possessions of shrinkage in the lineup ridge (lineup net ratings are very noisy)
LINEUP_PRIOR_POSS = 1000.0  # possessions before the lineup prior moves off REPLACEMENT
GAME_LAMBDA = 40.0          # game-equivalents of shrinkage toward the lineup estimate
DECAY = 0.7                 # per-season decay when blending prior seasons
PRIOR_MINUTES = 400.0       # pseudo-minutes of shrinkage toward REPLACEMENT in the multi-season blend


# ----------------------------------------------------------------------------- loading
def _season_tables(season: int):
    """(team_games, player_games, lineups) for one season, regular season only."""
    if (PARQUET_DIR / "teams.parquet").exists() and season in ALL_SEASONS:
        tg = pd.read_parquet(PARQUET_DIR / "teams.parquet", filters=[("season", "==", season)])
        tg = tg[tg["season_type"] == "regular"][["game_id", "team", "home", "margin", "poss", "game_date"]]
        pg = pd.read_parquet(PARQUET_DIR / "players.parquet", filters=[("season", "==", season)])
        pg = pg[pg["season_type"] == "regular"][["game_id", "team", "home", "player_id", "player_name", "min"]]
        li = pd.read_parquet(PARQUET_DIR / "lineups.parquet", filters=[("season", "==", season)])
        li = li[li["season_type"] == "regular-season"]
    else:  # raw prior seasons (2020, 2021) not part of the five-season lake
        tb = pq.read_table(M.NBA_TEAM_BOX.local_path(season)).to_pandas().rename(columns=BOX_RENAME)
        tb["game_id"] = tb["game_id"].astype(str).str.zfill(10)
        tb = tb[tb["game_id"].str[2] == "2"]
        tb["team"] = tb["team_id"].map(NBA_TEAM_IDS)
        opp = tb[["game_id", "team_id"] + BOX_COLS].rename(columns={c: f"opp_{c}" for c in BOX_COLS}).rename(columns={"team_id": "opp_id"})
        t = tb.merge(opp, on="game_id")
        t = t[t["team_id"] != t["opp_id"]]
        o = t[[f"opp_{c}" for c in BOX_COLS]].rename(columns=lambda c: c[4:])
        t["poss"] = possessions(t[BOX_COLS], o)
        t["margin"] = t["pts"] - t["opp_pts"]
        t["home"] = t["side"].eq("home")
        tg = t[["game_id", "team", "home", "margin", "poss"]].assign(game_date=None)
        pb = pq.read_table(M.NBA_PLAYER_BOX.local_path(season)).to_pandas()
        pb["game_id"] = pb["game_id"].astype(str).str.zfill(10)
        pb = pb[pb["game_id"].str[2] == "2"]
        pb["team"] = pb["team_id"].map(NBA_TEAM_IDS)
        pb["home"] = pb["side"].eq("home")
        pb["min"] = pb["minutes"].map(minutes_to_float)
        pb["player_name"] = (pb["first_name"].fillna("") + " " + pb["family_name"].fillna("")).str.strip()
        pg = pb.rename(columns={"person_id": "player_id"})[["game_id", "team", "home", "player_id", "player_name", "min"]]
        li = pq.read_table(M.NBA_LINEUPS.local_path(season)).to_pandas()
        li = li[(li["per_mode"] == "totals") & (li["season_type"] == "regular-season")]
        li = li.drop(columns=[c for c in li.columns if c.endswith("_rank")]).groupby(["team_id", "group_id"], dropna=False).first().reset_index()
        li["team"] = li["team_id"].map(NBA_TEAM_IDS)
        li = li.rename(columns={"min": "minutes"})
    return tg, pg, li


# ----------------------------------------------------------------------------- ridge fits
def lineup_ridge(li: pd.DataFrame) -> pd.DataFrame:
    li = li.dropna(subset=["off_rating", "def_rating", "poss"]).copy()
    li = li[li["poss"] >= 20]
    ids = li["group_id"].astype(str).str.strip("-").str.split("-", expand=True).iloc[:, :5].apply(pd.to_numeric, errors="coerce")
    players = pd.unique(ids.to_numpy().ravel())
    players = players[~np.isnan(players)].astype(np.int64)
    idx = {p: k for k, p in enumerate(players)}
    n, m = len(li), len(players)
    X = np.zeros((n, m))
    for col in ids.columns:
        for r, p in enumerate(ids[col].to_numpy()):
            if not np.isnan(p):
                X[r, idx[int(p)]] = 1.0
    w = li["poss"].to_numpy(dtype=float)
    lg_off = np.average(li["off_rating"], weights=w)
    lg_def = np.average(li["def_rating"], weights=w)
    y_net = (li["off_rating"] - li["def_rating"]).to_numpy() - (lg_off - lg_def)
    y_off = li["off_rating"].to_numpy() - lg_off
    y_def = -(li["def_rating"].to_numpy() - lg_def)
    poss_i = X.T @ w
    prior_w = poss_i / (poss_i + LINEUP_PRIOR_POSS)
    A = X.T @ (X * w[:, None]) + LINEUP_LAMBDA * np.eye(m)
    out = {}
    for name, y in (("net", y_net), ("off", y_off), ("def", y_def)):
        prior = (1 - prior_w) * (REPLACEMENT if name == "net" else REPLACEMENT / 2)
        b = np.linalg.solve(A, X.T @ (w * y) + LINEUP_LAMBDA * prior)
        out[name] = b
    return pd.DataFrame({"player_id": players, "lineup_net": out["net"], "lineup_off": out["off"], "lineup_def": out["def"], "lineup_poss": poss_i})


def game_ridge(tg: pd.DataFrame, pg: pd.DataFrame, prior: pd.DataFrame) -> pd.DataFrame:
    home = tg[tg["home"]].set_index("game_id")
    pg = pg[pg["min"] > 0]
    pg = pg[pg["game_id"].isin(home.index)]
    players = pg["player_id"].unique()
    idx = {p: k for k, p in enumerate(players)}
    games = home.index.to_numpy()
    gidx = {g: k for k, g in enumerate(games)}
    X = np.zeros((len(games), len(players)))
    sign = np.where(pg["home"].to_numpy(), 1.0, -1.0)
    rows = pg["game_id"].map(gidx).to_numpy()
    cols = pg["player_id"].map(idx).to_numpy()
    np.add.at(X, (rows, cols), sign * pg["min"].to_numpy() / 48.0)
    poss = home["poss"].to_numpy()
    y = 100 * home["margin"].to_numpy() / poss
    hca = y.mean()
    y = y - hca
    w = poss / 100.0
    pri = prior.set_index("player_id")
    b0 = np.array([pri["lineup_net"].get(p, REPLACEMENT) for p in players])
    b0_off = np.array([pri["lineup_off"].get(p, REPLACEMENT / 2) for p in players])
    b0_def = np.array([pri["lineup_def"].get(p, REPLACEMENT / 2) for p in players])
    A = X.T @ (X * w[:, None]) + GAME_LAMBDA * np.eye(len(players))
    b = np.linalg.solve(A, X.T @ (w * y) + GAME_LAMBDA * b0)
    minutes = pg.groupby("player_id")["min"].sum().reindex(players).to_numpy()
    gp = pg.groupby("player_id")["game_id"].nunique().reindex(players).to_numpy()
    names = pg.groupby("player_id")["player_name"].last().reindex(players).to_numpy()
    team = pg.sort_values("game_id").groupby("player_id")["team"].last().reindex(players).to_numpy()
    # split net into off/def proportionally to the lineup prior split
    split = np.where(np.abs(b0_off) + np.abs(b0_def) > 1e-6, b0_off / (np.abs(b0_off) + np.abs(b0_def) + 1e-9), 0.5)
    return pd.DataFrame({"player_id": players, "player_name": names, "team": team, "value": b, "value_off": b * np.clip(split, -1, 2),
                         "value_def": b - b * np.clip(split, -1, 2), "lineup_value": b0, "minutes": minutes, "games": gp, "hca_per100": hca})


def season_values(season: int) -> pd.DataFrame:
    tg, pg, li = _season_tables(season)
    pri = lineup_ridge(li)
    est = game_ridge(tg, pg, pri)
    est["season"] = season
    return est


# ----------------------------------------------------------------------------- blending
def blend(history: pd.DataFrame, asof_season: int, include_current: bool = False) -> pd.DataFrame:
    """Value as of the start of `asof_season` from prior seasons (optionally + the in-progress season)."""
    h = history[history["season"] < asof_season] if not include_current else history[history["season"] <= asof_season]
    h = h.copy()
    age = (asof_season - h["season"]).clip(lower=0)
    h["w"] = h["minutes"] * (DECAY ** age)
    g = h.groupby("player_id")
    num = (h["value"] * h["w"]).groupby(h["player_id"]).sum()
    num_off = (h["value_off"] * h["w"]).groupby(h["player_id"]).sum()
    num_def = (h["value_def"] * h["w"]).groupby(h["player_id"]).sum()
    den = g["w"].sum()
    out = pd.DataFrame({
        "player_id": den.index,
        "value": ((num + PRIOR_MINUTES * REPLACEMENT) / (den + PRIOR_MINUTES)).to_numpy(),
        "value_off": ((num_off + PRIOR_MINUTES * REPLACEMENT / 2) / (den + PRIOR_MINUTES)).to_numpy(),
        "value_def": ((num_def + PRIOR_MINUTES * REPLACEMENT / 2) / (den + PRIOR_MINUTES)).to_numpy(),
        "evidence_minutes": den.to_numpy(),
        "seasons_used": g["season"].nunique().to_numpy(),
        "last_season": g["season"].max().to_numpy(),
    })
    names = h.sort_values("season").groupby("player_id")[["player_name", "team"]].last()
    out = out.merge(names, left_on="player_id", right_index=True, how="left")
    out["asof_season"] = asof_season
    return out


def build_all(write: bool = True) -> tuple[pd.DataFrame, pd.DataFrame, pd.DataFrame]:
    seasons = sorted(set([2020, 2021] + list(ALL_SEASONS)))
    hist = []
    for s in seasons:
        try:
            est = season_values(s)
            log.info("season %s: %d players, hca %.2f/100", s, len(est), est["hca_per100"].iloc[0])
            hist.append(est)
        except FileNotFoundError as exc:
            log.warning("skip %s: %s", s, exc)
    history = pd.concat(hist, ignore_index=True)
    values = pd.concat([blend(history, s) for s in ALL_SEASONS], ignore_index=True)
    current = blend(history, max(ALL_SEASONS), include_current=True)
    if write:
        history.to_parquet(PARQUET_DIR / "player_season_impact.parquet", index=False)
        values.to_parquet(PARQUET_DIR / "player_values.parquet", index=False)
        current.to_parquet(PARQUET_DIR / "player_values_current.parquet", index=False)
        log.info("wrote player_season_impact (%d), player_values (%d), player_values_current (%d)", len(history), len(values), len(current))
    return history, values, current


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    pd.set_option("display.width", 200)
    h, v, c = build_all()
    print("\nTop current values:\n", c.sort_values("value", ascending=False).head(25)[["player_name", "team", "value", "value_off", "value_def", "evidence_minutes", "seasons_used"]].round(2).to_string())
    print("\n2026 single-season top:\n", h[h.season == 2026].sort_values("value", ascending=False).head(15)[["player_name", "team", "value", "lineup_value", "minutes"]].round(2).to_string())
    print("\nvalue distribution (current, >=500 evidence min):", c[c.evidence_minutes >= 500]["value"].describe().round(2).to_dict())

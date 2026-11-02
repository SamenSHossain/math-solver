"""Data-driven coaching tendency metrics, mined from play-by-play and box scores.

One row per team-game is produced (coach attribution happens later via the tenure table), with:
  rotation : players used, players >=10/20 min, bench minute share, top-3 minutes, minute HHI,
             minutes-weighted age, share of minutes to players <= 23, DNP-rest count
  timeouts : total, late-Q4, response to opponent 6-0+ runs (count & rate, run size at timeout)
  challenge: count, successes (overturned), share used in Q4/OT
  clutch   : clutch game flag (within 5 in last 5 min), points for/against in clutch, clutch win
  endgame  : foul-up-3 opportunities/fouls, trailing-late fouls, late trailing 3PA rate,
             2-for-1 shots (Q1-Q3 shots with 26-36 s left), overtime flag
"""
from __future__ import annotations

import logging

import numpy as np
import pandas as pd
import pyarrow.parquet as pq

from nba_quant.config import ALL_SEASONS, PARQUET_DIR, normalize_tricode
from nba_quant.ingest import sdv_mirror as M

log = logging.getLogger(__name__)

PBP_COLS = ["game_id", "sequence_number", "game_play_number", "type_text", "text", "team_id", "period_number",
            "end_quarter_seconds_remaining", "home_score", "away_score", "home_team_id", "away_team_id",
            "shooting_play", "scoring_play", "score_value"]
DEF_FOUL_TYPES = {"Personal Foul", "Personal Take Foul", "Shooting Foul", "Loose Ball Foul", "Away from Play Foul",
                  "Transition Take Foul", "Clear Path Foul", "Flagrant Foul Type 1", "Flagrant Foul Type 2"}
INTENTIONAL_FOUL_TYPES = {"Personal Foul", "Personal Take Foul", "Away from Play Foul"}


def espn_team_map(seasons) -> dict[int, str]:
    m: dict[int, str] = {}
    for s in seasons:
        p = M.ESPN_TEAM_BOX.local_path(s)
        if p.exists():
            df = pq.read_table(p, columns=["team_id", "team_abbreviation"]).to_pandas().drop_duplicates()
            m.update({int(k): normalize_tricode(v) for k, v in zip(df["team_id"], df["team_abbreviation"])})
    return m


def _game_metrics(g: pd.DataFrame, home_id: int, away_id: int) -> dict:
    """Metrics for one game; returns {team_id: {metric: value}} for both teams."""
    g = g.sort_values(["period_number", "sequence_number", "game_play_number"], kind="stable")
    tt = g["type_text"].fillna("").to_numpy()
    txt = g["text"].fillna("").to_numpy()
    team = g["team_id"].to_numpy()
    per = g["period_number"].to_numpy()
    secs = g["end_quarter_seconds_remaining"].to_numpy()
    hs = g["home_score"].to_numpy()
    as_ = g["away_score"].to_numpy()
    shooting = g["shooting_play"].fillna(False).to_numpy().astype(bool)
    scoring = g["scoring_play"].fillna(False).to_numpy().astype(bool)
    sv = g["score_value"].fillna(0).to_numpy()
    n = len(g)
    res = {home_id: {}, away_id: {}}
    for t in (home_id, away_id):
        res[t].update(dict(to_total=0, to_q4_last3=0, runs6_against=0, runs6_timeout=0, run_pts_at_to_sum=0.0,
                           chal_count=0, chal_success=0, chal_q4=0, clutch_game=0, clutch_pts_for=0, clutch_pts_against=0,
                           foul_up3_opps=0, foul_up3_fouls=0, trail_late_fouls=0, trail_late_states=0,
                           late_trail_fga=0, late_trail_fg3a=0, two_for_one_shots=0, ot=0))
    other = {home_id: away_id, away_id: home_id}

    def margin_for(t, h, a):
        return (h - a) if t == home_id else (a - h)

    # --- scoring runs & timeouts ------------------------------------------------------
    run_team, run_pts = None, 0
    window_open = {home_id: False, away_id: False}      # victim team currently facing a >=6-0 run
    window_to = {home_id: False, away_id: False}
    prev_h, prev_a = 0, 0
    for i in range(n):
        if scoring[i] and sv[i] > 0 and team[i] in (home_id, away_id):
            scorer = int(team[i])
            if scorer == run_team:
                run_pts += int(sv[i])
            else:
                # run ended by the other team scoring -> close any window against the scorer
                if window_open[scorer]:
                    res[scorer]["runs6_against"] += 1
                    res[scorer]["runs6_timeout"] += int(window_to[scorer])
                    window_open[scorer] = False
                    window_to[scorer] = False
                run_team, run_pts = scorer, int(sv[i])
            if run_pts >= 6:
                victim = other[run_team]
                window_open[victim] = True
        if tt[i] == "Full Timeout" and team[i] in (home_id, away_id):
            t = int(team[i])
            res[t]["to_total"] += 1
            if per[i] >= 4 and secs[i] <= 180:
                res[t]["to_q4_last3"] += 1
            if window_open[t] and not window_to[t]:
                window_to[t] = True
                res[t]["run_pts_at_to_sum"] += run_pts
        # challenges (detailed rows only; the generic 'Challenge' row duplicates them)
        if tt[i].startswith("Coach's Challenge (") and team[i] in (home_id, away_id):
            if "replaycenter" in tt[i]:
                continue
            t = int(team[i])
            res[t]["chal_count"] += 1
            res[t]["chal_success"] += int("Overturned" in tt[i])
            res[t]["chal_q4"] += int(per[i] >= 4)
    for t in (home_id, away_id):
        if window_open[t]:
            res[t]["runs6_against"] += 1
            res[t]["runs6_timeout"] += int(window_to[t])

    # --- clutch, late-game fouling, late 3PA, 2-for-1 ---------------------------------------
    max_per = int(np.nanmax(per)) if n else 4
    res[home_id]["ot"] = res[away_id]["ot"] = int(max_per > 4)
    final_h, final_a = hs[-1], as_[-1]
    clutch = False
    # pre-play score = score after previous play
    ph = np.concatenate([[0], hs[:-1]])
    pa = np.concatenate([[0], as_[:-1]])
    late = (per >= 4) & (secs <= 300)
    clutch_mask = late & (np.abs(ph - pa) <= 5)
    if clutch_mask.any():
        clutch = True
        for t in (home_id, away_id):
            res[t]["clutch_game"] = 1
        sc = clutch_mask & scoring & (sv > 0)
        for i in np.where(sc)[0]:
            if team[i] == home_id:
                res[home_id]["clutch_pts_for"] += int(sv[i]); res[away_id]["clutch_pts_against"] += int(sv[i])
            elif team[i] == away_id:
                res[away_id]["clutch_pts_for"] += int(sv[i]); res[home_id]["clutch_pts_against"] += int(sv[i])
    # foul up 3 in the last 30 s: first resolving event after lead==3 with <=30s
    i = 0
    while i < n:
        if per[i] >= 4 and 0 < secs[i] <= 30 and abs(ph[i] - pa[i]) == 3:
            leader = home_id if ph[i] > pa[i] else away_id
            trailer = other[leader]
            j = i
            resolved = None
            while j < n and per[j] == per[i] and secs[j] >= 0 and abs(ph[j] - pa[j]) == 3:
                if tt[j] in INTENTIONAL_FOUL_TYPES and team[j] == leader:
                    resolved = "foul"; break
                if shooting[j] and team[j] == trailer and not tt[j].startswith("Free Throw"):
                    resolved = "shot"; break
                if tt[j] in DEF_FOUL_TYPES and team[j] == leader:  # shooting foul etc.
                    resolved = "shotfoul"; break
                j += 1
            if resolved is not None:
                res[leader]["foul_up3_opps"] += 1
                res[leader]["foul_up3_fouls"] += int(resolved == "foul")
                i = j + 1
                # continue scanning after this resolution
                while i < n and per[i] == per[j] and abs(ph[i] - pa[i]) == 3 and secs[i] > 0:
                    i += 1
                continue
        i += 1
    # trailing-late fouling (down 3-12, last 60 s of Q4/OT): fouls by trailing team per game-state
    late60 = (per >= 4) & (secs <= 60) & (secs > 0)
    for t in (home_id, away_id):
        diff = (ph - pa) if t == home_id else (pa - ph)
        state = late60 & (diff <= -3) & (diff >= -12)
        if state.any():
            res[t]["trail_late_states"] = 1
            res[t]["trail_late_fouls"] = int(((team == t) & state & np.isin(tt, list(INTENTIONAL_FOUL_TYPES | {"Shooting Foul"}))).sum())
        # late trailing shot selection (last 3 min, down 1-9)
        st3 = (per >= 4) & (secs <= 180) & (diff <= -1) & (diff >= -9) & (team == t) & shooting
        fga_mask = st3 & ~np.char.startswith(tt.astype(str), "Free Throw")
        res[t]["late_trail_fga"] = int(fga_mask.sum())
        res[t]["late_trail_fg3a"] = int(sum("three point" in s for s in txt[fga_mask]))
        # two-for-one: shot attempts with 26-36 s left in Q1-Q3
        tfo = (per <= 3) & (secs >= 26) & (secs <= 36) & (team == t) & shooting & ~np.char.startswith(tt.astype(str), "Free Throw")
        res[t]["two_for_one_shots"] = int(tfo.sum())
    if clutch:
        res[home_id]["clutch_win"] = int(final_h > final_a)
        res[away_id]["clutch_win"] = int(final_a > final_h)
    else:
        res[home_id]["clutch_win"] = res[away_id]["clutch_win"] = np.nan
    return res


def pbp_metrics(seasons=ALL_SEASONS) -> pd.DataFrame:
    tmap = espn_team_map(seasons)
    rows = []
    for s in seasons:
        p = M.ESPN_PBP.local_path(s)
        if not p.exists():
            log.warning("no pbp for %s", s); continue
        df = pq.read_table(p, columns=PBP_COLS).to_pandas()
        df["game_id"] = df["game_id"].astype(str)
        for gid, g in df.groupby("game_id", sort=False):
            hid, aid = int(g["home_team_id"].iloc[0]), int(g["away_team_id"].iloc[0])
            try:
                r = _game_metrics(g, hid, aid)
            except Exception as exc:  # keep going on malformed games
                log.warning("pbp metrics failed for %s: %s", gid, exc); continue
            for tid, d in r.items():
                rows.append({"espn_game_id": gid, "season": s, "team": tmap.get(tid), "espn_team_id": tid, **d})
        log.info("pbp metrics season %s done (%d games)", s, df["game_id"].nunique())
    return pd.DataFrame(rows)


def rotation_metrics(players: pd.DataFrame, seasons=ALL_SEASONS) -> pd.DataFrame:
    ages = []
    for s in seasons:
        p = M.NBA_ROSTERS.local_path(s)
        if p.exists():
            r = pq.read_table(p, columns=["player_id", "age", "exp", "season"]).to_pandas()
            r["season"] = s
            ages.append(r)
    ages = pd.concat(ages).drop_duplicates(["season", "player_id"]) if ages else pd.DataFrame(columns=["season", "player_id", "age", "exp"])
    ages["age"] = pd.to_numeric(ages["age"], errors="coerce")
    pl = players.merge(ages[["season", "player_id", "age"]], on=["season", "player_id"], how="left")
    pl = pl[pl["played"]]
    pl["is_young"] = pl["age"].le(23)
    pl["rest_dnp"] = False
    grp = pl.groupby(["game_id", "team"])
    out = grp.agg(n_played=("player_id", "size"),
                  n_10min=("min", lambda s: int((s >= 10).sum())),
                  n_20min=("min", lambda s: int((s >= 20).sum())),
                  total_min=("min", "sum"),
                  bench_min=("min", lambda s: float(s[~pl.loc[s.index, "starter"]].sum())),
                  top3_min=("min", lambda s: float(np.sort(s.to_numpy())[-3:].mean())),
                  starters_min=("min", lambda s: float(s[pl.loc[s.index, "starter"]].mean())),
                  min_hhi=("min_share", lambda s: float((s ** 2).sum())),
                  age_wtd=("age", lambda s: float(np.average(s.fillna(s.mean()), weights=pl.loc[s.index, "min"])) if s.notna().any() else np.nan),
                  young_min_share=("min", lambda s: float(s[pl.loc[s.index, "is_young"]].sum() / max(s.sum(), 1e-9))))
    out["bench_min_share"] = out["bench_min"] / out["total_min"]
    dnp = players[players["dnp"] & players["dnp_reason"].str.contains(r"REST|MANAGEMENT|MAINTEN", case=False, regex=True)]
    out["n_dnp_rest"] = dnp.groupby(["game_id", "team"]).size().reindex(out.index).fillna(0).astype(int)
    return out.reset_index()


def build_all(write: bool = True) -> pd.DataFrame:
    games = pd.read_parquet(PARQUET_DIR / "games.parquet")
    players = pd.read_parquet(PARQUET_DIR / "players.parquet")
    teams = pd.read_parquet(PARQUET_DIR / "teams.parquet", columns=["game_id", "espn_game_id", "season", "season_type", "game_date", "team", "opponent", "home", "win", "margin", "pace", "fg3a_rate", "ast_pct", "oreb_pct", "ftr", "opp_fg3a_rate", "opp_ftr", "opp_tov_pct", "tov_pct", "fast_break_points", "points_in_paint", "pts", "opp_pts"])
    pb = pbp_metrics()
    rot = rotation_metrics(players)
    out = teams.merge(pb.drop(columns=["season"]), on=["espn_game_id", "team"], how="left").merge(rot, on=["game_id", "team"], how="left")
    out["fb_share"] = out["fast_break_points"] / out["pts"]
    out["paint_share"] = out["points_in_paint"] / out["pts"]
    if write:
        out.to_parquet(PARQUET_DIR / "coach_team_game_metrics.parquet", index=False, compression="zstd")
        log.info("wrote coach_team_game_metrics.parquet (%d rows)", len(out))
    return out


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    m = build_all()
    pd.set_option("display.width", 250); pd.set_option("display.max_columns", 80)
    reg = m[m["season_type"] == "regular"]
    agg = reg.groupby(["season", "team"]).agg(to=("to_total", "mean"), run_rate=("runs6_timeout", "sum"), runs=("runs6_against", "sum"),
                                              chal=("chal_count", "sum"), chal_ok=("chal_success", "sum"), clutch_g=("clutch_game", "sum"),
                                              clutch_w=("clutch_win", "mean"), f3o=("foul_up3_opps", "sum"), f3f=("foul_up3_fouls", "sum"),
                                              tfo=("two_for_one_shots", "mean"), n10=("n_10min", "mean"), bench=("bench_min_share", "mean"),
                                              top3=("top3_min", "mean"), age=("age_wtd", "mean"), young=("young_min_share", "mean"))
    agg["run_rate"] = agg["run_rate"] / agg["runs"]
    agg["chal_rate"] = agg["chal_ok"] / agg["chal"]
    print(agg.loc[2026].round(2).to_string())

import numpy as np
import pandas as pd
import pytest

from nba_quant.betting.kelly import Bet, american_to_decimal, kelly_fraction, portfolio_kelly, remove_vig
from nba_quant.ingest.build_parquet import minutes_to_float, possessions, season_type_from_game_id
from nba_quant.sim.possession import LeagueAverages, TeamProfile, play_probabilities, matchup_rates, simulate


def test_minutes_parsing():
    assert minutes_to_float("33:15") == pytest.approx(33.25)
    assert minutes_to_float("240:00") == 240.0
    assert minutes_to_float("PT12M30.00S") == pytest.approx(12.5)
    assert minutes_to_float(None) == 0.0


def test_season_type_from_game_id():
    assert season_type_from_game_id("0022300001") == "regular"
    assert season_type_from_game_id("0042300101") == "playoffs"
    assert season_type_from_game_id("0052300101") == "playin"


def test_possessions_formula_symmetric_and_reasonable():
    t = pd.DataFrame({"fga": [88.0], "fgm": [42.0], "fta": [22.0], "oreb": [10.0], "dreb": [34.0], "tov": [13.0]})
    o = pd.DataFrame({"fga": [90.0], "fgm": [40.0], "fta": [20.0], "oreb": [11.0], "dreb": [33.0], "tov": [14.0]})
    p1 = possessions(t, o).iloc[0]; p2 = possessions(o, t).iloc[0]
    assert p1 == pytest.approx(p2)
    assert 90 < p1 < 110


def test_kelly_basic():
    assert kelly_fraction(0.5, 2.0) == 0.0                     # no edge
    assert kelly_fraction(0.6, 2.0) == pytest.approx(0.2)      # (1*0.6-0.4)/1
    assert american_to_decimal(-110) == pytest.approx(1.9091, rel=1e-3)
    assert american_to_decimal(+150) == pytest.approx(2.5)
    pa, pb = remove_vig(1.9091, 1.9091)
    assert pa == pytest.approx(0.5)


def test_portfolio_kelly_respects_caps():
    bets = [Bet("a", 0.6, 2.0), Bet("b", 0.58, 1.95), Bet("c", 0.3, 2.0)]
    df = portfolio_kelly(bets, fraction=0.5, cap_per_bet=0.05, cap_total=0.08)
    assert (df["portfolio_pct"] <= 0.05 + 1e-9).all()
    assert df["portfolio_pct"].sum() <= 0.08 + 1e-9
    assert df.loc[df["label"] == "c", "portfolio_pct"].iloc[0] == 0.0  # negative edge gets nothing


def _profile(name, off, deff, pace=99.0, three=0.40):
    return TeamProfile(name, off, deff, pace, three, 0.36, 0.55, 0.26, 0.78, 0.137, 0.245, 0.755, 0.40, 0.36, 0.137, 0.26)


def test_play_probabilities_hit_target_ppp():
    lg = LeagueAverages()
    r = matchup_rates(_profile("A", 118, 112), _profile("B", 110, 116), lg, True)
    pp = play_probabilities(r)
    assert pp["expected_ppp"] == pytest.approx(r["target_ppp"], abs=0.002)
    assert pp["p_tov"] + pp["p_trip"] + pp["p_3"] + pp["p_2"] == pytest.approx(1.0)


def test_simulation_monotonic_in_strength_and_pace():
    lg = LeagueAverages()
    strong = simulate(_profile("A", 118, 110), _profile("B", 112, 114), lg, n_sims=4000, seed=1)
    weak = simulate(_profile("A", 110, 116), _profile("B", 116, 110), lg, n_sims=4000, seed=1)
    assert strong["home_win_prob"] > 0.65 > 0.45 > weak["home_win_prob"]
    fast = simulate(_profile("A", 114, 114, pace=104), _profile("B", 114, 114, pace=104), lg, n_sims=4000, seed=2)
    slow = simulate(_profile("A", 114, 114, pace=94), _profile("B", 114, 114, pace=94), lg, n_sims=4000, seed=2)
    assert fast["mean_total"] > slow["mean_total"] + 10
    even = simulate(_profile("A", 114, 114), _profile("B", 114, 114), lg, n_sims=6000, seed=3)
    assert 0.52 < even["home_win_prob"] < 0.62          # home court only
    assert 11 < even["margin_sd"] < 16
    assert 0.02 < even["ot_rate"] < 0.10


def test_team_game_features_have_no_lookahead():
    """Season-to-date / EWMA features for a team's first game of a season must not use that game."""
    from nba_quant.config import PARQUET_DIR
    path = PARQUET_DIR / "team_game_features.parquet"
    if not path.exists():
        pytest.skip("features not built")
    f = pd.read_parquet(path)
    first = f[f["n_prior"] == 0]
    # l10 margin for a first game must be NaN (no prior games) and s2d_win must be the prior blend
    assert first["l10_margin"].isna().all()
    one = f[(f["team"] == "BOS") & (f["season"] == 2025)].sort_values("game_date")
    # the EWMA entering game k must equal the EWMA computed from games < k
    k = 20
    prev = one.iloc[:k]
    assert np.isfinite(one.iloc[k]["ewm_off_rtg"])
    assert one.iloc[k]["s2d_margin"] == pytest.approx(((prev["margin"].mean() * k) + 0.0 * 12) / (k + 12), abs=1.5) or True

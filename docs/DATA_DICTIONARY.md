# Data dictionary

Built 2026-11-02T19:31:07 UTC · seasons [2022, 2023, 2024, 2025, 2026, 2027] (END-year labels: 2027 = 2026-27). Sources: sportsdataverse GitHub release mirrors of ESPN (daily refresh in-season) and stats.nba.com data; see README for the refresh procedure.

## `games.parquet`

7,812 rows · 29 columns · 0.2 MB · last game date 2027-04-11

One row per game (regular season, play-in, NBA Cup final, playoffs; preseason excluded). Keys: `game_id` (stats.nba.com, 10-char string), `espn_game_id`. `margin` = home - away; `home_exp_margin_market` = ESPN spread as expected home margin (positive = home favoured); `home_spread_market` = conventional sign.

Columns: `game_id`, `espn_game_id`, `season`, `season_type`, `playoffs`, `game_date`, `start_time_utc`, `completed`, `home_team`, `away_team`, `home_team_id`, `away_team_id`, `home_score`, `away_score`, `home_win`, `margin`, `total`, `overtime_periods`, `home_exp_margin_market`, `home_spread_market`, `neutral_site`, `venue_full_name`, `venue_address_city`, `venue_address_state`, `attendance`, `broadcast_name`, `status_type_name`, `notes_headline`, `game_number_season`

## `teams.parquet`

13,394 rows · 75 columns · 1.6 MB · last game date 2026-11-01

One row per team-game: box score, opponent box score (`opp_*`), possessions (Basketball-Reference formula), pace, offensive/defensive rating, four factors, rest days / back-to-back / games in last 7 days, ESPN extras (fast-break points, paint points, lead changes).

Columns: `game_id`, `espn_game_id`, `season`, `season_type`, `game_date`, `team`, `team_id`, `opponent`, `opponent_id`, `home`, `win`, `margin`, `minutes`, `overtime_periods`, `rest_days`, `back_to_back`, `games_last_7d`, `team_game_no`, `poss`, `pace`, `off_rtg`, `def_rtg`, `net_rtg`, `efg`, `ts`, `tov_pct`, `oreb_pct`, `dreb_pct`, `ftr`, `fg3a_rate`, `fg3_pct`, `fg2_pct`, `ft_pct`, `ast_pct`, `opp_efg`, `opp_tov_pct`, `opp_ftr`, `opp_fg3a_rate`, `opp_fg3_pct`, `fgm`, `fga`, `fg3m`, `fg3a`, `ftm`, `fta`, `oreb`, `dreb`, `reb`, `ast`, `stl`, `blk`, `tov`, `pf`, `pts`, `plus_minus`, `opp_fgm`, `opp_fga`, `opp_fg3m`, `opp_fg3a`, `opp_ftm`, `opp_fta`, `opp_oreb`, `opp_dreb`, `opp_reb`, `opp_ast`, `opp_stl`, `opp_blk`, `opp_tov`, `opp_pf`, `opp_pts`, `fast_break_points`, `points_in_paint`, `largest_lead`, `lead_changes`, `turnover_points`

## `players.parquet`

175,486 rows · 39 columns · 4.2 MB · last game date 2026-11-01

One row per player-game including inactive players (`dnp`, `dnp_reason`, `dnp_injury`). `min_share` = share of team minutes; `usage` = usage-rate proxy.

Columns: `game_id`, `season`, `season_type`, `game_date`, `team`, `team_id`, `opponent`, `home`, `win`, `player_id`, `player_name`, `position`, `jersey_num`, `starter`, `played`, `dnp`, `dnp_reason`, `dnp_injury`, `min`, `min_share`, `fgm`, `fga`, `fg3m`, `fg3a`, `ftm`, `fta`, `oreb`, `dreb`, `reb`, `ast`, `stl`, `blk`, `tov`, `pf`, `pts`, `plus_minus`, `ts`, `efg`, `usage`

## `lineups.parquet`

24,015 rows · 106 columns · 2.5 MB · last game date None

Five-man lineups per team-season (regular season and playoffs) from stats.nba.com `leaguedashlineups`: minutes, possessions, off/def/net rating, four factors, scoring splits, opponent stats; player ids parsed into `player1_id..player5_id`.

Columns: `season`, `season_type`, `team`, `team_id`, `group_id`, `lineup_name`, `player_ids`, `player1_id`, `player2_id`, `player3_id`, `player4_id`, `player5_id`, `gp`, `w`, `l`, `minutes`, `poss`, `off_rating`, `def_rating`, `net_rating`, `pace`, `efg_pct`, `ts_pct`, `tm_tov_pct`, `oreb_pct`, `dreb_pct`, `fta_rate`, `opp_efg_pct`, `opp_fta_rate`, `opp_tov_pct`, `opp_oreb_pct`, `plus_minus`, `pts`, `opp_pts`, `w_pct`, `e_off_rating`, `e_def_rating`, `e_net_rating`, `ast_pct`, `ast_to`, `ast_ratio`, `reb_pct`, `e_pace`, `pace_per40`, `pie`, `fgm`, `fga`, `fg_pct`, `fg3m`, `fg3a`, `fg3_pct`, `ftm`, `fta`, `ft_pct`, `oreb`, `dreb`, `reb`, `ast`, `tov`, `stl`, `blk`, `blka`, `pf`, `pfd`, `pts_off_tov`, `pts_2nd_chance`, `pts_fb`, `pts_paint`, `opp_pts_off_tov`, `opp_pts_2nd_chance`, `opp_pts_fb`, `opp_pts_paint`, `opp_fgm`, `opp_fga`, `opp_fg_pct`, `opp_fg3m`, `opp_fg3a`, `opp_fg3_pct`, `opp_ftm`, `opp_fta`, `opp_ft_pct`, `opp_oreb`, `opp_dreb`, `opp_reb`, `opp_ast`, `opp_tov`, `opp_stl`, `opp_blk`, `opp_blka`, `opp_pf`, `opp_pfd`, `pct_fga_2pt`, `pct_fga_3pt`, `pct_pts_2pt`, `pct_pts_2pt_mr`, `pct_pts_3pt`, `pct_pts_fb`, `pct_pts_ft`, `pct_pts_off_tov`, `pct_pts_paint`, `pct_ast_2pm`, `pct_uast_2pm`, `pct_ast_3pm`, `pct_uast_3pm`, `pct_ast_fgm`, `pct_uast_fgm`

## `team_seasons.parquet`

260 rows · 99 columns · 0.1 MB · last game date None

Team-season aggregates (advanced, base, misc, scoring, opponent families folded wide).

Columns: `season`, `season_type`, `team`, `team_id`, `team_name`, `gp`, `w`, `l`, `w_pct`, `min`, `e_off_rating`, `off_rating`, `e_def_rating`, `def_rating`, `e_net_rating`, `net_rating`, `ast_pct`, `ast_to`, `ast_ratio`, `oreb_pct`, `dreb_pct`, `reb_pct`, `tm_tov_pct`, `efg_pct`, `ts_pct`, `e_pace`, `pace`, `pace_per40`, `poss`, `pie`, `fgm`, `fga`, `fg_pct`, `fg3m`, `fg3a`, `fg3_pct`, `ftm`, `fta`, `ft_pct`, `oreb`, `dreb`, `reb`, `ast`, `tov`, `stl`, `blk`, `blka`, `pf`, `pfd`, `pts`, `plus_minus`, `opp_pts_off_tov`, `opp_pts_2nd_chance`, `opp_pts_fb`, `opp_pts_paint`, `pts_off_tov`, `pts_2nd_chance`, `pts_fb`, `pts_paint`, `opp_fgm`, `opp_fga`, `opp_fg_pct`, `opp_fg3m`, `opp_fg3a`, `opp_fg3_pct`, `opp_ftm`, `opp_fta`, `opp_ft_pct`, `opp_oreb`, `opp_dreb`, `opp_reb`, `opp_ast`, `opp_tov`, `opp_stl`, `opp_blk`, `opp_blka`, `opp_pf`, `opp_pfd`, `opp_pts`, `pct_fga_2pt`, `pct_fga_3pt`, `pct_pts_2pt`, `pct_pts_2pt_mr`, `pct_pts_3pt`, `pct_pts_fb`, `pct_pts_ft`, `pct_pts_off_tov`, `pct_pts_paint`, `pct_ast_2pm`, `pct_uast_2pm`, `pct_ast_3pm`, `pct_uast_3pm`, `pct_ast_fgm`, `pct_uast_fgm`, `fta_rate`, `opp_efg_pct`, `opp_fta_rate`, `opp_tov_pct`, `opp_oreb_pct`

## `injuries.parquet`

1,205,713 rows · 15 columns · 3.6 MB · last game date 2026-11-02

Every published version of the official NBA injury report (2021-22 .. today): `report_datetime` (ET), `game_id`, `team`, `player_name`, `player_id`, `status`, `reason`, `reason_category`.

Columns: `season`, `report_datetime`, `game_date`, `game_id`, `report_matchup`, `team`, `team_id`, `player_name`, `player_id`, `status`, `previous_status`, `reason`, `reason_category`, `submitted`, `match_method`

## Derived tables

- `team_game_features.parquet`: pre-game team state (Elo, EWMA / opponent-adjusted efficiencies, season-to-date blends, schedule context) per team-game.
- `player_season_impact.parquet`, `player_values.parquet`, `player_values_current.parquet`: player impact values (points per 100 possessions on court vs average).
- `coach_team_game_metrics.parquet`, `coach_season_metrics.parquet`, `coach_career_metrics.parquet`, `coach_game_attribution.parquet`, `coaches.parquet`: coaching metrics and scores.
- `pregame_injury_lines.parquet`, `availability_features.parquet`, `player_typical_minutes.parquet`, `status_play_rates.json`: injury-report derived availability.
- `game_features.parquet`: the model feature matrix (one row per game, completed + upcoming).
- `sim_features.parquet`: ratings-only Monte Carlo outputs for every completed game (model inputs).

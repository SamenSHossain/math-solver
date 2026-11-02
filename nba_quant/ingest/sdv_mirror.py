"""Download per-season parquet assets from the sportsdataverse GitHub release mirrors.

Two upstream pipelines publish to github.com/sportsdataverse/sportsdataverse-data releases:

* ``espn_nba_*``  – hoopR-nba-data (source: ESPN; refreshed daily in-season, so it carries
  the live 2026-27 season: schedule, team/player box scores, play-by-play, game rosters).
* ``nba_stats_*`` – hoopR-nba-stats-data (source: stats.nba.com; lineups, possessions,
  coaches, game rosters, official injury report, advanced season stats).

Assets are named ``<stem>_<season>.parquet`` with the season as its END year
(2027 == 2026-27). Downloads are cached under data/raw/<tag>/ and only re-fetched when
``force`` is set or the file is missing. This is the only network dependency of the
project: stats.nba.com / ESPN direct APIs are optional accelerators (see live.py).
"""
from __future__ import annotations

import logging
import os
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import requests

from nba_quant.config import ALL_SEASONS, RAW_DIR

log = logging.getLogger(__name__)

RELEASE_BASE = "https://github.com/sportsdataverse/sportsdataverse-data/releases/download"
RAW_BASE = "https://raw.githubusercontent.com/sportsdataverse"


@dataclass(frozen=True)
class Asset:
    tag: str          # release tag, e.g. espn_nba_team_boxscores
    stem: str         # file stem without season, e.g. team_box
    per_season: bool = True

    def filename(self, season: int | None = None) -> str:
        return f"{self.stem}_{season}.parquet" if self.per_season else f"{self.stem}.parquet"

    def url(self, season: int | None = None) -> str:
        return f"{RELEASE_BASE}/{self.tag}/{self.filename(season)}"

    def local_path(self, season: int | None = None) -> Path:
        return RAW_DIR / self.tag / self.filename(season)


# --- ESPN-sourced (daily refreshed) --------------------------------------------------
ESPN_SCHEDULE = Asset("espn_nba_schedules", "nba_schedule")
ESPN_TEAM_BOX = Asset("espn_nba_team_boxscores", "team_box")
ESPN_PLAYER_BOX = Asset("espn_nba_player_boxscores", "player_box")
ESPN_PBP = Asset("espn_nba_pbp", "play_by_play")
ESPN_GAME_ROSTERS = Asset("espn_nba_game_rosters", "game_rosters")
ESPN_TEAM_SEASON = Asset("espn_nba_team_season_stats", "team_season_stats")
ESPN_OFFICIALS = Asset("espn_nba_officials", "officials")
ESPN_ROSTERS = Asset("espn_nba_rosters", "rosters")

# --- NBA Stats-sourced -----------------------------------------------------------------
NBA_LINEUPS = Asset("nba_stats_lineups", "lineups")                   # leaguedashlineups
NBA_COACHES = Asset("nba_stats_coaches", "coaches")                   # commonteamroster coaches
NBA_TEAM_BOX = Asset("nba_stats_team_boxscores", "team_boxscores")
NBA_PLAYER_BOX = Asset("nba_stats_player_boxscores", "player_boxscores")
NBA_GAME_ROSTERS = Asset("nba_stats_game_rosters", "game_rosters")
NBA_PLAYER_LOGS = Asset("nba_stats_player_game_logs", "player_game_logs")
NBA_INJURY_REPORT = Asset("nba_stats_injury_report", "injury_report")  # official NBA report
NBA_SCHEDULE = Asset("nba_stats_schedules", "nba_schedule")
NBA_TEAM_SEASON = Asset("nba_stats_team_season_stats", "team_season_stats")
NBA_PLAYER_SEASON = Asset("nba_stats_player_season_stats", "player_season_stats")
NBA_ROSTERS = Asset("nba_stats_rosters", "rosters")
NBA_STANDINGS = Asset("nba_stats_standings", "standings")
NBA_GAME_MATCHUPS = Asset("nba_stats_game_matchups", "game_matchups")
NBA_SHOTS = Asset("nba_stats_shots", "shots")

CORE_ASSETS = [
    ESPN_SCHEDULE, ESPN_TEAM_BOX, ESPN_PLAYER_BOX, ESPN_GAME_ROSTERS, ESPN_TEAM_SEASON,
    NBA_LINEUPS, NBA_COACHES, NBA_TEAM_BOX, NBA_PLAYER_BOX, NBA_GAME_ROSTERS,
    NBA_PLAYER_LOGS, NBA_INJURY_REPORT, NBA_SCHEDULE, NBA_TEAM_SEASON, NBA_PLAYER_SEASON,
    NBA_ROSTERS, NBA_STANDINGS,
]
HEAVY_ASSETS = [ESPN_PBP]  # ~80-100 MB per season; needed for coaching/clutch metrics


def _session() -> requests.Session:
    s = requests.Session()
    s.headers["User-Agent"] = "nba-quant/0.1 (+https://github.com/samenshossain/math-solver)"
    ca = os.environ.get("REQUESTS_CA_BUNDLE") or os.environ.get("SSL_CERT_FILE")
    if ca and Path(ca).exists():
        s.verify = ca
    return s


def download(asset: Asset, season: int | None = None, force: bool = False,
             session: requests.Session | None = None, retries: int = 4) -> Path | None:
    """Fetch one asset to the raw cache. Returns the path, or None if the asset is absent (404)."""
    path = asset.local_path(season)
    if path.exists() and not force and path.stat().st_size > 0:
        return path
    path.parent.mkdir(parents=True, exist_ok=True)
    s = session or _session()
    url = asset.url(season)
    delay = 2.0
    for attempt in range(retries):
        try:
            r = s.get(url, timeout=180, stream=True, allow_redirects=True)
            if r.status_code == 404:
                log.info("absent: %s", url)
                return None
            r.raise_for_status()
            tmp = path.with_suffix(".part")
            with open(tmp, "wb") as fh:
                for chunk in r.iter_content(1 << 20):
                    fh.write(chunk)
            tmp.replace(path)
            log.info("downloaded %s (%.1f MB)", path.name, path.stat().st_size / 1e6)
            return path
        except requests.RequestException as exc:  # network blip: back off and retry
            log.warning("retry %d for %s: %s", attempt + 1, url, exc)
            time.sleep(delay)
            delay *= 2
    raise RuntimeError(f"failed to download {url}")


def download_many(assets: Iterable[Asset], seasons: Iterable[int] = ALL_SEASONS,
                  force: bool = False) -> dict[tuple[str, int | None], Path | None]:
    s = _session()
    out: dict[tuple[str, int | None], Path | None] = {}
    for a in assets:
        for season in (seasons if a.per_season else [None]):
            out[(a.tag, season)] = download(a, season, force=force, session=s)
    return out


def download_schedule_master(force: bool = False) -> Path:
    """Committed stats.nba.com schedule master (all seasons, game ids + dates)."""
    path = RAW_DIR / "nba_stats_master" / "nba_stats_schedule_master.parquet"
    if path.exists() and not force:
        return path
    path.parent.mkdir(parents=True, exist_ok=True)
    url = f"{RAW_BASE}/hoopR-nba-stats-data/main/nba_stats/nba_stats_schedule_master.parquet"
    r = _session().get(url, timeout=120)
    r.raise_for_status()
    path.write_bytes(r.content)
    return path


if __name__ == "__main__":  # quick manual run: python -m nba_quant.ingest.sdv_mirror
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    res = download_many(CORE_ASSETS)
    missing = [k for k, v in res.items() if v is None]
    print(f"fetched {len(res) - len(missing)} assets; absent: {missing}")

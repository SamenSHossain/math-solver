"""Central configuration: paths, seasons, team identity maps."""
from __future__ import annotations

import os
from pathlib import Path

ROOT = Path(os.environ.get("NBA_QUANT_ROOT", Path(__file__).resolve().parents[1]))
DATA_DIR = ROOT / "data"
RAW_DIR = DATA_DIR / "raw"
PARQUET_DIR = DATA_DIR / "parquet"
RESEARCH_DIR = DATA_DIR / "research"
PRED_DIR = DATA_DIR / "predictions"
MODEL_DIR = ROOT / "models"

# Seasons are labelled by their END year (2026 == the 2025-26 season), matching the
# sportsdataverse release assets. "Last five seasons" + the live 2026-27 season.
HISTORY_SEASONS = [2022, 2023, 2024, 2025, 2026]
CURRENT_SEASON = 2027
ALL_SEASONS = HISTORY_SEASONS + [CURRENT_SEASON]

# ESPN tri-codes -> NBA Stats tri-codes where they differ.
ESPN_TO_NBA_TRICODE = {
    "GS": "GSW", "NY": "NYK", "NO": "NOP", "SA": "SAS", "UTAH": "UTA", "WSH": "WAS",
    "PHX": "PHX", "BKN": "BKN", "CHA": "CHA", "LAC": "LAC", "LAL": "LAL", "OKC": "OKC",
}

# stats.nba.com team ids -> tricode (stable since 2014).
NBA_TEAM_IDS = {
    1610612737: "ATL", 1610612738: "BOS", 1610612751: "BKN", 1610612766: "CHA",
    1610612741: "CHI", 1610612739: "CLE", 1610612742: "DAL", 1610612743: "DEN",
    1610612765: "DET", 1610612744: "GSW", 1610612745: "HOU", 1610612754: "IND",
    1610612746: "LAC", 1610612747: "LAL", 1610612763: "MEM", 1610612748: "MIA",
    1610612749: "MIL", 1610612750: "MIN", 1610612740: "NOP", 1610612752: "NYK",
    1610612760: "OKC", 1610612753: "ORL", 1610612755: "PHI", 1610612756: "PHX",
    1610612757: "POR", 1610612758: "SAC", 1610612759: "SAS", 1610612761: "TOR",
    1610612762: "UTA", 1610612764: "WAS",
}
TRICODE_TO_NBA_ID = {v: k for k, v in NBA_TEAM_IDS.items()}

TEAM_NAMES = {
    "ATL": "Atlanta Hawks", "BOS": "Boston Celtics", "BKN": "Brooklyn Nets",
    "CHA": "Charlotte Hornets", "CHI": "Chicago Bulls", "CLE": "Cleveland Cavaliers",
    "DAL": "Dallas Mavericks", "DEN": "Denver Nuggets", "DET": "Detroit Pistons",
    "GSW": "Golden State Warriors", "HOU": "Houston Rockets", "IND": "Indiana Pacers",
    "LAC": "LA Clippers", "LAL": "Los Angeles Lakers", "MEM": "Memphis Grizzlies",
    "MIA": "Miami Heat", "MIL": "Milwaukee Bucks", "MIN": "Minnesota Timberwolves",
    "NOP": "New Orleans Pelicans", "NYK": "New York Knicks", "OKC": "Oklahoma City Thunder",
    "ORL": "Orlando Magic", "PHI": "Philadelphia 76ers", "PHX": "Phoenix Suns",
    "POR": "Portland Trail Blazers", "SAC": "Sacramento Kings", "SAS": "San Antonio Spurs",
    "TOR": "Toronto Raptors", "UTA": "Utah Jazz", "WAS": "Washington Wizards",
}


def normalize_tricode(code: str | None) -> str | None:
    if code is None:
        return None
    code = str(code).upper().strip()
    return ESPN_TO_NBA_TRICODE.get(code, code)


for _d in (RAW_DIR, PARQUET_DIR, RESEARCH_DIR, PRED_DIR, MODEL_DIR):
    _d.mkdir(parents=True, exist_ok=True)

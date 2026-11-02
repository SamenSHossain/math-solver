"""End-to-end pipeline: download mirrors -> parquet lake -> features -> coaching -> models -> predictions.

    python scripts/build_all.py                 # full rebuild (uses cached raw downloads)
    python scripts/build_all.py --refresh       # re-download the live-season assets first
    python scripts/build_all.py --skip-train    # keep the saved models
    python scripts/build_all.py --date 2026-11-03
"""
from __future__ import annotations

import argparse, logging, subprocess, sys
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from nba_quant.config import CURRENT_SEASON  # noqa: E402
from nba_quant.ingest import sdv_mirror as M  # noqa: E402
from nba_quant.ingest.build_parquet import build_all as build_lake  # noqa: E402
from nba_quant.features import ratings, player_impact, injuries, build_features  # noqa: E402
from nba_quant.coaching import metrics as coach_metrics, scores as coach_scores  # noqa: E402

log = logging.getLogger("build_all")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--refresh", action="store_true", help="force re-download of current-season assets")
    ap.add_argument("--download-all", action="store_true", help="download every season (first run)")
    ap.add_argument("--skip-train", action="store_true")
    ap.add_argument("--skip-sim-features", action="store_true", help="skip the (slow) historical simulation features")
    ap.add_argument("--date", default=str(date.today()), help="predict games through this date (YYYY-MM-DD)")
    args = ap.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(name)s %(message)s")

    if args.download_all:
        M.download_many(M.CORE_ASSETS + M.HEAVY_ASSETS)
        M.download_many([M.NBA_LINEUPS, M.NBA_PLAYER_BOX, M.NBA_TEAM_BOX, M.NBA_SCHEDULE], seasons=[2020, 2021])
    if args.refresh:
        M.download_many(M.CORE_ASSETS + M.HEAVY_ASSETS, seasons=[CURRENT_SEASON], force=True)
    M.download_schedule_master()

    log.info("1/7 parquet lake"); build_lake()
    log.info("2/7 team ratings"); ratings.build_all()
    log.info("3/7 player impact"); player_impact.build_all()
    log.info("4/7 coaching metrics + scores"); coach_metrics.build_all(); coach_scores.build_scores()
    log.info("5/7 availability + game features"); injuries.build(through_date=args.date); build_features.build(through_date=args.date)
    if not args.skip_sim_features:
        log.info("6/7 historical sim features (slow)"); subprocess.run([sys.executable, str(ROOT / "scripts" / "run_sim_features.py"), "300"], check=True)
    if not args.skip_train:
        log.info("6/7 train models"); from nba_quant.model import train; train.main()
    log.info("7/7 slate predictions"); from nba_quant.model import predict; predict.main(args.date)
    log.info("done")


if __name__ == "__main__":
    main()

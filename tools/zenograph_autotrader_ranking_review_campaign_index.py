#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zenograph_ranking_review_campaign_index import (  # noqa: E402
    build_zenograph_ranking_review_campaign_index,
    render_zenograph_ranking_review_campaign_index_csv,
    render_zenograph_ranking_review_campaign_index_daily_block_reason_csv,
    render_zenograph_ranking_review_campaign_index_daily_csv,
    render_zenograph_ranking_review_campaign_index_markdown,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Index ZenoGraph ranking review campaign bundles under a campaign root.",
        epilog=(
            "Advanced experimental automation review index. "
            "This only scans non-executing review artifacts."
        ),
    )
    parser.add_argument(
        "--campaign-root",
        type=Path,
        default=ROOT / "internal" / "zenograph_shadow",
    )
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--gate-status", choices=("allowed", "blocked"), default=None)
    parser.add_argument("--run-id-prefix", type=str, default=None)
    parser.add_argument("--git-prefix", type=str, default=None)
    parser.add_argument("--dirty-state", choices=("clean", "dirty"), default=None)
    parser.add_argument("--generated-since-utc", type=str, default=None)
    parser.add_argument("--generated-until-utc", type=str, default=None)
    parser.add_argument("--markdown-out", type=Path, default=None)
    parser.add_argument("--csv-out", type=Path, default=None)
    parser.add_argument("--csv-daily-out", type=Path, default=None)
    parser.add_argument("--csv-daily-block-reasons-out", type=Path, default=None)
    parser.add_argument("--out", type=Path, default=None)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    payload = build_zenograph_ranking_review_campaign_index(
        campaign_root=args.campaign_root,
        limit=args.limit,
        gate_status=args.gate_status,
        run_id_prefix=args.run_id_prefix,
        git_prefix=args.git_prefix,
        dirty_state=args.dirty_state,
        generated_since_utc=args.generated_since_utc,
        generated_until_utc=args.generated_until_utc,
    )
    text = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
    if args.markdown_out is not None:
        args.markdown_out.parent.mkdir(parents=True, exist_ok=True)
        args.markdown_out.write_text(
            render_zenograph_ranking_review_campaign_index_markdown(payload),
            encoding="utf-8",
        )
    if args.csv_out is not None:
        args.csv_out.parent.mkdir(parents=True, exist_ok=True)
        args.csv_out.write_text(
            render_zenograph_ranking_review_campaign_index_csv(payload),
            encoding="utf-8",
        )
    if args.csv_daily_out is not None:
        args.csv_daily_out.parent.mkdir(parents=True, exist_ok=True)
        args.csv_daily_out.write_text(
            render_zenograph_ranking_review_campaign_index_daily_csv(payload),
            encoding="utf-8",
        )
    if args.csv_daily_block_reasons_out is not None:
        args.csv_daily_block_reasons_out.parent.mkdir(parents=True, exist_ok=True)
        args.csv_daily_block_reasons_out.write_text(
            render_zenograph_ranking_review_campaign_index_daily_block_reason_csv(payload),
            encoding="utf-8",
        )
    sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

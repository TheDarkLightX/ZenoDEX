#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zenograph_ranking_review_campaign_index import (  # noqa: E402
    build_zenograph_ranking_review_campaign_index,
)
from src.integration.zenograph_ranking_review_campaign_report import (  # noqa: E402
    render_zenograph_ranking_review_campaign_html,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Render a read-only HTML report for ZenoGraph ranking review campaigns.",
        epilog=(
            "Advanced experimental automation review report. "
            "This is a read-only artifact and does not affect execution."
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
    parser.add_argument("--html-out", type=Path, required=True)
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
    args.html_out.parent.mkdir(parents=True, exist_ok=True)
    args.html_out.write_text(
        render_zenograph_ranking_review_campaign_html(payload),
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

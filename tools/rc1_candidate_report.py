#!/usr/bin/env python3
"""Render a static HTML report for release-candidate receipts."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]

if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

try:
    from src.integration.rc1_candidate_index import build_candidate_index_payload
    from src.integration.rc1_candidate_report import render_candidate_report_html
except ModuleNotFoundError:  # pragma: no cover - script execution path
    from integration.rc1_candidate_index import build_candidate_index_payload
    from integration.rc1_candidate_report import render_candidate_report_html


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Render a static HTML report for current release-candidate receipts.")
    parser.add_argument(
        "--campaign-root",
        default="internal/rc1_candidates",
        help="root directory containing candidate receipt bundles",
    )
    parser.add_argument("--ready-state", choices=("ready", "blocked"))
    parser.add_argument("--run-id-prefix")
    parser.add_argument("--html-out", required=True, help="path to write the HTML report")
    args = parser.parse_args(argv)

    payload = build_candidate_index_payload(
        REPO_ROOT / args.campaign_root,
        ready_state=args.ready_state,
        run_id_prefix=args.run_id_prefix,
    )
    html_out = Path(args.html_out)
    html_out.parent.mkdir(parents=True, exist_ok=True)
    html_out.write_text(render_candidate_report_html(payload), encoding="utf-8")
    print(f"wrote {html_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""List and summarize release-candidate receipts."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]

if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

try:
    from src.integration.rc1_candidate_index import (
        build_candidate_index_payload,
        render_candidate_index_csv,
        render_candidate_index_markdown,
        render_candidate_index_text,
    )
except ModuleNotFoundError:  # pragma: no cover - script execution path
    from integration.rc1_candidate_index import (
        build_candidate_index_payload,
        render_candidate_index_csv,
        render_candidate_index_markdown,
        render_candidate_index_text,
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Index current release-candidate receipt directories.")
    parser.add_argument(
        "--campaign-root",
        default="internal/rc1_candidates",
        help="root directory containing candidate receipt bundles",
    )
    parser.add_argument("--format", choices=("text", "json", "markdown"), default="text")
    parser.add_argument("--ready-state", choices=("ready", "blocked"))
    parser.add_argument("--run-id-prefix")
    parser.add_argument("--csv-out", help="optional path to write a flat CSV export")
    args = parser.parse_args(argv)

    payload = build_candidate_index_payload(
        REPO_ROOT / args.campaign_root,
        ready_state=args.ready_state,
        run_id_prefix=args.run_id_prefix,
    )
    if args.csv_out:
        csv_path = Path(args.csv_out)
        csv_path.parent.mkdir(parents=True, exist_ok=True)
        csv_path.write_text(render_candidate_index_csv(payload), encoding="utf-8")
    if args.format == "json":
        print(json.dumps(payload, indent=2, sort_keys=True))
    elif args.format == "markdown":
        print(render_candidate_index_markdown(payload), end="")
    else:
        print(render_candidate_index_text(payload), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zenograph_ranking_stage_summary import (  # noqa: E402
    render_zenograph_ranking_stage_markdown,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Render a human-readable markdown summary for a ZenoGraph ranking stage report.",
        epilog=(
            "Advanced experimental automation reporting tool. "
            "This only formats non-executing staging output."
        ),
    )
    parser.add_argument("--stage-report-file", required=True, type=Path)
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args(argv)

    payload = json.loads(args.stage_report_file.read_text(encoding="utf-8"))
    text = render_zenograph_ranking_stage_markdown(payload)
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
    sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

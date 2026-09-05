#!/usr/bin/env python3
"""Check exact V3 research-plan selection; JSON result, nonzero on any drift."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.whole_program_plan_admission_v2 import REPO_ROOT, check_active_whole_program_plan_v2


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json", action="store_true", help="JSON is always emitted")
    args = parser.parse_args(argv)
    report = check_active_whole_program_plan_v2(root=args.root)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

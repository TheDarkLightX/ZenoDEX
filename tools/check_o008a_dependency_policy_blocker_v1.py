#!/usr/bin/env python3
"""Check the canonical source-bound O-008A dependency-policy blocker."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.o008a_dependency_policy_blocker_v1 import (  # noqa: E402
    canonical_json_bytes,
    check_blocker,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    report = check_blocker(args.root)
    print(canonical_json_bytes(report).decode("utf-8"))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())

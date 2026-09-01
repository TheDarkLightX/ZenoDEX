#!/usr/bin/env python3
"""Check the source-pinned O-008A RISC0 dependency patch."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.o008a_risc0_dependency_patch_v1 import (  # noqa: E402
    canonical_json_bytes_v1,
    check_v1,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument(
        "--subject",
        required=True,
        help="literal lowercase 40-hex commit SHA to validate",
    )
    args = parser.parse_args()
    report = check_v1(args.root, args.subject)
    print(canonical_json_bytes_v1(report).decode("utf-8"))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Check the canonical source-bound O-008A resolution admission."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.o008a_dependency_resolution_admission_v2 import (  # noqa: E402
    canonical_json_bytes,
    check_admission,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    report = check_admission(args.root)
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())

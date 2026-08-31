#!/usr/bin/env python3
"""Build or check the canonical O-004 V2 operator-surface artifact."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.operator_surface_registry_v2 import (  # noqa: E402
    ARTIFACT_RELATIVE_PATH_V2,
    build_registry_bytes_v2,
    check_registry_v2,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--out", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    output = args.out or (root / ARTIFACT_RELATIVE_PATH_V2)
    if args.check:
        if args.out is not None:
            print("ERROR: --out is not supported with topology-aware --check")
            return 2
        report = check_registry_v2(root)
        if report["ok"] is not True:
            print(f"ERROR: invalid artifact: {report['findings']}")
            return 1
        print(f"OK {output}")
        return 0
    expected = build_registry_bytes_v2(root)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(expected)
    print(f"wrote {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

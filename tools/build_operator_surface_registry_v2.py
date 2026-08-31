#!/usr/bin/env python3
"""Build or check the canonical O-004 V2 operator-surface artifact."""

from __future__ import annotations

import argparse
from pathlib import Path

from tools.operator_surface_registry_v2 import (
    ARTIFACT_RELATIVE_PATH_V2,
    build_registry_bytes_v2,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--out", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    output = args.out or (root / ARTIFACT_RELATIVE_PATH_V2)
    expected = build_registry_bytes_v2(root)
    if args.check:
        if not output.is_file() or output.read_bytes() != expected:
            print(f"ERROR: stale or missing artifact: {output}")
            return 1
        print(f"OK {output}")
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(expected)
    print(f"wrote {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

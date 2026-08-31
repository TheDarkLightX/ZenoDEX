#!/usr/bin/env python3
"""Check the canonical O-004 V2 operator-surface artifact."""

from __future__ import annotations

import argparse
from pathlib import Path

from tools.operator_surface_registry_v2 import canonical_json_bytes_v2, check_registry_v2


def check_operator_surface_registry_v2(root: Path) -> dict[str, object]:
    return check_registry_v2(root)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    report = check_operator_surface_registry_v2(args.root)
    print(canonical_json_bytes_v2(report).decode("utf-8"))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())

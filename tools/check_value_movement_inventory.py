#!/usr/bin/env python3
"""Fail-closed shell for the immutable value-movement inventory core."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from fcis_inventory_core import (
    SourceFile,
    canonical_report,
    parse_inventory,
    validate_inventory,
)

REPO = Path(__file__).resolve().parents[1]
DEFAULT_INVENTORY = REPO / "config/runtime_fcis/value_moving_surfaces_v1.json"
SOURCE_SUFFIXES = frozenset({".py", ".rs", ".sql"})


def _inside_repo(path: Path) -> Path:
    resolved = path.resolve()
    resolved.relative_to(REPO.resolve())
    return resolved


def _read_sources(scan_roots: tuple[str, ...]) -> tuple[SourceFile, ...]:
    sources: list[SourceFile] = []
    for raw_root in scan_roots:
        root = _inside_repo(REPO / raw_root)
        if not root.is_dir():
            raise ValueError(f"scan root is not a directory: {raw_root}")
        for path in sorted(root.rglob("*")):
            if path.is_file() and path.suffix in SOURCE_SUFFIXES:
                sources.append(
                    SourceFile(
                        path=path.relative_to(REPO).as_posix(),
                        text=path.read_text(encoding="utf-8"),
                    )
                )
    paths = tuple(source.path for source in sources)
    if len(paths) != len(set(paths)):
        raise ValueError("scan roots overlap")
    return tuple(sources)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--inventory", type=Path, default=DEFAULT_INVENTORY)
    parser.add_argument("--require-release", action="store_true")
    parser.add_argument("--show-bindings", action="store_true")
    args = parser.parse_args()

    inventory_path = _inside_repo(args.inventory)
    raw = json.loads(inventory_path.read_text(encoding="utf-8"))
    inventory = parse_inventory(raw)
    sources = _read_sources(inventory.scan_roots)
    diagnostics = validate_inventory(
        inventory,
        sources,
        require_release=args.require_release,
    )
    report = canonical_report(
        inventory,
        sources,
        diagnostics,
        require_release=args.require_release,
    )
    if args.show_bindings or diagnostics:
        print(report, end="")
    return 1 if diagnostics else 0


if __name__ == "__main__":
    raise SystemExit(main())

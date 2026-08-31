#!/usr/bin/env python3
"""CLI for the fail-closed critical BVA coverage inventory."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.bva.critical_surface_coverage_common_v1 import CoverageManifestError  # noqa: E402
from tools.bva.critical_surface_coverage_v1 import (  # noqa: E402
    DEFAULT_MANIFEST,
    REQUIRED_BOUNDARY_CLASSES,
    check_manifest,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Validate critical value-moving BVA coverage inventory."
    )
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = check_manifest(args.manifest, require_complete=args.require_complete)
    except CoverageManifestError as exc:
        print(json.dumps({"ok": False, "error": str(exc)}, sort_keys=True))
        return 1
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))


__all__ = [
    "CoverageManifestError",
    "DEFAULT_MANIFEST",
    "REQUIRED_BOUNDARY_CLASSES",
    "check_manifest",
    "main",
]

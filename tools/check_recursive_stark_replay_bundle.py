#!/usr/bin/env python3
"""Check an artifact-pinned local recursive STARK replay bundle."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.recursive_stark_replay_manifest import (  # noqa: E402
    check_recursive_stark_replay_bundle_v1,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundle", type=Path)
    parser.add_argument(
        "--expected-manifest-sha256",
        help="Optional externally supplied sha256:<64 lowercase hex> digest of manifest.json",
    )
    args = parser.parse_args(list(argv) if argv is not None else sys.argv[1:])
    report = check_recursive_stark_replay_bundle_v1(
        args.bundle,
        expected_manifest_sha256=args.expected_manifest_sha256,
    )
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

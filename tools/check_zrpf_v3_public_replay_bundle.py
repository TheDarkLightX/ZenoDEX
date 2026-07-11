#!/usr/bin/env python3
"""Statically check and optionally execute the ZRPF V3 public replay bundle."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if __name__ == "__main__" and not sys.flags.isolated:
    os.execv(
        sys.executable,
        [sys.executable, "-I", str(Path(__file__).resolve()), *sys.argv[1:]],
    )
sys.path.insert(0, str(ROOT))

from src.integration import zrpf_public_replay_bundle as replay  # noqa: E402

if Path(replay.__file__).resolve() != ROOT / "src/integration/zrpf_public_replay_bundle.py":
    raise RuntimeError("public replay implementation import escaped the repository root")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", type=Path, default=ROOT / replay.DEFAULT_BUNDLE_RELATIVE)
    parser.add_argument("--reference", type=Path, default=ROOT / replay.DEFAULT_REFERENCE_RELATIVE)
    parser.add_argument(
        "--execute",
        action="store_true",
        help=(
            "opt in to running the digest-pinned native verifier as the current user; "
            "static checking is the default"
        ),
    )
    args = parser.parse_args()
    report = replay.check_bundle(
        bundle_directory=args.bundle,
        reference_path=args.reference,
        execute=args.execute,
    )
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

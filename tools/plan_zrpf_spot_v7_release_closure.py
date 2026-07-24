#!/usr/bin/env python3
"""Emit one canonical authority-neutral Spot V7 release-closure plan."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Sequence

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as v6_planner
from tools import zrpf_spot_v7_release_closure as release
from tools.zrpf_v6_identity_executor_types import ExecutionError
from tools.zrpf_v6_identity_materialization_git import MaterializationError


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Emit an authority-neutral post-G Spot V7 release-closure plan."
    )
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--runtime-identity", type=Path, required=True)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        runtime = v6_planner.load_canonical_json(
            args.runtime_identity,
            "Spot V7 build runtime identity",
        )
        plan = release.build_release_closure_plan(args.repository, runtime)
        sys.stdout.buffer.write(release.canonical_bytes(plan))
    except (
        ExecutionError,
        MaterializationError,
        OSError,
        release.ReleaseClosureError,
        v6_planner.RebuildPlanError,
    ) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

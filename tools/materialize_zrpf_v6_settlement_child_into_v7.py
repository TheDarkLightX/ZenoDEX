#!/usr/bin/env python3
"""CLI for authority-neutral V6 settlement to V7 child-policy materialization."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Sequence

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools.zrpf_v6_identity_executor_types import ExecutionError
from tools.zrpf_v6_v7_child_policy_materialization import (
    MaterializationError,
    MaterializationRequest,
    apply_materialization,
    check_materialization,
)


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    for name in ("check", "apply"):
        command = subparsers.add_parser(name)
        command.add_argument("--c1-commit", required=True)
        command.add_argument("--plan", type=Path, required=True)
        command.add_argument("--observations", type=Path, required=True)
        command.add_argument("--report", type=Path, required=True)
        if name == "apply":
            command.add_argument("--manifest-out", type=Path, required=True)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    request = MaterializationRequest(
        repo_root=planner.REPO_ROOT,
        c1_commit=args.c1_commit,
        plan_path=args.plan,
        observations_path=args.observations,
        report_path=args.report,
    )
    try:
        if args.command == "check":
            result = check_materialization(request)
        else:
            result = apply_materialization(request, manifest_output=args.manifest_out)
        sys.stdout.buffer.write(planner.canonical_bytes(result))
    except (
        ExecutionError,
        MaterializationError,
        OSError,
        planner.RebuildPlanError,
    ) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""CLI for the authority-neutral committed V6-to-V7 post-pin check."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Sequence

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools import zrpf_v6_v7_post_pin_governance as governance
from tools.zrpf_v6_identity_executor_types import ExecutionError
from tools.zrpf_v6_identity_materialization_git import MaterializationError


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Check the fixed committed V6-to-V7 post-pin evidence chain; "
            "the result is authority-neutral."
        )
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        result = governance.check_post_pin_governance(planner.REPO_ROOT)
        sys.stdout.buffer.write(planner.canonical_bytes(result))
    except (
        ExecutionError,
        governance.GovernanceError,
        MaterializationError,
        planner.RebuildPlanError,
        OSError,
    ) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Fail closed when the exact-subject O-005 completion certificate drifts."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

try:
    from tools.build_m6_normative_requirements_v1 import (
        ShellRejectV1,
        _read_bounded_regular_file_v1,
        _require_inert_path_v1,
    )
    from tools.build_m6_o005_requirements_floor_completion_v1 import (
        JSON_OUTPUT,
        REPO_ROOT,
        load_subject_snapshot_v1,
    )
    from tools.m6_o005_requirements_floor_completion_v1 import (
        CHECK_SCHEMA_V1,
        MAX_ARTIFACT_BYTES_V1,
        CompletionRejectV1,
        check_requirements_floor_completion_artifact_v1,
    )
except ModuleNotFoundError:
    from build_m6_normative_requirements_v1 import (
        ShellRejectV1,
        _read_bounded_regular_file_v1,
        _require_inert_path_v1,
    )
    from build_m6_o005_requirements_floor_completion_v1 import (  # type: ignore[no-redef]
        JSON_OUTPUT,
        REPO_ROOT,
        load_subject_snapshot_v1,
    )
    from m6_o005_requirements_floor_completion_v1 import (  # type: ignore[no-redef]
        CHECK_SCHEMA_V1,
        MAX_ARTIFACT_BYTES_V1,
        CompletionRejectV1,
        check_requirements_floor_completion_artifact_v1,
    )


def _failure_report_v1(exc: CompletionRejectV1 | ShellRejectV1) -> dict[str, object]:
    return {
        "artifact_sha256": "",
        "closed_value_movement_gates": 0,
        "current_successor_o005_status": "OPEN",
        "findings": [{"code": exc.code, "detail": exc.detail, "path": exc.path}],
        "manifest_complete": False,
        "ok": False,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "requirements_closed": False,
        "schema": CHECK_SCHEMA_V1,
        "semantic_closure_complete": False,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }


def check_m6_o005_requirements_floor_completion_v1(
    root: Path | str = REPO_ROOT, artifact_path: Path | str | None = None
) -> dict[str, object]:
    """Acquire bounded inputs once, then delegate all certificate logic to the core."""

    try:
        inert_root = _require_inert_path_v1(root, "O005 completion checker root")
        path = (
            inert_root / JSON_OUTPUT
            if artifact_path is None
            else _require_inert_path_v1(artifact_path, "O005 completion certificate")
        )
        raw = _read_bounded_regular_file_v1(
            path, MAX_ARTIFACT_BYTES_V1, "O005 completion certificate"
        )
        snapshot = load_subject_snapshot_v1(inert_root)
    except (CompletionRejectV1, ShellRejectV1) as exc:
        return _failure_report_v1(exc)
    return check_requirements_floor_completion_artifact_v1(raw, snapshot)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    args = parser.parse_args(argv)
    report = check_m6_o005_requirements_floor_completion_v1(args.root)
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())

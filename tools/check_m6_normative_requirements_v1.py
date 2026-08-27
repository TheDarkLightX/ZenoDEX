#!/usr/bin/env python3
"""Fail closed when the M6 normative requirements registry drifts or promotes."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

try:
    from tools.build_m6_normative_requirements_v1 import (
        ARTIFACT_MAX_BYTES_V1,
        JSON_OUTPUT,
        REPO_ROOT,
        ShellRejectV1,
        _read_bounded_regular_file_v1,
        load_source_snapshot_v1,
    )
    from tools.m6_normative_requirements_v1 import (
        CHECK_SCHEMA_V1,
        RequirementsRejectV1,
        check_requirements_registry_v1,
    )
except ModuleNotFoundError:
    from build_m6_normative_requirements_v1 import (  # type: ignore[no-redef]
        ARTIFACT_MAX_BYTES_V1,
        JSON_OUTPUT,
        REPO_ROOT,
        ShellRejectV1,
        _read_bounded_regular_file_v1,
        load_source_snapshot_v1,
    )
    from m6_normative_requirements_v1 import (  # type: ignore[no-redef]
        CHECK_SCHEMA_V1,
        RequirementsRejectV1,
        check_requirements_registry_v1,
    )


def _shell_failure_report_v1(
    exc: ShellRejectV1 | RequirementsRejectV1,
) -> dict[str, object]:
    return {
        "artifact_sha256": "",
        "expected_registry_root": None,
        "findings": [{"code": exc.code, "detail": exc.detail, "path": exc.path}],
        "manifest_complete": False,
        "ok": False,
        "production_authority": "NONE",
        "production_promotion": False,
        "release_eligible": False,
        "requirements_closed": False,
        "schema": CHECK_SCHEMA_V1,
        "semantic_capability_coverage_complete": False,
        "semantic_closure_complete": False,
        "semantic_target_inventory_complete": False,
        "settlement_authority": "NONE",
        "source_row_census_complete": False,
        "structural_mapping_complete": False,
        "value_movement_claim_allowed": False,
    }


def check_m6_normative_requirements_v1(
    root: Path = REPO_ROOT,
    artifact_path: Path | None = None,
) -> dict[str, object]:
    """Read bounded shell inputs once, then delegate trust decisions to the core."""

    source = artifact_path or root / JSON_OUTPUT
    try:
        raw_artifact = _read_bounded_regular_file_v1(
            source, ARTIFACT_MAX_BYTES_V1, "requirements artifact"
        )
        snapshot = load_source_snapshot_v1(root)
    except (ShellRejectV1, RequirementsRejectV1) as exc:
        return _shell_failure_report_v1(exc)
    return check_requirements_registry_v1(raw_artifact, snapshot).to_json()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    args = parser.parse_args(argv)
    report = check_m6_normative_requirements_v1(args.root)
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())

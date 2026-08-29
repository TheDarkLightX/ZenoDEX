#!/usr/bin/env python3
"""Fail closed when O005 semantic-resolution evidence drifts or promotes."""

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
    from tools.build_m6_o005_semantic_resolutions_v1 import (
        JSON_OUTPUT,
        REPO_ROOT,
        load_o005_source_bytes_v1,
    )
    from tools.m6_o005_semantic_resolutions_v1 import (
        CHECK_SCHEMA_V1,
        MAX_ARTIFACT_BYTES_V1,
        SemanticResolutionRejectV1,
        check_semantic_resolution_artifact_v1,
    )
except ModuleNotFoundError:
    from build_m6_normative_requirements_v1 import (  # type: ignore[no-redef]
        ShellRejectV1,
        _read_bounded_regular_file_v1,
        _require_inert_path_v1,
    )
    from build_m6_o005_semantic_resolutions_v1 import (  # type: ignore[no-redef]
        JSON_OUTPUT,
        REPO_ROOT,
        load_o005_source_bytes_v1,
    )
    from m6_o005_semantic_resolutions_v1 import (  # type: ignore[no-redef]
        CHECK_SCHEMA_V1,
        MAX_ARTIFACT_BYTES_V1,
        SemanticResolutionRejectV1,
        check_semantic_resolution_artifact_v1,
    )


def _failure_report_v1(exc: SemanticResolutionRejectV1 | ShellRejectV1) -> dict[str, object]:
    return {
        "artifact_sha256": "",
        "closed_value_movement_gates": 0,
        "expected_artifact_sha256": "",
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
        "source_resolution_bijection_verified": False,
        "structural_mapping_complete": False,
        "value_movement_claim_allowed": False,
        "vm_ledger_closed_gate_count": 0,
    }


def check_m6_o005_semantic_resolutions_v1(
    root: Path | str = REPO_ROOT,
    artifact_path: Path | str | None = None,
) -> dict[str, object]:
    """Read immutable bytes once and delegate registry checks to the pure core."""

    try:
        inert_root = _require_inert_path_v1(root, "O005 checker root")
        path = (
            inert_root / JSON_OUTPUT
            if artifact_path is None
            else _require_inert_path_v1(artifact_path, "O005 checker artifact")
        )
        raw = _read_bounded_regular_file_v1(
            path,
            MAX_ARTIFACT_BYTES_V1,
            "O005 semantic-resolution artifact",
        )
        source_raw = load_o005_source_bytes_v1(inert_root)
    except (SemanticResolutionRejectV1, ShellRejectV1) as exc:
        return _failure_report_v1(exc)
    return check_semantic_resolution_artifact_v1(raw, source_raw)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    args = parser.parse_args(argv)
    report = check_m6_o005_semantic_resolutions_v1(args.root)
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())

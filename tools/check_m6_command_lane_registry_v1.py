#!/usr/bin/env python3
"""Fail closed when the research-only M6 command-to-lane registry drifts."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.core.m6_command_lane_registry_v1 import (  # noqa: E402
    CHECK_SCHEMA_V1,
    CommandLaneRegistryRejectV1,
    check_registry_artifact_v1,
)
from tools.build_m6_command_lane_registry_v1 import (  # noqa: E402
    JSON_OUTPUT,
    MAX_INPUT_BYTES_V1,
    load_source_snapshot_v1,
)
from tools.build_m6_normative_requirements_v1 import (  # noqa: E402
    ShellRejectV1,
    _read_bounded_regular_file_v1,
)
from tools.m6_normative_requirements_v1 import (  # noqa: E402
    RequirementsRejectV1,
    canonical_json_bytes_v1,
    decode_json_object_v1,
)


def _failure_report(code: str, detail: str) -> dict[str, object]:
    return {
        "artifact_sha256": "",
        "findings": [{"code": code, "detail": detail, "path": "checker"}],
        "ok": False,
        "mounted": False,
        "production_authority": "NONE",
        "registered_command_mapping_complete": False,
        "registry_root": None,
        "release_backed": False,
        "requirements_target_coverage_complete": False,
        "schema": CHECK_SCHEMA_V1,
        "semantic_launch_alignment_complete": False,
        "settlement_authority": "NONE",
        "value_movement_claim_allowed": False,
        "whole_economy_command_vocabulary_complete": False,
    }


def check_m6_command_lane_registry_v1(
    root: Path = REPO_ROOT,
    artifact_path: Path | None = None,
) -> dict[str, object]:
    """Read one bounded artifact then compare it to the pure source-bound projection."""

    source = artifact_path or root / JSON_OUTPUT
    try:
        raw_artifact = _read_bounded_regular_file_v1(
            source, MAX_INPUT_BYTES_V1, "registry artifact"
        )
        artifact = decode_json_object_v1(raw_artifact, "registry artifact")
        if canonical_json_bytes_v1(artifact) != raw_artifact:
            return _failure_report("NONCANONICAL_ARTIFACT", "artifact bytes are not canonical JSON")
        snapshot = load_source_snapshot_v1(root)
        if snapshot.captured_head != snapshot.rechecked_head:
            return _failure_report(
                "HEAD_CHANGED_DURING_CAPTURE", "Git HEAD changed during checker capture"
            )
    except (CommandLaneRegistryRejectV1, RequirementsRejectV1, ShellRejectV1) as exc:
        return _failure_report(exc.code, exc.detail)
    except (MemoryError, OSError, RecursionError, TypeError, ValueError) as exc:
        return _failure_report("CHECKER_INPUT_ERROR", type(exc).__name__)
    return check_registry_artifact_v1(artifact, raw_artifact, snapshot).to_json()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    args = parser.parse_args(argv)
    report = check_m6_command_lane_registry_v1(args.root)
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())

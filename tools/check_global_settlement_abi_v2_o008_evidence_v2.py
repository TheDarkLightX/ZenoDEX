#!/usr/bin/env python3
"""Fail-closed checker for a future explicit-subject O-008 V2 artifact."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.global_settlement_abi_v2_o008_evidence_v2 import (
    STATUS_V2,
    EvidenceV2Error,
    build_evidence_v2,
    canonical_json_bytes_v2,
    current_path_sha256_v2,
    decode_json_object_v2,
    resolve_repo_root_v2,
)


def check_evidence_v2(path: Path, *, root: Path, stage_a_commit: str) -> dict[str, Any]:
    """Check exact generated content and separately report current applicability."""

    errors: list[str] = []
    expected: dict[str, object] = {}
    try:
        raw = path.read_bytes()
        decode_json_object_v2(
            raw, context=str(path), require_canonical=True
        )
        expected = build_evidence_v2(root, stage_a_commit)
        if raw != canonical_json_bytes_v2(expected):
            errors.append("artifact differs from exact source extraction")
    except (EvidenceV2Error, OSError) as exc:
        errors.append(f"artifact/source validation failed: {type(exc).__name__}: {exc}")
    current_drift: list[str] = []
    if not errors:
        resolved_root = resolve_repo_root_v2(root)
        pins: dict[str, str] = {}
        source_manifest = expected.get("source_manifest")
        historical = expected.get("historical_v1_preservation")
        dependencies = expected.get("historical_stage_a_dependencies")
        active_plan = expected.get("active_plan")
        if type(source_manifest) is not list or type(historical) is not dict:
            errors.append("generated evidence has malformed source manifests")
        elif type(dependencies) is not dict or type(active_plan) is not dict:
            errors.append("generated evidence has malformed binding manifests")
        else:
            for row in source_manifest:
                if type(row) is not dict:
                    errors.append("malformed source manifest row")
                    break
                row_path = row.get("path")
                digest = row.get("sha256")
                if type(row_path) is not str or type(digest) is not str:
                    errors.append("malformed source manifest pin")
                    break
                pins[row_path] = digest
            for path_text, pinned in historical.items():
                if type(path_text) is not str or type(pinned) is not dict:
                    errors.append("malformed historical pin")
                    break
                digest = pinned.get("sha256")
                if type(digest) is not str:
                    errors.append("malformed historical digest")
                    break
                pins[path_text] = digest
            for binding in active_plan.values():
                if type(binding) is not dict:
                    errors.append("malformed active-plan binding")
                    break
                binding_path = binding.get("path")
                digest = binding.get("sha256")
                if type(binding_path) is not str or type(digest) is not str:
                    errors.append("malformed active-plan pin")
                    break
                pins[binding_path] = digest
        if not errors:
            checked_paths = expected.get("checked_paths")
            current_paths = expected.get("current_applicability_paths")
            if (
                type(checked_paths) is not list
                or type(current_paths) is not list
                or current_paths != sorted(pins)
                or any(type(item) is not str for item in checked_paths)
                or any(type(item) is not str for item in current_paths)
                or not set(current_paths).issubset(checked_paths)
            ):
                errors.append("checker checked-path closure drift")
            else:
                for path_text in current_paths:
                    if current_path_sha256_v2(resolved_root, path_text) != pins[path_text]:
                        current_drift.append(path_text)
    historical_valid = not errors
    return {
        "ok": historical_valid,
        "historical_valid": historical_valid,
        "status": STATUS_V2 if historical_valid else "INVALID_FAIL_CLOSED",
        "stage_a_commit": stage_a_commit,
        "release_ready": False,
        "authority": "NONE",
        "closed_value_movement_gates": 0,
        "required_value_movement_gates": 12,
        "current_applicable": historical_valid and not current_drift,
        "current_source_drift": sorted(current_drift),
        "errors": errors,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifact", type=Path)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--stage-a-commit", required=True)
    args = parser.parse_args(argv)
    report = check_evidence_v2(args.artifact, root=args.root, stage_a_commit=args.stage_a_commit)
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

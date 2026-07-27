#!/usr/bin/env python3
"""Fail-closed checker for canonical M5-P4B0 refinement evidence."""

# ruff: noqa: E402 -- executable tools must add the repository root before src imports

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import cast

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from src.core.fcis_legacy_refinement_admission import decode_canonical_json_bytes_v1
from src.core.fcis_legacy_refinement_values import CanonicalParseRejectV1
from src.state.canonical import canonical_json_bytes, sha256_hex
from tools.build_fcis_m5_p4b0_refinement import ARTIFACT_PATH_V1, artifact_bytes_v1

CHECK_SCHEMA_V1 = "zenodex/fcis-m5-p4b0-refinement-check/v1"


def _report(ok: bool, code: str, verdict: str = "INVALID") -> dict[str, object]:
    return {
        "code": code,
        "mount_authorized": False,
        "ok": ok,
        "schema": CHECK_SCHEMA_V1,
        "verdict": verdict,
    }


def check_artifact_v1(
    repo_root: Path,
    artifact_path: Path,
    *,
    require_all_refine: bool,
) -> tuple[int, dict[str, object]]:
    if not artifact_path.exists():
        return 1, _report(False, "artifact_missing")
    raw = artifact_path.read_bytes()
    decoded = decode_canonical_json_bytes_v1(raw)
    if type(decoded) is CanonicalParseRejectV1:
        return 1, _report(False, f"artifact_parse_{decoded.code.value}")
    if type(decoded) is not dict:
        return 1, _report(False, "artifact_wrong_root_type")
    artifact = cast(dict[str, object], decoded)
    stored_hash = artifact.get("artifact_sha256")
    payload = {key: value for key, value in artifact.items() if key != "artifact_sha256"}
    if stored_hash != sha256_hex(canonical_json_bytes(payload)):
        return 1, _report(False, "artifact_hash_mismatch")
    try:
        expected = artifact_bytes_v1(repo_root)
    except (KeyError, OSError, TypeError, ValueError) as error:
        return 1, _report(False, f"semantic_rebuild_failed:{type(error).__name__}")
    if raw != expected:
        return 1, _report(False, "semantic_rebuild_mismatch")
    counts_value = artifact.get("result_counts")
    if type(counts_value) is not dict:
        return 1, _report(False, "result_counts_invalid")
    counts = cast(dict[str, object], counts_value)
    mismatches = counts.get("mismatch")
    invalid = counts.get("invalid_evidence")
    if type(mismatches) is not int or type(invalid) is not int:
        return 1, _report(False, "result_counts_invalid")
    if invalid != 0:
        return 1, _report(False, "invalid_evidence_present")
    verdict = cast(str, artifact.get("verdict"))
    if require_all_refine and mismatches != 0:
        return 2, _report(False, "mismatches_block_promotion", verdict)
    return 0, _report(True, "artifact_valid", verdict)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path)
    parser.add_argument("--require-all-refine", action="store_true")
    args = parser.parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    artifact_path = args.artifact or (repo_root / ARTIFACT_PATH_V1)
    status, report = check_artifact_v1(
        repo_root,
        artifact_path,
        require_all_refine=args.require_all_refine,
    )
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return status


if __name__ == "__main__":
    raise SystemExit(main())

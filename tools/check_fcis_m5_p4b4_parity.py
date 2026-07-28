#!/usr/bin/env python3
"""Fail-closed semantic checker for FCIS M5-P4B4 parity evidence."""

# ruff: noqa: E402 -- executable tools add the repository root before imports

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import cast

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from src.state.canonical import canonical_json_bytes, sha256_hex
from tools.build_fcis_m5_p4b4_parity import ARTIFACT_PATH_V1, artifact_bytes_v1

CHECK_SCHEMA_V1 = "zenodex/fcis-m5-p4b4-direct-parity-check/v1"


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
) -> tuple[int, dict[str, object]]:
    if not artifact_path.exists():
        return 1, _report(False, "artifact_missing")
    raw = artifact_path.read_bytes()
    try:
        decoded = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError):
        return 1, _report(False, "artifact_parse_failed")
    if type(decoded) is not dict:
        return 1, _report(False, "artifact_wrong_root_type")
    artifact = cast(dict[str, object], decoded)
    if raw != canonical_json_bytes(artifact) + b"\n":
        return 1, _report(False, "artifact_not_canonical")
    stored_hash = artifact.get("artifact_sha256")
    payload = {key: value for key, value in artifact.items() if key != "artifact_sha256"}
    if stored_hash != sha256_hex(canonical_json_bytes(payload)):
        return 1, _report(False, "artifact_hash_mismatch")
    try:
        expected = artifact_bytes_v1(repo_root)
    except (KeyError, OSError, subprocess.SubprocessError, TypeError, ValueError):
        return 1, _report(False, "semantic_rebuild_failed")
    if raw != expected:
        return 1, _report(False, "semantic_rebuild_mismatch")
    counts = artifact.get("result_counts")
    if type(counts) is not dict:
        return 1, _report(False, "result_counts_invalid")
    exact_counts = cast(dict[str, object], counts)
    if exact_counts.get("mismatch") != 0:
        return 2, _report(False, "parity_mismatch", cast(str, artifact.get("verdict")))
    return 0, _report(True, "artifact_valid", cast(str, artifact.get("verdict")))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path)
    args = parser.parse_args()
    artifact_path = args.artifact or (_REPO_ROOT / ARTIFACT_PATH_V1)
    status, report = check_artifact_v1(_REPO_ROOT, artifact_path)
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return status


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Check the quarantine status of the historical M6 ATDD contract.

The preserved 18-workflow/81-scenario contract is useful historical research
context.  This checker records why it cannot serve as exact-subject G1
evidence and keeps that distinction machine-readable.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
LEGACY_CONTRACT = REPO_ROOT / "docs/research/m6_global_economic_core_atdd_bdd_v1.json"
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_LEGACY_ATDD_QUARANTINE_V1.json"
SCHEMA = "zenodex/production-readiness-g1-legacy-atdd-quarantine/v1"

sys.path.insert(0, str(REPO_ROOT))
from tools import check_m6_global_economic_core_atdd_v1 as legacy  # noqa: E402
from tools import check_production_readiness_g1_semantics as semantics  # noqa: E402


def _load(path: Path) -> dict[str, Any]:
    duplicates: list[str] = []

    def hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                duplicates.append(key)
            result[key] = value
        return result

    with path.open(encoding="utf-8") as stream:
        value = json.load(stream, object_pairs_hook=hook)
    if duplicates:
        raise ValueError(f"duplicate JSON keys: {sorted(set(duplicates))}")
    if not isinstance(value, dict):
        raise ValueError("artifact root must be an object")
    return value


def _encoded(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _write_atomic(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(_encoded(value))
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def _is_ancestor(commit: Any, repo_root: Path) -> bool:
    if not isinstance(commit, str) or len(commit) != 40:
        return False
    result = subprocess.run(
        ["git", "merge-base", "--is-ancestor", commit, "HEAD"],
        cwd=repo_root,
        check=False,
    )
    return result.returncode == 0


def _head_matches(commit: Any, repo_root: Path) -> bool:
    if not isinstance(commit, str):
        return False
    result = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"],
        cwd=repo_root,
        check=False,
        capture_output=True,
        text=True,
    )
    return result.returncode == 0 and result.stdout.strip() == commit


def _count_errors(errors: Sequence[str], marker: str) -> int:
    return sum(marker in error for error in errors)


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    contract = legacy.load_contract(LEGACY_CONTRACT)
    validation = legacy.validate_contract(contract, repo_root)
    semantic = semantics.build_document(repo_root)
    errors = validation["errors"]
    base_commit = contract.get("base_commit")
    base_head_mismatch = _count_errors(errors, "base_commit must equal current repository HEAD")
    source_pin_mismatches = _count_errors(errors, "sha256 mismatch")
    other_errors = len(errors) - base_head_mismatch - source_pin_mismatches
    reasons = [
        "HISTORICAL_BASE_COMMIT_NOT_CURRENT_HEAD",
        "LEGACY_SOURCE_PINS_DRIFTED",
    ]
    if other_errors:
        reasons.append("LEGACY_STRUCTURAL_VALIDATION_ERRORS")
    return {
        "schema": SCHEMA,
        "version": "v1",
        "status": "LEGACY_ATDD_QUARANTINED_RESEARCH_ONLY",
        "production_promotion": False,
        "source_subject": semantic["source_subject"],
        "source_pins": semantic["source_pins"],
        "legacy_contract": {
            "path": "docs/research/m6_global_economic_core_atdd_bdd_v1.json",
            "schema": validation["contract_schema"],
            "status": validation["contract_status"],
            "base_commit": base_commit,
            "base_commit_is_ancestor_of_current_head": _is_ancestor(base_commit, repo_root),
            "base_commit_matches_current_head": _head_matches(base_commit, repo_root),
            "validation_ok": validation["ok"],
            "validation_error_count": len(errors),
            "source_pin_count": validation["source_pin_count"],
            "workflow_count": validation["workflow_count"],
            "scenario_count": validation["scenario_count"],
        },
        "quarantine": {
            "quarantined": True,
            "reasons": reasons,
            "base_head_mismatch_count": base_head_mismatch,
            "source_pin_mismatch_count": source_pin_mismatches,
            "other_validation_error_count": other_errors,
            "production_authority": "NONE",
            "usable_as_exact_subject_g1_evidence": False,
        },
        "exit_gate": {
            "complete": False,
            "status": "LEGACY_ATDD_NOT_EXACT_SUBJECT",
            "production_authority": "NONE",
        },
        "nonclaims": [
            "The historical contract remains preserved research context and is not repinned here.",
            "Quarantine does not prove, implement, mount, or authorize any command.",
            "The legacy ATDD command must continue to fail closed until a separately reviewed exact-subject contract exists.",
            "The current G1 source binding does not promote the historical 18-workflow contract.",
        ],
    }


def check_artifact(path: Path, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    observed: dict[str, Any] = {}
    ancestry = subprocess.run(
        ["git", "merge-base", "--is-ancestor", semantics.SOURCE_SUBJECT, "HEAD"],
        cwd=repo_root,
        check=False,
    )
    if ancestry.returncode != 0:
        errors.append("current HEAD does not descend from the frozen G1 source subject")
    try:
        expected = build_document(repo_root)
        observed = _load(path)
        if observed != expected:
            errors.append("artifact differs from the exact-subject generated ATDD quarantine")
    except (OSError, ValueError, KeyError, TypeError, legacy.ContractError) as exc:
        errors.append(str(exc))

    legacy_contract = observed.get("legacy_contract")
    quarantine = observed.get("quarantine")
    return {
        "schema": "zenodex/production-readiness-g1-legacy-atdd-quarantine-check/v1",
        "ok": not errors,
        "quarantined": quarantine.get("quarantined") is True if isinstance(quarantine, Mapping) else False,
        "legacy_validation_ok": legacy_contract.get("validation_ok") if isinstance(legacy_contract, Mapping) else False,
        "validation_error_count": legacy_contract.get("validation_error_count", 0)
        if isinstance(legacy_contract, Mapping)
        else 0,
        "source_pin_mismatch_count": quarantine.get("source_pin_mismatch_count", 0)
        if isinstance(quarantine, Mapping)
        else 0,
        "g1_complete": False,
        "production_ready": False,
        "production_authority": "NONE",
        "errors": errors,
        "nonclaim": "PASS means only that the historical ATDD quarantine is exact and source-bound; it does not promote G1 or production readiness.",
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    if args.write:
        _write_atomic(args.output, build_document(args.repo_root))
    report = check_artifact(args.output, args.repo_root)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("PASS" if report["ok"] else "FAIL")
        for error in report["errors"]:
            print(f"error: {error}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

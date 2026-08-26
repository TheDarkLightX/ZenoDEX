#!/usr/bin/env python3
"""Fail closed when the active whole-program plan loses scope or semantics."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path
from typing import Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PLAN = Path("docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json")
CAPABILITY_MANIFEST = Path("docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json")
SCHEMA = "zenodex/whole-program-plan/v2"
EXPECTED_VM_GATES = tuple(f"VM-{index:02d}" for index in range(1, 13))
EXPECTED_OBLIGATIONS = tuple(f"O-{index:03d}" for index in range(1, 11))
EXPECTED_POLICIES = tuple(f"UP-{index:02d}" for index in range(1, 21))
EXPECTED_TAU_COMMIT = "0b038824c8583a1a902ef54369d3d0ecf3384cf5"
EXPECTED_PROOF_SHAPE = {
    "module_receipts_per_route_min": 1,
    "module_receipts_per_route_max": 8,
    "commands_per_epoch_min": 1,
    "commands_per_epoch_max": 64,
    "module_leaf_occurrences_per_epoch_max": 64,
    "aggregation_fanout": 8,
    "command_aggregation_levels_max": 2,
    "required_rejections": [
        "zero_route_receipts",
        "nine_route_receipts",
        "zero_epoch_commands",
        "sixty_five_epoch_commands",
        "journal_byte_excess",
        "cycle_budget_excess",
    ],
}
FORBIDDEN_PLAN_TEXT = (
    "/tmp/",
    "/home/",
    "M6PromotionSubjectV2",
    "GlobalCommandV2",
    "GlobalEconomicStateV2",
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")


def _without_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _load_object(path: Path) -> Mapping[str, object]:
    value = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_without_duplicate_keys,
    )
    if type(value) is not dict:
        raise TypeError(f"{path.name} root must be an object")
    return value


def _exact_ids(rows: object, field: str) -> tuple[object, ...]:
    if type(rows) is not list or any(type(row) is not dict for row in rows):
        return ()
    return tuple(row.get(field) for row in rows)


def _safe_repo_path(root: Path, raw: object) -> Path | None:
    if type(raw) is not str or not raw or Path(raw).is_absolute() or ".." in Path(raw).parts:
        return None
    candidate = (root / raw).resolve()
    try:
        candidate.relative_to(root.resolve())
    except ValueError:
        return None
    return candidate


def _git_tree_for_commit(root: Path, commit: str) -> str | None:
    env = {
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "PATH": os.environ.get("PATH", ""),
    }
    try:
        completed = subprocess.run(
            [
                "git",
                "-c",
                "core.hooksPath=/dev/null",
                "-C",
                str(root),
                "rev-parse",
                "--verify",
                f"{commit}^{{tree}}",
            ],
            check=False,
            capture_output=True,
            env=env,
            text=True,
            timeout=5,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if completed.returncode != 0:
        return None
    tree = completed.stdout.strip()
    return tree if _COMMIT_RE.fullmatch(tree) else None


def check_whole_program_plan_v2(
    root: Path = REPO_ROOT,
    plan_path: Path | None = None,
) -> dict[str, object]:
    findings: list[str] = []
    source = plan_path or root / DEFAULT_PLAN
    try:
        plan = _load_object(source)
        capability_manifest = _load_object(root / CAPABILITY_MANIFEST)
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        return {
            "schema": "zenodex/whole-program-plan-check/v2",
            "ok": False,
            "production_authority": "NONE",
            "findings": [f"plan inputs cannot be loaded: {type(exc).__name__}: {exc}"],
        }

    if plan.get("schema") != SCHEMA:
        findings.append("whole-program plan schema mismatch")
    if plan.get("status") != "RESEARCH_ONLY_ACTIVE_IMPLEMENTATION_PLAN":
        findings.append("plan status must remain research-only")

    authority = plan.get("authority")
    expected_authority = {
        "production_authority": "NONE",
        "settlement_authority": "NONE",
        "release_ready": False,
        "production_ready": False,
    }
    if authority != expected_authority:
        findings.append("authority ceiling drift")

    subject = plan.get("subject")
    subject_tree_verified = False
    if type(subject) is not dict:
        findings.append("subject must be an object")
    else:
        base_commit = subject.get("implementation_base_commit")
        base_tree = subject.get("implementation_base_tree")
        if type(base_commit) is not str or not _COMMIT_RE.fullmatch(base_commit):
            findings.append("implementation base commit must be exact lowercase SHA-1")
        if type(base_tree) is not str or not _COMMIT_RE.fullmatch(base_tree):
            findings.append("implementation base tree must be exact lowercase SHA-1")
        if type(base_commit) is str and _COMMIT_RE.fullmatch(base_commit):
            observed_tree = _git_tree_for_commit(root, base_commit)
            if observed_tree is None or observed_tree != base_tree:
                findings.append("implementation base commit and tree do not match Git objects")
            else:
                subject_tree_verified = True
        binding = subject.get("plan_commit_binding")
        if type(binding) is not str or "self-referential" not in binding:
            findings.append("plan must state its non-self-referential commit binding")

    normative_inputs = plan.get("normative_inputs")
    expected_normative_paths = (
        "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json",
        "docs/research/ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md",
        "docs/research/ZENODEX_M6_ASSET_PRECISION_POLICY_V1.json",
    )
    if _exact_ids(normative_inputs, "path") != expected_normative_paths:
        findings.append("normative input set or order drift")
    if type(normative_inputs) is list:
        for row in normative_inputs:
            if type(row) is not dict:
                continue
            path = _safe_repo_path(root, row.get("path"))
            expected_hash = row.get("sha256")
            if path is None or type(expected_hash) is not str or not _SHA256_RE.fullmatch(expected_hash):
                findings.append("normative input path or SHA-256 is invalid")
                continue
            try:
                actual_hash = hashlib.sha256(path.read_bytes()).hexdigest()
            except OSError as exc:
                findings.append(f"normative input unreadable: {path.name}: {type(exc).__name__}")
                continue
            if actual_hash != expected_hash:
                findings.append(f"normative input hash drift: {path.relative_to(root)}")

    architecture = plan.get("selected_architecture")
    if type(architecture) is not dict:
        findings.append("selected architecture must be an object")
    else:
        if architecture.get("settlement_abi") != "GlobalSettlementABI V1":
            findings.append("GlobalSettlementABI V1 selection drift")
        manifest_lanes = capability_manifest.get("lanes")
        expected_lanes = _exact_ids(manifest_lanes, "lane_id")
        observed_lanes = architecture.get("closed_lane_registry")
        if type(observed_lanes) is not list or tuple(observed_lanes) != expected_lanes:
            findings.append("closed lane registry does not match the capability manifest")
        if architecture.get("initial_recursive_qualification") != EXPECTED_PROOF_SHAPE:
            findings.append("initial recursive qualification shape drift")

    upstream = plan.get("upstream_dependencies")
    if type(upstream) is not list or len(upstream) != 1 or type(upstream[0]) is not dict:
        findings.append("current Tau dependency pin must be one exact row")
    elif upstream[0].get("observed_commit") != EXPECTED_TAU_COMMIT:
        findings.append("current Tau dependency commit drift")

    if _exact_ids(plan.get("value_movement_gates"), "gate_id") != EXPECTED_VM_GATES:
        findings.append("value-movement gate set or order drift")
    if _exact_ids(plan.get("next_obligations"), "obligation_id") != EXPECTED_OBLIGATIONS:
        findings.append("next-obligation set or order drift")
    if _exact_ids(plan.get("unresolved_semantic_decisions"), "decision_id") != EXPECTED_POLICIES:
        findings.append("unresolved semantic-decision set or order drift")

    verdict = plan.get("baseline_verdict")
    if type(verdict) is not dict or verdict.get("closed_value_movement_gates") != 0:
        findings.append("baseline verdict must not claim a closed value-movement gate")
    if type(verdict) is not dict or verdict.get("value_movement_gate_count") != 12:
        findings.append("value-movement gate count drift")

    serialized = json.dumps(plan, sort_keys=True, separators=(",", ":"))
    for forbidden in FORBIDDEN_PLAN_TEXT:
        if forbidden in serialized:
            findings.append(f"forbidden plan text present: {forbidden}")

    capability_count = 0
    manifest_lanes = capability_manifest.get("lanes")
    if type(manifest_lanes) is list:
        for row in manifest_lanes:
            if type(row) is not dict:
                continue
            capabilities = row.get("capabilities")
            if type(capabilities) is list:
                capability_count += len(capabilities)

    return {
        "schema": "zenodex/whole-program-plan-check/v2",
        "ok": not findings,
        "production_authority": "NONE",
        "release_ready": False,
        "subject_tree_verified": subject_tree_verified,
        "capability_count": capability_count,
        "value_movement_gate_count": 12,
        "closed_value_movement_gate_count": 0,
        "findings": findings,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--plan", type=Path)
    args = parser.parse_args(argv)
    report = check_whole_program_plan_v2(args.root, args.plan)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

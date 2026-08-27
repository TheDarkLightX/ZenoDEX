#!/usr/bin/env python3
"""Verify exact research-plan admission without granting economic authority."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Final, Mapping

try:
    from tools.build_m6_normative_requirements_v1 import (
        ShellRejectV1,
        _read_bounded_regular_file_v1,
        _run_git_v1,
    )
except ModuleNotFoundError:
    from build_m6_normative_requirements_v1 import (
        ShellRejectV1,
        _read_bounded_regular_file_v1,
        _run_git_v1,
    )

try:
    from tools.m6_normative_requirements_v1 import (
        RequirementsRejectV1,
        canonical_json_bytes_v1,
        decode_json_object_v1,
    )
except ModuleNotFoundError:
    from m6_normative_requirements_v1 import (
        RequirementsRejectV1,
        canonical_json_bytes_v1,
        decode_json_object_v1,
    )

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RECEIPT = Path("docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json")
DEFAULT_REGISTRY = Path("docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json")
RECEIPT_SCHEMA = "zenodex/plan-admission-receipt/v1"
REGISTRY_SCHEMA = "zenodex/active-whole-program-plan-registry/v1"
PLAN_SCHEMA = "zenodex/whole-program-plan/v2.1"
PLAN_STATUS = "RESEARCH_ONLY_CANDIDATE_PENDING_ADMISSION"
PLAN_COMMIT = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
PLAN_PARENT = "87048abf3bed2adba0e316e4f9c2ea93f438aeb6"
PLAN_TREE = "7978c0df78428e806e5f19281df537fe1cfc7451"
PLAN_PATH = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
PLAN_SHA256 = "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f"
MAX_ADMISSION_INPUT_BYTES_V1: Final = 65_536
EXPECTED_AUTHORITY = {
    "production_authority": "NONE",
    "settlement_authority": "NONE",
    "release_authority": "NONE",
    "value_movement_authority": "NONE",
}
EXPECTED_NORMATIVE_INPUTS = (
    (
        "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json",
        "34930be9d4d69c4c46c7c97f57fd492d4c95061f8960f936261a8a3415d5db95",
    ),
    (
        "docs/research/ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md",
        "32985ee88b0b15a0b6ef1408e60ac1767f93e20eade434090011e144ecd56990",
    ),
    (
        "docs/research/ZENODEX_M6_ASSET_PRECISION_POLICY_V1.json",
        "d1427502b4a6eea32fdc0895b9f872d13eea6dc9670cec2a117dcb9d96fdb815",
    ),
)
UPSTREAM_DEPENDENCIES_SHA256 = "a1bccbf7e07520e9ad990ed904cb602b519e7a35310d3a75d2815b2545e6adb9"
EXPECTED_UPSTREAM_DEPENDENCY_BINDING = {
    "plan_field_sha256": UPSTREAM_DEPENDENCIES_SHA256,
    "dependency_count": 2,
    "evidence_class": "DECLARATIONS_FROM_ADMITTED_PLAN_NOT_REPLAYED_BY_THIS_CHECKER",
    "authority": "NONE",
}
EXPECTED_SELECTION_PREMISE = {
    "classification": "EXTERNAL_USER_DIRECTIVE_NOT_MACHINE_VERIFIED",
    "selected_plan_commit": PLAN_COMMIT,
    "scope": "RESEARCH_IMPLEMENTATION_COORDINATION_ONLY",
    "authority": "NONE",
}
REVIEW_COMMIT = "87048abf3bed2adba0e316e4f9c2ea93f438aeb6"
REVIEW_BLOB = "638d1ed55d70ad410f86fa52dc4e5bb9b7980364"
REVIEW_PATH = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2_1_FABLE_ADVISORY_REVIEW.md"
REVIEW_SHA256 = "a901dde42ab21685fdc76f910ab05f37219da033e1dfceee8783a65128832678"
RAW_REVIEW_SHA256 = "6093fbaa06371bcf36d88825863055e9b35a5b1de583418ee70f62bcb58435fa"
EXPECTED_ADVISORY_REVIEW = {
    "reviewer_class": "FABLE_5_HIGH",
    "artifact_commit": REVIEW_COMMIT,
    "artifact_blob": REVIEW_BLOB,
    "artifact_path": REVIEW_PATH,
    "artifact_sha256": REVIEW_SHA256,
    "raw_report_sha256": RAW_REVIEW_SHA256,
    "verdict": "REVISE_CORRECTIONS_RECORDED",
    "authority": "NONE",
    "evidence_class": "HASH_BOUND_ADVISORY_ARTIFACT",
}
EXPECTED_ADMISSION_SCOPE = (
    "The exact plan commit becomes the active research-only implementation plan. "
    "It may order work and evidence obligations. It cannot authorize settlement, "
    "value movement, release, migration, or production claims."
)
EXPECTED_NONCLAIMS = [
    "This receipt is not a proof of architectural soundness.",
    "This receipt does not close any value-movement gate or capability row.",
    "The user-selection premise is external and not machine verified.",
    (
        "The upstream Tau dependencies and raw advisory report are referenced by "
        "admitted artifacts and are not independently replayed by this checker."
    ),
    (
        "This receipt grants no production, settlement, release, migration, or "
        "value-moving authority."
    ),
]
EXPECTED_REPLACEMENT_RULE = (
    "A successor registry must bind one exact reviewed plan commit and its valid "
    "admission receipt. Concurrent active plans reject."
)
EXPECTED_REGISTRY_NONCLAIM = "Active means selected for research implementation coordination only."
EXPECTED_PLAN_ADMISSION_MODEL = {
    "human_selection": "EXTERNAL_USER_DIRECTIVE_REQUIRED_NOT_MACHINE_VERIFIED",
    "llm_review": "ADVISORY_HASHED_ARTIFACT_ONLY",
    "deterministic_evidence": "REPLAYED_BY_ADMISSION_CHECKER",
    "authority_effect": "NONE",
}
EXPECTED_PLAN_ADVISORY_REVIEWS = [
    {
        "reviewer": "FABLE_5_HIGH",
        "artifact_path": REVIEW_PATH,
        "external_raw_report_sha256": RAW_REVIEW_SHA256,
        "verdict": "REVISE_V2_CORRECTIONS_APPLIED_TO_V2_1",
        "authority": "ADVISORY_NONE",
    }
]
EXPECTED_RECEIPT_KEYS = {
    "schema",
    "status",
    "admitted_plan",
    "subject_files",
    "normative_inputs",
    "upstream_dependency_binding",
    "selection_premise",
    "advisory_review",
    "authority",
    "admission_scope",
    "nonclaims",
    "receipt_payload_sha256",
}
EXPECTED_REGISTRY_KEYS = {
    "schema",
    "status",
    "active_plan_count",
    "active_plans",
    "authority",
    "replacement_rule",
    "nonclaim",
}
EXPECTED_SUBJECT_FILES = (
    ("docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json", PLAN_SHA256),
    (
        "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.md",
        "da42739f085b3344d4a1240ea0a77fa91b9def05c5c6a530dad7d789d2e920f6",
    ),
    (
        "tests/test_check_whole_program_plan_v2.py",
        "f58daad9829e7c6843c7a34caf010fdfd57f18e5f6ee0c21c6acf35726f3f695",
    ),
    (
        "tools/check_whole_program_plan_v2.py",
        "468790671f6bc1e9bfe9925ffd03844bc35d47f98e0a9a9cdb18783f169f6a4d",
    ),
)
_SHA1_RE = re.compile(r"^[0-9a-f]{40}$")


def _load_object(path: Path, *, role: str) -> Mapping[str, object]:
    raw = _read_bounded_regular_file_v1(path, MAX_ADMISSION_INPUT_BYTES_V1, role)
    return decode_json_object_v1(raw, role)


def _git(root: Path, args: list[str]) -> bytes | None:
    try:
        _, stdout, _ = _run_git_v1(root, tuple(args))
    except ShellRejectV1:
        return None
    return stdout.encode("utf-8")


def _canonical_payload_hash(receipt: Mapping[str, object]) -> str:
    payload = dict(receipt)
    payload.pop("receipt_payload_sha256", None)
    return hashlib.sha256(canonical_json_bytes_v1(payload)).hexdigest()


def _changed_file_pairs(value: object) -> tuple[tuple[object, object], ...]:
    if type(value) is not list or any(type(row) is not dict for row in value):
        return ()
    return tuple((row.get("path"), row.get("sha256")) for row in value)


def _exact_file_rows(
    pairs: tuple[tuple[str, str], ...],
) -> list[dict[str, str]]:
    return [{"path": path, "sha256": digest} for path, digest in pairs]


def check_whole_program_plan_admission_v1(
    root: Path = REPO_ROOT,
    receipt_path: Path | None = None,
    registry_path: Path | None = None,
) -> dict[str, object]:
    findings: list[str] = []
    try:
        receipt = _load_object(
            receipt_path or root / DEFAULT_RECEIPT,
            role="admission receipt",
        )
        registry = _load_object(
            registry_path or root / DEFAULT_REGISTRY,
            role="active-plan registry",
        )
    except (ShellRejectV1, RequirementsRejectV1) as exc:
        return {
            "schema": "zenodex/plan-admission-check/v1",
            "ok": False,
            "active_research_plan_count": 0,
            "production_authority": "NONE",
            "findings": [f"admission inputs cannot be loaded: {exc.code}"],
        }
    except (MemoryError, OSError, RecursionError, TypeError, ValueError) as exc:
        return {
            "schema": "zenodex/plan-admission-check/v1",
            "ok": False,
            "active_research_plan_count": 0,
            "production_authority": "NONE",
            "findings": [f"admission inputs cannot be loaded: {type(exc).__name__}: {exc}"],
        }

    if receipt.get("schema") != RECEIPT_SCHEMA:
        findings.append("admission receipt schema mismatch")
    if set(receipt) != EXPECTED_RECEIPT_KEYS:
        findings.append("admission receipt field set drift")
    if receipt.get("status") != "ADMITTED_RESEARCH_IMPLEMENTATION_PLAN":
        findings.append("admission receipt status drift")
    if receipt.get("authority") != EXPECTED_AUTHORITY:
        findings.append("admission authority ceiling drift")
    if receipt.get("admission_scope") != EXPECTED_ADMISSION_SCOPE:
        findings.append("admission scope drift")
    if receipt.get("nonclaims") != EXPECTED_NONCLAIMS:
        findings.append("admission nonclaims drift")

    admitted = receipt.get("admitted_plan")
    expected_admitted = {
        "schema": PLAN_SCHEMA,
        "commit": PLAN_COMMIT,
        "parent": PLAN_PARENT,
        "tree": PLAN_TREE,
        "plan_path": PLAN_PATH,
        "plan_sha256": PLAN_SHA256,
    }
    if admitted != expected_admitted:
        findings.append("admitted plan subject drift")

    commit = admitted.get("commit") if type(admitted) is dict else None
    if type(commit) is not str or not _SHA1_RE.fullmatch(commit):
        findings.append("admitted plan commit is not exact")
    else:
        observed_parent = _git(root, ["rev-parse", f"{commit}^"])
        observed_tree = _git(root, ["rev-parse", f"{commit}^{{tree}}"])
        if observed_parent is None or observed_parent.decode().strip() != PLAN_PARENT:
            findings.append("admitted plan parent does not replay")
        if observed_tree is None or observed_tree.decode().strip() != PLAN_TREE:
            findings.append("admitted plan tree does not replay")
    if _git(root, ["merge-base", "--is-ancestor", PLAN_COMMIT, "HEAD"]) != b"":
        findings.append("admitted plan commit is not on current HEAD lineage")

    if receipt.get("subject_files") != _exact_file_rows(EXPECTED_SUBJECT_FILES):
        findings.append("admitted subject-file inventory or hash drift")
    if receipt.get("normative_inputs") != _exact_file_rows(EXPECTED_NORMATIVE_INPUTS):
        findings.append("admission normative-input binding drift")
    if receipt.get("upstream_dependency_binding") != EXPECTED_UPSTREAM_DEPENDENCY_BINDING:
        findings.append("admission upstream-dependency binding drift")
    if receipt.get("selection_premise") != EXPECTED_SELECTION_PREMISE:
        findings.append("external user-selection premise drift")
    for path, expected_hash in EXPECTED_SUBJECT_FILES:
        blob = _git(root, ["show", f"{PLAN_COMMIT}:{path}"])
        if blob is None or hashlib.sha256(blob).hexdigest() != expected_hash:
            findings.append(f"admitted subject file does not replay: {path}")
    for path, expected_hash in EXPECTED_NORMATIVE_INPUTS:
        blob = _git(root, ["show", f"{PLAN_COMMIT}:{path}"])
        if blob is None or hashlib.sha256(blob).hexdigest() != expected_hash:
            findings.append(f"admitted normative input does not replay: {path}")

    plan_blob = _git(root, ["show", f"{PLAN_COMMIT}:{PLAN_PATH}"])
    if plan_blob is None:
        findings.append("admitted plan blob is unavailable")
        plan: Mapping[str, object] = {}
    else:
        try:
            plan_value = decode_json_object_v1(plan_blob, "admitted plan blob")
        except RequirementsRejectV1:
            plan_value = None
        plan = plan_value if type(plan_value) is dict else {}
        if hashlib.sha256(plan_blob).hexdigest() != PLAN_SHA256:
            findings.append("admitted plan blob hash drift")
    if plan.get("schema") != PLAN_SCHEMA or plan.get("status") != PLAN_STATUS:
        findings.append("admitted plan was not a research candidate")
    plan_normative = plan.get("normative_inputs")
    if _changed_file_pairs(plan_normative) != EXPECTED_NORMATIVE_INPUTS:
        findings.append("admitted plan normative inputs do not match receipt")
    plan_upstream = plan.get("upstream_dependencies")
    if type(plan_upstream) is not list or len(plan_upstream) != 2:
        findings.append("admitted plan upstream-dependency cardinality drift")
    else:
        observed_upstream_hash = hashlib.sha256(canonical_json_bytes_v1(plan_upstream)).hexdigest()
        if observed_upstream_hash != UPSTREAM_DEPENDENCIES_SHA256:
            findings.append("admitted plan upstream dependencies do not match receipt")
    plan_authority = plan.get("authority")
    if type(plan_authority) is not dict or any(
        (
            plan_authority.get("production_authority") != "NONE",
            plan_authority.get("settlement_authority") != "NONE",
            plan_authority.get("release_ready") is not False,
            plan_authority.get("production_ready") is not False,
        )
    ):
        findings.append("admitted plan authority does not remain closed")
    if plan.get("admission_model") != EXPECTED_PLAN_ADMISSION_MODEL:
        findings.append("admitted plan admission model drift")
    if plan.get("advisory_reviews") != EXPECTED_PLAN_ADVISORY_REVIEWS:
        findings.append("admitted plan advisory-review declaration drift")

    if receipt.get("advisory_review") != EXPECTED_ADVISORY_REVIEW:
        findings.append("advisory review binding drift")
    if _git(root, ["merge-base", "--is-ancestor", REVIEW_COMMIT, "HEAD"]) != b"":
        findings.append("advisory review commit is not on current HEAD lineage")
    review_tree_entry = _git(root, ["ls-tree", REVIEW_COMMIT, "--", REVIEW_PATH])
    expected_review_tree_entry = f"100644 blob {REVIEW_BLOB}\t{REVIEW_PATH}\n".encode()
    if review_tree_entry != expected_review_tree_entry:
        findings.append("advisory review tree entry does not replay")
    review_blob = _git(root, ["show", f"{REVIEW_COMMIT}:{REVIEW_PATH}"])
    if review_blob is None or hashlib.sha256(review_blob).hexdigest() != REVIEW_SHA256:
        findings.append("advisory review artifact does not replay")

    receipt_hash = _canonical_payload_hash(receipt)
    if receipt.get("receipt_payload_sha256") != receipt_hash:
        findings.append("admission receipt payload hash mismatch")

    if registry.get("schema") != REGISTRY_SCHEMA or registry.get("status") != "RESEARCH_ONLY":
        findings.append("active-plan registry schema or status drift")
    if set(registry) != EXPECTED_REGISTRY_KEYS:
        findings.append("active-plan registry field set drift")
    if registry.get("authority") != EXPECTED_AUTHORITY:
        findings.append("active-plan registry authority ceiling drift")
    if registry.get("replacement_rule") != EXPECTED_REPLACEMENT_RULE:
        findings.append("active-plan registry replacement rule drift")
    if registry.get("nonclaim") != EXPECTED_REGISTRY_NONCLAIM:
        findings.append("active-plan registry nonclaim drift")
    active_plans = registry.get("active_plans")
    active_plan_count = registry.get("active_plan_count")
    if (
        type(active_plan_count) is not int
        or active_plan_count != 1
        or type(active_plans) is not list
        or len(active_plans) != 1
    ):
        findings.append("active-plan registry must contain exactly one plan")
    else:
        expected_active = {
            "plan_schema": PLAN_SCHEMA,
            "plan_commit": PLAN_COMMIT,
            "plan_tree": PLAN_TREE,
            "plan_path": PLAN_PATH,
            "plan_sha256": PLAN_SHA256,
            "admission_receipt_path": str(DEFAULT_RECEIPT),
            "admission_receipt_payload_sha256": receipt_hash,
            "activation_class": "ACTIVE_RESEARCH_IMPLEMENTATION_PLAN",
        }
        if active_plans[0] != expected_active:
            findings.append("active-plan registry subject or receipt binding drift")

    serialized = json.dumps([receipt, registry], sort_keys=True)
    if "/tmp/" in serialized or "/home/" in serialized:
        findings.append("machine-specific path present in admission evidence")

    return {
        "schema": "zenodex/plan-admission-check/v1",
        "ok": not findings,
        "active_research_plan_count": 1 if not findings else 0,
        "active_plan_commit": PLAN_COMMIT if not findings else None,
        "production_authority": "NONE",
        "settlement_authority": "NONE",
        "closed_value_movement_gate_count": 0,
        "findings": findings,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args(argv)
    report = check_whole_program_plan_admission_v1()
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

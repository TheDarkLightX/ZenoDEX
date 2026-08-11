#!/usr/bin/env python3
"""Validate the source-bound Luna completeness review for the M6 core draft."""

from __future__ import annotations

import argparse
import importlib
import json
import re
import sys
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

contract_checker = importlib.import_module("tools.check_m6_global_economic_core_atdd_v1")


DEFAULT_REVIEW = (
    REPO_ROOT / "docs/research/m6_global_economic_core_luna_completeness_review_v1.json"
)
SCHEMA = "zenodex/m6-global-economic-core-luna-completeness-review/v1"
STATUS = "RESEARCH_ONLY_REVIEWED_WITH_BLOCKERS"

ROOT_KEYS = {
    "schema",
    "status",
    "production_promotion",
    "review_subject",
    "current_revision",
    "source_pins",
    "confirmed_findings",
    "required_spec_expansions",
    "scope_decisions",
    "discarded_review_artifacts",
    "nonclaims",
}
REVIEW_SUBJECT_KEYS = {
    "base_commit",
    "contract_sha256",
    "esso_model_sha256",
    "fleet_manifest_ref",
    "reviewer_model",
    "review_task_ids",
}
CURRENT_REVISION_KEYS = {
    "contract_path",
    "contract_sha256",
    "esso_model_path",
    "esso_model_sha256",
    "revision_scope",
}
FINDING_KEYS = {
    "id",
    "classification",
    "severity",
    "title",
    "affected_requirements",
    "witness",
    "evidence",
    "status",
    "required_disposition",
}
EXPANSION_KEYS = {
    "id",
    "title",
    "required_scenario_classes",
    "minimum_acceptance",
}
SCOPE_KEYS = {"feature", "status", "rule"}

EXPECTED_TASKS = {
    "m6-completeness-users",
    "m6-completeness-accounting",
    "m6-completeness-authority",
    "m6-completeness-durability",
    "m6-completeness-formal",
}
EXPECTED_FINDINGS = {f"CE-{index:03d}" for index in range(1, 9)}
EXPECTED_EXPANSIONS = {f"RSE-{index:03d}" for index in range(1, 12)}
EXPECTED_SCOPE_FEATURES = {
    "zUSD emergency shutdown",
    "confidential sealed-bid settlement",
    "test faucet and unsigned intents",
    "generic non-zUSD token mint and burn",
    "autotrader and autonomous governance",
    "cross-shard and remote destination effects",
}
ALLOWED_CLASSIFICATIONS = {
    "EXPLOIT_OR_COUNTEREXAMPLE",
    "SEMANTIC_GAP",
    "ASSURANCE_DEBT",
}
ALLOWED_SEVERITIES = {"BLOCKER", "HIGH", "MEDIUM", "LOW"}
ALLOWED_FINDING_STATUSES = {
    "OPEN_BLOCKER",
    "OPEN_PRODUCT_AND_THEOREM_DECISION",
    "REPAIRED_IN_BOUNDED_MODEL",
}
SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")


def _exact_keys(value: Any, expected: set[str], label: str, errors: list[str]) -> bool:
    if not isinstance(value, Mapping):
        errors.append(f"{label} must be an object")
        return False
    actual = set(value)
    if actual != expected:
        errors.append(
            f"{label} keys differ: missing={sorted(expected - actual)}, "
            f"surplus={sorted(actual - expected)}"
        )
        return False
    return True


def _string(value: Any, label: str, errors: list[str]) -> bool:
    if not isinstance(value, str) or not value.strip():
        errors.append(f"{label} must be a nonempty string")
        return False
    return True


def _unique_strings(value: Any, label: str, errors: list[str]) -> list[str] | None:
    if not isinstance(value, list) or not value:
        errors.append(f"{label} must be a nonempty list")
        return None
    if any(not isinstance(item, str) or not item.strip() for item in value):
        errors.append(f"{label} must contain nonempty strings")
        return None
    if len(value) != len(set(value)):
        errors.append(f"{label} must not contain duplicates")
        return None
    return value


def _hash_matches(path: Path, expected: Any, label: str, errors: list[str]) -> None:
    if not isinstance(expected, str) or SHA256_RE.fullmatch(expected) is None:
        errors.append(f"{label} must be 64 lowercase hexadecimal characters")
        return
    if not path.is_file():
        errors.append(f"{label} path does not exist: {path}")
        return
    actual = contract_checker._sha256(path)
    if actual != expected:
        errors.append(f"{label} mismatch: expected={expected}, actual={actual}")


def validate_review(review: Mapping[str, Any], repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    if not _exact_keys(review, ROOT_KEYS, "review", errors):
        return _report(review, 0, 0, 0, 0, errors)
    if review["schema"] != SCHEMA:
        errors.append(f"schema must equal {SCHEMA!r}")
    if review["status"] != STATUS:
        errors.append(f"status must equal {STATUS!r}")
    if review["production_promotion"] is not False:
        errors.append("production_promotion must be the JSON boolean false")

    subject = review["review_subject"]
    if _exact_keys(subject, REVIEW_SUBJECT_KEYS, "review_subject", errors):
        for field in (
            "base_commit",
            "contract_sha256",
            "esso_model_sha256",
            "fleet_manifest_ref",
            "reviewer_model",
        ):
            _string(subject[field], f"review_subject.{field}", errors)
        if subject["reviewer_model"] != "gpt-5.6-luna":
            errors.append("review_subject.reviewer_model must equal 'gpt-5.6-luna'")
        tasks = _unique_strings(
            subject["review_task_ids"], "review_subject.review_task_ids", errors
        )
        if tasks is not None and set(tasks) != EXPECTED_TASKS:
            errors.append("review_task_ids must equal the five closed Luna review tasks")

    revision = review["current_revision"]
    if _exact_keys(revision, CURRENT_REVISION_KEYS, "current_revision", errors):
        contract_path = revision["contract_path"]
        model_path = revision["esso_model_path"]
        if _string(contract_path, "current_revision.contract_path", errors):
            _hash_matches(
                repo_root / contract_path,
                revision["contract_sha256"],
                "current_revision.contract_sha256",
                errors,
            )
        if _string(model_path, "current_revision.esso_model_path", errors):
            _hash_matches(
                repo_root / model_path,
                revision["esso_model_sha256"],
                "current_revision.esso_model_sha256",
                errors,
            )
        _string(revision["revision_scope"], "current_revision.revision_scope", errors)

    source_pin_count = contract_checker._validate_source_pins(
        review["source_pins"], repo_root, errors
    )

    findings = review["confirmed_findings"]
    finding_ids: list[str] = []
    if not isinstance(findings, list):
        errors.append("confirmed_findings must be a list")
        findings = []
    for index, finding in enumerate(findings):
        label = f"confirmed_findings[{index}]"
        if not _exact_keys(finding, FINDING_KEYS, label, errors):
            continue
        finding_ids.append(finding["id"])
        if finding["classification"] not in ALLOWED_CLASSIFICATIONS:
            errors.append(f"{label}.classification is not allowed")
        if finding["severity"] not in ALLOWED_SEVERITIES:
            errors.append(f"{label}.severity is not allowed")
        if finding["status"] not in ALLOWED_FINDING_STATUSES:
            errors.append(f"{label}.status is not allowed")
        for field in ("id", "title", "witness", "required_disposition"):
            _string(finding[field], f"{label}.{field}", errors)
        requirements = _unique_strings(
            finding["affected_requirements"], f"{label}.affected_requirements", errors
        )
        if requirements is not None:
            unknown = set(requirements) - contract_checker.EXPECTED_INVARIANTS
            if unknown:
                errors.append(f"{label} contains unknown invariant IDs: {sorted(unknown)}")
        _unique_strings(finding["evidence"], f"{label}.evidence", errors)
    if set(finding_ids) != EXPECTED_FINDINGS or len(finding_ids) != len(set(finding_ids)):
        errors.append("finding IDs must be exactly CE-001 through CE-008")

    expansions = review["required_spec_expansions"]
    expansion_ids: list[str] = []
    if not isinstance(expansions, list):
        errors.append("required_spec_expansions must be a list")
        expansions = []
    for index, expansion in enumerate(expansions):
        label = f"required_spec_expansions[{index}]"
        if not _exact_keys(expansion, EXPANSION_KEYS, label, errors):
            continue
        expansion_ids.append(expansion["id"])
        _string(expansion["id"], f"{label}.id", errors)
        _string(expansion["title"], f"{label}.title", errors)
        _unique_strings(
            expansion["required_scenario_classes"],
            f"{label}.required_scenario_classes",
            errors,
        )
        _unique_strings(expansion["minimum_acceptance"], f"{label}.minimum_acceptance", errors)
    if set(expansion_ids) != EXPECTED_EXPANSIONS or len(expansion_ids) != len(set(expansion_ids)):
        errors.append("expansion IDs must be exactly RSE-001 through RSE-011")

    scopes = review["scope_decisions"]
    scope_features: list[str] = []
    if not isinstance(scopes, list):
        errors.append("scope_decisions must be a list")
        scopes = []
    for index, scope in enumerate(scopes):
        label = f"scope_decisions[{index}]"
        if not _exact_keys(scope, SCOPE_KEYS, label, errors):
            continue
        for field in sorted(SCOPE_KEYS):
            _string(scope[field], f"{label}.{field}", errors)
        scope_features.append(scope["feature"])
    if set(scope_features) != EXPECTED_SCOPE_FEATURES or len(scope_features) != len(
        set(scope_features)
    ):
        errors.append("scope_decisions must equal the closed expected feature set")

    _unique_strings(review["discarded_review_artifacts"], "discarded_review_artifacts", errors)
    _unique_strings(review["nonclaims"], "nonclaims", errors)

    contract_path = repo_root / str(revision.get("contract_path", ""))
    if contract_path.is_file():
        try:
            contract = contract_checker.load_contract(contract_path)
            contract_report = contract_checker.validate_contract(contract, repo_root)
            if not contract_report["ok"]:
                errors.append(f"current contract failed its checker: {contract_report['errors']}")
        except contract_checker.ContractError as exc:
            errors.append(f"current contract could not be decoded: {exc}")

    return _report(
        review,
        source_pin_count,
        len(set(finding_ids)),
        len(set(expansion_ids)),
        len(set(scope_features)),
        errors,
    )


def _report(
    review: Mapping[str, Any],
    source_pin_count: int,
    finding_count: int,
    expansion_count: int,
    scope_count: int,
    errors: Sequence[str],
) -> dict[str, Any]:
    return {
        "schema": "zenodex/m6-global-economic-core-luna-completeness-review-check/v1",
        "ok": not errors,
        "review_schema": review.get("schema"),
        "review_status": review.get("status"),
        "production_promotion": review.get("production_promotion"),
        "source_pin_count": source_pin_count,
        "finding_count": finding_count,
        "required_spec_expansion_count": expansion_count,
        "scope_decision_count": scope_count,
        "errors": list(errors),
        "nonclaim": "review closure and reproductions do not prove or mount M6",
    }


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--review", type=Path, default=DEFAULT_REVIEW)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        review = contract_checker.load_contract(args.review)
        report = validate_review(review, args.repo_root.resolve())
    except contract_checker.ContractError as exc:
        report = {
            "schema": "zenodex/m6-global-economic-core-luna-completeness-review-check/v1",
            "ok": False,
            "errors": [str(exc)],
            "nonclaim": "no review packet was accepted",
        }
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

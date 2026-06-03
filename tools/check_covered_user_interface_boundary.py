#!/usr/bin/env python3
"""Validate the internal covered user-interface boundary manifest."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.covered_ui_lint import RULES, result_payload, scan_paths  # noqa: E402

MANIFEST_SCHEMA = "zenodex.covered_user_interface_boundary.v0"
REPORT_SCHEMA = "zenodex.covered_user_interface_boundary_report.v0"
LINT_SCHEMA = "zenodex/covered-ui-lint/v1"

ALLOWED_STATUSES = {"internal_boundary_only", "testnet_only"}
REQUIRED_CONTROLS = {
    "self_custody_wallet_signing",
    "no_ui_investment_recommendations",
    "objective_route_and_price_labels",
    "no_specific_transaction_solicitation",
    "no_custody_or_fund_control",
    "no_order_flow_or_affiliate_bias",
    "covered_ui_lint_strict",
    "public_claim_scope_gate",
    "counsel_review_required",
}
REQUIRED_NON_CLAIMS = {
    "broker_dealer_registration_clearance",
    "securities_law_clearance",
    "investment_advice",
    "custody_or_fund_control",
    "transaction_recommendations",
    "public_launch_readiness",
}


def validate_covered_user_interface_boundary_v0(
    manifest: Any,
    *,
    base_dir: Path | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != MANIFEST_SCHEMA:
        errors.append("schema mismatch")

    status = _str(obj.get("status"), "status", errors)
    public_claims_allowed = _bool(obj.get("public_claims_allowed"), "public_claims_allowed", errors)
    activation_allowed = _bool(obj.get("activation_allowed"), "activation_allowed", errors)
    counsel_review_required = _bool(obj.get("counsel_review_required"), "counsel_review_required", errors)
    legal_review_complete = _bool(obj.get("legal_review_complete"), "legal_review_complete", errors)
    if status is not None and status not in ALLOWED_STATUSES:
        errors.append("status must be internal_boundary_only or testnet_only")
    if public_claims_allowed is not False:
        errors.append("public_claims_allowed must be false")
    if activation_allowed is not False:
        errors.append("activation_allowed must be false")
    if counsel_review_required is not True:
        errors.append("counsel_review_required must be true")
    if legal_review_complete is not False:
        errors.append("legal_review_complete must be false")

    controls = _required_string_set(obj.get("controls"), "controls", required=REQUIRED_CONTROLS)
    non_claims = _required_string_set(obj.get("non_claims"), "non_claims", required=REQUIRED_NON_CLAIMS)
    lint_policy = _validate_lint_policy(obj.get("lint_policy"))
    promotion_boundary = _validate_promotion_boundary(obj.get("promotion_boundary"))

    if not controls["ok"]:
        errors.append("controls rejected")
    if not non_claims["ok"]:
        errors.append("non_claims rejected")
    if not lint_policy["ok"]:
        errors.append("lint_policy rejected")
    if not promotion_boundary["ok"]:
        errors.append("promotion_boundary rejected")

    lint_report = _run_lint(obj.get("ui_paths"), base_dir=base_dir)
    if not lint_report["ok"]:
        errors.append("covered_ui_lint rejected")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "facts": {
            "status": status,
            "public_claims_allowed": public_claims_allowed,
            "activation_allowed": activation_allowed,
            "counsel_review_required": counsel_review_required,
            "legal_review_complete": legal_review_complete,
            "scanned_file_count": lint_report["facts"].get("scanned_file_count"),
            "finding_count": lint_report["facts"].get("finding_count"),
        },
        "controls": controls,
        "non_claims": non_claims,
        "lint_policy": lint_policy,
        "lint": lint_report,
        "promotion_boundary": promotion_boundary,
    }


def _validate_lint_policy(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "lint_policy", errors)
    strict = _bool(obj.get("strict"), "lint_policy.strict", errors)
    max_findings = _int_between(obj.get("max_findings"), "lint_policy.max_findings", errors, 0, 0)
    required_rule_ids = _required_string_set(
        obj.get("required_rule_ids"),
        "lint_policy.required_rule_ids",
        required=frozenset(rule.rule_id for rule in RULES),
    )
    if strict is not True:
        errors.append("lint_policy.strict must be true")
    if max_findings != 0:
        errors.append("lint_policy.max_findings must be 0")
    if not required_rule_ids["ok"]:
        errors.append("lint_policy.required_rule_ids rejected")
    return {
        "ok": not errors,
        "errors": errors,
        "facts": {"strict": strict, "max_findings": max_findings},
        "required_rule_ids": required_rule_ids,
    }


def _validate_promotion_boundary(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "promotion_boundary", errors)
    if _bool(obj.get("public_launch_allowed"), "promotion_boundary.public_launch_allowed", errors) is not False:
        errors.append("promotion_boundary.public_launch_allowed must be false")
    if _bool(obj.get("claim_registry_entry_allowed"), "promotion_boundary.claim_registry_entry_allowed", errors) is not False:
        errors.append("promotion_boundary.claim_registry_entry_allowed must be false")
    if _bool(obj.get("requires_external_legal_review"), "promotion_boundary.requires_external_legal_review", errors) is not True:
        errors.append("promotion_boundary.requires_external_legal_review must be true")
    blockers = _required_string_set(
        obj.get("blockers"),
        "promotion_boundary.blockers",
        required=frozenset(
            {
                "external_counsel_review_not_complete",
                "covered_ui_lint_must_remain_clean",
                "public_claim_scope_must_remain_non_advisory",
            }
        ),
    )
    if not blockers["ok"]:
        errors.append("promotion_boundary.blockers rejected")
    return {"ok": not errors, "errors": errors, "blockers": blockers}


def _run_lint(value: Any, *, base_dir: Path | None) -> dict[str, Any]:
    errors: list[str] = []
    paths = _string_list(value, "ui_paths", errors)
    if not paths:
        errors.append("ui_paths must not be empty")
    scan_inputs = [str((base_dir / path) if base_dir is not None else Path(path)) for path in paths]
    files, findings = scan_paths(scan_inputs)
    payload = result_payload(files, findings)
    if payload.get("schema") != LINT_SCHEMA:
        errors.append("covered UI lint schema mismatch")
    finding_count = int(payload.get("finding_count", 0) or 0)
    if finding_count != 0:
        errors.append("covered UI lint must have zero findings")
    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "ui_paths": paths,
            "scanned_file_count": payload.get("scanned_file_count"),
            "finding_count": payload.get("finding_count"),
            "severity_counts": payload.get("severity_counts"),
            "rule_counts": payload.get("rule_counts"),
        },
        "findings": payload.get("findings", []),
    }


def _required_string_set(value: Any, field: str, *, required: frozenset[str] | set[str]) -> dict[str, Any]:
    errors: list[str] = []
    items = _string_list(value, field, errors)
    seen = set(items)
    missing = sorted(set(required) - seen)
    unknown = sorted(seen - set(required))
    if missing:
        errors.append(f"{field} missing required values: {','.join(missing)}")
    if unknown:
        errors.append(f"{field} contains unknown values: {','.join(unknown)}")
    return {"ok": not errors, "errors": errors, "values": sorted(seen), "missing": missing, "unknown": unknown}


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    errors.append(f"{name} must be an object")
    return {}


def _string_list(value: Any, name: str, errors: list[str]) -> list[str]:
    if not isinstance(value, list):
        errors.append(f"{name} must be a list")
        return []
    out: list[str] = []
    for item in value:
        if not isinstance(item, str) or not item.strip():
            errors.append(f"{name} entries must be non-empty strings")
            continue
        out.append(item.strip())
    return out


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if isinstance(value, str) and value.strip():
        return value.strip()
    errors.append(f"{name} must be a non-empty string")
    return None


def _bool(value: Any, name: str, errors: list[str]) -> bool | None:
    if isinstance(value, bool):
        return value
    errors.append(f"{name} must be a bool")
    return None


def _int_between(value: Any, name: str, errors: list[str], minimum: int, maximum: int) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool):
        if value < minimum or value > maximum:
            errors.append(f"{name} must be in [{minimum}, {maximum}]")
        return int(value)
    errors.append(f"{name} must be an int")
    return None


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    manifest_path = args.manifest.resolve()
    report = validate_covered_user_interface_boundary_v0(
        _load_json(manifest_path),
        base_dir=manifest_path.parents[2] if len(manifest_path.parents) >= 3 else None,
    )
    if args.pretty:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, separators=(",", ":"), sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

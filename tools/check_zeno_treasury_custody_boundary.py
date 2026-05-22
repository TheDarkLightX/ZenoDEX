#!/usr/bin/env python3
"""Validate the internal ZENO treasury custody boundary."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Mapping

MANIFEST_SCHEMA = "zenodex.treasury_custody_boundary.v0"
REPORT_SCHEMA = "zenodex.treasury_custody_boundary_report.v0"

ALLOWED_STATUSES = {"internal_research_only", "testnet_only"}
ALLOWED_TAU_WALLET_MATURITY = {"unproven", "testnet_only", "production_ready"}
ALLOWED_REVIEW_STATUS = {"required_not_complete", "complete"}

REQUIRED_CONTROLS = frozenset(
    {
        "threshold_multisig_or_threshold_signature",
        "independent_signers",
        "signer_geographic_separation",
        "hardware_or_hardened_signing",
        "transaction_simulation",
        "timelock",
        "spending_caps",
        "dual_control_release",
        "emergency_freeze",
        "signer_rotation",
        "audit_log",
        "no_demo_keys",
        "no_single_key_treasury",
        "staged_funding",
    }
)

REQUIRED_ATTACK_QUERIES = frozenset(
    {
        "single_signer_compromise",
        "wallet_software_bug",
        "social_engineering",
        "governance_capture",
        "hot_wallet_drain",
        "signer_collusion",
        "immature_tau_wallet_dependency",
    }
)

REQUIRED_NON_CLAIMS = frozenset(
    {
        "no_tau_net_multisig_maturity_claim",
        "no_public_treasury_launch_readiness",
        "no_custody_security_complete",
        "no_legal_clearance",
        "no_single_wallet_full_treasury",
    }
)


def validate_treasury_custody_boundary_v0(manifest: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != MANIFEST_SCHEMA:
        errors.append("schema mismatch")

    status = _str(obj.get("status"), "status", errors)
    public_claims_allowed = _bool(obj.get("public_claims_allowed"), "public_claims_allowed", errors)
    counsel_review_required = _bool(obj.get("counsel_review_required"), "counsel_review_required", errors)
    counsel_review_status = _str(obj.get("counsel_review_status"), "counsel_review_status", errors)
    tau_wallet_maturity = _str(
        obj.get("tau_net_multisig_wallet_maturity"),
        "tau_net_multisig_wallet_maturity",
        errors,
    )
    full_treasury_live_funding_allowed = _bool(
        obj.get("full_treasury_live_funding_allowed"),
        "full_treasury_live_funding_allowed",
        errors,
    )

    if status is not None and status not in ALLOWED_STATUSES:
        errors.append("status must be internal_research_only or testnet_only")
    if public_claims_allowed is not False:
        errors.append("public_claims_allowed must be false")
    if counsel_review_required is not True:
        errors.append("counsel_review_required must be true")
    if counsel_review_status is not None and counsel_review_status not in ALLOWED_REVIEW_STATUS:
        errors.append("counsel_review_status must be required_not_complete or complete")
    if tau_wallet_maturity is not None and tau_wallet_maturity not in ALLOWED_TAU_WALLET_MATURITY:
        errors.append("tau_net_multisig_wallet_maturity is unsupported")
    if tau_wallet_maturity != "production_ready" and full_treasury_live_funding_allowed is not False:
        errors.append("full live treasury funding requires production-ready Tau Net threshold custody")

    custody_params = _validate_custody_params(
        obj.get("custody_params"),
        tau_wallet_maturity=tau_wallet_maturity,
    )
    controls = _validate_required_string_set(obj.get("controls"), field="controls", required=REQUIRED_CONTROLS)
    attack_queries = _validate_attack_queries(obj.get("attack_queries"))
    promotion_boundary = _validate_promotion_boundary(obj.get("promotion_boundary"))

    for section_name, section in (
        ("custody_params", custody_params),
        ("controls", controls),
        ("attack_queries", attack_queries),
        ("promotion_boundary", promotion_boundary),
    ):
        if not section["ok"]:
            errors.append(f"{section_name} rejected")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "facts": {
            "status": status,
            "public_claims_allowed": public_claims_allowed,
            "counsel_review_required": counsel_review_required,
            "counsel_review_status": counsel_review_status,
            "tau_net_multisig_wallet_maturity": tau_wallet_maturity,
            "full_treasury_live_funding_allowed": full_treasury_live_funding_allowed,
            "signer_count": custody_params["facts"].get("signer_count"),
            "signer_threshold": custody_params["facts"].get("signer_threshold"),
            "max_live_treasury_wallet_token": custody_params["facts"].get("max_live_treasury_wallet_token"),
        },
        "custody_params": custody_params,
        "controls": controls,
        "attack_queries": attack_queries,
        "promotion_boundary": promotion_boundary,
    }


def _validate_custody_params(value: Any, *, tau_wallet_maturity: str | None) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "custody_params", errors)
    total_treasury = _int_ge(
        obj.get("total_treasury_allocation_token"),
        "custody_params.total_treasury_allocation_token",
        errors,
        1,
    )
    max_live = _int_ge(
        obj.get("max_live_treasury_wallet_token"),
        "custody_params.max_live_treasury_wallet_token",
        errors,
        1,
    )
    max_single = _int_ge(
        obj.get("max_single_disbursement_token"),
        "custody_params.max_single_disbursement_token",
        errors,
        1,
    )
    max_epoch = _int_ge(
        obj.get("max_epoch_disbursement_token"),
        "custody_params.max_epoch_disbursement_token",
        errors,
        1,
    )
    signer_count = _int_ge(obj.get("signer_count"), "custody_params.signer_count", errors, 5)
    signer_threshold = _int_ge(obj.get("signer_threshold"), "custody_params.signer_threshold", errors, 3)
    timelock_hours = _int_ge(obj.get("timelock_hours"), "custody_params.timelock_hours", errors, 24)
    emergency_freeze_threshold = _int_ge(
        obj.get("emergency_freeze_threshold"),
        "custody_params.emergency_freeze_threshold",
        errors,
        1,
    )
    key_rotation_days = _int_ge(obj.get("key_rotation_days"), "custody_params.key_rotation_days", errors, 1)

    if total_treasury is not None and max_live is not None:
        if max_live > total_treasury:
            errors.append("max_live_treasury_wallet_token exceeds total_treasury_allocation_token")
        if tau_wallet_maturity != "production_ready" and max_live * 50 > total_treasury:
            errors.append("max_live_treasury_wallet_token must be <= 2% of treasury allocation while custody is unproven")
    if max_live is not None and max_single is not None and max_single > max_live:
        errors.append("max_single_disbursement_token exceeds max_live_treasury_wallet_token")
    if max_live is not None and max_epoch is not None and max_epoch > max_live:
        errors.append("max_epoch_disbursement_token exceeds max_live_treasury_wallet_token")
    if signer_count is not None and signer_threshold is not None:
        if signer_threshold > signer_count:
            errors.append("signer_threshold exceeds signer_count")
        if signer_threshold * 2 <= signer_count:
            errors.append("signer_threshold must be strict majority of signer_count")
    if emergency_freeze_threshold is not None and signer_threshold is not None:
        if emergency_freeze_threshold > signer_threshold:
            errors.append("emergency_freeze_threshold must be <= signer_threshold")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "total_treasury_allocation_token": total_treasury,
            "max_live_treasury_wallet_token": max_live,
            "max_single_disbursement_token": max_single,
            "max_epoch_disbursement_token": max_epoch,
            "signer_count": signer_count,
            "signer_threshold": signer_threshold,
            "timelock_hours": timelock_hours,
            "emergency_freeze_threshold": emergency_freeze_threshold,
            "key_rotation_days": key_rotation_days,
        },
    }


def _validate_attack_queries(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    queries_raw = value
    if not isinstance(queries_raw, list):
        errors.append("attack_queries must be a list")
        queries_raw = []

    seen_ids: set[str] = set()
    reports: list[dict[str, Any]] = []
    for index, item in enumerate(queries_raw):
        query_errors: list[str] = []
        query = _mapping(item, f"attack_queries[{index}]", query_errors)
        query_id = _str(query.get("id"), f"attack_queries[{index}].id", query_errors)
        condition = _str(query.get("condition"), f"attack_queries[{index}].condition", query_errors)
        mitigation = _str(query.get("mitigation"), f"attack_queries[{index}].mitigation", query_errors)
        expected_result = _str(query.get("expected_result"), f"attack_queries[{index}].expected_result", query_errors)
        if query_id is not None:
            if query_id in seen_ids:
                query_errors.append("attack query id must be unique")
            seen_ids.add(query_id)
        if expected_result is not None and expected_result not in {"rejected", "bounded"}:
            query_errors.append("attack query expected_result must be rejected or bounded")
        reports.append(
            {
                "id": query_id,
                "ok": not query_errors,
                "status": "accepted" if not query_errors else "rejected",
                "errors": query_errors,
                "facts": {
                    "condition": condition,
                    "mitigation": mitigation,
                    "expected_result": expected_result,
                },
            }
        )
    missing = sorted(REQUIRED_ATTACK_QUERIES - seen_ids)
    if missing:
        errors.append("missing required attack queries")
    if any(not report["ok"] for report in reports):
        errors.append("one or more attack queries rejected")
    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "missing_required_attack_queries": missing,
            "attack_query_count": len(reports),
        },
        "items": reports,
    }


def _validate_promotion_boundary(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "promotion_boundary", errors)
    public_claim_allowed = _bool(
        obj.get("public_claim_allowed"),
        "promotion_boundary.public_claim_allowed",
        errors,
    )
    claim_registry_entry_allowed = _bool(
        obj.get("claim_registry_entry_allowed"),
        "promotion_boundary.claim_registry_entry_allowed",
        errors,
    )
    if public_claim_allowed is not False:
        errors.append("promotion_boundary.public_claim_allowed must be false")
    if claim_registry_entry_allowed is not False:
        errors.append("promotion_boundary.claim_registry_entry_allowed must be false")
    non_claims = _validate_required_string_set(
        obj.get("non_claims"),
        field="promotion_boundary.non_claims",
        required=REQUIRED_NON_CLAIMS,
    )
    if not non_claims["ok"]:
        errors.append("promotion boundary missing required non-claims")
    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "public_claim_allowed": public_claim_allowed,
            "claim_registry_entry_allowed": claim_registry_entry_allowed,
            "missing_required_non_claims": non_claims["facts"].get("missing_required"),
        },
        "non_claims": non_claims,
    }


def _validate_required_string_set(value: Any, *, field: str, required: frozenset[str]) -> dict[str, Any]:
    errors: list[str] = []
    items_raw = value
    if not isinstance(items_raw, list):
        errors.append(f"{field} must be a list")
        items_raw = []
    items: set[str] = set()
    for index, item in enumerate(items_raw):
        if not isinstance(item, str) or not item:
            errors.append(f"{field}[{index}] must be a non-empty string")
            continue
        items.add(item)
    missing = sorted(required - items)
    if missing:
        errors.append(f"{field} missing required items")
    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "items": sorted(items),
            "item_count": len(items),
            "missing_required": missing,
        },
    }


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    errors.append(f"{name} must be an object")
    return {}


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if isinstance(value, str) and value:
        return value
    errors.append(f"{name} must be a non-empty string")
    return None


def _bool(value: Any, name: str, errors: list[str]) -> bool | None:
    if isinstance(value, bool):
        return value
    errors.append(f"{name} must be a boolean")
    return None


def _int_ge(value: Any, name: str, errors: list[str], minimum: int) -> int | None:
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{name} must be an int")
        return None
    if value < minimum:
        errors.append(f"{name} must be >= {minimum}")
        return None
    return int(value)


def _load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = validate_treasury_custody_boundary_v0(_load_json(args.manifest))
    if args.pretty:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

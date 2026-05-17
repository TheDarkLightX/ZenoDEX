#!/usr/bin/env python3
"""Validate an internal ZenoCover proof-triggered claim-verifier model."""

from __future__ import annotations

import argparse
import json
from itertools import product
from pathlib import Path
from typing import Any, Mapping

MANIFEST_SCHEMA = "zenodex.zenocover.claim_verifier_model.v0"
REPORT_SCHEMA = "zenodex.zenocover.claim_verifier_report.v0"

FAILURE_KINDS = {
    "ledger_replay_failure",
    "oracle_policy_failure",
    "proof_metadata_binding_failure",
    "settlement_invariant_failure",
}


def validate_zenocover_claim_verifier_model_v0(manifest: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != MANIFEST_SCHEMA:
        errors.append("schema mismatch")

    policy = _validate_policy(obj.get("policy"))
    claims = _validate_claims(obj.get("claims"), policy=policy)
    sweep = _run_attack_query_sweep(policy)

    if not policy["ok"]:
        errors.append("policy rejected")
    if not claims["ok"]:
        errors.append("one or more claims rejected")
    if not sweep["ok"]:
        errors.append("attack query sweep found unsafe example")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "policy": policy,
        "claims": claims,
        "attack_query_sweep": sweep,
    }


def _validate_policy(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "policy", errors)
    settlement_asset = _str(obj.get("settlement_asset"), "policy.settlement_asset", errors)
    reserve_available = _int_ge(obj.get("reserve_available"), "policy.reserve_available", errors, 0)
    min_reserve_after_payout = _int_ge(
        obj.get("min_reserve_after_payout"),
        "policy.min_reserve_after_payout",
        errors,
        0,
    )
    aggregate_payout_cap = _int_ge(
        obj.get("aggregate_payout_cap"),
        "policy.aggregate_payout_cap",
        errors,
        0,
    )
    per_claim_cap = _int_ge(obj.get("per_claim_cap"), "policy.per_claim_cap", errors, 0)
    verifier_bond = _int_ge(obj.get("verifier_bond"), "policy.verifier_bond", errors, 0)
    verifier_slash_amount = _int_ge(
        obj.get("verifier_slash_amount"),
        "policy.verifier_slash_amount",
        errors,
        0,
    )
    verifier_future_value_lost = _int_ge(
        obj.get("verifier_future_value_lost"),
        "policy.verifier_future_value_lost",
        errors,
        0,
    )
    max_invalid_claim_gain = _int_ge(
        obj.get("max_invalid_claim_gain"),
        "policy.max_invalid_claim_gain",
        errors,
        0,
    )

    allowed_raw = obj.get("allowed_failure_kinds")
    if not isinstance(allowed_raw, list):
        errors.append("policy.allowed_failure_kinds must be a list")
        allowed: set[str] = set()
    else:
        allowed = set()
        for index, item in enumerate(allowed_raw):
            parsed = _str(item, f"policy.allowed_failure_kinds[{index}]", errors)
            if parsed is not None:
                allowed.add(parsed)
                if parsed not in FAILURE_KINDS:
                    errors.append("policy.allowed_failure_kinds contains unsupported failure kind")
    if not allowed:
        errors.append("policy.allowed_failure_kinds must be non-empty")

    if None not in (reserve_available, min_reserve_after_payout, aggregate_payout_cap):
        spendable = int(reserve_available) - int(min_reserve_after_payout)
        if int(aggregate_payout_cap) > spendable:
            errors.append("aggregate_payout_cap exceeds reserve_available minus min_reserve_after_payout")
    if None not in (verifier_bond, verifier_slash_amount):
        if int(verifier_slash_amount) > int(verifier_bond):
            errors.append("verifier_slash_amount exceeds verifier_bond")
    if None not in (verifier_slash_amount, verifier_future_value_lost, max_invalid_claim_gain):
        downside = int(verifier_slash_amount) + int(verifier_future_value_lost)
        if int(max_invalid_claim_gain) > downside:
            errors.append("max_invalid_claim_gain exceeds verifier downside")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "settlement_asset": settlement_asset,
            "reserve_available": reserve_available,
            "min_reserve_after_payout": min_reserve_after_payout,
            "aggregate_payout_cap": aggregate_payout_cap,
            "per_claim_cap": per_claim_cap,
            "verifier_bond": verifier_bond,
            "verifier_slash_amount": verifier_slash_amount,
            "verifier_future_value_lost": verifier_future_value_lost,
            "max_invalid_claim_gain": max_invalid_claim_gain,
            "allowed_failure_kinds": sorted(allowed),
        },
    }


def _validate_claims(value: Any, *, policy: Mapping[str, Any]) -> dict[str, Any]:
    errors: list[str] = []
    claims_raw = value
    if not isinstance(claims_raw, list):
        errors.append("claims must be a list")
        claims_raw = []

    seen_ids: set[str] = set()
    paid_keys: set[str] = set()
    claim_reports: list[dict[str, Any]] = []
    aggregate_authorized = 0
    for index, item in enumerate(claims_raw):
        claim_errors: list[str] = []
        claim = _mapping(item, f"claims[{index}]", claim_errors)
        claim_id = _str(claim.get("id"), f"claims[{index}].id", claim_errors)
        claim_key = _str(claim.get("claim_key"), f"claims[{index}].claim_key", claim_errors)
        failure_kind = _str(claim.get("failure_kind"), f"claims[{index}].failure_kind", claim_errors)
        requested_payout = _int_ge(
            claim.get("requested_payout"),
            f"claims[{index}].requested_payout",
            claim_errors,
            0,
        )
        coverage_limit = _int_ge(
            claim.get("coverage_limit"),
            f"claims[{index}].coverage_limit",
            claim_errors,
            0,
        )
        loss_amount = _int_ge(
            claim.get("loss_amount"),
            f"claims[{index}].loss_amount",
            claim_errors,
            0,
        )
        expected_authorized = _int_ge(
            claim.get("expected_authorized_payout"),
            f"claims[{index}].expected_authorized_payout",
            claim_errors,
            0,
        )
        if claim_id is not None:
            if claim_id in seen_ids:
                claim_errors.append("claim id must be unique")
            seen_ids.add(claim_id)
        duplicate_key_seen = claim_key in paid_keys if claim_key is not None else False

        if failure_kind is not None:
            allowed = set(policy.get("facts", {}).get("allowed_failure_kinds", []))
            if failure_kind not in allowed:
                claim_errors.append("failure_kind is not allowed by policy")

        authorized = None
        covered_event = None
        if None not in (requested_payout, coverage_limit, loss_amount, failure_kind):
            authorized, covered_event = _authorized_payout(
                policy,
                claim,
                duplicate_key_seen=duplicate_key_seen,
            )
            if expected_authorized is not None and expected_authorized != authorized:
                claim_errors.append("expected_authorized_payout mismatch")
            if authorized > 0 and claim_key is not None:
                paid_keys.add(claim_key)
            aggregate_authorized += authorized

        claim_reports.append(
            {
                "id": claim_id,
                "claim_key": claim_key,
                "failure_kind": failure_kind,
                "ok": not claim_errors,
                "errors": claim_errors,
                "facts": {
                    "covered_event": covered_event,
                    "duplicate_key_seen": duplicate_key_seen,
                    "requested_payout": requested_payout,
                    "coverage_limit": coverage_limit,
                    "loss_amount": loss_amount,
                    "expected_authorized_payout": expected_authorized,
                    "computed_authorized_payout": authorized,
                },
            }
        )

    facts = policy.get("facts", {})
    aggregate_cap = _optional_int(facts.get("aggregate_payout_cap"))
    reserve_available = _optional_int(facts.get("reserve_available"))
    min_reserve_after_payout = _optional_int(facts.get("min_reserve_after_payout"))
    if aggregate_cap is not None and aggregate_authorized > aggregate_cap:
        errors.append("aggregate authorized payout exceeds aggregate_payout_cap")
    if reserve_available is not None and min_reserve_after_payout is not None:
        if reserve_available - aggregate_authorized < min_reserve_after_payout:
            errors.append("aggregate authorized payout violates min_reserve_after_payout")
    if any(not report["ok"] for report in claim_reports):
        errors.append("one or more claim rows rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "claim_count": len(claim_reports),
            "aggregate_authorized_payout": aggregate_authorized,
        },
        "items": claim_reports,
    }


def _authorized_payout(
    policy: Mapping[str, Any],
    claim: Mapping[str, Any],
    *,
    duplicate_key_seen: bool,
) -> tuple[int, bool]:
    covered = _covered_event(claim, duplicate_key_seen=duplicate_key_seen)
    if not covered:
        return 0, False
    facts = policy.get("facts", {})
    per_claim_cap = _optional_int(facts.get("per_claim_cap")) or 0
    requested_payout = _optional_int(claim.get("requested_payout")) or 0
    coverage_limit = _optional_int(claim.get("coverage_limit")) or 0
    loss_amount = _optional_int(claim.get("loss_amount")) or 0
    return min(requested_payout, coverage_limit, loss_amount, per_claim_cap), True


def _covered_event(claim: Mapping[str, Any], *, duplicate_key_seen: bool) -> bool:
    evidence = claim.get("event_evidence")
    if not isinstance(evidence, Mapping):
        return False
    if duplicate_key_seen:
        return False
    if _bool(evidence.get("policy_active")) is not True:
        return False
    if _bool(evidence.get("within_claim_window")) is not True:
        return False
    if _bool(evidence.get("already_paid")) is True:
        return False
    if _bool(evidence.get("exclusion_applies")) is True:
        return False

    failure_kind = claim.get("failure_kind")
    if failure_kind == "settlement_invariant_failure":
        return (
            _bool(evidence.get("ledger_header_body_bound")) is True
            and _bool(evidence.get("settlement_replay_ok")) is True
            and _bool(evidence.get("failure_certificate_valid")) is True
            and _bool(evidence.get("invariant_breach_confirmed")) is True
        )
    if failure_kind == "ledger_replay_failure":
        return (
            _bool(evidence.get("accepted_header")) is True
            and _bool(evidence.get("deterministic_replay_ok")) is False
            and _bool(evidence.get("replay_failure_certificate_valid")) is True
        )
    if failure_kind == "proof_metadata_binding_failure":
        return (
            _bool(evidence.get("accepted_header")) is True
            and _bool(evidence.get("proof_metadata_present")) is True
            and _bool(evidence.get("proof_verification_report_ok")) is True
            and _bool(evidence.get("proof_metadata_binding_ok")) is False
        )
    if failure_kind == "oracle_policy_failure":
        return (
            _bool(evidence.get("oracle_policy_id_match")) is True
            and _bool(evidence.get("oracle_quorum_ok")) is True
            and _bool(evidence.get("oracle_observation_fresh")) is True
            and _bool(evidence.get("oracle_policy_violation_confirmed")) is True
        )
    return False


def _run_attack_query_sweep(policy: Mapping[str, Any]) -> dict[str, Any]:
    facts = policy.get("facts", {})
    per_claim_cap = _optional_int(facts.get("per_claim_cap")) or 0
    allowed = list(facts.get("allowed_failure_kinds", []))
    values = sorted({0, per_claim_cap, per_claim_cap + 1})
    unsafe_examples: list[dict[str, Any]] = []
    checked = 0
    for failure_kind in allowed:
        for policy_active, within_window, already_paid, exclusion_applies in product((False, True), repeat=4):
            for requested_payout, coverage_limit, loss_amount in product(values, repeat=3):
                evidence = {
                    "policy_active": policy_active,
                    "within_claim_window": within_window,
                    "already_paid": already_paid,
                    "exclusion_applies": exclusion_applies,
                    **_positive_evidence_for_kind(failure_kind),
                }
                claim = {
                    "failure_kind": failure_kind,
                    "requested_payout": requested_payout,
                    "coverage_limit": coverage_limit,
                    "loss_amount": loss_amount,
                    "event_evidence": evidence,
                }
                payout, covered = _authorized_payout(policy, claim, duplicate_key_seen=False)
                checked += 1
                if (not covered and payout != 0) or payout > min(
                    requested_payout,
                    coverage_limit,
                    loss_amount,
                    per_claim_cap,
                ):
                    unsafe_examples.append(
                        {
                            "failure_kind": failure_kind,
                            "covered_event": covered,
                            "payout": payout,
                            "requested_payout": requested_payout,
                            "coverage_limit": coverage_limit,
                            "loss_amount": loss_amount,
                            "evidence": evidence,
                        }
                    )
                    if len(unsafe_examples) >= 8:
                        break
            if len(unsafe_examples) >= 8:
                break
        if len(unsafe_examples) >= 8:
            break

    return {
        "ok": not unsafe_examples,
        "checked_cases": checked,
        "unsafe_examples": unsafe_examples,
        "queries": [
            "accepted_invalid_event_has_positive_payout",
            "payout_exceeds_requested_loss_coverage_or_per_claim_cap",
        ],
    }


def _positive_evidence_for_kind(failure_kind: str) -> dict[str, bool]:
    if failure_kind == "settlement_invariant_failure":
        return {
            "ledger_header_body_bound": True,
            "settlement_replay_ok": True,
            "failure_certificate_valid": True,
            "invariant_breach_confirmed": True,
        }
    if failure_kind == "ledger_replay_failure":
        return {
            "accepted_header": True,
            "deterministic_replay_ok": False,
            "replay_failure_certificate_valid": True,
        }
    if failure_kind == "proof_metadata_binding_failure":
        return {
            "accepted_header": True,
            "proof_metadata_present": True,
            "proof_verification_report_ok": True,
            "proof_metadata_binding_ok": False,
        }
    if failure_kind == "oracle_policy_failure":
        return {
            "oracle_policy_id_match": True,
            "oracle_quorum_ok": True,
            "oracle_observation_fresh": True,
            "oracle_policy_violation_confirmed": True,
        }
    return {}


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or value == "":
        errors.append(f"{name} must be a non-empty string")
        return None
    return value


def _bool(value: Any) -> bool | None:
    if not isinstance(value, bool):
        return None
    return value


def _int_ge(value: Any, name: str, errors: list[str], minimum: int) -> int | None:
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{name} must be an int")
        return None
    if value < minimum:
        errors.append(f"{name} must be >= {minimum}")
        return None
    return int(value)


def _optional_int(value: Any) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    return None


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    report = validate_zenocover_claim_verifier_model_v0(manifest)
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

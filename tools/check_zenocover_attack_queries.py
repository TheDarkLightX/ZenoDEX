#!/usr/bin/env python3
"""Validate bounded ZenoCover cross-surface attack queries."""

from __future__ import annotations

import argparse
import json
import sys
from itertools import product
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_zenocover_claim_verifier_model import (  # noqa: E402
    validate_zenocover_claim_verifier_model_v0,
)
from tools.check_zenocover_reserve_solvency import (  # noqa: E402
    validate_zenocover_reserve_solvency_v0,
)
from tools.check_zenocover_reserve_withdrawal_safety import (  # noqa: E402
    validate_reserve_withdrawal_safety_v0,
)

MANIFEST_SCHEMA = "zenodex.zenocover.attack_query_manifest.v0"
REPORT_SCHEMA = "zenodex.zenocover.attack_query_report.v0"
DEFAULT_MANIFEST = ROOT / "internal" / "zenocover" / "ATTACK_QUERY_MANIFEST_V0.json"


def validate_zenocover_attack_queries_v0(
    manifest: Any,
    *,
    base_dir: str | Path = ROOT,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != MANIFEST_SCHEMA:
        errors.append("schema mismatch")

    reserve_report = validate_zenocover_reserve_solvency_v0(
        obj.get("reserve_solvency_manifest"),
        base_dir=base_dir,
    )
    claim_report = validate_zenocover_claim_verifier_model_v0(obj.get("claim_verifier_model"))
    withdrawal_report = validate_reserve_withdrawal_safety_v0(obj.get("reserve_withdrawal_safety"))
    if reserve_report.get("ok") is not True:
        errors.append("reserve solvency component rejected")
    if claim_report.get("ok") is not True:
        errors.append("claim verifier component rejected")
    if withdrawal_report.get("ok") is not True:
        errors.append("reserve withdrawal component rejected")

    consistency = _check_component_consistency(
        reserve_report=reserve_report,
        claim_report=claim_report,
        withdrawal_report=withdrawal_report,
    )
    if consistency["ok"] is not True:
        errors.append("component consistency rejected")

    attack_sweep = _run_cross_attack_query_sweep(
        claim_report=claim_report,
        withdrawal_report=withdrawal_report,
        max_examples=_int_or_default(obj.get("max_unsafe_examples"), 8),
    )
    if attack_sweep["ok"] is not True:
        errors.append("cross attack query sweep found unsafe example")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "component_status": {
            "reserve_solvency": reserve_report.get("status"),
            "claim_verifier": claim_report.get("status"),
            "reserve_withdrawal": withdrawal_report.get("status"),
        },
        "consistency": consistency,
        "cross_attack_query_sweep": attack_sweep,
        "reserve_solvency": reserve_report,
        "claim_verifier": claim_report,
        "reserve_withdrawal": withdrawal_report,
    }


def _check_component_consistency(
    *,
    reserve_report: Mapping[str, Any],
    claim_report: Mapping[str, Any],
    withdrawal_report: Mapping[str, Any],
) -> dict[str, Any]:
    errors: list[str] = []
    reserve_facts = _facts(reserve_report)
    policy_facts = _facts(claim_report.get("policy"))
    pool_facts = _facts(withdrawal_report.get("pool"))

    reserve_asset = reserve_facts.get("reserve_asset")
    settlement_asset = policy_facts.get("settlement_asset")
    pool_asset = pool_facts.get("reserve_asset")
    if _all_not_none(reserve_asset, settlement_asset) and reserve_asset != settlement_asset:
        errors.append("reserve asset must match claim settlement asset")
    if _all_not_none(reserve_asset, pool_asset) and reserve_asset != pool_asset:
        errors.append("reserve asset must match withdrawal pool asset")

    reserve_balance = _optional_int(reserve_facts.get("reserve_balance"))
    policy_reserve = _optional_int(policy_facts.get("reserve_available"))
    pool_reserve = _optional_int(pool_facts.get("reserve_balance"))
    if _all_not_none(reserve_balance, policy_reserve) and reserve_balance != policy_reserve:
        errors.append("reserve balance must match claim verifier reserve_available")
    if _all_not_none(reserve_balance, pool_reserve) and reserve_balance != pool_reserve:
        errors.append("reserve balance must match withdrawal pool reserve_balance")

    active_required = _optional_int(reserve_facts.get("active_required_collateral"))
    active_liability = _optional_int(pool_facts.get("active_liability"))
    if _all_not_none(active_required, active_liability) and active_liability < active_required:
        errors.append("withdrawal active_liability is below reserve-solvency active required collateral")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "reserve_asset": reserve_asset,
            "settlement_asset": settlement_asset,
            "pool_asset": pool_asset,
            "reserve_balance": reserve_balance,
            "policy_reserve_available": policy_reserve,
            "pool_reserve_balance": pool_reserve,
            "active_required_collateral": active_required,
            "withdrawal_active_liability": active_liability,
        },
    }


def _run_cross_attack_query_sweep(
    *,
    claim_report: Mapping[str, Any],
    withdrawal_report: Mapping[str, Any],
    max_examples: int,
) -> dict[str, Any]:
    policy_facts = _facts(claim_report.get("policy"))
    pool_facts = _facts(withdrawal_report.get("pool"))
    reserve_balance = _optional_int(pool_facts.get("reserve_balance"))
    active_liability = _optional_int(pool_facts.get("active_liability"))
    pending_liability = _optional_int(pool_facts.get("pending_claim_window_liability"))
    min_surplus = _optional_int(pool_facts.get("min_surplus"))
    aggregate_cap = _optional_int(policy_facts.get("aggregate_payout_cap"))
    min_reserve_after_payout = _optional_int(policy_facts.get("min_reserve_after_payout"))
    per_claim_cap = _optional_int(policy_facts.get("per_claim_cap")) or 0

    required = (
        reserve_balance,
        active_liability,
        pending_liability,
        min_surplus,
        aggregate_cap,
        min_reserve_after_payout,
    )
    if any(value is None for value in required):
        return {
            "ok": False,
            "checked_cases": 0,
            "unsafe_examples": [
                {
                    "query": "cross_surface_prerequisites_present",
                    "reason": "required policy or pool facts are missing",
                }
            ],
            "queries": _query_names(),
        }

    reserve = int(reserve_balance)
    active = int(active_liability)
    pending = int(pending_liability)
    surplus = int(min_surplus)
    cap = int(aggregate_cap)
    policy_floor = int(min_reserve_after_payout)
    amount_values = _attack_amount_values(
        reserve_balance=reserve,
        active_liability=active,
        pending_claim_window_liability=pending,
        min_surplus=surplus,
        aggregate_payout_cap=cap,
        min_reserve_after_payout=policy_floor,
        per_claim_cap=per_claim_cap,
    )

    unsafe_examples: list[dict[str, Any]] = []
    checked = 0
    if reserve - cap < policy_floor:
        unsafe_examples.append(
            {
                "query": "aggregate_cap_breaches_policy_reserve_floor",
                "reserve_balance": reserve,
                "aggregate_payout_cap": cap,
                "post_claim_reserve": reserve - cap,
                "min_reserve_after_payout": policy_floor,
            }
        )

    for cooldown_complete, claim_window_closed, amount in product((False, True), (False, True), amount_values):
        accepted, liability_floor = _withdrawal_acceptance(
            reserve_balance=reserve,
            active_liability=active,
            pending_claim_window_liability=pending,
            min_surplus=surplus,
            amount=amount,
            cooldown_complete=cooldown_complete,
            claim_window_closed=claim_window_closed,
        )
        checked += 1
        if accepted and not claim_window_closed:
            post_withdrawal = reserve - amount
            post_worst_claim = post_withdrawal - cap
            if post_worst_claim < policy_floor:
                unsafe_examples.append(
                    {
                        "query": "withdraw_then_worst_claim_breaches_policy_reserve_floor",
                        "amount": amount,
                        "post_withdrawal_reserve": post_withdrawal,
                        "aggregate_payout_cap": cap,
                        "post_worst_claim_reserve": post_worst_claim,
                        "min_reserve_after_payout": policy_floor,
                        "liability_floor": liability_floor,
                    }
                )
        if len(unsafe_examples) >= max_examples:
            break

    post_claim_reserve = reserve - cap
    for cooldown_complete, claim_window_closed, amount in product((False, True), (False, True), amount_values):
        accepted, liability_floor = _withdrawal_acceptance(
            reserve_balance=post_claim_reserve,
            active_liability=active,
            pending_claim_window_liability=pending,
            min_surplus=surplus,
            amount=amount,
            cooldown_complete=cooldown_complete,
            claim_window_closed=claim_window_closed,
        )
        checked += 1
        if accepted:
            post_sequence = post_claim_reserve - amount
            required_floor = max(policy_floor, liability_floor)
            if post_sequence < required_floor:
                unsafe_examples.append(
                    {
                        "query": "worst_claim_then_withdraw_breaches_combined_floor",
                        "amount": amount,
                        "post_claim_reserve": post_claim_reserve,
                        "post_sequence_reserve": post_sequence,
                        "combined_floor": required_floor,
                        "policy_floor": policy_floor,
                        "liability_floor": liability_floor,
                    }
                )
        if len(unsafe_examples) >= max_examples:
            break

    return {
        "ok": not unsafe_examples,
        "checked_cases": checked,
        "unsafe_examples": unsafe_examples,
        "queries": _query_names(),
        "bounds": {
            "amount_values": amount_values,
            "aggregate_payout_cap": cap,
            "min_reserve_after_payout": policy_floor,
            "reserve_balance": reserve,
        },
    }


def _attack_amount_values(
    *,
    reserve_balance: int,
    active_liability: int,
    pending_claim_window_liability: int,
    min_surplus: int,
    aggregate_payout_cap: int,
    min_reserve_after_payout: int,
    per_claim_cap: int,
) -> list[int]:
    open_floor = active_liability + pending_claim_window_liability + min_surplus
    closed_floor = active_liability + min_surplus
    claim_spendable = reserve_balance - aggregate_payout_cap - min_reserve_after_payout
    values = {
        0,
        1,
        per_claim_cap,
        aggregate_payout_cap,
        max(0, reserve_balance - open_floor),
        max(0, reserve_balance - closed_floor),
        max(0, claim_spendable),
        max(0, claim_spendable + 1),
        reserve_balance,
        reserve_balance + 1,
    }
    return sorted(values)


def _withdrawal_acceptance(
    *,
    reserve_balance: int,
    active_liability: int,
    pending_claim_window_liability: int,
    min_surplus: int,
    amount: int,
    cooldown_complete: bool,
    claim_window_closed: bool,
) -> tuple[bool, int]:
    pending_floor = 0 if claim_window_closed else pending_claim_window_liability
    liability_floor = active_liability + pending_floor + min_surplus
    if not cooldown_complete:
        return False, liability_floor
    if amount < 0:
        return False, liability_floor
    return reserve_balance - amount >= liability_floor, liability_floor


def _query_names() -> list[str]:
    return [
        "aggregate_cap_breaches_policy_reserve_floor",
        "withdraw_then_worst_claim_breaches_policy_reserve_floor",
        "worst_claim_then_withdraw_breaches_combined_floor",
    ]


def _facts(report_or_section: Any) -> Mapping[str, Any]:
    if isinstance(report_or_section, Mapping) and isinstance(report_or_section.get("facts"), Mapping):
        return report_or_section["facts"]
    return {}


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _optional_int(value: Any) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool):
        return int(value)
    return None


def _int_or_default(value: Any, default: int) -> int:
    if isinstance(value, int) and not isinstance(value, bool) and value > 0:
        return int(value)
    return default


def _all_not_none(*values: object) -> bool:
    return all(value is not None for value in values)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path, nargs="?", default=DEFAULT_MANIFEST)
    parser.add_argument("--base-dir", type=Path, default=ROOT)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    report = validate_zenocover_attack_queries_v0(manifest, base_dir=args.base_dir)
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Validate an internal ZenoCover reserve-withdrawal safety model."""

from __future__ import annotations

import argparse
import json
from itertools import product
from pathlib import Path
from typing import Any, Mapping

MANIFEST_SCHEMA = "zenodex.zenocover.reserve_withdrawal_safety.v0"
REPORT_SCHEMA = "zenodex.zenocover.reserve_withdrawal_safety_report.v0"


def validate_reserve_withdrawal_safety_v0(manifest: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != MANIFEST_SCHEMA:
        errors.append("schema mismatch")

    pool = _validate_pool(obj.get("pool"))
    requests = _validate_requests(obj.get("withdrawal_requests"), pool=pool)
    sweep = _run_attack_query_sweep(pool)

    if not pool["ok"]:
        errors.append("pool rejected")
    if not requests["ok"]:
        errors.append("one or more withdrawal requests rejected")
    if not sweep["ok"]:
        errors.append("attack query sweep found unsafe withdrawal")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "pool": pool,
        "withdrawal_requests": requests,
        "attack_query_sweep": sweep,
    }


def _validate_pool(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "pool", errors)
    reserve_asset = _str(obj.get("reserve_asset"), "pool.reserve_asset", errors)
    reserve_balance = _int_ge(obj.get("reserve_balance"), "pool.reserve_balance", errors, 0)
    active_liability = _int_ge(obj.get("active_liability"), "pool.active_liability", errors, 0)
    pending_claim_window_liability = _int_ge(
        obj.get("pending_claim_window_liability"),
        "pool.pending_claim_window_liability",
        errors,
        0,
    )
    min_surplus = _int_ge(obj.get("min_surplus"), "pool.min_surplus", errors, 0)
    if None not in (reserve_balance, active_liability, pending_claim_window_liability, min_surplus):
        initial_floor = int(active_liability) + int(pending_claim_window_liability) + int(min_surplus)
        if int(reserve_balance) < initial_floor:
            errors.append("reserve_balance below active and pending liability floor")
    else:
        initial_floor = None

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "reserve_asset": reserve_asset,
            "reserve_balance": reserve_balance,
            "active_liability": active_liability,
            "pending_claim_window_liability": pending_claim_window_liability,
            "min_surplus": min_surplus,
            "initial_liability_floor": initial_floor,
        },
    }


def _validate_requests(value: Any, *, pool: Mapping[str, Any]) -> dict[str, Any]:
    errors: list[str] = []
    requests_raw = value
    if not isinstance(requests_raw, list):
        errors.append("withdrawal_requests must be a list")
        requests_raw = []

    facts = pool.get("facts", {})
    current_reserve = _optional_int(facts.get("reserve_balance")) or 0
    active_liability = _optional_int(facts.get("active_liability")) or 0
    pending_liability = _optional_int(facts.get("pending_claim_window_liability")) or 0
    min_surplus = _optional_int(facts.get("min_surplus")) or 0
    seen_ids: set[str] = set()
    request_reports: list[dict[str, Any]] = []
    accepted_total = 0

    for index, item in enumerate(requests_raw):
        request_errors: list[str] = []
        request = _mapping(item, f"withdrawal_requests[{index}]", request_errors)
        request_id = _str(request.get("id"), f"withdrawal_requests[{index}].id", request_errors)
        amount = _int_ge(
            request.get("amount"),
            f"withdrawal_requests[{index}].amount",
            request_errors,
            0,
        )
        cooldown_complete = _bool(
            request.get("cooldown_complete"),
            f"withdrawal_requests[{index}].cooldown_complete",
            request_errors,
        )
        claim_window_closed = _bool(
            request.get("claim_window_closed"),
            f"withdrawal_requests[{index}].claim_window_closed",
            request_errors,
        )
        expected_accepted = _bool(
            request.get("expected_accepted"),
            f"withdrawal_requests[{index}].expected_accepted",
            request_errors,
        )
        expected_post_reserve = _int_ge(
            request.get("expected_post_reserve"),
            f"withdrawal_requests[{index}].expected_post_reserve",
            request_errors,
            0,
        )
        if request_id is not None:
            if request_id in seen_ids:
                request_errors.append("withdrawal request id must be unique")
            seen_ids.add(request_id)

        accepted = False
        post_reserve = current_reserve
        floor = None
        if None not in (amount, cooldown_complete, claim_window_closed):
            accepted, floor = _withdrawal_acceptance(
                reserve_balance=current_reserve,
                active_liability=active_liability,
                pending_claim_window_liability=pending_liability,
                min_surplus=min_surplus,
                amount=int(amount),
                cooldown_complete=bool(cooldown_complete),
                claim_window_closed=bool(claim_window_closed),
            )
            if accepted:
                post_reserve = current_reserve - int(amount)
                accepted_total += int(amount)
            if expected_accepted is not None and expected_accepted != accepted:
                request_errors.append("expected_accepted mismatch")
            if expected_post_reserve is not None and expected_post_reserve != post_reserve:
                request_errors.append("expected_post_reserve mismatch")
            if accepted and post_reserve < floor:
                request_errors.append("accepted withdrawal violates liability floor")
        current_reserve = post_reserve

        request_reports.append(
            {
                "id": request_id,
                "ok": not request_errors,
                "errors": request_errors,
                "facts": {
                    "amount": amount,
                    "cooldown_complete": cooldown_complete,
                    "claim_window_closed": claim_window_closed,
                    "expected_accepted": expected_accepted,
                    "accepted": accepted,
                    "liability_floor": floor,
                    "post_reserve": post_reserve,
                },
            }
        )

    if any(not report["ok"] for report in request_reports):
        errors.append("one or more withdrawal rows rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "accepted_withdrawal_total": accepted_total,
            "final_reserve_balance": current_reserve,
        },
        "items": request_reports,
    }


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


def _run_attack_query_sweep(pool: Mapping[str, Any]) -> dict[str, Any]:
    facts = pool.get("facts", {})
    reserve_balance = _optional_int(facts.get("reserve_balance")) or 0
    active_liability = _optional_int(facts.get("active_liability")) or 0
    pending_liability = _optional_int(facts.get("pending_claim_window_liability")) or 0
    min_surplus = _optional_int(facts.get("min_surplus")) or 0
    values = sorted({0, 1, reserve_balance, reserve_balance + 1})
    unsafe_examples: list[dict[str, Any]] = []
    checked = 0
    for cooldown_complete, claim_window_closed, amount in product((False, True), (False, True), values):
        accepted, floor = _withdrawal_acceptance(
            reserve_balance=reserve_balance,
            active_liability=active_liability,
            pending_claim_window_liability=pending_liability,
            min_surplus=min_surplus,
            amount=amount,
            cooldown_complete=cooldown_complete,
            claim_window_closed=claim_window_closed,
        )
        checked += 1
        if accepted and reserve_balance - amount < floor:
            unsafe_examples.append(
                {
                    "cooldown_complete": cooldown_complete,
                    "claim_window_closed": claim_window_closed,
                    "amount": amount,
                    "post_reserve": reserve_balance - amount,
                    "liability_floor": floor,
                }
            )

    return {
        "ok": not unsafe_examples,
        "checked_cases": checked,
        "unsafe_examples": unsafe_examples,
        "queries": [
            "withdraw_before_claim_window_closed_and_remaining_reserve_below_active_liability",
            "accepted_withdrawal_violates_liability_floor",
        ],
    }


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


def _bool(value: Any, name: str, errors: list[str]) -> bool | None:
    if not isinstance(value, bool):
        errors.append(f"{name} must be a bool")
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
    report = validate_reserve_withdrawal_safety_v0(manifest)
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

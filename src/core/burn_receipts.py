"""
Deterministic burn receipts backed by decomposed accounting rails.

This is the imperative-shell binding for the burn-receipt Tau work:
- replay/policy rail
- amount/budget rail
- supply rail
- batch-sum rail

The verifier is fail-closed and purely structural. It does not verify external
cryptography or nullifier storage directly; those facts must be supplied as
host flags in the receipt body.
"""

from __future__ import annotations

from typing import Any, Dict, Tuple

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex


def _receipt_int(value: Any) -> int:
    if isinstance(value, bool):
        raise TypeError("bool is not a burn receipt integer")
    return int(value)


def burn_receipt_hash(receipt_body: Dict[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes("zenodex.burn_receipt/v1") + canonical_json_bytes(receipt_body))


def _rail_replay_guard(*, do_burn: int, receipt_bound: int, nullifier_unused: int, policy_ok: int) -> bool:
    if do_burn not in (0, 1):
        return False
    if receipt_bound not in (0, 1) or nullifier_unused not in (0, 1) or policy_ok not in (0, 1):
        return False
    if do_burn == 0:
        return True
    return bool(receipt_bound == 1 and nullifier_unused == 1 and policy_ok == 1)


def _rail_amount_guard(*, do_burn: int, burn_amount: int, receipt_amount: int, burn_budget: int) -> bool:
    for v in (burn_amount, receipt_amount, burn_budget):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0x7FFF:
            return False
    if do_burn == 0:
        return burn_amount == 0 and receipt_amount == 0
    return bool(burn_amount > 0 and burn_amount == receipt_amount and burn_budget >= burn_amount)


def _rail_supply_guard(*, do_burn: int, burn_amount: int, supply_before: int, supply_after: int) -> bool:
    if not isinstance(burn_amount, int) or isinstance(burn_amount, bool) or burn_amount < 0 or burn_amount > 0x7FFF:
        return False
    for v in (supply_before, supply_after):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            return False
    if do_burn == 0:
        return supply_after == supply_before
    return bool(supply_before >= burn_amount and supply_after == supply_before - burn_amount)


def _rail_batch_sum_guard(*, do_burn: int, burn_amount: int, batch_burn_sum_before: int, batch_burn_sum_after: int) -> bool:
    if not isinstance(burn_amount, int) or isinstance(burn_amount, bool) or burn_amount < 0 or burn_amount > 0x7FFF:
        return False
    if not isinstance(batch_burn_sum_before, int) or isinstance(batch_burn_sum_before, bool) or batch_burn_sum_before < 0 or batch_burn_sum_before > 0x7FFF:
        return False
    if not isinstance(batch_burn_sum_after, int) or isinstance(batch_burn_sum_after, bool) or batch_burn_sum_after < 0 or batch_burn_sum_after > 0xFFFF:
        return False
    if do_burn == 0:
        return batch_burn_sum_after == batch_burn_sum_before
    return bool(batch_burn_sum_after == batch_burn_sum_before + burn_amount)


def make_burn_receipt(
    *,
    asset_id: str,
    batch_id: str,
    nullifier: str,
    tx_ref: str,
    policy_version: str,
    do_burn: int,
    receipt_bound: int,
    nullifier_unused: int,
    policy_ok: int,
    burn_amount: int,
    receipt_amount: int,
    burn_budget: int,
    supply_before: int,
    supply_after: int,
    batch_burn_sum_before: int,
    batch_burn_sum_after: int,
) -> Dict[str, Any]:
    body = {
        "schema": "zenodex/burn_receipt/v1",
        "asset_id": str(asset_id),
        "batch_id": str(batch_id),
        "nullifier": str(nullifier),
        "tx_ref": str(tx_ref),
        "policy_version": str(policy_version),
        "host": {
            "do_burn": int(do_burn),
            "receipt_bound": int(receipt_bound),
            "nullifier_unused": int(nullifier_unused),
            "policy_ok": int(policy_ok),
        },
        "accounting": {
            "burn_amount": int(burn_amount),
            "receipt_amount": int(receipt_amount),
            "burn_budget": int(burn_budget),
            "supply_before": int(supply_before),
            "supply_after": int(supply_after),
            "batch_burn_sum_before": int(batch_burn_sum_before),
            "batch_burn_sum_after": int(batch_burn_sum_after),
        },
    }
    return {"body": body, "receipt_hash": burn_receipt_hash(body)}


def verify_burn_receipt(receipt: object) -> Tuple[bool, str]:
    if not isinstance(receipt, dict):
        return False, "bad_receipt_type"
    body = receipt.get("body")
    if not isinstance(body, dict):
        return False, "missing_body"
    if body.get("schema") != "zenodex/burn_receipt/v1":
        return False, "bad_schema"

    want_hash = receipt.get("receipt_hash")
    if not isinstance(want_hash, str) or not want_hash:
        return False, "missing_receipt_hash"
    if burn_receipt_hash(body) != want_hash:
        return False, "hash_mismatch"

    for key in ("asset_id", "batch_id", "nullifier", "tx_ref", "policy_version"):
        val = body.get(key)
        if not isinstance(val, str) or not val:
            return False, f"bad_{key}"

    host = body.get("host")
    accounting = body.get("accounting")
    if not isinstance(host, dict):
        return False, "bad_host"
    if not isinstance(accounting, dict):
        return False, "bad_accounting"

    try:
        do_burn = _receipt_int(host.get("do_burn"))
        receipt_bound = _receipt_int(host.get("receipt_bound"))
        nullifier_unused = _receipt_int(host.get("nullifier_unused"))
        policy_ok = _receipt_int(host.get("policy_ok"))
        burn_amount = _receipt_int(accounting.get("burn_amount"))
        receipt_amount = _receipt_int(accounting.get("receipt_amount"))
        burn_budget = _receipt_int(accounting.get("burn_budget"))
        supply_before = _receipt_int(accounting.get("supply_before"))
        supply_after = _receipt_int(accounting.get("supply_after"))
        batch_burn_sum_before = _receipt_int(accounting.get("batch_burn_sum_before"))
        batch_burn_sum_after = _receipt_int(accounting.get("batch_burn_sum_after"))
    except (TypeError, ValueError, OverflowError):
        return False, "bad_numeric_field"

    if not _rail_replay_guard(
        do_burn=do_burn,
        receipt_bound=receipt_bound,
        nullifier_unused=nullifier_unused,
        policy_ok=policy_ok,
    ):
        return False, "replay_guard_failed"
    if not _rail_amount_guard(
        do_burn=do_burn,
        burn_amount=burn_amount,
        receipt_amount=receipt_amount,
        burn_budget=burn_budget,
    ):
        return False, "amount_guard_failed"
    if not _rail_supply_guard(
        do_burn=do_burn,
        burn_amount=burn_amount,
        supply_before=supply_before,
        supply_after=supply_after,
    ):
        return False, "supply_guard_failed"
    if not _rail_batch_sum_guard(
        do_burn=do_burn,
        burn_amount=burn_amount,
        batch_burn_sum_before=batch_burn_sum_before,
        batch_burn_sum_after=batch_burn_sum_after,
    ):
        return False, "batch_sum_guard_failed"
    return True, "ok"

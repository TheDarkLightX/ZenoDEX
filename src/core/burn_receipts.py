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

from dataclasses import dataclass
from typing import Any, Dict, Tuple

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

_IDENTITY_KEYS = ("asset_id", "batch_id", "nullifier", "tx_ref", "policy_version")


@dataclass(frozen=True)
class _BurnReceiptNumbers:
    do_burn: int
    receipt_bound: int
    nullifier_unused: int
    policy_ok: int
    burn_amount: int
    receipt_amount: int
    burn_budget: int
    supply_before: int
    supply_after: int
    batch_burn_sum_before: int
    batch_burn_sum_after: int


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


def _validate_burn_receipt_identity(body: Dict[str, Any]) -> str | None:
    for key in _IDENTITY_KEYS:
        val = body.get(key)
        if not isinstance(val, str) or not val:
            return f"bad_{key}"
    return None


def _parse_burn_receipt_numbers(host: Dict[str, Any], accounting: Dict[str, Any]) -> _BurnReceiptNumbers:
    return _BurnReceiptNumbers(
        do_burn=_receipt_int(host.get("do_burn")),
        receipt_bound=_receipt_int(host.get("receipt_bound")),
        nullifier_unused=_receipt_int(host.get("nullifier_unused")),
        policy_ok=_receipt_int(host.get("policy_ok")),
        burn_amount=_receipt_int(accounting.get("burn_amount")),
        receipt_amount=_receipt_int(accounting.get("receipt_amount")),
        burn_budget=_receipt_int(accounting.get("burn_budget")),
        supply_before=_receipt_int(accounting.get("supply_before")),
        supply_after=_receipt_int(accounting.get("supply_after")),
        batch_burn_sum_before=_receipt_int(accounting.get("batch_burn_sum_before")),
        batch_burn_sum_after=_receipt_int(accounting.get("batch_burn_sum_after")),
    )


def _burn_receipt_rail_error(numbers: _BurnReceiptNumbers) -> str | None:
    if not _rail_replay_guard(
        do_burn=numbers.do_burn,
        receipt_bound=numbers.receipt_bound,
        nullifier_unused=numbers.nullifier_unused,
        policy_ok=numbers.policy_ok,
    ):
        return "replay_guard_failed"
    if not _rail_amount_guard(
        do_burn=numbers.do_burn,
        burn_amount=numbers.burn_amount,
        receipt_amount=numbers.receipt_amount,
        burn_budget=numbers.burn_budget,
    ):
        return "amount_guard_failed"
    if not _rail_supply_guard(
        do_burn=numbers.do_burn,
        burn_amount=numbers.burn_amount,
        supply_before=numbers.supply_before,
        supply_after=numbers.supply_after,
    ):
        return "supply_guard_failed"
    if not _rail_batch_sum_guard(
        do_burn=numbers.do_burn,
        burn_amount=numbers.burn_amount,
        batch_burn_sum_before=numbers.batch_burn_sum_before,
        batch_burn_sum_after=numbers.batch_burn_sum_after,
    ):
        return "batch_sum_guard_failed"
    return None


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
            "do_burn": _receipt_int(do_burn),
            "receipt_bound": _receipt_int(receipt_bound),
            "nullifier_unused": _receipt_int(nullifier_unused),
            "policy_ok": _receipt_int(policy_ok),
        },
        "accounting": {
            "burn_amount": _receipt_int(burn_amount),
            "receipt_amount": _receipt_int(receipt_amount),
            "burn_budget": _receipt_int(burn_budget),
            "supply_before": _receipt_int(supply_before),
            "supply_after": _receipt_int(supply_after),
            "batch_burn_sum_before": _receipt_int(batch_burn_sum_before),
            "batch_burn_sum_after": _receipt_int(batch_burn_sum_after),
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
    try:
        actual_hash = burn_receipt_hash(body)
    except (TypeError, ValueError, OverflowError):
        return False, "bad_body_encoding"
    if actual_hash != want_hash:
        return False, "hash_mismatch"

    identity_error = _validate_burn_receipt_identity(body)
    if identity_error is not None:
        return False, identity_error

    host = body.get("host")
    accounting = body.get("accounting")
    if not isinstance(host, dict):
        return False, "bad_host"
    if not isinstance(accounting, dict):
        return False, "bad_accounting"

    try:
        numbers = _parse_burn_receipt_numbers(host, accounting)
    except (TypeError, ValueError, OverflowError):
        return False, "bad_numeric_field"

    rail_error = _burn_receipt_rail_error(numbers)
    if rail_error is not None:
        return False, rail_error
    return True, "ok"

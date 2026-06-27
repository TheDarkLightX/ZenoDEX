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

from ..runtime.authority import AuthorityMode, active_mode, decide
from ..runtime.rust_invoker import burn_rails_verify, canonical_domain_json_hash
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

_BURN_RECEIPT_HASH_LABEL = "zenodex.burn_receipt/v1"
BURN_RECEIPTS_SURFACE = "burn_receipts"
_BURN_RAIL_FIELDS = (
    "do_burn",
    "receipt_bound",
    "nullifier_unused",
    "policy_ok",
    "burn_amount",
    "receipt_amount",
    "burn_budget",
    "supply_before",
    "supply_after",
    "batch_burn_sum_before",
    "batch_burn_sum_after",
)


def _require_burn_receipt_int(value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError("burn receipt numeric fields must be strict ints")
    return int(value)


def _burn_receipt_hash_python(receipt_body: Dict[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes(_BURN_RECEIPT_HASH_LABEL) + canonical_json_bytes(receipt_body))


def burn_receipt_hash(receipt_body: Dict[str, Any]) -> str:
    """Authority-gated burn-receipt body hash using the canonical surface."""

    mode = active_mode("canonical")
    if mode is AuthorityMode.PYTHON_AUTHORITY:
        return _burn_receipt_hash_python(receipt_body)
    return decide(
        "canonical",
        mode,
        python_fn=lambda: _burn_receipt_hash_python(receipt_body),
        rust_fn=lambda: canonical_domain_json_hash(_BURN_RECEIPT_HASH_LABEL, receipt_body),
        compare=lambda python_hash, rust_hash: python_hash == rust_hash,
    ).result


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


def _verify_burn_rails_python(**kwargs: int) -> Tuple[bool, str]:
    if not _rail_replay_guard(
        do_burn=kwargs["do_burn"],
        receipt_bound=kwargs["receipt_bound"],
        nullifier_unused=kwargs["nullifier_unused"],
        policy_ok=kwargs["policy_ok"],
    ):
        return False, "replay_guard_failed"
    if not _rail_amount_guard(
        do_burn=kwargs["do_burn"],
        burn_amount=kwargs["burn_amount"],
        receipt_amount=kwargs["receipt_amount"],
        burn_budget=kwargs["burn_budget"],
    ):
        return False, "amount_guard_failed"
    if not _rail_supply_guard(
        do_burn=kwargs["do_burn"],
        burn_amount=kwargs["burn_amount"],
        supply_before=kwargs["supply_before"],
        supply_after=kwargs["supply_after"],
    ):
        return False, "supply_guard_failed"
    if not _rail_batch_sum_guard(
        do_burn=kwargs["do_burn"],
        burn_amount=kwargs["burn_amount"],
        batch_burn_sum_before=kwargs["batch_burn_sum_before"],
        batch_burn_sum_after=kwargs["batch_burn_sum_after"],
    ):
        return False, "batch_sum_guard_failed"
    return True, "ok"


def _rail_result_doc(result: Tuple[bool, str]) -> Dict[str, Any]:
    ok, reason = result
    return {"accept": ok, "reason": "ok" if ok else reason}


def _rust_rail_result_doc(tx: Dict[str, int]) -> Dict[str, Any]:
    out = burn_rails_verify(tx=tx)
    if (
        out.get("version") != 1
        or out.get("kernel") != BURN_RECEIPTS_SURFACE
        or not isinstance(out.get("accept"), bool)
        or not isinstance(out.get("pre_state_root"), str)
        or not isinstance(out.get("post_state_root"), str)
    ):
        raise ValueError("malformed burn rail authority output")
    if out["accept"]:
        if not isinstance(out.get("receipt_hash"), str) or out.get("reject_reason") is not None:
            raise ValueError("malformed accepted burn rail authority output")
    elif not isinstance(out.get("reject_reason"), str) or out.get("receipt_hash") is not None:
        raise ValueError("malformed rejected burn rail authority output")
    return {
        "accept": bool(out["accept"]),
        "reason": "ok" if out["accept"] else str(out["reject_reason"]),
    }


def _verify_burn_rails_authority(**kwargs: int) -> Tuple[bool, str]:
    mode = active_mode(BURN_RECEIPTS_SURFACE)
    if mode is AuthorityMode.PYTHON_AUTHORITY:
        return _verify_burn_rails_python(**kwargs)

    tx = {field: kwargs[field] for field in _BURN_RAIL_FIELDS}
    decision = decide(
        BURN_RECEIPTS_SURFACE,
        mode,
        python_fn=lambda: _rail_result_doc(_verify_burn_rails_python(**kwargs)),
        rust_fn=lambda: _rust_rail_result_doc(tx),
    )
    result = decision.result
    return bool(result["accept"]), str(result["reason"])


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


def verify_burn_receipt(receipt: Dict[str, Any]) -> Tuple[bool, str]:
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
        do_burn = _require_burn_receipt_int(host.get("do_burn"))
        receipt_bound = _require_burn_receipt_int(host.get("receipt_bound"))
        nullifier_unused = _require_burn_receipt_int(host.get("nullifier_unused"))
        policy_ok = _require_burn_receipt_int(host.get("policy_ok"))
        burn_amount = _require_burn_receipt_int(accounting.get("burn_amount"))
        receipt_amount = _require_burn_receipt_int(accounting.get("receipt_amount"))
        burn_budget = _require_burn_receipt_int(accounting.get("burn_budget"))
        supply_before = _require_burn_receipt_int(accounting.get("supply_before"))
        supply_after = _require_burn_receipt_int(accounting.get("supply_after"))
        batch_burn_sum_before = _require_burn_receipt_int(accounting.get("batch_burn_sum_before"))
        batch_burn_sum_after = _require_burn_receipt_int(accounting.get("batch_burn_sum_after"))
    except (TypeError, ValueError):
        return False, "bad_numeric_field"

    return _verify_burn_rails_authority(
        do_burn=do_burn,
        receipt_bound=receipt_bound,
        nullifier_unused=nullifier_unused,
        policy_ok=policy_ok,
        burn_amount=burn_amount,
        receipt_amount=receipt_amount,
        burn_budget=burn_budget,
        supply_before=supply_before,
        supply_after=supply_after,
        batch_burn_sum_before=batch_burn_sum_before,
        batch_burn_sum_after=batch_burn_sum_after,
    )

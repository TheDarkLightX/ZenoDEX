"""
Deterministic receipts for TEE-attested confidential extensions.

This module is intentionally narrow:
- It binds a metered extension execution to an approved enclave measurement.
- It checks local accounting and attestation freshness.
- It does not implement remote attestation cryptography itself.

Production attestation verification remains an external step. The output of that step
is reduced here to an approved measurement allowlist plus bounded epoch freshness.
"""

from __future__ import annotations

from typing import AbstractSet, Any, Dict, Iterable, Tuple

from ..state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes, domain_sep_bytes, sha256_hex


MAX_FEE = 0x7FFF
MAX_BALANCE = 0xFFFF
MAX_EPOCH = 0xFFFF
MAX_ATTESTATION_AGE = 0xFF
DEFAULT_POLICY_DIGEST = "0x" + ("0" * 64)


def confidential_extension_receipt_hash(receipt_body: Dict[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes("zenodex.confidential_extension_receipt/v1") + canonical_json_bytes(receipt_body))


def _to_measurement_set(values: Iterable[str] | AbstractSet[str]) -> set[str]:
    out = {str(v) for v in values}
    out.discard("")
    return out


def _canonical_policy_digest(value: object, *, name: str = "policy_digest") -> str:
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)  # type: ignore[arg-type]


def _fresh_attestation(*, current_epoch: int, attestation_epoch: int, max_attestation_age: int) -> bool:
    for value, upper in (
        (current_epoch, MAX_EPOCH),
        (attestation_epoch, MAX_EPOCH),
        (max_attestation_age, MAX_ATTESTATION_AGE),
    ):
        if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > upper:
            return False
    if attestation_epoch > current_epoch:
        return False
    return (current_epoch - attestation_epoch) <= max_attestation_age


def _accounting_ok(
    *,
    do_execute: int,
    fee_charged: int,
    receipt_fee: int,
    credit_before: int,
    credit_after: int,
    provider_balance_before: int,
    provider_balance_after: int,
) -> bool:
    for value, upper in (
        (fee_charged, MAX_FEE),
        (receipt_fee, MAX_FEE),
        (credit_before, MAX_BALANCE),
        (credit_after, MAX_BALANCE),
        (provider_balance_before, MAX_BALANCE),
        (provider_balance_after, MAX_BALANCE),
    ):
        if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > upper:
            return False
    if do_execute == 0:
        return (
            fee_charged == 0
            and receipt_fee == 0
            and credit_after == credit_before
            and provider_balance_after == provider_balance_before
        )
    return (
        fee_charged > 0
        and fee_charged == receipt_fee
        and credit_before >= fee_charged
        and credit_after == (credit_before - fee_charged)
        and provider_balance_after == (provider_balance_before + fee_charged)
        and provider_balance_after <= MAX_BALANCE
    )


def make_confidential_extension_receipt(
    *,
    extension_id: str,
    provider_id: str,
    request_id: str,
    policy_version: str,
    policy_digest: str = DEFAULT_POLICY_DIGEST,
    measurement: str,
    do_execute: int,
    policy_ok: int,
    nonce_unused: int,
    output_bound_ok: int,
    current_epoch: int,
    attestation_epoch: int,
    max_attestation_age: int,
    fee_charged: int,
    receipt_fee: int,
    credit_before: int,
    credit_after: int,
    provider_balance_before: int,
    provider_balance_after: int,
) -> Dict[str, Any]:
    canonical_policy_digest = _canonical_policy_digest(policy_digest)
    body = {
        "schema": "zenodex/confidential_extension_receipt/v1",
        "extension_id": str(extension_id),
        "provider_id": str(provider_id),
        "request_id": str(request_id),
        "policy_version": str(policy_version),
        "policy_digest": canonical_policy_digest,
        "measurement": str(measurement),
        "host": {
            "do_execute": int(do_execute),
            "policy_ok": int(policy_ok),
            "nonce_unused": int(nonce_unused),
            "output_bound_ok": int(output_bound_ok),
        },
        "attestation": {
            "current_epoch": int(current_epoch),
            "attestation_epoch": int(attestation_epoch),
            "max_attestation_age": int(max_attestation_age),
        },
        "accounting": {
            "fee_charged": int(fee_charged),
            "receipt_fee": int(receipt_fee),
            "credit_before": int(credit_before),
            "credit_after": int(credit_after),
            "provider_balance_before": int(provider_balance_before),
            "provider_balance_after": int(provider_balance_after),
        },
    }
    return {"body": body, "receipt_hash": confidential_extension_receipt_hash(body)}


def verify_confidential_extension_receipt(
    receipt: Dict[str, Any],
    *,
    approved_measurements: Iterable[str] | AbstractSet[str],
) -> Tuple[bool, str]:
    if not isinstance(receipt, dict):
        return False, "bad_receipt_type"
    body = receipt.get("body")
    if not isinstance(body, dict):
        return False, "missing_body"
    if body.get("schema") != "zenodex/confidential_extension_receipt/v1":
        return False, "bad_schema"

    want_hash = receipt.get("receipt_hash")
    if not isinstance(want_hash, str) or not want_hash:
        return False, "missing_receipt_hash"
    if confidential_extension_receipt_hash(body) != want_hash:
        return False, "hash_mismatch"

    for key in ("extension_id", "provider_id", "request_id", "policy_version", "measurement"):
        val = body.get(key)
        if not isinstance(val, str) or not val:
            return False, f"bad_{key}"
    try:
        canonical_policy_digest = _canonical_policy_digest(body.get("policy_digest"))
    except Exception:
        return False, "bad_policy_digest"
    if body.get("policy_digest") != canonical_policy_digest:
        return False, "bad_policy_digest"

    if body["measurement"] not in _to_measurement_set(approved_measurements):
        return False, "measurement_not_approved"

    host = body.get("host")
    attestation = body.get("attestation")
    accounting = body.get("accounting")
    if not isinstance(host, dict):
        return False, "bad_host"
    if not isinstance(attestation, dict):
        return False, "bad_attestation"
    if not isinstance(accounting, dict):
        return False, "bad_accounting"

    try:
        do_execute = int(host.get("do_execute"))
        policy_ok = int(host.get("policy_ok"))
        nonce_unused = int(host.get("nonce_unused"))
        output_bound_ok = int(host.get("output_bound_ok"))
        current_epoch = int(attestation.get("current_epoch"))
        attestation_epoch = int(attestation.get("attestation_epoch"))
        max_attestation_age = int(attestation.get("max_attestation_age"))
        fee_charged = int(accounting.get("fee_charged"))
        receipt_fee = int(accounting.get("receipt_fee"))
        credit_before = int(accounting.get("credit_before"))
        credit_after = int(accounting.get("credit_after"))
        provider_balance_before = int(accounting.get("provider_balance_before"))
        provider_balance_after = int(accounting.get("provider_balance_after"))
    except Exception:
        return False, "bad_numeric_field"

    if do_execute not in (0, 1):
        return False, "bad_do_execute"
    for flag, name in ((policy_ok, "policy_ok"), (nonce_unused, "nonce_unused"), (output_bound_ok, "output_bound_ok")):
        if flag not in (0, 1):
            return False, f"bad_{name}"

    if not _fresh_attestation(
        current_epoch=current_epoch,
        attestation_epoch=attestation_epoch,
        max_attestation_age=max_attestation_age,
    ):
        return False, "stale_attestation"

    if do_execute == 1 and not (policy_ok == 1 and nonce_unused == 1 and output_bound_ok == 1):
        return False, "attestation_guard_failed"

    if not _accounting_ok(
        do_execute=do_execute,
        fee_charged=fee_charged,
        receipt_fee=receipt_fee,
        credit_before=credit_before,
        credit_after=credit_after,
        provider_balance_before=provider_balance_before,
        provider_balance_after=provider_balance_after,
    ):
        return False, "accounting_guard_failed"
    return True, "ok"

from __future__ import annotations

from dataclasses import dataclass
from typing import AbstractSet, Any, Iterable, Mapping

from ..state.canonical import canonical_hex_fixed_allow_0x
from ..state.confidential_requests import (
    ConfidentialRequestKey,
    ConfidentialRequestTable,
    copy_confidential_request_table,
    evaluate_confidential_request_use_transition,
)
from .confidential_extension_receipts import verify_confidential_extension_receipt


def _canonical_policy_digest(value: object, *, name: str) -> str:
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)


def _require_flag(value: Any, *, name: str) -> bool:
    if isinstance(value, bool):
        return bool(value)
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be a bool or 0/1 int")
    if value not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1")
    return bool(value)


@dataclass(frozen=True)
class ConfidentialExtensionLiveAdmissionOutcome:
    do_execute_ok: bool
    receipt_verified_ok: bool
    policy_digest_match_ok: bool
    request_used_before: bool
    request_unused_ok: bool
    request_used_after: bool
    admission_ok: bool


def evaluate_confidential_extension_live_admission_gate(
    *,
    do_execute: Any,
    receipt_verified: Any,
    policy_digest_match: Any,
    request_used_before: Any,
) -> ConfidentialExtensionLiveAdmissionOutcome:
    do_execute_ok = _require_flag(do_execute, name="do_execute")
    receipt_verified_ok = _require_flag(receipt_verified, name="receipt_verified")
    policy_digest_match_ok = _require_flag(policy_digest_match, name="policy_digest_match")
    request_used = _require_flag(request_used_before, name="request_used_before")
    request_unused_ok = not request_used
    admission_ok = bool(
        do_execute_ok
        and receipt_verified_ok
        and policy_digest_match_ok
        and request_unused_ok
    )
    request_used_after = bool(request_used or admission_ok)
    return ConfidentialExtensionLiveAdmissionOutcome(
        do_execute_ok=do_execute_ok,
        receipt_verified_ok=receipt_verified_ok,
        policy_digest_match_ok=policy_digest_match_ok,
        request_used_before=request_used,
        request_unused_ok=request_unused_ok,
        request_used_after=request_used_after,
        admission_ok=admission_ok,
    )


def validate_confidential_extension_live_admission(
    *,
    receipt: Mapping[str, Any],
    approved_measurements: Iterable[str] | AbstractSet[str],
    expected_policy_digest: str,
    request_table: ConfidentialRequestTable,
) -> tuple[bool, str | None, ConfidentialRequestTable | None]:
    if not isinstance(receipt, Mapping):
        return False, "bad_receipt_type", None
    if not isinstance(request_table, ConfidentialRequestTable):
        raise TypeError("request_table must be a ConfidentialRequestTable")
    try:
        canonical_expected_policy_digest = _canonical_policy_digest(
            expected_policy_digest,
            name="expected_policy_digest",
        )
    except (TypeError, ValueError):
        return False, "bad_expected_policy_digest", None
    ok, err = verify_confidential_extension_receipt(
        dict(receipt),
        approved_measurements=approved_measurements,
    )
    if not ok:
        return False, err, None
    body = receipt.get("body")
    if not isinstance(body, Mapping):
        return False, "missing_body", None
    host = body.get("host")
    if not isinstance(host, Mapping):
        return False, "bad_host", None
    key = ConfidentialRequestKey(
        extension_id=str(body["extension_id"]),
        provider_id=str(body["provider_id"]),
        request_id=str(body["request_id"]),
    )
    updated = copy_confidential_request_table(request_table)
    request_used_before = updated.is_used(key)
    gate = evaluate_confidential_extension_live_admission_gate(
        do_execute=host.get("do_execute"),
        receipt_verified=True,
        policy_digest_match=body.get("policy_digest") == canonical_expected_policy_digest,
        request_used_before=request_used_before,
    )
    request_transition = evaluate_confidential_request_use_transition(
        request_used_before=request_used_before,
        consume_request=gate.admission_ok,
    )
    if not gate.do_execute_ok:
        return False, "not_executed", None
    if not gate.policy_digest_match_ok:
        return False, "policy_digest_mismatch", None
    if not request_transition.request_unused_ok:
        return False, "request_replay", None
    if request_transition.consume_applied:
        updated.mark_used(key)
    return True, None, updated

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

INTENT_NONCE_BATCH_POLICY_OK_PROCEED = "OkProceed"
INTENT_NONCE_BATCH_POLICY_OK_COPY = "OkCopy"
INTENT_NONCE_BATCH_POLICY_MISSING_INVALID_NONCE = "MissingInvalidNonce"
INTENT_NONCE_BATCH_POLICY_MIXED_PRESENCE = "MixedPresence"


def _require_bool(value: Any, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


@dataclass(frozen=True)
class IntentNonceBatchPolicyDecision:
    batch_ok: bool
    return_copy: bool
    reject_code: str


def evaluate_intent_nonce_batch_policy_gate(
    *,
    empty_batch: Any,
    require_all_nonces: Any,
    saw_nonce: Any,
    saw_missing: Any,
) -> IntentNonceBatchPolicyDecision:
    empty = _require_bool(empty_batch, name="empty_batch")
    require = _require_bool(require_all_nonces, name="require_all_nonces")
    saw_nonce_flag = _require_bool(saw_nonce, name="saw_nonce")
    saw_missing_flag = _require_bool(saw_missing, name="saw_missing")

    if empty:
        return IntentNonceBatchPolicyDecision(
            batch_ok=True,
            return_copy=True,
            reject_code=INTENT_NONCE_BATCH_POLICY_OK_COPY,
        )
    if require and saw_missing_flag:
        return IntentNonceBatchPolicyDecision(
            batch_ok=False,
            return_copy=False,
            reject_code=INTENT_NONCE_BATCH_POLICY_MISSING_INVALID_NONCE,
        )
    if saw_nonce_flag and saw_missing_flag:
        return IntentNonceBatchPolicyDecision(
            batch_ok=False,
            return_copy=False,
            reject_code=INTENT_NONCE_BATCH_POLICY_MIXED_PRESENCE,
        )
    if not saw_nonce_flag:
        return IntentNonceBatchPolicyDecision(
            batch_ok=True,
            return_copy=True,
            reject_code=INTENT_NONCE_BATCH_POLICY_OK_COPY,
        )
    return IntentNonceBatchPolicyDecision(
        batch_ok=True,
        return_copy=False,
        reject_code=INTENT_NONCE_BATCH_POLICY_OK_PROCEED,
    )


def intent_nonce_batch_policy_error(decision: IntentNonceBatchPolicyDecision) -> str | None:
    if decision.reject_code == INTENT_NONCE_BATCH_POLICY_MISSING_INVALID_NONCE:
        return "Missing/invalid nonce"
    if decision.reject_code == INTENT_NONCE_BATCH_POLICY_MIXED_PRESENCE:
        return "nonce presence must be consistent across batch"
    return None

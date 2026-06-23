"""Social recovery runtime receipts for ZenoKeyManager v0."""

from __future__ import annotations

from typing import Any, Sequence

from src.integration.zeno_key_manager import KEY_STATUS_ACTIVE, KeyRef, SocialRecoveryPolicy
from src.integration.zeno_ledger_v0 import hash_v0


RECOVERY_RECEIPT_SCHEMA_V0 = "zenodex/zeno_key_manager/recovery_receipt/v0"


def evaluate_recovery_rotation_v0(
    *,
    policy: SocialRecoveryPolicy,
    approvals: Sequence[str],
    requested_at_epoch: int,
    current_epoch: int,
    new_key_ref: KeyRef,
    recovery_nonce: str,
    cancelled: bool = False,
) -> dict[str, Any]:
    if not isinstance(policy, SocialRecoveryPolicy):
        raise TypeError("policy must be SocialRecoveryPolicy")
    if not isinstance(new_key_ref, KeyRef):
        raise TypeError("new_key_ref must be KeyRef")
    if not isinstance(recovery_nonce, str) or not recovery_nonce:
        raise ValueError("recovery_nonce must be a non-empty string")
    evaluation = policy.evaluate(
        approvals=approvals,
        requested_at_epoch=requested_at_epoch,
        current_epoch=current_epoch,
    )
    errors: list[str] = []
    if cancelled:
        errors.append("recovery_cancelled")
    if not evaluation["ok"]:
        errors.append("recovery_policy_not_satisfied")
    if new_key_ref.status != KEY_STATUS_ACTIVE:
        errors.append("new_key_not_active")
    if new_key_ref.replaces_key_id != policy.subject_key_id:
        errors.append("new_key_not_bound_to_subject")

    body = {
        "schema": RECOVERY_RECEIPT_SCHEMA_V0,
        "policy_hash": policy.public_dict()["policy_hash"],
        "subject_key_id": policy.subject_key_id,
        "new_key_ref": new_key_ref.public_dict(),
        "recovery_nonce": recovery_nonce,
        "requested_at_epoch": requested_at_epoch,
        "current_epoch": current_epoch,
        "evaluation_hash": evaluation["evaluation_hash"],
        "cancelled": bool(cancelled),
        "ok": not errors,
        "errors": tuple(errors),
    }
    return {**body, "receipt_hash": hash_v0("zeno_recovery_rotation_receipt_v0", body)}

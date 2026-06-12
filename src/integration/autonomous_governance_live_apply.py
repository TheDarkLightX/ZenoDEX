"""Deployed-facing admission wrapper for autonomous-governance state changes.

This module is the smallest node/apply boundary around the existing verified
pieces. It reuses the existing proposer/verifier path and requires:

- the current committed governance surface supplied by the caller;
- the current file-backed session-store head;
- an expected store hash and an expected live-context hash;
- a trajectory receipt that independently verifies from that head; and
- successful file-store admission, which advances exactly one live head.

Only after all checks pass does the wrapper return the receipt's final surface
state as `applied_state`. Every refusal returns the supplied committed surface
state as the no-op result.
"""

from __future__ import annotations

import os
from typing import Any, Mapping

from src.integration.autonomous_governance_q_policy import (
    _normalize_surface_state,
    policy_content_hash_v1,
)
from src.integration.autonomous_governance_session_store_file import (
    admit_autonomous_governance_session_file_continuation_v1,
    current_session_store_file_head_v1,
)
from src.integration.autonomous_governance_trajectory import (
    admit_verified_autonomous_governance_surface_trajectory_v1,
)
from src.integration.zeno_ledger_v0 import hash_v0

AUTONOMOUS_GOVERNANCE_LIVE_SESSION_FILE_UPDATE_SCHEMA_V1 = (
    "zenodex.autonomous_governance.live_session_file_update.v1"
)
AUTONOMOUS_GOVERNANCE_LIVE_SESSION_FILE_CONTEXT_SCHEMA_V1 = (
    "zenodex.autonomous_governance.live_session_file_context.v1"
)

_LIVE_CONTEXT_HASH_TAG = "autonomous_governance_live_session_file_context_v1"
_LIVE_UPDATE_HASH_TAG = "autonomous_governance_live_session_file_update_v1"

_NOT_CLAIMED = (
    "does_not_authorize_settlement",
    "does_not_change_immutable_rules",
    "does_not_claim_oracle_truth",
    "does_not_train_q_table_online",
    "does_not_claim_global_store_ordering",
)


def autonomous_governance_live_session_file_context_hash_v1(
    *,
    store_hash: str,
    head_pin_hash: str,
    committed_surface_state: Mapping[str, Any],
    trajectory_hash: str,
    expected_policy_hash: str,
) -> str:
    """Hash the exact live context a node is about to admit.

    The store path is intentionally excluded. A local path is deployment
    plumbing, while the safety context is the store head hash, the head pin, the
    committed surface, the trajectory receipt hash, and the policy pin.
    """

    state, state_errors = _normalize_surface_state(committed_surface_state)
    if state_errors:
        state = {}
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_LIVE_SESSION_FILE_CONTEXT_SCHEMA_V1,
        "store_hash": str(store_hash),
        "head_pin_hash": str(head_pin_hash),
        "committed_surface_state": state,
        "trajectory_hash": str(trajectory_hash),
        "expected_policy_hash": str(expected_policy_hash),
        "state_errors": tuple(state_errors),
    }
    return hash_v0(_LIVE_CONTEXT_HASH_TAG, body)


def _state_equals(left: Mapping[str, int], right: Mapping[str, Any]) -> bool:
    normalized, errors = _normalize_surface_state(right)
    return not errors and normalized == dict(left)


def admit_autonomous_governance_live_session_file_update_v1(
    *,
    store_path: str | os.PathLike[str],
    policy: object,
    trajectory_receipt: object,
    committed_surface_state: Mapping[str, Any],
    expected_policy_hash: object,
    expected_store_hash: object,
    expected_live_context_hash: object,
) -> dict[str, Any]:
    """Admit one live autonomous-governance update or return a no-op.

    This is the entry point a deployed node/apply layer should call before
    changing governance surface parameters. It reads the current file-store
    head, checks that the caller's committed surface equals that head, verifies
    the trajectory from that head, and advances the file store only if the
    caller's expected store hash and live-context hash match.
    """

    errors: list[str] = []
    committed, committed_errors = _normalize_surface_state(committed_surface_state)
    errors.extend(f"committed_{error}" for error in committed_errors)

    expected_hash = expected_policy_hash if isinstance(expected_policy_hash, str) else ""
    if not expected_hash:
        errors.append("live_expected_policy_hash_required")

    expected_store = expected_store_hash if isinstance(expected_store_hash, str) else ""
    if not expected_store:
        errors.append("live_expected_store_hash_required")

    expected_context = (
        expected_live_context_hash if isinstance(expected_live_context_hash, str) else ""
    )
    if not expected_context:
        errors.append("live_expected_context_hash_required")

    policy_hash = ""
    if isinstance(policy, Mapping):
        try:
            policy_hash = policy_content_hash_v1(policy)
        except (TypeError, ValueError):
            errors.append("live_policy_hash_unavailable")
    else:
        errors.append("live_policy_must_be_object")
    if expected_hash and policy_hash and policy_hash != expected_hash:
        errors.append("live_expected_policy_hash_mismatch")

    head_before = current_session_store_file_head_v1(path=store_path)
    if head_before.get("ok") is not True:
        errors.append("live_store_head_unavailable")
        errors.extend(str(error) for error in head_before.get("errors", ()))

    head_surface: dict[str, Any] = (
        dict(head_before.get("surface_state", {}))
        if isinstance(head_before.get("surface_state"), Mapping)
        else {}
    )
    if not committed_errors and head_before.get("ok") is True:
        if not _state_equals(committed, head_surface):
            errors.append("live_committed_surface_state_mismatch")
        if expected_store and head_before.get("store_hash") != expected_store:
            errors.append("live_expected_store_hash_mismatch")

    head_pin = (
        dict(head_before.get("head_pin", {}))
        if isinstance(head_before.get("head_pin"), Mapping)
        else {}
    )
    previous_chain_head = head_pin.get("trajectory_chain_head")
    if not isinstance(previous_chain_head, str) or not previous_chain_head:
        errors.append("live_previous_chain_head_unavailable")
        previous_chain_head = None

    receipt = trajectory_receipt if isinstance(trajectory_receipt, Mapping) else {}
    if not receipt:
        errors.append("live_trajectory_receipt_must_be_object")
    trajectory_hash = receipt.get("trajectory_hash", "") if receipt else ""
    if not isinstance(trajectory_hash, str) or not trajectory_hash:
        errors.append("live_trajectory_hash_required")
        trajectory_hash = ""

    live_context_hash = autonomous_governance_live_session_file_context_hash_v1(
        store_hash=str(head_before.get("store_hash", "")),
        head_pin_hash=str(head_pin.get("pin_hash", "")),
        committed_surface_state=committed if not committed_errors else {},
        trajectory_hash=trajectory_hash,
        expected_policy_hash=expected_hash,
    )
    if expected_context and live_context_hash != expected_context:
        errors.append("live_context_hash_mismatch")

    trajectory_admission: dict[str, Any] = {}
    if not errors:
        trajectory_admission = admit_verified_autonomous_governance_surface_trajectory_v1(
            receipt=receipt,
            policy=policy,
            expected_policy_hash=expected_hash,
            expected_initial_state=committed,
            expected_previous_chain_head=previous_chain_head,
        )
        if trajectory_admission.get("accepted") is not True:
            errors.append("live_trajectory_admission_refused")
            errors.extend(str(error) for error in trajectory_admission.get("errors", ()))

    file_admission: dict[str, Any] = {}
    if not errors:
        file_admission = admit_autonomous_governance_session_file_continuation_v1(
            path=store_path,
            receipt=receipt,
            policy=policy,
            expected_store_hash=expected_store,
        )
        if file_admission.get("admitted") is not True:
            errors.append("live_store_file_admission_refused")
            errors.extend(str(error) for error in file_admission.get("errors", ()))

    head_after: dict[str, Any] = {}
    applied_state: dict[str, int] = dict(committed) if not committed_errors else {}
    admitted = not errors
    if admitted:
        head_after = current_session_store_file_head_v1(path=store_path)
        if head_after.get("ok") is not True:
            errors.append("live_store_head_after_unavailable")
            errors.extend(str(error) for error in head_after.get("errors", ()))
            admitted = False
        else:
            final_state = receipt.get("final_state", {})
            head_after_surface = head_after.get("surface_state", {})
            if not isinstance(final_state, Mapping) or not _state_equals(
                dict(head_after_surface), final_state
            ):
                errors.append("live_store_head_final_state_mismatch")
                admitted = False
            else:
                applied_state = {
                    name: int(value) for name, value in dict(head_after_surface).items()
                }

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_LIVE_SESSION_FILE_UPDATE_SCHEMA_V1,
        "ok": admitted,
        "admitted": admitted,
        "errors": tuple(errors),
        "store_path": str(store_path),
        "expected_policy_hash": expected_hash,
        "expected_store_hash": expected_store,
        "expected_live_context_hash": expected_context,
        "live_context_hash": live_context_hash,
        "policy_hash": policy_hash,
        "trajectory_hash": trajectory_hash,
        "committed_state": dict(committed) if not committed_errors else {},
        "applied_state": applied_state if admitted else dict(committed),
        "store_hash_before": str(head_before.get("store_hash", "")),
        "store_hash_after": str(head_after.get("store_hash", ""))
        if head_after
        else str(file_admission.get("store_hash", "")),
        "head_before": head_before,
        "head_after": head_after,
        "trajectory_admission": trajectory_admission,
        "store_file_admission": file_admission,
        "not_claimed": _NOT_CLAIMED,
    }
    return {**body, "live_update_hash": hash_v0(_LIVE_UPDATE_HASH_TAG, body)}

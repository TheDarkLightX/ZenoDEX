"""Production proposer step for live autonomous-governance updates.

This module closes the proposer side of the WS5 live gap: it turns one fresh
oracle observation into at most one admitted governance-surface update, using
only the already-verified pieces:

- the frozen policy artifact, loaded from disk and pinned to an expected
  content hash before any evaluation;
- the committed surface state, read from the file-backed session-store head
  (never caller-supplied);
- the trajectory runner, which evaluates the policy through the exact
  governance gates;
- the live admission guard (`autonomous_governance_live_apply`), which stays
  the only store-head writer on the path.

The proposer is deliberately stateless. Every call re-reads the store head,
re-pins the policy, and either admits exactly one continuation segment or
refuses with the committed surface state as the no-op result. A receipt whose
trajectory changes nothing (no approved step, no bookkeeping movement) is
reported as a no-op without advancing the store, so refused proposals do not
grow the receipt archive.

Operational note: the session store archives full receipts, so admitted
segments grow the store file toward `MAX_SESSION_STORE_FILE_BYTES_V1`.
Deployments size their proposal cadence accordingly; store rotation is a
separate session-pin concern.

Non-claims: this module does not authorize settlement, does not change
immutable rules, does not claim oracle truth, does not train the policy
online, and does not claim global store ordering.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any, Mapping, TypeGuard

from src.integration.autonomous_governance_live_apply import (
    admit_autonomous_governance_live_session_file_update_v1,
    autonomous_governance_live_session_file_context_hash_v1,
)
from src.integration.autonomous_governance_q_policy import policy_content_hash_v1
from src.integration.autonomous_governance_session_store_file import (
    current_session_store_file_head_v1,
)
from src.integration.autonomous_governance_trajectory import (
    run_autonomous_governance_surface_trajectory_v1,
)
from src.integration.zeno_ledger_v0 import hash_v0

AUTONOMOUS_GOVERNANCE_PINNED_POLICY_SCHEMA_V1 = (
    "zenodex.autonomous_governance.pinned_policy_load.v1"
)
AUTONOMOUS_GOVERNANCE_LIVE_PROPOSER_RECEIPT_SCHEMA_V1 = (
    "zenodex.autonomous_governance.live_proposer_receipt.v1"
)
AUTONOMOUS_GOVERNANCE_LIVE_SURFACE_REPORT_SCHEMA_V1 = (
    "zenodex.autonomous_governance.live_surface_report.v1"
)

_PINNED_POLICY_HASH_TAG = "autonomous_governance_pinned_policy_load_v1"
_LIVE_PROPOSER_RECEIPT_HASH_TAG = "autonomous_governance_live_proposer_receipt_v1"
_LIVE_SURFACE_REPORT_HASH_TAG = "autonomous_governance_live_surface_report_v1"

MAX_POLICY_FILE_BYTES_V1 = 16 * 1024 * 1024

_NOT_CLAIMED = (
    "does_not_authorize_settlement",
    "does_not_change_immutable_rules",
    "does_not_claim_oracle_truth",
    "does_not_train_q_table_online",
    "does_not_claim_global_store_ordering",
)


def _is_plain_str(value: object) -> TypeGuard[str]:
    return type(value) is str


def _is_plain_int(value: object) -> TypeGuard[int]:
    return type(value) is int


def _plain_int_map(raw: object) -> dict[str, int] | None:
    """Materialize a mapping of plain-str keys to plain ints, or refuse.

    The mapping is iterated exactly once into a captured copy, so a hostile
    iterable cannot show clean values to validation and different values to
    use (two-pass TOCTOU).
    """

    if not isinstance(raw, Mapping):
        return None
    try:
        items = list(dict(raw).items())
    except Exception:
        return None
    out: dict[str, int] = {}
    for key, value in items:
        if not _is_plain_str(key) or not _is_plain_int(value):
            return None
        out[key] = value
    return out


def load_autonomous_governance_pinned_policy_v1(
    *,
    path: object,
    expected_policy_hash: object,
) -> dict[str, Any]:
    """Load a frozen policy artifact and pin it to the expected content hash.

    Both the recomputed content hash and the artifact's embedded
    ``policy_hash`` must equal ``expected_policy_hash``; the two are checked
    independently so a stale or edited embedded hash cannot ride on a correct
    content hash (hash-pin consistency).
    """

    errors: list[str] = []
    policy: dict[str, Any] = {}
    policy_hash = ""

    expected = expected_policy_hash if _is_plain_str(expected_policy_hash) else ""
    if not expected:
        errors.append("pinned_policy_expected_hash_required")

    if not isinstance(path, (str, os.PathLike)):
        errors.append("pinned_policy_path_must_be_pathlike")
    elif not errors:
        policy_path = Path(path)
        try:
            stat = policy_path.stat()
        except FileNotFoundError:
            errors.append("pinned_policy_file_missing")
        except OSError:
            errors.append("pinned_policy_file_stat_failed")
        else:
            if not policy_path.is_file():
                errors.append("pinned_policy_file_not_regular")
            elif stat.st_size > MAX_POLICY_FILE_BYTES_V1:
                errors.append("pinned_policy_file_too_large")
            else:
                try:
                    text = policy_path.read_text(encoding="utf-8")
                except UnicodeDecodeError:
                    errors.append("pinned_policy_file_utf8_invalid")
                except OSError:
                    errors.append("pinned_policy_file_read_failed")
                else:
                    try:
                        data = json.loads(text)
                    except json.JSONDecodeError:
                        errors.append("pinned_policy_file_json_invalid")
                    else:
                        if not isinstance(data, dict):
                            errors.append("pinned_policy_file_json_must_be_object")
                        else:
                            policy = data

    if policy and not errors:
        try:
            recomputed = policy_content_hash_v1(policy)
        except (TypeError, ValueError):
            recomputed = ""
        if not recomputed:
            errors.append("pinned_policy_hash_unavailable")
        elif recomputed != expected:
            errors.append("pinned_policy_content_hash_mismatch")
        embedded = policy.get("policy_hash")
        if not _is_plain_str(embedded) or embedded != expected:
            errors.append("pinned_policy_embedded_hash_mismatch")
        if not errors:
            policy_hash = recomputed

    ok = not errors
    if not ok:
        policy = {}
        policy_hash = ""
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_PINNED_POLICY_SCHEMA_V1,
        "ok": ok,
        "errors": tuple(errors),
        "policy_hash": policy_hash,
        "expected_policy_hash": expected,
    }
    return {
        **body,
        "policy": policy,
        "load_hash": hash_v0(_PINNED_POLICY_HASH_TAG, body),
    }


def current_autonomous_governance_live_surface_v1(
    *,
    store_path: str | os.PathLike[str],
) -> dict[str, Any]:
    """Read-only committed-surface report for a deployed node endpoint."""

    errors: list[str] = []
    head = current_session_store_file_head_v1(path=store_path)
    if head.get("ok") is not True:
        errors.extend(
            str(error) for error in head.get("errors", ()) if isinstance(error, str)
        )
        if not errors:
            errors.append("live_surface_store_head_unavailable")

    pin = head.get("head_pin") if isinstance(head.get("head_pin"), Mapping) else {}
    surface = _plain_int_map(head.get("surface_state"))
    if surface is None and not errors:
        errors.append("live_surface_state_invalid")

    ok = not errors
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_LIVE_SURFACE_REPORT_SCHEMA_V1,
        "ok": ok,
        "errors": tuple(errors),
        "surface_state": surface if ok and surface is not None else {},
        "store_hash": str(head.get("store_hash", "")) if ok else "",
        "head_pin_hash": str(pin.get("pin_hash", "")) if ok else "",
        "policy_hash": str(pin.get("policy_hash", "")) if ok else "",
        "segment_count": int(head.get("segment_count", 0)) if ok else 0,
        "last_update_epoch_final": (
            pin.get("last_update_epoch_final")
            if ok and _is_plain_int(pin.get("last_update_epoch_final"))
            else None
        ),
    }
    return {**body, "report_hash": hash_v0(_LIVE_SURFACE_REPORT_HASH_TAG, body)}


def _refusal(
    errors: list[str],
    *,
    committed: dict[str, int] | None,
    observation: dict[str, int] | None,
    current_epoch: int | None,
    proposal_epoch: int | None,
    policy_hash: str,
) -> dict[str, Any]:
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_LIVE_PROPOSER_RECEIPT_SCHEMA_V1,
        "ok": False,
        "admitted": False,
        "no_op": False,
        "errors": tuple(errors),
        "policy_hash": policy_hash,
        "committed_surface_state": dict(committed) if committed is not None else {},
        "applied_state": dict(committed) if committed is not None else {},
        "store_hash_before": "",
        "store_hash_after": "",
        "trajectory_hash": "",
        "live_context_hash": "",
        "live_update_hash": "",
        "step_admitted": False,
        "step_action_id": "",
        "step_reason": "",
        "step_errors": (),
        "current_epoch": current_epoch,
        "proposal_epoch": proposal_epoch,
        "not_claimed": _NOT_CLAIMED,
    }
    # The snapshot is only ever a validated plain-int map (or None), so every
    # refusal receipt is canonically hashable by construction.
    body = {**body, "observation": dict(observation) if observation is not None else {}}
    return {
        **body,
        "proposer_receipt_hash": hash_v0(_LIVE_PROPOSER_RECEIPT_HASH_TAG, body),
    }


def propose_autonomous_governance_live_update_v1(
    *,
    store_path: str | os.PathLike[str],
    policy: object,
    expected_policy_hash: object,
    observation: object,
    current_epoch: object,
    proposal_epoch: object,
) -> dict[str, Any]:
    """Propose and (when admissible) admit one live governance-surface step.

    The committed surface state and every carry-in are taken from the store
    head pin, never from the caller. The policy chooses the candidate action,
    the exact governance gates inside the trajectory runner decide
    admissibility, and the live admission guard decides whether the store head
    advances. Every refusal returns the committed state unchanged.
    """

    errors: list[str] = []

    expected = expected_policy_hash if _is_plain_str(expected_policy_hash) else ""
    if not expected:
        errors.append("proposer_expected_policy_hash_required")

    current_epoch_value: int | None = None
    if isinstance(current_epoch, int) and _is_plain_int(current_epoch) and current_epoch >= 0:
        current_epoch_value = current_epoch
    else:
        errors.append("proposer_current_epoch_must_be_nonnegative_plain_int")

    proposal_epoch_value: int | None = None
    if isinstance(proposal_epoch, int) and _is_plain_int(proposal_epoch) and proposal_epoch >= 0:
        proposal_epoch_value = proposal_epoch
    else:
        errors.append("proposer_proposal_epoch_must_be_nonnegative_plain_int")

    observation_snapshot: dict[str, int] | None = None
    if isinstance(observation, Mapping):
        # Materialize once: the captured copy feeds both the trajectory run
        # and the proposer receipt, so a lying mapping cannot show different
        # values to each consumer. Observations are integer telemetry by
        # contract; enforcing plain ints here also keeps every receipt body
        # canonically hashable by construction.
        observation_snapshot = _plain_int_map(observation)
        if observation_snapshot is None:
            errors.append("proposer_observation_must_be_plain_int_map")
    else:
        errors.append("proposer_observation_must_be_mapping")

    if not isinstance(policy, Mapping):
        errors.append("proposer_policy_must_be_mapping")

    if (
        errors
        or observation_snapshot is None
        or current_epoch_value is None
        or proposal_epoch_value is None
    ):
        if not errors:
            errors.append("proposer_inputs_invalid")
        return _refusal(
            errors,
            committed=None,
            observation=observation_snapshot,
            current_epoch=current_epoch_value,
            proposal_epoch=proposal_epoch_value,
            policy_hash="",
        )

    head = current_session_store_file_head_v1(path=store_path)
    if head.get("ok") is not True:
        head_errors = [
            f"proposer_head_{error}"
            for error in head.get("errors", ())
            if isinstance(error, str)
        ] or ["proposer_store_head_unavailable"]
        return _refusal(
            head_errors,
            committed=None,
            observation=observation_snapshot,
            current_epoch=current_epoch_value,
            proposal_epoch=proposal_epoch_value,
            policy_hash="",
        )

    committed = _plain_int_map(head.get("surface_state"))
    pin = head.get("head_pin") if isinstance(head.get("head_pin"), Mapping) else {}
    store_hash_before = head.get("store_hash")
    pin_hash = pin.get("pin_hash")
    chain_head = pin.get("trajectory_chain_head")
    trajectory_used = _plain_int_map(pin.get("trajectory_used_final"))
    previous_deltas = _plain_int_map(pin.get("previous_approved_deltas_final"))
    last_update_raw = pin.get("last_update_epoch_final")
    last_update = last_update_raw if _is_plain_int(last_update_raw) else None
    pin_policy_hash = pin.get("policy_hash")

    if committed is None:
        errors.append("proposer_committed_surface_invalid")
    if not _is_plain_str(store_hash_before) or not store_hash_before:
        errors.append("proposer_store_hash_invalid")
    if not _is_plain_str(pin_hash) or not pin_hash:
        errors.append("proposer_head_pin_hash_invalid")
    if not _is_plain_str(chain_head) or not chain_head:
        errors.append("proposer_head_chain_head_invalid")
    if trajectory_used is None:
        errors.append("proposer_head_trajectory_used_invalid")
    if previous_deltas is None:
        errors.append("proposer_head_previous_deltas_invalid")
    if last_update_raw is not None and last_update is None:
        errors.append("proposer_head_last_update_epoch_invalid")
    if not _is_plain_str(pin_policy_hash) or pin_policy_hash != expected:
        # The store head was opened under one pinned policy; proposing under a
        # different artifact must refuse before any evaluation.
        errors.append("proposer_head_policy_hash_mismatch")

    if (
        errors
        or committed is None
        or trajectory_used is None
        or previous_deltas is None
    ):
        if not errors:
            errors.append("proposer_head_invalid")
        return _refusal(
            errors,
            committed=committed,
            observation=observation_snapshot,
            current_epoch=current_epoch_value,
            proposal_epoch=proposal_epoch_value,
            policy_hash="",
        )

    receipt = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=dict(committed),
        steps=[
            {
                "observation": dict(observation_snapshot),
                "current_epoch": current_epoch_value,
                "proposal_epoch": proposal_epoch_value,
            }
        ],
        expected_policy_hash=expected,
        last_update_epoch=last_update,
        trajectory_used=dict(trajectory_used),
        previous_approved_deltas=dict(previous_deltas),
        previous_chain_head=str(chain_head),
    )
    receipt_ok = isinstance(receipt, Mapping) and receipt.get("ok") is True
    trajectory_hash = (
        str(receipt.get("trajectory_hash", ""))
        if isinstance(receipt, Mapping)
        else ""
    )
    step_records = (
        receipt.get("steps") if isinstance(receipt, Mapping) else None
    )
    step_admitted = False
    step_action_id = ""
    step_reason = ""
    step_errors: tuple[str, ...] = ()
    if isinstance(step_records, (list, tuple)) and step_records:
        first = step_records[0]
        if isinstance(first, Mapping):
            step_admitted = first.get("admitted") is True
            raw_action = first.get("action_id")
            step_action_id = raw_action if _is_plain_str(raw_action) else ""
            raw_reason = first.get("reason")
            step_reason = raw_reason if _is_plain_str(raw_reason) else ""
            step_errors = tuple(
                str(error)
                for error in first.get("step_errors", ())
                if isinstance(error, str)
            )

    if not receipt_ok or not trajectory_hash:
        run_errors = [
            f"proposer_trajectory_{error}"
            for error in (receipt.get("errors", ()) if isinstance(receipt, Mapping) else ())
            if isinstance(error, str)
        ] or ["proposer_trajectory_failed"]
        return _refusal(
            run_errors,
            committed=committed,
            observation=observation_snapshot,
            current_epoch=current_epoch_value,
            proposal_epoch=proposal_epoch_value,
            policy_hash=expected,
        )

    final_state = _plain_int_map(receipt.get("final_state"))
    used_final = _plain_int_map(receipt.get("trajectory_used_final"))
    deltas_final = _plain_int_map(receipt.get("previous_approved_deltas_final"))
    last_update_final_raw = receipt.get("last_update_epoch_final")
    zero_change = (
        final_state == committed
        and used_final == trajectory_used
        and deltas_final == previous_deltas
        and (
            last_update_final_raw == last_update
            if last_update is not None
            else last_update_final_raw is None
        )
    )
    if zero_change:
        # Nothing to persist: the step was refused or produced no movement and
        # no bookkeeping change. Refused proposals must not grow the store.
        body = {
            "schema": AUTONOMOUS_GOVERNANCE_LIVE_PROPOSER_RECEIPT_SCHEMA_V1,
            "ok": True,
            "admitted": False,
            "no_op": True,
            "errors": (),
            "policy_hash": expected,
            "committed_surface_state": dict(committed),
            "applied_state": dict(committed),
            "store_hash_before": str(store_hash_before),
            "store_hash_after": str(store_hash_before),
            "trajectory_hash": trajectory_hash,
            "live_context_hash": "",
            "live_update_hash": "",
            "step_admitted": step_admitted,
            "step_action_id": step_action_id,
            "step_reason": step_reason,
            "step_errors": step_errors,
            "current_epoch": current_epoch_value,
            "proposal_epoch": proposal_epoch_value,
            "observation": observation_snapshot,
            "not_claimed": _NOT_CLAIMED,
        }
        return {
            **body,
            "proposer_receipt_hash": hash_v0(_LIVE_PROPOSER_RECEIPT_HASH_TAG, body),
        }

    live_context_hash = autonomous_governance_live_session_file_context_hash_v1(
        store_hash=str(store_hash_before),
        head_pin_hash=str(pin_hash),
        committed_surface_state=dict(committed),
        trajectory_hash=trajectory_hash,
        expected_policy_hash=expected,
    )
    admission = admit_autonomous_governance_live_session_file_update_v1(
        store_path=store_path,
        policy=policy,
        trajectory_receipt=receipt,
        committed_surface_state=dict(committed),
        expected_policy_hash=expected,
        expected_store_hash=str(store_hash_before),
        expected_live_context_hash=live_context_hash,
    )
    admitted = admission.get("admitted") is True and admission.get("ok") is True
    admission_errors = tuple(
        f"proposer_admission_{error}"
        for error in admission.get("errors", ())
        if isinstance(error, str)
    )
    applied = _plain_int_map(admission.get("applied_state"))
    if applied is None:
        applied = dict(committed)
        if admitted:
            admitted = False
            admission_errors = (*admission_errors, "proposer_applied_state_invalid")

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_LIVE_PROPOSER_RECEIPT_SCHEMA_V1,
        "ok": admitted,
        "admitted": admitted,
        "no_op": False,
        "errors": admission_errors,
        "policy_hash": expected,
        "committed_surface_state": dict(committed),
        "applied_state": dict(applied),
        "store_hash_before": str(admission.get("store_hash_before", "")),
        "store_hash_after": str(admission.get("store_hash_after", "")),
        "trajectory_hash": trajectory_hash,
        "live_context_hash": live_context_hash,
        "live_update_hash": str(admission.get("live_update_hash", "")),
        "step_admitted": step_admitted,
        "step_action_id": step_action_id,
        "step_reason": step_reason,
        "step_errors": step_errors,
        "current_epoch": current_epoch_value,
        "proposal_epoch": proposal_epoch_value,
        "observation": observation_snapshot,
        "not_claimed": _NOT_CLAIMED,
    }
    return {
        **body,
        "proposer_receipt_hash": hash_v0(_LIVE_PROPOSER_RECEIPT_HASH_TAG, body),
    }

"""Cross-trajectory session continuity for autonomous governance.

`run_autonomous_governance_surface_trajectory_v1` bounds one trajectory: within
it, `trajectory_used` is monotone, anti-oscillation screens reversals, and the
cooldown clock carries. But the runner takes its carry-in state
(`trajectory_used`, `previous_approved_deltas`, `last_update_epoch`) from the
caller. Nothing binds trajectory N+1's carry-in to trajectory N's finals, so a
sequence of individually green, individually verifiable trajectories can:

- reset the movement budget at every boundary (slow-drip: K segments of
  budget-limit drift = K x budget total drift, every receipt verifying);
- reset the oscillation history at every boundary (flip direction each
  segment, never screened);
- reset the cooldown clock and replay old epoch windows.

The within-trajectory budget theorem (ESSO `gov_trajectory_thread_v1`, Lean
`AutoGovSafetyEnvelope`) remains correct, but this attack lives at a boundary
the theorem does not model.

This module owns the boundary:

```text
continue_autonomous_governance_surface_trajectory_v1(policy, previous_receipt, steps, ...)
  -> next trajectory receipt whose carry-in is the parent's finals, and whose
     chain genesis pins the parent's chain head (previous_chain_head input);
verify_autonomous_governance_surface_session_v1(receipts, policy)
  -> independent re-derivation over the whole session: every receipt replays,
     every boundary carries exactly, the session-level drift obeys the one
     shared budget. A client refuses any session that does not.
```

Session semantics (fail-closed, deliberately conservative):

- a session has one policy artifact and one trajectory budget for its entire
  lifetime; the budget never refills at a boundary. A spent budget means the
  session can only hold. Renewing autonomy starts a new session, an authority
  decision (quorum-gated like policy rotation in
  `autonomous_governance_policy_pin.py`) rather than an operator convenience.
- segment 0 must be a fresh genesis: no `previous_chain_head`, zero
  `trajectory_used`, empty `previous_approved_deltas`, no `last_update_epoch`.
  Carried-in state without a verifiable parent is indistinguishable from a
  forged reset, so it is refused.
- every boundary must carry all threading state exactly: chain-head linkage
  alone is not continuity (an attacker can pin the true parent head while
  resetting `trajectory_used`; the verifier refuses that mismatch).
- epochs must be strictly increasing across the boundary as well as within each
  segment, so a segment cannot replay an already-consumed epoch window.

Honest boundaries: the verifier checks the session it is shown. It cannot see
receipts that were withheld, so refusing forks (two continuations extending the
same parent) is the job of a deployed session-head pin: the single live head a
governance admission path advances only on verified continuation. That binding
is the next layer, mirroring the policy-pin lineage; this module provides the
verification it would consume. The receipt still does not claim observations or
the epoch clock are true.
"""

from __future__ import annotations

from typing import Any, Callable, Mapping, Sequence, TypeGuard

from src.integration.autonomous_governance_hostile_input import (
    is_canonically_encodable,
)
from src.integration.autonomous_governance_q_policy import (
    SURFACE_PARAMETER_NAMES_V1,
    _normalize_trajectory_budget,
    _policy_content_hash_for_receipt,
)
from src.integration.autonomous_governance_trajectory import (
    AUTONOMOUS_GOVERNANCE_TRAJECTORY_SCHEMA_V1,
    STATUS_COMPLETED,
    _structural_rejection_receipt,
    run_autonomous_governance_surface_trajectory_v1,
    verify_autonomous_governance_surface_trajectory_v1,
)
from src.integration.zeno_ledger_v0 import hash_v0

_HASH_V0: Callable[[str, object], str] = hash_v0

AUTONOMOUS_GOVERNANCE_SESSION_VERIFICATION_SCHEMA_V1 = (
    "zenodex.autonomous_governance.q_surface_session_verification.v1"
)
_SESSION_VERIFICATION_HASH_TAG = (
    "autonomous_governance_q_surface_session_verification_v1"
)

# Bind the trusted run/verify surface once at import, matching the lane's
# discipline: a later monkeypatch cannot become the session authority.
_RUN_TRAJECTORY = run_autonomous_governance_surface_trajectory_v1
_VERIFY_TRAJECTORY = verify_autonomous_governance_surface_trajectory_v1

MAX_SESSION_RECEIPTS_V1 = 4096


def _is_plain_int(value: object) -> TypeGuard[int]:
    return type(value) is int


def _last_input_epoch(receipt: Mapping[str, Any]) -> int | None:
    """Largest validated step epoch of a runner-produced receipt.

    The runner enforces strictly increasing epochs within a trajectory, so the
    last input step holds the maximum; tolerate malformed shapes by returning
    None (callers treat that as not extendable / not linkable).
    """

    input_steps = receipt.get("input_steps")
    if not isinstance(input_steps, Sequence) or isinstance(
        input_steps, (str, bytes, bytearray)
    ):
        return None
    last: int | None = None
    for step in input_steps:
        if not isinstance(step, Mapping):
            return None
        epoch = step.get("current_epoch")
        if not _is_plain_int(epoch):
            return None
        if last is None or int(epoch) > last:
            last = int(epoch)
    return last


def _first_step_epoch(steps: object) -> int | None:
    """Best-effort first current_epoch of the NEXT segment's raw step inputs.

    Only used for the cross-boundary monotonicity refusal; structurally bad
    steps fall through to the runner's own validation, which rejects the whole
    trajectory as a no-op anyway.
    """

    if not isinstance(steps, Sequence) or isinstance(steps, (str, bytes, bytearray)):
        return None
    for step in steps:
        if not isinstance(step, Mapping):
            return None
        epoch = step.get("current_epoch")
        return int(epoch) if _is_plain_int(epoch) else None
    return None


def continue_autonomous_governance_surface_trajectory_v1(
    *,
    policy: Mapping[str, Any],
    previous_receipt: object,
    steps: Sequence[Mapping[str, Any]],
    expected_policy_hash: str,
) -> dict[str, Any]:
    """Run the next trajectory segment of a session, fail-closed.

    The parent receipt is fully re-verified (replay, chain walk, policy hash)
    before anything runs; carry-in is then derived only from the verified
    parent's finals. The caller cannot supply threading state.
    Any defect yields a structural-rejection receipt (a deterministic no-op),
    never a trajectory that silently restarts the budget.
    """

    structural_errors: list[str] = []

    # A policy or expected-hash hostile to canonical encoding would crash the
    # rejection receipt that should refuse it; gate both before they are hashed
    # or embedded. The parent receipt is gated by the trajectory verifier.
    policy_for_hash: Mapping[str, Any] | dict[str, Any] = policy
    if policy is not None and not is_canonically_encodable(policy):
        structural_errors.append("policy_not_canonically_encodable")
        policy_for_hash = {}
    if not is_canonically_encodable(expected_policy_hash):
        structural_errors.append("expected_policy_hash_not_canonically_encodable")
        expected_policy_hash = ""

    policy_hash = _policy_content_hash_for_receipt(policy_for_hash, structural_errors)

    if not isinstance(expected_policy_hash, str) or not expected_policy_hash:
        structural_errors.append("expected_policy_hash_required")
        expected_policy_hash = (
            "" if not isinstance(expected_policy_hash, str) else expected_policy_hash
        )

    verification = _VERIFY_TRAJECTORY(receipt=previous_receipt, policy=policy_for_hash)
    if verification.get("ok") is not True:
        structural_errors.append("session_parent_receipt_unverified")
        structural_errors.extend(
            f"session_parent_verification:{error}"
            for error in verification.get("errors", ())
        )
        return _structural_rejection_receipt(
            errors=structural_errors,
            expected_policy_hash=expected_policy_hash,
            policy_hash=policy_hash,
            initial_state={},
        )

    # A verified receipt is a Mapping with runner-produced shape (replay
    # matched); the isinstance gate keeps this total without trusting that.
    if not isinstance(previous_receipt, Mapping):
        structural_errors.append("session_parent_receipt_unverified")
        return _structural_rejection_receipt(
            errors=structural_errors,
            expected_policy_hash=expected_policy_hash,
            policy_hash=policy_hash,
            initial_state={},
        )
    parent = dict(previous_receipt)

    if parent.get("status") != STATUS_COMPLETED or parent.get("ok") is not True:
        structural_errors.append(
            f"session_parent_not_extendable:{parent.get('status')}"
        )
    if expected_policy_hash and parent.get("policy_hash") != expected_policy_hash:
        structural_errors.append("session_policy_hash_mismatch")

    parent_last_epoch = _last_input_epoch(parent)
    if parent_last_epoch is None:
        structural_errors.append("session_parent_epochs_unreadable")
    else:
        first_epoch = _first_step_epoch(steps)
        if first_epoch is not None and first_epoch <= parent_last_epoch:
            structural_errors.append("session_epochs_not_strictly_increasing")

    chain_head = parent.get("chain_head")
    if not isinstance(chain_head, str) or not chain_head:
        structural_errors.append("session_parent_chain_head_missing")

    if structural_errors:
        return _structural_rejection_receipt(
            errors=structural_errors,
            expected_policy_hash=expected_policy_hash,
            policy_hash=policy_hash,
            initial_state={},
        )

    last_update_epoch = parent.get("last_update_epoch_final")
    return _RUN_TRAJECTORY(
        policy=policy,
        initial_surface_state=dict(parent["final_state"]),
        steps=steps,
        expected_policy_hash=expected_policy_hash,
        last_update_epoch=(
            int(last_update_epoch) if _is_plain_int(last_update_epoch) else None
        ),
        trajectory_budget=dict(parent["trajectory_budget"]),
        trajectory_used=dict(parent["trajectory_used_final"]),
        previous_approved_deltas=dict(parent["previous_approved_deltas_final"]),
        previous_chain_head=str(chain_head),
    )


def _session_verification_body(
    *,
    ok: bool,
    errors: Sequence[str],
    checks: Mapping[str, bool],
    receipt_count: int,
    policy_hash: str = "",
    trajectory_budget: Mapping[str, int] | None = None,
    session_drift: Mapping[str, int] | None = None,
    session_used_final: Mapping[str, int] | None = None,
    session_chain_head: str = "",
) -> dict[str, Any]:
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SESSION_VERIFICATION_SCHEMA_V1,
        "ok": ok,
        "errors": tuple(errors),
        "checks": dict(checks),
        "receipt_count": receipt_count,
        "policy_hash": policy_hash,
        "trajectory_budget": dict(trajectory_budget or {}),
        "session_drift": dict(session_drift or {}),
        "session_used_final": dict(session_used_final or {}),
        "session_chain_head": session_chain_head,
    }
    return {
        **body,
        "verification_hash": _HASH_V0(_SESSION_VERIFICATION_HASH_TAG, body),
    }


def verify_autonomous_governance_surface_session_v1(
    *,
    receipts: object,
    policy: object,
    expected_policy_hash: str | None = None,
) -> dict[str, Any]:
    """Verify an ordered sequence of trajectory receipts as one session.

    Checks, all of which must pass:

    1. shape: a non-empty bounded sequence of trajectory receipts;
    2. every receipt independently verifies against the policy artifact
       (full replay + chain walk via the trajectory verifier);
    3. the first receipt is a fresh genesis (no previous_chain_head, zero
       used, empty oscillation history, no cooldown carry);
    4. every boundary carries exactly: previous_chain_head == parent chain
       head, initial_state == parent final_state, trajectory_used == parent
       trajectory_used_final, previous_approved_deltas == parent
       previous_approved_deltas_final, last_update_epoch == parent
       last_update_epoch_final;
    5. one policy hash and one trajectory budget across the whole session
       (and the caller's expected_policy_hash, when pinned);
    6. epochs strictly increase across boundaries;
    7. every receipt is a completed, ok trajectory;
    8. independently re-derived session accounting: per-parameter session
       drift equals the sum of per-receipt drifts, |session drift| <=
       session used <= budget, and used is monotone across receipts.

    Verification proves the session is exactly the deterministic outcome of
    its pinned inputs under one budget. It does not prove the session shown is
    the only continuation of its genesis; refusing forks requires the single
    pinned live head (see module docstring).
    """

    checks = {
        "receipts_shape_ok": False,
        "receipts_individually_verified": False,
        "genesis_fresh_ok": False,
        "boundary_carry_ok": False,
        "policy_hash_consistent_ok": False,
        "budget_consistent_ok": False,
        "budget_policy_bound_ok": False,
        "epochs_strictly_increasing_ok": False,
        "statuses_ok": False,
        "session_accounting_ok": False,
    }
    errors: list[str] = []

    if (
        not isinstance(receipts, Sequence)
        or isinstance(receipts, (str, bytes, bytearray))
        or not receipts
    ):
        return _session_verification_body(
            ok=False,
            errors=["session_receipts_must_be_nonempty_sequence"],
            checks=checks,
            receipt_count=0,
        )
    if len(receipts) > MAX_SESSION_RECEIPTS_V1:
        return _session_verification_body(
            ok=False,
            errors=[
                f"session_receipts_exceed_max:{len(receipts)}>{MAX_SESSION_RECEIPTS_V1}"
            ],
            checks=checks,
            receipt_count=len(receipts),
        )
    shape_ok = True
    for index, receipt in enumerate(receipts):
        if (
            not isinstance(receipt, Mapping)
            or receipt.get("schema") != AUTONOMOUS_GOVERNANCE_TRAJECTORY_SCHEMA_V1
        ):
            errors.append(f"session_receipt_malformed:{index}")
            shape_ok = False
    checks["receipts_shape_ok"] = shape_ok
    if not shape_ok:
        return _session_verification_body(
            ok=False, errors=errors, checks=checks, receipt_count=len(receipts)
        )

    records: list[dict[str, Any]] = [dict(receipt) for receipt in receipts]

    individually_verified = True
    for index, record in enumerate(records):
        verification = _VERIFY_TRAJECTORY(receipt=record, policy=policy)
        if verification.get("ok") is not True:
            individually_verified = False
            errors.append(f"session_receipt_unverified:{index}")
            errors.extend(
                f"session_receipt_verification:{index}:{error}"
                for error in verification.get("errors", ())
            )
    checks["receipts_individually_verified"] = individually_verified
    if not individually_verified:
        return _session_verification_body(
            ok=False, errors=errors, checks=checks, receipt_count=len(records)
        )

    # Every receipt replayed: runner-produced shapes are now guaranteed.
    genesis = records[0]
    genesis_carry = dict(genesis.get("carry_in", {}))
    genesis_fresh = True
    if "previous_chain_head" in genesis_carry:
        errors.append("session_genesis_carries_chain_head")
        genesis_fresh = False
    if any(int(v) != 0 for v in dict(genesis_carry.get("trajectory_used", {})).values()):
        errors.append("session_genesis_used_not_zero")
        genesis_fresh = False
    if dict(genesis_carry.get("previous_approved_deltas", {})):
        errors.append("session_genesis_oscillation_history_not_empty")
        genesis_fresh = False
    if genesis_carry.get("last_update_epoch") is not None:
        errors.append("session_genesis_cooldown_carry_not_none")
        genesis_fresh = False
    checks["genesis_fresh_ok"] = genesis_fresh

    boundary_ok = True
    epochs_ok = True
    for index in range(1, len(records)):
        parent = records[index - 1]
        child = records[index]
        carry = dict(child.get("carry_in", {}))
        if carry.get("previous_chain_head") != parent.get("chain_head"):
            errors.append(f"session_previous_chain_head_mismatch:{index}")
            boundary_ok = False
        if dict(child.get("initial_state", {})) != dict(parent.get("final_state", {})):
            errors.append(f"session_initial_state_mismatch:{index}")
            boundary_ok = False
        if dict(carry.get("trajectory_used", {})) != dict(
            parent.get("trajectory_used_final", {})
        ):
            errors.append(f"session_carry_used_mismatch:{index}")
            boundary_ok = False
        if dict(carry.get("previous_approved_deltas", {})) != dict(
            parent.get("previous_approved_deltas_final", {})
        ):
            errors.append(f"session_carry_oscillation_history_mismatch:{index}")
            boundary_ok = False
        if carry.get("last_update_epoch") != parent.get("last_update_epoch_final"):
            errors.append(f"session_carry_cooldown_mismatch:{index}")
            boundary_ok = False
        parent_last = _last_input_epoch(parent)
        child_first = _first_step_epoch(child.get("input_steps"))
        if parent_last is None or child_first is None or child_first <= parent_last:
            errors.append(f"session_epochs_not_strictly_increasing:{index}")
            epochs_ok = False
    checks["boundary_carry_ok"] = boundary_ok
    checks["epochs_strictly_increasing_ok"] = epochs_ok

    policy_hashes = {str(record.get("policy_hash", "")) for record in records}
    policy_hash_ok = len(policy_hashes) == 1 and "" not in policy_hashes
    session_policy_hash = next(iter(policy_hashes)) if len(policy_hashes) == 1 else ""
    if not policy_hash_ok:
        errors.append("session_policy_hash_inconsistent")
    if expected_policy_hash is not None and (
        not isinstance(expected_policy_hash, str)
        or session_policy_hash != expected_policy_hash
    ):
        errors.append("session_expected_policy_hash_mismatch")
        policy_hash_ok = False
    checks["policy_hash_consistent_ok"] = policy_hash_ok

    budgets = [dict(record.get("trajectory_budget", {})) for record in records]
    budget_ok = all(budget == budgets[0] for budget in budgets[1:])
    if not budget_ok:
        errors.append("session_trajectory_budget_inconsistent")
    checks["budget_consistent_ok"] = budget_ok

    policy_budget, policy_budget_errors = _normalize_trajectory_budget(
        None, policy=policy if isinstance(policy, Mapping) else {}
    )
    budget_policy_bound_ok = not policy_budget_errors and budgets[0] == policy_budget
    if policy_budget_errors:
        errors.extend(
            f"session_policy_trajectory_budget_invalid:{error}"
            for error in policy_budget_errors
        )
    if not budget_policy_bound_ok and not policy_budget_errors:
        errors.append("session_trajectory_budget_policy_mismatch")
    checks["budget_policy_bound_ok"] = budget_policy_bound_ok
    budget = policy_budget if budget_policy_bound_ok else budgets[0]

    statuses_ok = all(
        record.get("status") == STATUS_COMPLETED and record.get("ok") is True
        for record in records
    )
    if not statuses_ok:
        errors.append("session_contains_non_ok_trajectory")
    checks["statuses_ok"] = statuses_ok

    # Independent session accounting, re-derived from the receipts (the same
    # discipline as the trajectory verifier's chain walk: a second code path).
    accounting_ok = True
    initial_state = dict(records[0].get("initial_state", {}))
    final_state = dict(records[-1].get("final_state", {}))
    used_final = dict(records[-1].get("trajectory_used_final", {}))
    session_drift: dict[str, int] = {}
    for name in SURFACE_PARAMETER_NAMES_V1:
        drift = int(final_state.get(name, 0)) - int(initial_state.get(name, 0))
        session_drift[name] = drift
        summed = sum(
            int(dict(record.get("cumulative_realized_drift", {})).get(name, 0))
            for record in records
        )
        if drift != summed:
            errors.append(f"session_drift_conservation_broken:{name}")
            accounting_ok = False
        if abs(drift) > int(used_final.get(name, 0)):
            errors.append(f"session_drift_exceeds_used:{name}")
            accounting_ok = False
    for name, limit in budget.items():
        if int(used_final.get(name, 0)) > int(limit):
            errors.append(f"session_used_exceeds_budget:{name}")
            accounting_ok = False
    previous_used: dict[str, int] = {}
    for index, record in enumerate(records):
        used = dict(record.get("trajectory_used_final", {}))
        for name in SURFACE_PARAMETER_NAMES_V1:
            if int(used.get(name, 0)) < int(previous_used.get(name, 0)):
                errors.append(f"session_used_not_monotone:{index}:{name}")
                accounting_ok = False
        previous_used = used
    checks["session_accounting_ok"] = accounting_ok

    ok = all(checks.values()) and not errors
    return _session_verification_body(
        ok=ok,
        errors=errors,
        checks=checks,
        receipt_count=len(records),
        policy_hash=session_policy_hash,
        trajectory_budget={str(k): int(v) for k, v in budget.items()},
        session_drift=session_drift,
        session_used_final={
            name: int(used_final.get(name, 0)) for name in SURFACE_PARAMETER_NAMES_V1
        },
        session_chain_head=str(records[-1].get("chain_head", "")),
    )

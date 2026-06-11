"""Deterministic multi-step autonomous-governance trajectory runner and verifier.

`commit_autonomous_governance_surface_q_policy_v1` applies ONE autonomous step.
Operating it across epochs requires the caller to thread four pieces of state
between calls — the applied surface state, `trajectory_used`,
`previous_approved_deltas`, and `last_update_epoch`. Forget one kwarg and the
cooldown, trajectory-budget, or anti-oscillation guard silently stops binding.
The policy factory threads this state correctly inside its replay harness; the
runtime had no production equivalent.

This module owns that threading correct-by-construction:

```text
run_autonomous_governance_surface_trajectory_v1(policy, initial_state, steps, ...)
  -> hash-chained trajectory receipt (self-contained, deterministic)
verify_autonomous_governance_surface_trajectory_v1(receipt, policy)
  -> independent re-derivation; a client refuses any trajectory that does not replay
```

Threading semantics deliberately match the factory's long-horizon replay
(`tools/autonomous_governance_policy_factory.py::_replay_long_horizon_sequences`
in the lane of record — the 7k-line factory is intentionally not snapshotted
on this branch):

- state advances only on an admitted step; rejection is a recorded no-op;
- `trajectory_used`, `previous_approved_deltas`, and `last_update_epoch` update
  only on an admitted step whose realized deltas are nonzero — an admitted
  "hold" does NOT reset the cooldown;
- realized deltas are measured from applied state, not action declarations.
- every single-step call is given an `expected_committed_context_hash`, binding
  the state, epochs, previous deltas, and trajectory usage the runner is
  threading.

Fail-closed posture (stricter than the single-step path, on purpose):

- `expected_policy_hash` is REQUIRED — multi-step autonomy never runs unpinned;
- the policy must declare a COMPLETE safety envelope (every control present);
- every parameter any action can move must be covered by a trajectory budget;
- structural input defects reject the whole trajectory as a no-op
  (validation before mutation); semantic per-step rejections (safety, gates)
  are recorded no-ops and the trajectory continues, which is the system
  working as designed;
- each step is re-audited against invariants re-derived from the import-bound
  `gov_gate` guardrail constants (a second, independent derivation of the
  per-surface bounds/step caps). Any breach means the inner commit step broke
  its contract: the runner refuses the suspect state and halts.

Honest boundaries: the receipt does not claim the observations or the epoch
clock are true — binding observations to oracle attestations is a separate
obligation. Verification proves the receipt is exactly the deterministic
outcome of the pinned inputs under the pinned policy and gates, nothing more.
The per-step timelock relation is epoch-relative and stays owned by the gates;
it is not re-audited here.
"""

from __future__ import annotations

from typing import Any, Callable, Mapping, Sequence, TypeGuard

from src.integration.autonomous_governance_hostile_input import (
    is_canonically_encodable,
    is_canonically_encodable_without_size_limit,
)
from src.integration.autonomous_governance_q_policy import (
    SURFACE_PARAMETER_NAMES_V1,
    commit_autonomous_governance_surface_q_policy_v1,
    governance_surface_context_hash_v1,
    policy_content_hash_v1,
    _normalize_policy,
    _normalize_surface_int_map,
    _normalize_surface_state,
    _normalize_trajectory_budget,
    _policy_content_hash_for_receipt,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.tau_specs.governance import gov_gate

# Typed import-bound alias (also pins the hash function against later
# monkeypatching of the ledger module).
_HASH_V0: Callable[[str, object], str] = hash_v0


AUTONOMOUS_GOVERNANCE_TRAJECTORY_SCHEMA_V1 = (
    "zenodex.autonomous_governance.q_surface_trajectory.v1"
)
AUTONOMOUS_GOVERNANCE_TRAJECTORY_VERIFICATION_SCHEMA_V1 = (
    "zenodex.autonomous_governance.q_surface_trajectory_verification.v1"
)

_TRAJECTORY_HASH_TAG = "autonomous_governance_q_surface_trajectory_v1"
_CHAIN_HASH_TAG = "autonomous_governance_q_surface_trajectory_chain_v1"
_VERIFICATION_HASH_TAG = "autonomous_governance_q_surface_trajectory_verification_v1"

MAX_TRAJECTORY_STEPS_V1 = 4096

STEP_INPUT_FIELDS_V1 = frozenset({"observation", "current_epoch", "proposal_epoch"})

REQUIRED_SAFETY_CONTROLS_V1 = (
    "emergency_pause",
    "max_divergence_bps",
    "max_freshness_lag_epochs",
    "max_volatility_bps",
    "min_cooldown_epochs",
    "min_liquidity_depth_bps",
)

STATUS_COMPLETED = "completed"
STATUS_REJECTED_STRUCTURAL = "rejected_structural"
STATUS_HALTED_INVARIANT_BREACH = "halted_invariant_breach"

_NOT_CLAIMED = (
    "does_not_authorize_settlement",
    "does_not_change_immutable_rules",
    "does_not_claim_oracle_truth",
    "does_not_train_q_table_online",
    "does_not_claim_observation_truth",
    "does_not_claim_epoch_clock_truth",
)

# Bind the trusted single-step commit path and the guardrail constants once at
# import, matching the discipline of the runtime evaluator: a later monkeypatch
# or forged wrapper cannot become the authority for trajectory execution.
_COMMIT_SURFACE_STEP = commit_autonomous_governance_surface_q_policy_v1
_FEE_MAX_BPS = gov_gate.FEE_MAX_BPS
_FEE_STEP_BPS = gov_gate.FEE_STEP_BPS
_SPLIT_SHARE_MAX = gov_gate.SPLIT_SHARE_MAX
_SPLIT_SUM = gov_gate.SPLIT_SUM
_SPLIT_STEP_BPS = gov_gate.SPLIT_STEP_BPS
_RATIO_MIN_BPS = gov_gate.RATIO_MIN_BPS
_RATIO_MAX_BPS = gov_gate.RATIO_MAX_BPS
_RATIO_STEP_BPS = gov_gate.RATIO_STEP_BPS
_FUNDING_CAP_MAX_BPS = gov_gate.FUNDING_CAP_MAX_BPS
_FUNDING_STEP_BPS = gov_gate.FUNDING_STEP_BPS
_WHALE_STAKER_BPS_MAX = gov_gate.WHALE_STAKER_BPS_MAX
_WHALE_STEP_BPS = gov_gate.WHALE_STEP_BPS

_ROUTER_SHARE_NAMES = ("buyburn_bps", "stakers_bps", "reserve_bps", "hosts_bps")


def _is_plain_int(value: object) -> TypeGuard[int]:
    """Exact-type integer guard: rejects bool and every int subclass."""

    return type(value) is int


def _is_plain_bool(value: object) -> TypeGuard[bool]:
    return type(value) is bool


def _normalize_carry_deltas(raw: object) -> tuple[dict[str, int], list[str]]:
    """Strictly validate carried-in previous approved deltas (signed ints)."""

    if raw is None:
        return {}, []
    if not isinstance(raw, Mapping):
        return {}, ["previous_approved_deltas_must_be_object"]
    errors: list[str] = []
    out: dict[str, int] = {}
    for key, value in raw.items():
        if key not in SURFACE_PARAMETER_NAMES_V1:
            errors.append(f"unknown_previous_approved_delta_parameter:{key}")
            continue
        if not _is_plain_int(value):
            errors.append(f"previous_approved_deltas.{key} must be an int")
            continue
        out[str(key)] = value
    return out, errors


def _validate_safety_envelope(policy: Mapping[str, Any]) -> list[str]:
    """Require a complete, well-typed safety envelope for multi-step autonomy.

    The single-step evaluator only enforces the controls a policy declares; a
    policy with `safety: {}` runs with no oracle safety checks at all. For an
    autonomous trajectory an absent control is an unbounded control, so every
    control must be present (an operator who wants a control disabled must say
    so with an explicit extreme value, which then appears in the receipt).
    """

    safety = policy.get("safety", {})
    if not isinstance(safety, Mapping):
        return ["safety_must_be_object"]
    errors: list[str] = []
    for name in REQUIRED_SAFETY_CONTROLS_V1:
        if name not in safety:
            errors.append(f"incomplete_safety_envelope:{name}")
            continue
        value = safety.get(name)
        if name == "emergency_pause":
            if not _is_plain_bool(value):
                errors.append("safety.emergency_pause must be a bool")
        elif not _is_plain_int(value) or value < 0:
            errors.append(f"safety.{name} must be a non-negative int")
    return errors


def _movable_parameters(policy: Mapping[str, Any]) -> tuple[str, ...]:
    movable: set[str] = set()
    actions = policy.get("actions", ())
    if isinstance(actions, Sequence):
        for action in actions:
            if not isinstance(action, Mapping):
                continue
            deltas = action.get("deltas", {})
            if not isinstance(deltas, Mapping):
                continue
            for name, delta in deltas.items():
                if _is_plain_int(delta) and delta != 0:
                    movable.add(str(name))
    return tuple(sorted(movable))


def _validate_step_inputs(steps: object) -> tuple[list[dict[str, Any]], list[str]]:
    """Structural validation of the step sequence (validate before mutation).

    Shape defects here are integration failures, not market conditions: the
    whole trajectory is rejected as a no-op rather than guessing. Semantic
    defects (unknown observation fields, safety breaches, gate rejections) are
    handled per step by the evaluator and become recorded no-op steps.
    """

    if not isinstance(steps, Sequence) or isinstance(steps, (str, bytes, bytearray)):
        return [], ["trajectory_steps_must_be_sequence"]
    if not steps:
        return [], ["trajectory_steps_empty"]
    if len(steps) > MAX_TRAJECTORY_STEPS_V1:
        return [], [f"trajectory_steps_exceed_max:{len(steps)}>{MAX_TRAJECTORY_STEPS_V1}"]
    errors: list[str] = []
    validated: list[dict[str, Any]] = []
    previous_epoch: int | None = None
    for index, raw in enumerate(steps):
        if not isinstance(raw, Mapping):
            errors.append(f"trajectory_step_must_be_object:{index}")
            continue
        for key in raw:
            if key not in STEP_INPUT_FIELDS_V1:
                errors.append(f"trajectory_step_unknown_field:{index}:{key}")
        for key in sorted(STEP_INPUT_FIELDS_V1):
            if key not in raw:
                errors.append(f"trajectory_step_missing_field:{index}:{key}")
        current_epoch = raw.get("current_epoch")
        proposal_epoch = raw.get("proposal_epoch")
        if not _is_plain_int(current_epoch) or current_epoch < 0:
            errors.append(f"trajectory_step_current_epoch_invalid:{index}")
            current_epoch = None
        if not _is_plain_int(proposal_epoch) or proposal_epoch < 0:
            errors.append(f"trajectory_step_proposal_epoch_invalid:{index}")
            proposal_epoch = None
        observation = raw.get("observation")
        normalized_observation: dict[str, int] = {}
        if not isinstance(observation, Mapping):
            errors.append(f"trajectory_step_observation_must_be_object:{index}")
        else:
            for key, value in observation.items():
                if not isinstance(key, str):
                    errors.append(f"trajectory_step_observation_key_invalid:{index}")
                    continue
                if not _is_plain_int(value):
                    errors.append(
                        f"trajectory_step_observation_value_invalid:{index}:{key}"
                    )
                    continue
                normalized_observation[key] = value
        if current_epoch is not None:
            if previous_epoch is not None and current_epoch <= previous_epoch:
                errors.append(f"trajectory_epochs_not_strictly_increasing:{index}")
            previous_epoch = current_epoch
        if current_epoch is None or proposal_epoch is None:
            continue
        validated.append(
            {
                "index": index,
                "observation": normalized_observation,
                "current_epoch": current_epoch,
                "proposal_epoch": proposal_epoch,
            }
        )
    return validated, errors


def _audit_step_transition(
    *,
    admitted: bool,
    state_before: Mapping[str, int],
    applied_state: Mapping[str, Any],
    proposed_state: Mapping[str, Any],
    used_before: Mapping[str, int],
    used_after: Mapping[str, int],
    trajectory_budget: Mapping[str, int],
) -> tuple[str, ...]:
    """Independently re-derive the per-step invariants from gov_gate constants.

    This is the dual-checker tripwire: the gates already enforced these bounds
    inside the commit step, and this function re-derives them through separate
    code against the same immutable guardrail constants. A breach means the
    inner step broke its contract (code drift, not runtime forgery — the commit
    path is import-bound) and the trajectory must refuse the suspect state.
    """

    breaches: list[str] = []
    applied: dict[str, int] = {}
    for name in SURFACE_PARAMETER_NAMES_V1:
        value = applied_state.get(name) if isinstance(applied_state, Mapping) else None
        if not _is_plain_int(value) or value < 0:
            breaches.append(f"invariant_breach:applied_state_shape:{name}")
            continue
        applied[name] = value
    if breaches:
        return tuple(breaches)

    if not admitted:
        for name in SURFACE_PARAMETER_NAMES_V1:
            if applied[name] != state_before[name]:
                breaches.append(f"invariant_breach:reject_not_noop:{name}")
    else:
        for name in SURFACE_PARAMETER_NAMES_V1:
            proposed = (
                proposed_state.get(name) if isinstance(proposed_state, Mapping) else None
            )
            if not _is_plain_int(proposed) or applied[name] != proposed:
                breaches.append(f"invariant_breach:admitted_not_proposed:{name}")

        def delta(name: str) -> int:
            return applied[name] - state_before[name]

        if abs(delta("fee_bps")) > _FEE_STEP_BPS:
            breaches.append("invariant_breach:fee_step")
        if applied["fee_bps"] > _FEE_MAX_BPS:
            breaches.append("invariant_breach:fee_bound")
        if abs(delta("funding_cap_bps")) > _FUNDING_STEP_BPS:
            breaches.append("invariant_breach:funding_step")
        if applied["funding_cap_bps"] > _FUNDING_CAP_MAX_BPS:
            breaches.append("invariant_breach:funding_bound")
        for share in _ROUTER_SHARE_NAMES:
            if abs(delta(share)) > _SPLIT_STEP_BPS:
                breaches.append(f"invariant_breach:router_step:{share}")
            if applied[share] > _SPLIT_SHARE_MAX:
                breaches.append(f"invariant_breach:router_share_bound:{share}")
        if sum(applied[share] for share in _ROUTER_SHARE_NAMES) != _SPLIT_SUM:
            breaches.append("invariant_breach:router_sum")
        if abs(delta("mcr_bps")) > _RATIO_STEP_BPS:
            breaches.append("invariant_breach:collateral_step:mcr")
        if abs(delta("ccr_bps")) > _RATIO_STEP_BPS:
            breaches.append("invariant_breach:collateral_step:ccr")
        if applied["mcr_bps"] < _RATIO_MIN_BPS:
            breaches.append("invariant_breach:collateral_bound:mcr")
        if applied["ccr_bps"] > _RATIO_MAX_BPS:
            breaches.append("invariant_breach:collateral_bound:ccr")
        if applied["mcr_bps"] > applied["ccr_bps"]:
            breaches.append("invariant_breach:collateral_order")
        if abs(delta("staker_bps")) > _WHALE_STEP_BPS:
            breaches.append("invariant_breach:whale_step")
        if applied["staker_bps"] > _WHALE_STAKER_BPS_MAX:
            breaches.append("invariant_breach:whale_bound")

    state_changing = admitted and any(
        applied[name] != state_before[name] for name in SURFACE_PARAMETER_NAMES_V1
    )
    for name in SURFACE_PARAMETER_NAMES_V1:
        moved = abs(applied[name] - state_before[name]) if state_changing else 0
        if used_after.get(name) != used_before.get(name, 0) + moved:
            breaches.append(f"invariant_breach:used_accounting:{name}")
    for name, limit in trajectory_budget.items():
        if used_after.get(name, 0) > limit:
            breaches.append(f"invariant_breach:budget_exceeded:{name}")
    return tuple(breaches)


def _chain_genesis(
    *,
    policy_hash: str,
    initial_state: Mapping[str, int],
    carry_in: Mapping[str, Any],
    trajectory_budget: Mapping[str, int],
) -> str:
    return _HASH_V0(
        _CHAIN_HASH_TAG,
        {
            "genesis": {
                "schema": AUTONOMOUS_GOVERNANCE_TRAJECTORY_SCHEMA_V1,
                "policy_hash": policy_hash,
                "initial_state": dict(initial_state),
                "carry_in": dict(carry_in),
                "trajectory_budget": dict(trajectory_budget),
            }
        },
    )


def _chain_link(*, prev: str, index: int, step_hash: str) -> str:
    return _HASH_V0(
        _CHAIN_HASH_TAG,
        {"prev": prev, "index": index, "step_hash": step_hash},
    )


def _structural_rejection_receipt(
    *,
    errors: Sequence[str],
    expected_policy_hash: str,
    policy_hash: str,
    initial_state: Mapping[str, int],
) -> dict[str, Any]:
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_TRAJECTORY_SCHEMA_V1,
        "status": STATUS_REJECTED_STRUCTURAL,
        "policy_id": "",
        "policy_hash": policy_hash,
        "expected_policy_hash": expected_policy_hash,
        "initial_state": dict(initial_state),
        "final_state": dict(initial_state),
        "carry_in": {},
        "trajectory_budget": {},
        "input_steps": (),
        "input_step_count": 0,
        "step_count": 0,
        "admitted_count": 0,
        "rejected_count": 0,
        "state_changing_count": 0,
        "cumulative_realized_drift": {},
        "trajectory_used_final": {},
        "previous_approved_deltas_final": {},
        "last_update_epoch_final": None,
        "chain_genesis": "",
        "chain_head": "",
        "halted_early": False,
        "halt_index": None,
        "invariant_report": {},
        "steps": (),
        "ok": False,
        "errors": tuple(errors),
        "not_claimed": _NOT_CLAIMED,
    }
    return {**body, "trajectory_hash": _HASH_V0(_TRAJECTORY_HASH_TAG, body)}


def _invariant_report_from_records(
    *,
    records: Sequence[Mapping[str, Any]],
    initial_state: Mapping[str, int],
    final_state: Mapping[str, int],
    carry_used: Mapping[str, int],
    used_final: Mapping[str, int],
    breach_errors: Sequence[str],
) -> dict[str, bool]:
    """Derive the trajectory-level invariant report from the step records.

    The first five flags summarize the absence of per-step breach families; the
    conservation flags are re-derived here from the records (a second code
    path, also reused verbatim by the verifier).
    """

    def family_clean(prefix: str) -> bool:
        return not any(str(error).startswith(prefix) for error in breach_errors)

    adopted = [record for record in records if record.get("adopted") is True]
    drift_conservation_ok = True
    drift_within_used_ok = True
    for name in SURFACE_PARAMETER_NAMES_V1:
        realized_sum = sum(
            int(record["realized_deltas"].get(name, 0)) for record in adopted
        )
        drift = int(final_state.get(name, 0)) - int(initial_state.get(name, 0))
        if drift != realized_sum:
            drift_conservation_ok = False
        moved = int(used_final.get(name, 0)) - int(carry_used.get(name, 0))
        if abs(drift) > moved:
            drift_within_used_ok = False
    return {
        "reject_is_noop_ok": family_clean("invariant_breach:reject_not_noop"),
        "admitted_applies_proposed_ok": family_clean(
            "invariant_breach:admitted_not_proposed"
        )
        and family_clean("invariant_breach:applied_state_shape"),
        "surface_caps_ok": all(
            family_clean(f"invariant_breach:{family}")
            for family in (
                "fee_",
                "funding_",
                "router_",
                "collateral_",
                "whale_",
            )
        ),
        "budget_accounting_ok": family_clean("invariant_breach:used_accounting"),
        "budget_within_limits_ok": family_clean("invariant_breach:budget_exceeded"),
        "drift_conservation_ok": drift_conservation_ok,
        "drift_within_trajectory_used_ok": drift_within_used_ok,
    }


def _input_encodability_errors(
    named_inputs: Sequence[tuple[str, object]]
) -> list[str]:
    """Refuse untrusted inputs that cannot enter a canonically hashed receipt.

    A surrogate field name, a recursion-bomb nesting, or an object whose
    __str__ raises is hostile to the receipt's own hashing, not to the
    governance math. Caught here, before any normalization quotes a key or any
    blob reaches the content hash, a hostile input becomes a deterministic
    structural rejection whose receipt still hashes — never a crash. Benign
    inputs are encodable, so this gate is transparent to every real trajectory.
    """

    return [
        f"trajectory_input_not_canonically_encodable:{name}"
        for name, value in named_inputs
        if value is not None and not is_canonically_encodable(value)
    ]


def run_autonomous_governance_surface_trajectory_v1(
    *,
    policy: Mapping[str, Any],
    initial_surface_state: Mapping[str, Any],
    steps: Sequence[Mapping[str, Any]],
    expected_policy_hash: str,
    last_update_epoch: int | None = None,
    trajectory_budget: Mapping[str, Any] | None = None,
    trajectory_used: Mapping[str, Any] | None = None,
    previous_approved_deltas: Mapping[str, Any] | None = None,
    previous_chain_head: str | None = None,
) -> dict[str, Any]:
    """Run a multi-step autonomous governance trajectory, fail-closed.

    Total function: every input yields a deterministic receipt. Structural
    defects reject the whole trajectory as a no-op. Per-step safety/gate
    rejections are recorded no-ops (`ok` stays True — fail-closed rejection is
    the system working). An invariant tripwire breach refuses the suspect state
    and halts with `ok=False`.

    `previous_chain_head` is an optional INPUT binding for session continuity
    (see `autonomous_governance_session.py`): a continuation trajectory pins the
    chain head of the trajectory it extends, so the session verifier can refuse
    carry-state resets at trajectory boundaries. When omitted, `carry_in` (and
    therefore every receipt hash) is byte-identical to the pre-session format —
    it is a pinned input like `expected_policy_hash`, never a self-claim.

    The receipt is self-contained: `verify_autonomous_governance_surface_trajectory_v1`
    re-runs it from the embedded inputs and the policy artifact alone.
    """

    # Gate the structural blob inputs that flow verbatim into the receipt body
    # or the content hash. The two type-validated scalars below
    # (expected_policy_hash, previous_chain_head) are gated at their own checks
    # so they keep their existing, more specific labels.
    encodability_errors = _input_encodability_errors(
        (
            ("policy", policy),
            ("initial_surface_state", initial_surface_state),
            ("steps", steps),
            ("trajectory_budget", trajectory_budget),
            ("trajectory_used", trajectory_used),
            ("previous_approved_deltas", previous_approved_deltas),
        )
    )
    if encodability_errors:
        return _structural_rejection_receipt(
            errors=encodability_errors,
            expected_policy_hash="",
            policy_hash="",
            initial_state={},
        )

    structural_errors: list[str] = []

    # A surrogate-bearing str passes the isinstance check but would crash the
    # carry_in hash; fold the encodability test into the existing label so the
    # refusal is `previous_chain_head_invalid` for every malformed head.
    if previous_chain_head is not None and (
        not isinstance(previous_chain_head, str)
        or not previous_chain_head
        or not is_canonically_encodable(previous_chain_head)
    ):
        structural_errors.append("previous_chain_head_invalid")
        previous_chain_head = None

    # Likewise a surrogate-bearing expected_policy_hash str: null it so the
    # existing `expected_policy_hash_required` path fires instead of the value
    # reaching the receipt body.
    if isinstance(expected_policy_hash, str) and not is_canonically_encodable(
        expected_policy_hash
    ):
        expected_policy_hash = ""
    if not isinstance(expected_policy_hash, str) or not expected_policy_hash:
        structural_errors.append("expected_policy_hash_required")
        expected_policy_hash = "" if not isinstance(expected_policy_hash, str) else expected_policy_hash

    normalized_policy, policy_errors = _normalize_policy(
        policy, parameter_names=SURFACE_PARAMETER_NAMES_V1
    )
    structural_errors.extend(policy_errors)

    policy_hash = _policy_content_hash_for_receipt(policy, structural_errors)
    if expected_policy_hash and policy_hash != expected_policy_hash:
        structural_errors.append("policy_hash_mismatch")

    structural_errors.extend(_validate_safety_envelope(normalized_policy))

    initial_state, initial_errors = _normalize_surface_state(initial_surface_state)
    structural_errors.extend(
        f"initial_{error}" for error in initial_errors
    )

    if trajectory_budget is not None:
        budget, budget_errors = _normalize_surface_int_map(
            trajectory_budget, name="trajectory_budget"
        )
    else:
        budget, budget_errors = _normalize_trajectory_budget(
            None, policy=normalized_policy
        )
    structural_errors.extend(budget_errors)

    for name in _movable_parameters(normalized_policy):
        if name not in budget:
            structural_errors.append(f"trajectory_budget_missing:{name}")

    carry_used, carry_used_errors = _normalize_surface_int_map(
        trajectory_used if trajectory_used is not None else {},
        name="trajectory_used",
    )
    structural_errors.extend(carry_used_errors)

    carry_prev, carry_prev_errors = _normalize_carry_deltas(previous_approved_deltas)
    structural_errors.extend(carry_prev_errors)

    if last_update_epoch is not None and (
        not _is_plain_int(last_update_epoch) or last_update_epoch < 0
    ):
        structural_errors.append("last_update_epoch must be a non-negative int")
        last_update_epoch = None

    validated_steps, step_errors = _validate_step_inputs(steps)
    structural_errors.extend(step_errors)

    if structural_errors:
        return _structural_rejection_receipt(
            errors=structural_errors,
            expected_policy_hash=expected_policy_hash,
            policy_hash=policy_hash,
            initial_state=initial_state if not initial_errors else {},
        )

    carry_in: dict[str, Any] = {
        "last_update_epoch": last_update_epoch,
        "trajectory_used": dict(carry_used),
        "previous_approved_deltas": dict(carry_prev),
    }
    if previous_chain_head is not None:
        carry_in["previous_chain_head"] = previous_chain_head
    chain = _chain_genesis(
        policy_hash=policy_hash,
        initial_state=initial_state,
        carry_in=carry_in,
        trajectory_budget=budget,
    )
    chain_genesis = chain

    state = dict(initial_state)
    used = {name: int(carry_used.get(name, 0)) for name in SURFACE_PARAMETER_NAMES_V1}
    prev_deltas = dict(carry_prev)
    update_epoch = last_update_epoch

    input_steps = tuple(
        {
            "index": step["index"],
            "observation": dict(step["observation"]),
            "current_epoch": step["current_epoch"],
            "proposal_epoch": step["proposal_epoch"],
        }
        for step in validated_steps
    )

    records: list[dict[str, Any]] = []
    breach_errors: list[str] = []
    admitted_count = 0
    rejected_count = 0
    state_changing_count = 0
    halted_early = False
    halt_index: int | None = None

    for step in validated_steps:
        index = int(step["index"])
        current_epoch = int(step["current_epoch"])
        committed_context_hash = governance_surface_context_hash_v1(
            surface_state=state,
            current_epoch=current_epoch,
            proposal_epoch=int(step["proposal_epoch"]),
            last_update_epoch=update_epoch,
            previous_approved_deltas=prev_deltas,
            trajectory_used=used,
        )
        outcome = _COMMIT_SURFACE_STEP(
            policy=policy,
            surface_state=state,
            observation=step["observation"],
            current_epoch=current_epoch,
            proposal_epoch=int(step["proposal_epoch"]),
            last_update_epoch=update_epoch,
            expected_policy_hash=expected_policy_hash,
            expected_committed_context_hash=committed_context_hash,
            previous_approved_deltas=prev_deltas,
            trajectory_budget=budget,
            trajectory_used=used,
        )
        admitted = outcome.get("admitted") is True
        applied_raw = outcome.get("applied_state")
        applied = dict(applied_raw) if isinstance(applied_raw, Mapping) else {}
        realized = {
            name: (int(applied[name]) - state[name])
            if _is_plain_int(applied.get(name))
            else 0
            for name in SURFACE_PARAMETER_NAMES_V1
        }
        state_changing = admitted and any(realized.values())
        used_after = dict(used)
        if state_changing:
            for name, delta in realized.items():
                used_after[name] = used_after[name] + abs(delta)

        audit_errors = _audit_step_transition(
            admitted=admitted,
            state_before=state,
            applied_state=applied,
            proposed_state=outcome.get("proposed_state", {}),
            used_before=used,
            used_after=used_after,
            trajectory_budget=budget,
        )

        receipt = outcome.get("receipt", {})
        receipt_errors = (
            tuple(str(error) for error in receipt.get("errors", ()))
            if isinstance(receipt, Mapping)
            else ()
        )
        action_id = (
            str(receipt.get("action_id", "")) if isinstance(receipt, Mapping) else ""
        )
        adopted = admitted and not audit_errors
        record: dict[str, Any] = {
            "index": index,
            "current_epoch": current_epoch,
            "admitted": admitted,
            "adopted": adopted,
            "reason": str(outcome.get("reason", "")),
            "action_id": action_id,
            "step_errors": receipt_errors,
            "invariant_breaches": audit_errors,
            "realized_deltas": realized,
            "state_before": dict(state),
            "state_after": {
                name: applied[name] if _is_plain_int(applied.get(name)) else state[name]
                for name in SURFACE_PARAMETER_NAMES_V1
            },
            "state_changing": state_changing,
            "trajectory_used_after": dict(used_after),
            "last_update_epoch_after": current_epoch if state_changing else update_epoch,
            "committed_context_hash": committed_context_hash,
            "step_hash": str(outcome.get("step_hash", "")),
            "receipt_hash": str(outcome.get("receipt_hash", "")),
        }
        chain = _chain_link(prev=chain, index=index, step_hash=record["step_hash"])
        record["chain_hash"] = chain
        records.append(record)

        if audit_errors:
            # The inner step broke its contract: refuse the suspect state and halt.
            breach_errors.extend(audit_errors)
            halted_early = True
            halt_index = index
            break

        if admitted:
            admitted_count += 1
            state = {name: int(applied[name]) for name in SURFACE_PARAMETER_NAMES_V1}
            used = used_after
            if state_changing:
                state_changing_count += 1
                prev_deltas = dict(realized)
                update_epoch = current_epoch
        else:
            rejected_count += 1

    final_state = dict(state)
    invariant_report = _invariant_report_from_records(
        records=records,
        initial_state=initial_state,
        final_state=final_state,
        carry_used=carry_used,
        used_final=used,
        breach_errors=breach_errors,
    )
    errors = tuple(breach_errors)
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_TRAJECTORY_SCHEMA_V1,
        "status": STATUS_HALTED_INVARIANT_BREACH if halted_early else STATUS_COMPLETED,
        "policy_id": str(normalized_policy.get("policy_id", "")),
        "policy_hash": policy_hash,
        "expected_policy_hash": expected_policy_hash,
        "initial_state": dict(initial_state),
        "final_state": final_state,
        "carry_in": carry_in,
        "trajectory_budget": dict(budget),
        "input_steps": input_steps,
        "input_step_count": len(input_steps),
        "step_count": len(records),
        "admitted_count": admitted_count,
        "rejected_count": rejected_count,
        "state_changing_count": state_changing_count,
        "cumulative_realized_drift": {
            name: final_state[name] - initial_state[name]
            for name in SURFACE_PARAMETER_NAMES_V1
        },
        "trajectory_used_final": dict(used),
        "previous_approved_deltas_final": dict(prev_deltas),
        "last_update_epoch_final": update_epoch,
        "chain_genesis": chain_genesis,
        "chain_head": chain,
        "halted_early": halted_early,
        "halt_index": halt_index,
        "invariant_report": invariant_report,
        "steps": tuple(records),
        "ok": not errors,
        "errors": errors,
        "not_claimed": _NOT_CLAIMED,
    }
    return {**body, "trajectory_hash": _HASH_V0(_TRAJECTORY_HASH_TAG, body)}


def _verification_failure(
    errors: Sequence[str],
    checks: Mapping[str, bool],
    *,
    presented_hash: str = "",
    recomputed_hash: str = "",
    trajectory_ok: bool = False,
) -> dict[str, Any]:
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_TRAJECTORY_VERIFICATION_SCHEMA_V1,
        "ok": False,
        "errors": tuple(errors),
        "checks": dict(checks),
        "presented_trajectory_hash": presented_hash,
        "recomputed_trajectory_hash": recomputed_hash,
        "trajectory_ok": trajectory_ok,
    }
    return {**body, "verification_hash": _HASH_V0(_VERIFICATION_HASH_TAG, body)}


def verify_autonomous_governance_surface_trajectory_v1(
    *,
    receipt: object,
    policy: object,
) -> dict[str, Any]:
    """Independently verify a trajectory receipt against the policy artifact.

    Trust the math, not the runner: the receipt embeds its inputs, so a client
    re-derives the entire trajectory — every gate decision, every threading
    update, every chain link — and refuses the receipt unless the recomputation
    is canonically identical. Checks:

    1. the presented `trajectory_hash` binds the presented body;
    2. the policy artifact hashes to the pinned `policy_hash`;
    3. an independent hash-chain walk over the presented step records;
    4. full deterministic replay from the embedded inputs, compared by
       canonical content hash (so a JSON round-trip of the receipt still
       verifies, and any semantic divergence fails).

    Verification proves fidelity, not success: a receipt for a halted or
    rejection-heavy trajectory verifies if it faithfully records that outcome.
    Read `trajectory_ok` for the trajectory's own ok bit.
    """

    checks = {
        "receipt_shape_ok": False,
        "trajectory_hash_binds_body": False,
        "policy_hash_matches": False,
        "status_verifiable": False,
        "chain_walk_ok": False,
        "replay_matches": False,
        "invariant_report_matches": False,
    }
    errors: list[str] = []

    if not isinstance(receipt, Mapping):
        return _verification_failure(["trajectory_receipt_must_be_object"], checks)
    # Refuse a receipt or policy that cannot enter the verification receipt's
    # own canonical hash (surrogate field, recursion-bomb nesting): a forgery
    # hostile to encoding must fail verification, not crash the verifier.
    if not is_canonically_encodable_without_size_limit(receipt):
        return _verification_failure(
            ["trajectory_receipt_not_canonically_encodable"], checks
        )
    if policy is not None and not is_canonically_encodable(policy):
        return _verification_failure(["policy_not_canonically_encodable"], checks)
    presented = dict(receipt)
    presented_hash_claim = presented.pop("trajectory_hash", None)
    if not isinstance(presented_hash_claim, str) or not presented_hash_claim:
        errors.append("trajectory_hash_missing")
        return _verification_failure(errors, checks)
    if presented.get("schema") != AUTONOMOUS_GOVERNANCE_TRAJECTORY_SCHEMA_V1:
        errors.append("trajectory_schema_invalid")
        return _verification_failure(errors, checks)
    checks["receipt_shape_ok"] = True

    try:
        presented_body_hash = _HASH_V0(_TRAJECTORY_HASH_TAG, presented)
    except (TypeError, ValueError):
        errors.append("trajectory_receipt_unhashable")
        return _verification_failure(errors, checks)
    if presented_body_hash != presented_hash_claim:
        errors.append("trajectory_hash_mismatch")
        return _verification_failure(
            errors, checks, presented_hash=presented_hash_claim
        )
    checks["trajectory_hash_binds_body"] = True
    trajectory_ok = presented.get("ok") is True

    policy_hash = ""
    if isinstance(policy, Mapping):
        try:
            policy_hash = policy_content_hash_v1(policy)
        except (TypeError, ValueError):
            errors.append("policy_hash_unavailable")
    else:
        errors.append("policy_must_be_object")
    if policy_hash and policy_hash == presented.get("policy_hash"):
        checks["policy_hash_matches"] = True
    else:
        errors.append("policy_hash_mismatch")

    if presented.get("status") == STATUS_REJECTED_STRUCTURAL:
        errors.append("structural_rejection_receipt_not_verifiable")
        return _verification_failure(
            errors,
            checks,
            presented_hash=presented_hash_claim,
            trajectory_ok=trajectory_ok,
        )
    checks["status_verifiable"] = True

    input_steps = presented.get("input_steps")
    step_records = presented.get("steps")
    carry_in = presented.get("carry_in")
    if (
        not isinstance(input_steps, Sequence)
        or isinstance(input_steps, (str, bytes, bytearray))
        or not isinstance(step_records, Sequence)
        or isinstance(step_records, (str, bytes, bytearray))
        or not isinstance(carry_in, Mapping)
        or not isinstance(presented.get("initial_state"), Mapping)
        or not isinstance(presented.get("trajectory_budget"), Mapping)
    ):
        errors.append("trajectory_receipt_fields_malformed")
        return _verification_failure(
            errors,
            checks,
            presented_hash=presented_hash_claim,
            trajectory_ok=trajectory_ok,
        )

    # Independent chain walk over the presented records (separate code path
    # from the replay below).
    chain_ok = True
    try:
        chain = _chain_genesis(
            policy_hash=str(presented.get("policy_hash", "")),
            initial_state={
                str(k): int(v) for k, v in dict(presented["initial_state"]).items()
            },
            carry_in=dict(carry_in),
            trajectory_budget={
                str(k): int(v) for k, v in dict(presented["trajectory_budget"]).items()
            },
        )
        if chain != presented.get("chain_genesis"):
            errors.append("chain_genesis_mismatch")
            chain_ok = False
        for record in step_records:
            if not isinstance(record, Mapping):
                errors.append("chain_record_malformed")
                chain_ok = False
                break
            chain = _chain_link(
                prev=chain,
                index=int(record.get("index", -1)),
                step_hash=str(record.get("step_hash", "")),
            )
            if chain != record.get("chain_hash"):
                errors.append(f"chain_link_mismatch:{record.get('index')}")
                chain_ok = False
                break
        if chain_ok and chain != presented.get("chain_head"):
            errors.append("chain_head_mismatch")
            chain_ok = False
    except (TypeError, ValueError):
        errors.append("chain_walk_failed")
        chain_ok = False
    checks["chain_walk_ok"] = chain_ok

    # Full deterministic replay from the embedded inputs.
    replay_ok = False
    recomputed_hash = ""
    invariant_matches = False
    try:
        if not isinstance(policy, Mapping):
            raise TypeError("policy_must_be_object")
        replay_steps = [
            {
                "observation": dict(step.get("observation", {})),
                "current_epoch": step.get("current_epoch"),
                "proposal_epoch": step.get("proposal_epoch"),
            }
            for step in input_steps
            if isinstance(step, Mapping)
        ]
        carried_head = carry_in.get("previous_chain_head")
        recomputed = run_autonomous_governance_surface_trajectory_v1(
            policy=policy,
            initial_surface_state=dict(presented["initial_state"]),
            steps=replay_steps,
            expected_policy_hash=str(presented.get("expected_policy_hash", "")),
            last_update_epoch=carry_in.get("last_update_epoch"),
            trajectory_budget=dict(presented["trajectory_budget"]),
            trajectory_used=dict(carry_in.get("trajectory_used", {})),
            previous_approved_deltas=dict(
                carry_in.get("previous_approved_deltas", {})
            ),
            previous_chain_head=(
                carried_head if isinstance(carried_head, str) else None
            ),
        )
        recomputed_hash = str(recomputed.get("trajectory_hash", ""))
        replay_ok = bool(recomputed_hash) and recomputed_hash == presented_body_hash
        if not replay_ok:
            errors.append("replay_divergence")
        recomputed_report = recomputed.get("invariant_report", {})
        presented_report = presented.get("invariant_report", {})
        invariant_matches = (
            isinstance(recomputed_report, Mapping)
            and isinstance(presented_report, Mapping)
            and dict(recomputed_report) == dict(presented_report)
        )
        if not invariant_matches:
            errors.append("invariant_report_mismatch")
    except (TypeError, ValueError):
        errors.append("replay_failed")
    checks["replay_matches"] = replay_ok
    checks["invariant_report_matches"] = invariant_matches

    ok = all(checks.values()) and not errors
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_TRAJECTORY_VERIFICATION_SCHEMA_V1,
        "ok": ok,
        "errors": tuple(errors),
        "checks": checks,
        "presented_trajectory_hash": presented_hash_claim,
        "recomputed_trajectory_hash": recomputed_hash,
        "trajectory_ok": trajectory_ok,
    }
    return {**body, "verification_hash": _HASH_V0(_VERIFICATION_HASH_TAG, body)}

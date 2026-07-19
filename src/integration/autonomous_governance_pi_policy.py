"""Frozen PI-policy artifact runtime for autonomous governance (production shape).

This module promotes the reference PI proposer
(`src/tau_specs/governance/gov_proposers.pi_propose`, velocity-form integer PI)
into the artifact-runtime discipline used by the frozen Q/EBRM path
(`autonomous_governance_q_policy.py`):

- the controller tuning is ONE hash-pinned artifact
  (`zenodex.autonomous_governance.pi_policy.v1`); the pin is re-checked inside
  the use boundary, so a swapped/mutated artifact is a hard fail-closed error;
- the committed governance surface and epochs can be bound to an expected
  committed-context hash (`governance_surface_context_hash_v1`), closing the
  proposer-asserted-`curr` hole at this boundary (the §5.2 binding
  precondition of `docs/AUTONOMOUS_GOVERNANCE_ARCHITECTURE.md`);
- the candidate is gated by the EXACT verified gate for the policy's surface,
  import-bound at module load (no forged-wrapper surface);
- a rejected or errored step is a TOTAL no-op — the proposed state equals the
  committed state AND the controller state does not advance — so a rejected
  step is replay-invisible, matching the epoch machine's no-op-on-reject
  discipline;
- every step emits a canonical, hash-bound receipt.

The proposer has NO authority: the gate decides admissibility, and live
application additionally requires the node-anchored admission path
(`autonomous_governance_live_registry.py` ->
`autonomous_governance_live_apply.py`).

NOT claimed: that the tuning is economically good, that `measured` is the true
market value (it inherits the oracle trust posture), or that this module alone
constitutes deployed governance authority.
"""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.autonomous_governance_q_policy import (
    _normalize_surface_state,
    governance_surface_context_hash_v1,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.tau_specs.governance import gov_gate, gov_proposers

AUTONOMOUS_GOVERNANCE_PI_POLICY_SCHEMA_V1 = "zenodex.autonomous_governance.pi_policy.v1"
AUTONOMOUS_GOVERNANCE_PI_STEP_SCHEMA_V1 = "zenodex.autonomous_governance.pi_surface_step.v1"

_PI_POLICY_HASH_TAG = "autonomous_governance_pi_policy_v1"
_PI_STEP_HASH_TAG = "autonomous_governance_pi_surface_step_v1"

# Trusted call surfaces, bound once at import (same discipline as
# autonomous_governance_q_policy.py): a call-time attribute lookup is
# monkeypatch-swappable, which would re-open the forged-gate surface.
_PI_PROPOSE = gov_proposers.pi_propose
_PI_CONFIG = gov_proposers.PIConfig
_PI_SCALAR_GATES = {
    "fee_bps": gov_gate.fee_revision_ok,
    "funding_cap_bps": gov_gate.funding_rate_revision_ok,
    "staker_bps": gov_gate.whale_defense_revision_ok,
}

_PI_POLICY_INT_FIELDS = (
    "setpoint",
    "kp_num",
    "kp_den",
    "ki_num",
    "ki_den",
    "deadband",
    "out_lo",
    "out_hi",
)

_NOT_CLAIMED = (
    "does_not_authorize_settlement",
    "does_not_claim_measured_value_truth",
    "does_not_claim_tuning_is_economically_good",
    "does_not_bypass_exact_gates",
)


def _is_plain_int(value: object) -> bool:
    return type(value) is int


def normalize_autonomous_governance_pi_policy_v1(
    policy: object,
) -> tuple[dict[str, Any], list[str]]:
    """Validate a PI policy artifact fail-closed; return (normalized, errors).

    The normalized artifact is a fresh plain dict (snapshot discipline: the
    caller's object is never read again after this returns).  Field validation
    delegates to the reference `PIConfig` constructor, so the artifact accepts
    exactly the tunings the reference controller accepts (plain ints, positive
    denominators, `deadband >= 0`, `out_lo <= out_hi`).
    """
    errors: list[str] = []
    if not isinstance(policy, Mapping):
        return {}, ["pi_policy_must_be_object"]
    schema = policy.get("schema")
    if schema != AUTONOMOUS_GOVERNANCE_PI_POLICY_SCHEMA_V1:
        errors.append("pi_policy_schema_mismatch")
    surface = policy.get("surface")
    if type(surface) is not str or surface not in _PI_SCALAR_GATES:
        errors.append("pi_policy_surface_unsupported")
        surface = ""
    fields: dict[str, int] = {}
    for name in _PI_POLICY_INT_FIELDS:
        value = policy.get(name)
        if not _is_plain_int(value):
            errors.append(f"pi_policy_{name}_must_be_plain_int")
        else:
            fields[name] = value
    extra = set(policy.keys()) - ({"schema", "surface"} | set(_PI_POLICY_INT_FIELDS))
    if extra:
        # An unknown key would be unvalidated semantic surface that still
        # changes the pinned hash; refuse rather than hash it silently.
        errors.append("pi_policy_unknown_keys")
    if not errors:
        try:
            _PI_CONFIG(**fields)
        except (TypeError, ValueError):
            errors.append("pi_policy_config_invalid")
    if errors:
        return {}, errors
    normalized = {
        "schema": AUTONOMOUS_GOVERNANCE_PI_POLICY_SCHEMA_V1,
        "surface": surface,
        **{name: fields[name] for name in _PI_POLICY_INT_FIELDS},
    }
    return normalized, []


def pi_policy_content_hash_v1(policy: object) -> str:
    """Canonical pin over a VALID PI policy artifact (fail-closed on invalid)."""
    normalized, errors = normalize_autonomous_governance_pi_policy_v1(policy)
    if errors:
        raise ValueError(f"invalid pi policy artifact: {errors}")
    return hash_v0(_PI_POLICY_HASH_TAG, normalized)


def evaluate_autonomous_governance_pi_policy_step_v1(
    *,
    policy: object,
    committed_surface_state: Mapping[str, Any],
    measured: object,
    prev_error: object,
    approved: object,
    proposal_epoch: object,
    current_epoch: object,
    last_update_epoch: object = None,
    expected_policy_hash: object = None,
    expected_committed_context_hash: object = None,
) -> dict[str, Any]:
    """One frozen PI step against committed state, gated by the exact gate.

    Production discipline:

    - `expected_policy_hash` is REQUIRED (a missing pin is an error, not a
      default): the step acts only on the exact pinned artifact;
    - if `expected_committed_context_hash` is supplied, it must equal the
      recomputed `governance_surface_context_hash_v1` over the committed
      surface state and epochs — a caller cannot substitute its own anchor;
    - any error or gate rejection yields a TOTAL no-op: `final_state` equals
      the committed state and `prev_error_out == prev_error` (the controller
      state does not advance on a step that did not commit).
    """
    errors: list[str] = []

    normalized_policy, policy_errors = normalize_autonomous_governance_pi_policy_v1(policy)
    errors.extend(policy_errors)
    policy_hash = ""
    if not policy_errors:
        policy_hash = hash_v0(_PI_POLICY_HASH_TAG, normalized_policy)

    expected_hash = expected_policy_hash if type(expected_policy_hash) is str else ""
    if not expected_hash:
        errors.append("pi_expected_policy_hash_required")
    elif policy_hash and policy_hash != expected_hash:
        errors.append("pi_expected_policy_hash_mismatch")

    state, state_errors = _normalize_surface_state(committed_surface_state)
    errors.extend(f"pi_committed_{error}" for error in state_errors)

    if not _is_plain_int(measured):
        errors.append("pi_measured_must_be_plain_int")
        measured = 0
    if not _is_plain_int(prev_error):
        errors.append("pi_prev_error_must_be_plain_int")
        prev_error = 0
    if type(approved) is not bool:
        errors.append("pi_approved_must_be_bool")
        approved = False
    context_inputs_ok = True
    if not _is_plain_int(proposal_epoch):
        errors.append("pi_proposal_epoch_must_be_plain_int")
        proposal_epoch = 0
        context_inputs_ok = False
    elif proposal_epoch < 0:
        errors.append("pi_proposal_epoch_must_be_nonnegative")
        proposal_epoch = 0
        context_inputs_ok = False
    if not _is_plain_int(current_epoch):
        errors.append("pi_current_epoch_must_be_plain_int")
        current_epoch = 0
        context_inputs_ok = False
    elif current_epoch < 0:
        errors.append("pi_current_epoch_must_be_nonnegative")
        current_epoch = 0
        context_inputs_ok = False
    if last_update_epoch is not None:
        if not _is_plain_int(last_update_epoch):
            errors.append("pi_last_update_epoch_must_be_plain_int")
            last_update_epoch = None
            context_inputs_ok = False
        elif last_update_epoch < 0:
            errors.append("pi_last_update_epoch_must_be_nonnegative")
            last_update_epoch = None
            context_inputs_ok = False

    context_hash = ""
    if not state_errors and context_inputs_ok:
        context_hash = governance_surface_context_hash_v1(
            surface_state=state,
            current_epoch=int(current_epoch),
            proposal_epoch=int(proposal_epoch),
            last_update_epoch=last_update_epoch
            if last_update_epoch is None
            else int(last_update_epoch),
        )
    expected_context = (
        expected_committed_context_hash
        if type(expected_committed_context_hash) is str
        else ""
    )
    if expected_context and context_hash and context_hash != expected_context:
        errors.append("pi_committed_context_hash_mismatch")

    surface = normalized_policy.get("surface", "") if normalized_policy else ""
    curr = state.get(surface, 0) if surface else 0

    candidate = curr
    prev_error_out = prev_error
    deadband_frozen = False
    gate_admitted = False
    if not errors:
        cfg = _PI_CONFIG(
            **{name: normalized_policy[name] for name in _PI_POLICY_INT_FIELDS}
        )
        result = _PI_PROPOSE(curr, measured, prev_error, cfg)
        candidate = result.proposed
        deadband_frozen = candidate == curr and result.prev_error == prev_error
        gate = _PI_SCALAR_GATES[surface]
        verdict = gate(approved, True, proposal_epoch, current_epoch, curr, candidate)
        if type(verdict) is not bool:
            errors.append("pi_gate_verdict_must_be_bool")
        else:
            gate_admitted = verdict
        if gate_admitted and not errors:
            # The controller state advances ONLY on an admitted step.
            prev_error_out = result.prev_error

    admitted = gate_admitted and not errors
    final_state = dict(state)
    if admitted and surface:
        final_state[surface] = candidate

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_PI_STEP_SCHEMA_V1,
        "ok": admitted,
        "admitted": admitted,
        "errors": tuple(errors),
        "policy_hash": policy_hash,
        "expected_policy_hash": expected_hash,
        "surface": surface,
        "curr": int(curr),
        "measured": int(measured),
        "prev_error_in": int(prev_error),
        "prev_error_out": int(prev_error_out),
        "candidate": int(candidate),
        "deadband_frozen": deadband_frozen,
        "gate_admitted": gate_admitted,
        "approved": bool(approved),
        "proposal_epoch": int(proposal_epoch),
        "current_epoch": int(current_epoch),
        "committed_context_hash": context_hash,
        "expected_committed_context_hash": expected_context,
        "committed_state": dict(state),
        "final_state": final_state,
        "not_claimed": _NOT_CLAIMED,
    }
    return {**body, "step_hash": hash_v0(_PI_STEP_HASH_TAG, body)}

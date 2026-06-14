"""Quorum-gated session-head pin: the single live head fork refusal needs.

`verify_autonomous_governance_surface_session_v1` proves a presented receipt
sequence is one correctly carried session, but it can only judge what it is
shown. Two continuations of the same parent both verify; whichever an attacker
withholds, the other looks like "the" session. Refusing forks therefore needs
a single live head: one pinned record per session that an admission path
advances only on verified continuation, exactly the policy-pin lineage pattern
("who approves the brain" -> "who bounds the campaign" -> this module: "which
campaign is live").

Records and rules:

- `open_autonomous_governance_session_v1` creates the genesis head. Starting
  an autonomous campaign is an authority decision: the genesis exists only if
  a signature quorum approved it inline through
  `evaluate_governance_authority_v0` (same discipline as policy rotation: a
  pre-made receipt is integrity, not authority). The signed payload binds the
  policy hash, the policy-pin hash (the quorum-authorized brain), the genesis
  trajectory hash and chain head, the registry hash, and the proposal epoch,
  an approval cannot be replayed for a different brain, a different genesis
  trajectory, or under a different registry. The genesis trajectory receipt
  must fully verify and be session-fresh (no carried head, zero used, empty
  oscillation history, no cooldown carry).
- `advance_autonomous_governance_session_v1` moves the head. Advancing is not
  quorum-gated, because bounded autonomy inside the session is the point, but it is
  math-gated: the presented receipt must fully verify against the pinned
  policy and extend the pinned head exactly (chain-head linkage plus carry
  equality plus budget/policy equality plus cross-boundary epoch
  monotonicity, re-derived here independently of the session verifier), and
  the session-lifetime accounting tripwire must hold
  (|final - session_initial| <= used <= budget, used monotone).
- `verify_session_pin_chain_v1` audits an archived lineage in a DECLARED
  SCOPE. Pin records are self-hashed summaries, so without the archived
  trajectory receipts the walk proves linearity and internal coherence only
  (`scope="integrity_only"`, `authenticity_verified=False`). An internally
  consistent lineage can be forged wholesale. Passing the receipts (one per
  pin) upgrades the audit: every receipt is replayed through the trajectory
  verifier, every pinned summary is re-derived from its receipt, the genesis
  is re-checked session-fresh, and every boundary is re-checked between the
  actual receipts (`scope="receipts_replayed"`,
  `authenticity_verified=True`).

Honest boundaries: only the receipts-replayed scope proves every head move
was a verified continuation; integrity-only is for records already trusted
from the live single-head store, never for third-party archives. Keeping
exactly one live head per session (compare-and-swap on the current record,
distributing it) is the deployed store / ordering-DA layer's job, as with the
policy pin. Re-verifying the genesis quorum's BLS signatures later requires
the archived envelopes.
"""

from __future__ import annotations

from typing import Any, Callable, Mapping, Sequence, TypeGuard

from src.integration.autonomous_governance_hostile_input import (
    is_canonically_encodable,
    safe_field_label,
)
from src.integration.autonomous_governance_policy_pin import (
    verify_policy_pin_v1,
)
from src.integration.autonomous_governance_q_policy import (
    SURFACE_PARAMETER_NAMES_V1,
    _policy_content_hash_for_receipt,
)
from src.integration.autonomous_governance_session import (
    _first_step_epoch,
    _last_input_epoch,
    _policy_budget_binding_errors,
)
from src.integration.autonomous_governance_trajectory import (
    STATUS_COMPLETED,
    verify_autonomous_governance_surface_trajectory_v1,
)
from src.integration.zeno_governance_authority import (
    GOVERNANCE_ACTION_PAYLOAD_KIND_V0,
    evaluate_governance_authority_v0,
    governance_action_payload_hash_v0,
)
from src.integration.zeno_key_manager_v0 import KeyBackendDescriptor
from src.integration.zeno_ledger_v0 import hash_v0

_HASH_V0: Callable[[str, object], str] = hash_v0
_EVALUATE_AUTHORITY = evaluate_governance_authority_v0
_PAYLOAD_HASH = governance_action_payload_hash_v0
_VERIFY_TRAJECTORY = verify_autonomous_governance_surface_trajectory_v1
_VERIFY_POLICY_PIN = verify_policy_pin_v1

AUTONOMOUS_GOVERNANCE_SESSION_PIN_SCHEMA_V1 = (
    "zenodex.autonomous_governance.session_pin.v1"
)
AUTONOMOUS_GOVERNANCE_SESSION_OPEN_SCHEMA_V1 = (
    "zenodex.autonomous_governance.session_open.v1"
)
AUTONOMOUS_GOVERNANCE_SESSION_ADVANCE_SCHEMA_V1 = (
    "zenodex.autonomous_governance.session_advance.v1"
)
SESSION_OPEN_ACTION_ID_V1 = "gov:open-autonomous-governance-session"
SESSION_OPEN_ACTION_KIND_V1 = "autonomous_governance_session_genesis_v1"

_SESSION_PIN_HASH_TAG = "autonomous_governance_session_pin_v1"
_SESSION_OPEN_HASH_TAG = "autonomous_governance_session_open_v1"
_SESSION_ADVANCE_HASH_TAG = "autonomous_governance_session_advance_v1"
_REGISTRY_HASH_TAG = "autonomous_governance_signer_registry_pin_v1"

SESSION_GENESIS_PREVIOUS_PIN_HASH = ""

PIN_KIND_GENESIS = "genesis"
PIN_KIND_ADVANCE = "advance"

_SESSION_PIN_FIELDS_V1 = (
    "schema",
    "kind",
    "policy_id",
    "policy_hash",
    "policy_pin_hash",
    "registry_hash",
    "advance_index",
    "previous_session_pin_hash",
    "session_genesis_pin_hash",
    "trajectory_hash",
    "trajectory_chain_head",
    "session_initial_state",
    "segment_initial_state",
    "final_state",
    "trajectory_used_final",
    "previous_approved_deltas_final",
    "last_update_epoch_final",
    "last_input_epoch",
    "trajectory_budget",
    "authority_receipt_hash",
    "pinned_at_epoch",
    "pin_hash",
)

_NOT_CLAIMED = (
    "does_not_keep_the_single_live_head_stored_or_distributed",
    "does_not_verify_archived_signatures_later",
    "does_not_replace_full_session_receipt_verification",
)


def _is_plain_int(value: object) -> TypeGuard[int]:
    return type(value) is int


def _session_pin_body_hash(body: Mapping[str, Any]) -> str:
    return _HASH_V0(_SESSION_PIN_HASH_TAG, dict(body))


def _safe_field_label(key: object) -> str:
    """Total, canonical-safe label for a (possibly hostile) field name.

    Delegates to the shared guard so a name whose own __str__/__repr__ raises
    becomes a fixed placeholder rather than crashing error formatting; benign
    names pass through byte-identically. Surrogate names are ASCII-escaped.
    """

    return safe_field_label(key)


def session_registry_hash_v1(registry: object) -> str:
    """Same canonical registry hash domain as the policy-pin lineage."""

    if not isinstance(registry, Mapping):
        raise TypeError("registry must be a JSON object")
    return _HASH_V0(_REGISTRY_HASH_TAG, dict(registry))


def session_genesis_payload_v1(
    *,
    policy_hash: str,
    policy_pin_hash: str,
    genesis_trajectory_hash: str,
    genesis_chain_head: str,
    registry_hash: str,
    proposal_epoch: int,
) -> dict[str, Any]:
    """The exact governance-action payload a session-opening quorum signs."""

    return {
        "action_id": SESSION_OPEN_ACTION_ID_V1,
        "kind": SESSION_OPEN_ACTION_KIND_V1,
        "policy_hash": policy_hash,
        "policy_pin_hash": policy_pin_hash,
        "genesis_trajectory_hash": genesis_trajectory_hash,
        "genesis_chain_head": genesis_chain_head,
        "registry_hash": registry_hash,
        "proposal_epoch": proposal_epoch,
    }


def _surface_int_map(raw: object) -> dict[str, int] | None:
    """Exact nine-parameter non-negative-int map, else None."""

    if not isinstance(raw, Mapping):
        return None
    out: dict[str, int] = {}
    for name in SURFACE_PARAMETER_NAMES_V1:
        value = raw.get(name)
        if not _is_plain_int(value) or value < 0:
            return None
        out[name] = value
    if set(raw) != set(SURFACE_PARAMETER_NAMES_V1):
        return None
    return out


def _signed_int_map(raw: object) -> dict[str, int] | None:
    """Subset map of surface parameters to plain ints (deltas), else None."""

    if not isinstance(raw, Mapping):
        return None
    out: dict[str, int] = {}
    for key, value in raw.items():
        if key not in SURFACE_PARAMETER_NAMES_V1 or not _is_plain_int(value):
            return None
        out[str(key)] = value
    return out


def _budget_map(raw: object) -> dict[str, int] | None:
    if not isinstance(raw, Mapping):
        return None
    out: dict[str, int] = {}
    for key, value in raw.items():
        if key not in SURFACE_PARAMETER_NAMES_V1 or not _is_plain_int(value) or value < 0:
            return None
        out[str(key)] = value
    return out


def _validate_session_pin(pin: object) -> tuple[dict[str, Any], list[str]]:
    """Exact-shape, hash-recomputed, kind-consistent session-pin validation."""

    if not isinstance(pin, Mapping):
        return {}, ["session_pin_must_be_object"]
    errors: list[str] = []
    for key in pin:
        if key not in _SESSION_PIN_FIELDS_V1:
            errors.append(f"session_pin_unknown_field:{_safe_field_label(key)}")
    for key in _SESSION_PIN_FIELDS_V1:
        if key not in pin:
            errors.append(f"session_pin_missing_field:{key}")
    if errors:
        return {}, errors
    if pin.get("schema") != AUTONOMOUS_GOVERNANCE_SESSION_PIN_SCHEMA_V1:
        errors.append("session_pin_schema_invalid")
    kind = pin.get("kind")
    if kind not in (PIN_KIND_GENESIS, PIN_KIND_ADVANCE):
        errors.append("session_pin_kind_invalid")
    for key in (
        "policy_id",
        "policy_hash",
        "policy_pin_hash",
        "registry_hash",
        "previous_session_pin_hash",
        "session_genesis_pin_hash",
        "trajectory_hash",
        "trajectory_chain_head",
        "authority_receipt_hash",
        "pin_hash",
    ):
        if not isinstance(pin.get(key), str):
            errors.append(f"session_pin_field_must_be_string:{key}")
    for key in ("advance_index", "last_input_epoch", "pinned_at_epoch"):
        if not _is_plain_int(pin.get(key)) or int(pin.get(key, -1)) < 0:
            errors.append(f"session_pin_field_must_be_nonnegative_int:{key}")
    last_update = pin.get("last_update_epoch_final")
    if last_update is not None and (not _is_plain_int(last_update) or last_update < 0):
        errors.append("session_pin_field_invalid:last_update_epoch_final")
    for key in ("session_initial_state", "segment_initial_state", "final_state", "trajectory_used_final"):
        if _surface_int_map(pin.get(key)) is None:
            errors.append(f"session_pin_field_invalid:{key}")
    if _signed_int_map(pin.get("previous_approved_deltas_final")) is None:
        errors.append("session_pin_field_invalid:previous_approved_deltas_final")
    if _budget_map(pin.get("trajectory_budget")) is None:
        errors.append("session_pin_field_invalid:trajectory_budget")
    if errors:
        return {}, errors

    if kind == PIN_KIND_GENESIS:
        if pin.get("advance_index") != 0:
            errors.append("session_pin_genesis_index_must_be_zero")
        if pin.get("previous_session_pin_hash") != SESSION_GENESIS_PREVIOUS_PIN_HASH:
            errors.append("session_pin_genesis_must_anchor_empty")
        if pin.get("session_genesis_pin_hash") != "":
            errors.append("session_pin_genesis_self_anchor_must_be_empty")
        if not pin.get("authority_receipt_hash"):
            errors.append("session_pin_genesis_requires_authority_receipt")
        if dict(pin["segment_initial_state"]) != dict(pin["session_initial_state"]):
            errors.append("session_pin_genesis_initial_state_mismatch")
    else:
        if int(pin["advance_index"]) < 1:
            errors.append("session_pin_advance_index_must_be_positive")
        if not pin.get("previous_session_pin_hash"):
            errors.append("session_pin_advance_requires_previous")
        if not pin.get("session_genesis_pin_hash"):
            errors.append("session_pin_advance_requires_genesis_anchor")
        if pin.get("authority_receipt_hash") != "":
            errors.append("session_pin_advance_must_not_claim_authority")
    if errors:
        return {}, errors

    normalized = {key: pin[key] for key in _SESSION_PIN_FIELDS_V1}
    body = dict(normalized)
    claimed = body.pop("pin_hash")
    try:
        recomputed = _session_pin_body_hash(body)
    except (TypeError, ValueError):
        # A known string field can still carry canonical-JSON-rejected content
        # (unpaired surrogates); a hostile pin must refuse, not crash the
        # recompute.
        errors.append("session_pin_unhashable")
        return {}, errors
    if recomputed != claimed:
        errors.append("session_pin_hash_mismatch")
        return {}, errors
    return normalized, []


def _genesis_freshness_errors(receipt: Mapping[str, Any]) -> list[str]:
    """Session-fresh genesis rules, re-derived from the receipt's carry-in.

    A carried-in past without a verifiable parent is indistinguishable from a
    forged reset, so the genesis of a session must start from nothing.
    """

    errors: list[str] = []
    carry_raw = receipt.get("carry_in")
    carry = dict(carry_raw) if isinstance(carry_raw, Mapping) else {}
    if "previous_chain_head" in carry:
        errors.append("session_genesis_carries_chain_head")
    if any(
        _is_plain_int(value) and value != 0
        for value in dict(carry.get("trajectory_used", {}) or {}).values()
    ):
        errors.append("session_genesis_used_not_zero")
    if dict(carry.get("previous_approved_deltas", {}) or {}):
        errors.append("session_genesis_oscillation_history_not_empty")
    if carry.get("last_update_epoch") is not None:
        errors.append("session_genesis_cooldown_carry_not_none")
    return errors


def _receipt_summary(
    receipt: Mapping[str, Any], errors: list[str], *, prefix: str
) -> dict[str, Any]:
    """Extract the pinned summary from a VERIFIED trajectory receipt."""

    summary: dict[str, Any] = {}
    if receipt.get("status") != STATUS_COMPLETED or receipt.get("ok") is not True:
        errors.append(f"{prefix}_receipt_not_extendable:{receipt.get('status')}")
        return summary
    final_state = _surface_int_map(receipt.get("final_state"))
    initial_state = _surface_int_map(receipt.get("initial_state"))
    used_final = _surface_int_map(receipt.get("trajectory_used_final"))
    prev_deltas = _signed_int_map(receipt.get("previous_approved_deltas_final"))
    budget = _budget_map(receipt.get("trajectory_budget"))
    last_epoch = _last_input_epoch(receipt)
    last_update = receipt.get("last_update_epoch_final")
    if (
        final_state is None
        or initial_state is None
        or used_final is None
        or prev_deltas is None
        or budget is None
        or last_epoch is None
        or (last_update is not None and not _is_plain_int(last_update))
        or not isinstance(receipt.get("trajectory_hash"), str)
        or not isinstance(receipt.get("chain_head"), str)
        or not receipt.get("trajectory_hash")
        or not receipt.get("chain_head")
    ):
        errors.append(f"{prefix}_receipt_summary_unreadable")
        return summary
    summary.update(
        {
            "initial_state": initial_state,
            "final_state": final_state,
            "trajectory_used_final": used_final,
            "previous_approved_deltas_final": prev_deltas,
            "trajectory_budget": budget,
            "last_input_epoch": int(last_epoch),
            "last_update_epoch_final": last_update,
            "trajectory_hash": str(receipt["trajectory_hash"]),
            "chain_head": str(receipt["chain_head"]),
            "policy_hash": str(receipt.get("policy_hash", "")),
            "policy_id": str(receipt.get("policy_id", "")),
        }
    )
    return summary


def _boundary_errors(
    *,
    head: Mapping[str, Any],
    receipt: Mapping[str, Any],
    summary: Mapping[str, Any],
    prefix: str,
) -> list[str]:
    """Every boundary-carry rule between a pinned head and the next receipt."""

    errors: list[str] = []
    carry_raw = receipt.get("carry_in")
    carry = dict(carry_raw) if isinstance(carry_raw, Mapping) else {}
    if carry.get("previous_chain_head") != head["trajectory_chain_head"]:
        errors.append(f"{prefix}_chain_head_mismatch")
    if dict(summary["initial_state"]) != dict(head["final_state"]):
        errors.append(f"{prefix}_initial_state_mismatch")
    if dict(carry.get("trajectory_used", {}) or {}) != dict(
        head["trajectory_used_final"]
    ):
        errors.append(f"{prefix}_carry_used_mismatch")
    if dict(carry.get("previous_approved_deltas", {}) or {}) != dict(
        head["previous_approved_deltas_final"]
    ):
        errors.append(f"{prefix}_carry_oscillation_history_mismatch")
    if carry.get("last_update_epoch") != head["last_update_epoch_final"]:
        errors.append(f"{prefix}_carry_cooldown_mismatch")
    if dict(summary["trajectory_budget"]) != dict(head["trajectory_budget"]):
        errors.append(f"{prefix}_budget_mismatch")
    if str(summary["policy_hash"]) != str(head["policy_hash"]):
        errors.append(f"{prefix}_receipt_policy_hash_mismatch")
    first_epoch = _first_step_epoch(receipt.get("input_steps"))
    if first_epoch is None or first_epoch <= int(head["last_input_epoch"]):
        errors.append(f"{prefix}_epochs_not_strictly_increasing")
    return errors


_PIN_RECEIPT_BINDING_FIELDS = (
    ("trajectory_hash", "trajectory_hash"),
    ("trajectory_chain_head", "chain_head"),
    ("segment_initial_state", "initial_state"),
    ("final_state", "final_state"),
    ("trajectory_used_final", "trajectory_used_final"),
    ("previous_approved_deltas_final", "previous_approved_deltas_final"),
    ("last_update_epoch_final", "last_update_epoch_final"),
    ("last_input_epoch", "last_input_epoch"),
    ("trajectory_budget", "trajectory_budget"),
    ("policy_hash", "policy_hash"),
    ("policy_id", "policy_id"),
)


def _pin_receipt_binding_errors(
    pin: Mapping[str, Any],
    summary: Mapping[str, Any],
    *,
    prefix: str,
) -> list[str]:
    """The pinned summary must equal the receipt-derived facts, field by field."""

    errors: list[str] = []
    for pin_field, summary_field in _PIN_RECEIPT_BINDING_FIELDS:
        pinned = pin[pin_field]
        derived = summary[summary_field]
        if isinstance(pinned, Mapping) or isinstance(derived, Mapping):
            matches = isinstance(pinned, Mapping) and isinstance(
                derived, Mapping
            ) and dict(pinned) == dict(derived)
        else:
            matches = pinned == derived
        if not matches:
            errors.append(f"{prefix}_pin_receipt_binding_mismatch:{pin_field}")
    return errors


def _session_accounting_errors(
    *,
    session_initial_state: Mapping[str, int],
    summary: Mapping[str, Any],
    previous_used: Mapping[str, int],
    prefix: str,
) -> list[str]:
    """Session-lifetime tripwire, re-derived from the summaries."""

    errors: list[str] = []
    final_state = dict(summary["final_state"])
    used_final = dict(summary["trajectory_used_final"])
    budget = dict(summary["trajectory_budget"])
    for name in SURFACE_PARAMETER_NAMES_V1:
        drift = int(final_state[name]) - int(session_initial_state.get(name, 0))
        if abs(drift) > int(used_final[name]):
            errors.append(f"{prefix}_session_drift_exceeds_used:{name}")
        if int(used_final[name]) < int(previous_used.get(name, 0)):
            errors.append(f"{prefix}_session_used_not_monotone:{name}")
    for name, limit in budget.items():
        if int(used_final.get(name, 0)) > int(limit):
            errors.append(f"{prefix}_session_used_exceeds_budget:{name}")
    return errors


def open_autonomous_governance_session_v1(
    *,
    policy: object,
    policy_pin: object,
    genesis_receipt: object,
    registry: object,
    signature_envelopes: Sequence[Mapping[str, Any]],
    current_epoch: int,
    proposal_epoch: int,
    min_delay_epochs: int,
    tau_policy_receipt: Mapping[str, Any],
    backend_descriptors: Sequence[KeyBackendDescriptor | Mapping[str, Any]],
    evidence_claims: Sequence[Mapping[str, Any]] = (),
    required_evidence_claims: Sequence[str] = (),
    production_mode: bool = True,
) -> dict[str, Any]:
    """Open a session: pin the genesis head under inline quorum authority."""

    errors: list[str] = []

    # A policy/registry hostile to canonical hashing (recursion-bomb nesting)
    # would crash the genesis content hash before the session could refuse it.
    policy_for_hash: object = policy
    if policy is not None and not is_canonically_encodable(policy):
        errors.append("policy_not_canonically_encodable")
        policy_for_hash = {}
    registry_for_hash: object = registry
    if registry is not None and not is_canonically_encodable(registry):
        errors.append("registry_not_canonically_encodable")
        registry_for_hash = {}
    if not is_canonically_encodable(evidence_claims):
        errors.append("evidence_claims_not_canonically_encodable")
        evidence_claims = ()
    if not is_canonically_encodable(required_evidence_claims):
        errors.append("required_evidence_claims_not_canonically_encodable")
        required_evidence_claims = ()

    pin_verification = _VERIFY_POLICY_PIN(
        pin=policy_pin, policy=policy_for_hash, registry=registry_for_hash
    )
    policy_pin_hash = str(pin_verification.get("pin_hash", ""))
    if pin_verification.get("ok") is not True or not (
        pin_verification.get("policy_bound") is True
        and pin_verification.get("registry_bound") is True
    ):
        errors.append("session_policy_pin_unverified")
        errors.extend(
            f"policy_pin:{error}" for error in pin_verification.get("errors", ())
        )

    policy_hash = _policy_content_hash_for_receipt(policy_for_hash, errors)

    receipt_verification = _VERIFY_TRAJECTORY(
        receipt=genesis_receipt, policy=policy_for_hash
    )
    summary: dict[str, Any] = {}
    if receipt_verification.get("ok") is not True:
        errors.append("session_genesis_receipt_unverified")
        errors.extend(
            f"genesis_receipt:{error}"
            for error in receipt_verification.get("errors", ())
        )
    elif isinstance(genesis_receipt, Mapping):
        summary = _receipt_summary(genesis_receipt, errors, prefix="session_genesis")
        errors.extend(_genesis_freshness_errors(genesis_receipt))
        _, budget_errors = _policy_budget_binding_errors(
            policy=policy_for_hash,
            receipt_budget=summary.get("trajectory_budget"),
            prefix="session_genesis",
        )
        errors.extend(budget_errors)

    registry_hash = ""
    try:
        registry_hash = session_registry_hash_v1(registry)
    except TypeError:
        errors.append("registry_must_be_object")

    normalized_proposal_epoch = proposal_epoch if _is_plain_int(proposal_epoch) else -1
    if normalized_proposal_epoch < 0:
        errors.append("proposal_epoch must be a non-negative int")
        normalized_proposal_epoch = 0

    payload = session_genesis_payload_v1(
        policy_hash=policy_hash,
        policy_pin_hash=policy_pin_hash,
        genesis_trajectory_hash=str(summary.get("trajectory_hash", "")),
        genesis_chain_head=str(summary.get("chain_head", "")),
        registry_hash=registry_hash,
        proposal_epoch=normalized_proposal_epoch,
    )
    payload_hash = _PAYLOAD_HASH(payload)

    authority_receipt = _EVALUATE_AUTHORITY(
        action_id=SESSION_OPEN_ACTION_ID_V1,
        payload_kind=GOVERNANCE_ACTION_PAYLOAD_KIND_V0,
        payload_hash=payload_hash,
        registry=registry if isinstance(registry, Mapping) else {},
        signature_envelopes=signature_envelopes,
        current_epoch=current_epoch,
        proposal_epoch=proposal_epoch,
        min_delay_epochs=min_delay_epochs,
        tau_policy_receipt=tau_policy_receipt,
        backend_descriptors=backend_descriptors,
        evidence_claims=evidence_claims,
        required_evidence_claims=required_evidence_claims,
        production_mode=production_mode,
    )
    if authority_receipt.get("ok") is not True:
        errors.append("authority_rejected")
        errors.extend(
            f"authority:{error}" for error in authority_receipt.get("errors", ())
        )
    if authority_receipt.get("quorum_report") is None:
        if "authority_rejected" not in errors:
            errors.append("authority_quorum_missing")

    pin: dict[str, Any] = {}
    if not errors:
        pin_body = {
            "schema": AUTONOMOUS_GOVERNANCE_SESSION_PIN_SCHEMA_V1,
            "kind": PIN_KIND_GENESIS,
            "policy_id": str(summary["policy_id"]),
            "policy_hash": policy_hash,
            "policy_pin_hash": policy_pin_hash,
            "registry_hash": registry_hash,
            "advance_index": 0,
            "previous_session_pin_hash": SESSION_GENESIS_PREVIOUS_PIN_HASH,
            "session_genesis_pin_hash": "",
            "trajectory_hash": str(summary["trajectory_hash"]),
            "trajectory_chain_head": str(summary["chain_head"]),
            "session_initial_state": dict(summary["initial_state"]),
            "segment_initial_state": dict(summary["initial_state"]),
            "final_state": dict(summary["final_state"]),
            "trajectory_used_final": dict(summary["trajectory_used_final"]),
            "previous_approved_deltas_final": dict(
                summary["previous_approved_deltas_final"]
            ),
            "last_update_epoch_final": summary["last_update_epoch_final"],
            "last_input_epoch": int(summary["last_input_epoch"]),
            "trajectory_budget": dict(summary["trajectory_budget"]),
            "authority_receipt_hash": str(authority_receipt.get("receipt_hash", "")),
            "pinned_at_epoch": int(authority_receipt.get("current_epoch", 0)),
        }
        pin = {**pin_body, "pin_hash": _session_pin_body_hash(pin_body)}

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SESSION_OPEN_SCHEMA_V1,
        "open_payload": payload,
        "open_payload_hash": payload_hash,
        "authority_receipt": authority_receipt,
        "pin": pin,
        "ok": not errors,
        "errors": tuple(errors),
        "not_claimed": _NOT_CLAIMED,
    }
    return {**body, "open_hash": _HASH_V0(_SESSION_OPEN_HASH_TAG, body)}


def advance_autonomous_governance_session_v1(
    *,
    current_pin: object,
    receipt: object,
    policy: object,
) -> dict[str, Any]:
    """Advance the session head on a verified continuation, math-gated.

    Every boundary rule the session verifier enforces between two receipts is
    re-derived here between the pinned summary and the presented receipt.
    the head cannot move on chain-head linkage alone.
    """

    errors: list[str] = []
    # A policy hostile to its own content hash (recursion-bomb nesting) would
    # crash before the head could refuse it; gate it fail-closed.
    policy_for_hash: object = policy
    if policy is not None and not is_canonically_encodable(policy):
        errors.append("policy_not_canonically_encodable")
        policy_for_hash = {}
    head, head_errors = _validate_session_pin(current_pin)
    errors.extend(f"current_{error}" for error in head_errors)

    policy_hash = _policy_content_hash_for_receipt(policy_for_hash, errors)
    if head and policy_hash and policy_hash != head.get("policy_hash"):
        errors.append("advance_policy_hash_mismatch")
    if head:
        _, budget_errors = _policy_budget_binding_errors(
            policy=policy_for_hash,
            receipt_budget=head.get("trajectory_budget"),
            prefix="current",
        )
        errors.extend(budget_errors)

    receipt_verification = _VERIFY_TRAJECTORY(receipt=receipt, policy=policy_for_hash)
    summary: dict[str, Any] = {}
    if receipt_verification.get("ok") is not True:
        errors.append("advance_receipt_unverified")
        errors.extend(
            f"advance_receipt:{error}"
            for error in receipt_verification.get("errors", ())
        )
    elif isinstance(receipt, Mapping):
        summary = _receipt_summary(receipt, errors, prefix="advance")
        _, budget_errors = _policy_budget_binding_errors(
            policy=policy_for_hash,
            receipt_budget=summary.get("trajectory_budget"),
            prefix="advance",
        )
        errors.extend(budget_errors)

    if head and summary and isinstance(receipt, Mapping):
        errors.extend(
            _boundary_errors(
                head=head, receipt=receipt, summary=summary, prefix="advance"
            )
        )
        errors.extend(
            _session_accounting_errors(
                session_initial_state=dict(head["session_initial_state"]),
                summary=summary,
                previous_used=dict(head["trajectory_used_final"]),
                prefix="advance",
            )
        )

    pin: dict[str, Any] = {}
    if not errors:
        session_genesis_pin_hash = (
            str(head["pin_hash"])
            if head["kind"] == PIN_KIND_GENESIS
            else str(head["session_genesis_pin_hash"])
        )
        pin_body = {
            "schema": AUTONOMOUS_GOVERNANCE_SESSION_PIN_SCHEMA_V1,
            "kind": PIN_KIND_ADVANCE,
            "policy_id": str(head["policy_id"]),
            "policy_hash": str(head["policy_hash"]),
            "policy_pin_hash": str(head["policy_pin_hash"]),
            "registry_hash": str(head["registry_hash"]),
            "advance_index": int(head["advance_index"]) + 1,
            "previous_session_pin_hash": str(head["pin_hash"]),
            "session_genesis_pin_hash": session_genesis_pin_hash,
            "trajectory_hash": str(summary["trajectory_hash"]),
            "trajectory_chain_head": str(summary["chain_head"]),
            "session_initial_state": dict(head["session_initial_state"]),
            "segment_initial_state": dict(summary["initial_state"]),
            "final_state": dict(summary["final_state"]),
            "trajectory_used_final": dict(summary["trajectory_used_final"]),
            "previous_approved_deltas_final": dict(
                summary["previous_approved_deltas_final"]
            ),
            "last_update_epoch_final": summary["last_update_epoch_final"],
            "last_input_epoch": int(summary["last_input_epoch"]),
            "trajectory_budget": dict(summary["trajectory_budget"]),
            "authority_receipt_hash": "",
            "pinned_at_epoch": int(summary["last_input_epoch"]),
        }
        pin = {**pin_body, "pin_hash": _session_pin_body_hash(pin_body)}

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SESSION_ADVANCE_SCHEMA_V1,
        "pin": pin,
        "ok": not errors,
        "errors": tuple(errors),
        "not_claimed": _NOT_CLAIMED,
    }
    return {**body, "advance_hash": _HASH_V0(_SESSION_ADVANCE_HASH_TAG, body)}


SESSION_PIN_CHAIN_SCOPE_INTEGRITY_ONLY = "integrity_only"
SESSION_PIN_CHAIN_SCOPE_RECEIPTS_REPLAYED = "receipts_replayed"


def verify_session_pin_chain_v1(
    pins: Sequence[object],
    *,
    policy: object = None,
    receipts: Sequence[object] | None = None,
) -> dict[str, Any]:
    """Audit an archived session-pin lineage end to end in a declared scope.

    Always checked: linear linkage, kind/index discipline, one policy +
    policy-pin + registry + budget + session-initial-state for the whole
    session, segment initial states threading through final states, strictly
    increasing input epochs, and the per-record session accounting tripwire.
    With `policy` given, the lineage is bound to that artifact's content hash.

    Scope is the load-bearing distinction:

    - WITHOUT `receipts` the result has `scope="integrity_only"` and
      `authenticity_verified=False`. Pin records are self-hashed summaries; an
      internally consistent lineage can be forged wholesale, so this scope
      proves linearity and internal coherence, not that any verified
      continuation ever produced the records. It is the right check for
      records already trusted from the live single-head store, never for
      third-party archives.
    - WITH `receipts` (one archived trajectory receipt per pin, `policy`
      required) every receipt is fully re-verified through the trajectory
      verifier, every pinned summary field is re-derived from its receipt and
      must match exactly, the genesis receipt must be session-fresh, and every
      boundary is re-checked between the actual receipts. Only then does the
      result carry `scope="receipts_replayed"` and `authenticity_verified=True`
      with the claim that every head move was a verified continuation.
    """

    replay_mode = receipts is not None
    scope = (
        SESSION_PIN_CHAIN_SCOPE_RECEIPTS_REPLAYED
        if replay_mode
        else SESSION_PIN_CHAIN_SCOPE_INTEGRITY_ONLY
    )

    def _failure(errors: Sequence[str], *, length: int = 0) -> dict[str, Any]:
        return {
            "ok": False,
            "scope": scope,
            "authenticity_verified": False,
            "errors": tuple(errors),
            "length": length,
            "head_pin_hash": "",
            "session_genesis_pin_hash": "",
        }

    errors: list[str] = []
    if not isinstance(pins, Sequence) or isinstance(pins, (str, bytes, bytearray)):
        return _failure(["session_pin_chain_must_be_sequence"])
    if not pins:
        return _failure(["session_pin_chain_empty"])

    receipt_list: list[object] = []
    if replay_mode:
        if policy is None:
            return _failure(
                ["session_pin_chain_policy_required_for_replay"], length=len(pins)
            )
        if not isinstance(receipts, Sequence) or isinstance(
            receipts, (str, bytes, bytearray)
        ):
            return _failure(
                ["session_pin_chain_receipts_must_be_sequence"], length=len(pins)
            )
        if len(receipts) != len(pins):
            return _failure(
                [
                    "session_pin_chain_receipt_count_mismatch:"
                    f"{len(receipts)}!={len(pins)}"
                ],
                length=len(pins),
            )
        receipt_list = list(receipts)

    expected_policy_hash = ""
    if policy is not None:
        if not is_canonically_encodable(policy):
            errors.append("policy_not_canonically_encodable")
        else:
            hash_errors: list[str] = []
            expected_policy_hash = _policy_content_hash_for_receipt(policy, hash_errors)
            errors.extend(hash_errors)

    genesis: dict[str, Any] = {}
    previous: dict[str, Any] = {}
    previous_receipt: Mapping[str, Any] | None = None
    head_hash = ""
    for index, pin in enumerate(pins):
        normalized, pin_errors = _validate_session_pin(pin)
        if pin_errors:
            errors.extend(f"pin[{index}]:{error}" for error in pin_errors)
            break
        if index == 0:
            if normalized["kind"] != PIN_KIND_GENESIS:
                errors.append(f"pin[{index}]:session_chain_must_start_at_genesis")
                break
            genesis = normalized
        else:
            if normalized["kind"] != PIN_KIND_ADVANCE:
                errors.append(f"pin[{index}]:session_chain_duplicate_genesis")
                break
            if normalized["advance_index"] != index:
                errors.append(f"pin[{index}]:advance_index_mismatch")
                break
            if normalized["previous_session_pin_hash"] != previous["pin_hash"]:
                errors.append(f"pin[{index}]:chain_link_mismatch")
                break
            if normalized["session_genesis_pin_hash"] != genesis["pin_hash"]:
                errors.append(f"pin[{index}]:session_anchor_mismatch")
                break
            for field in (
                "policy_id",
                "policy_hash",
                "policy_pin_hash",
                "registry_hash",
            ):
                if normalized[field] != genesis[field]:
                    errors.append(f"pin[{index}]:session_{field}_inconsistent")
            if dict(normalized["trajectory_budget"]) != dict(
                genesis["trajectory_budget"]
            ):
                errors.append(f"pin[{index}]:session_trajectory_budget_inconsistent")
            if dict(normalized["session_initial_state"]) != dict(
                genesis["session_initial_state"]
            ):
                errors.append(f"pin[{index}]:session_initial_state_inconsistent")
            if dict(normalized["segment_initial_state"]) != dict(
                previous["final_state"]
            ):
                errors.append(f"pin[{index}]:segment_initial_state_mismatch")
            if int(normalized["last_input_epoch"]) <= int(previous["last_input_epoch"]):
                errors.append(f"pin[{index}]:session_epochs_not_strictly_increasing")
            if errors:
                break
        if expected_policy_hash and normalized["policy_hash"] != expected_policy_hash:
            errors.append(f"pin[{index}]:session_policy_hash_mismatch")
            break
        if policy is not None:
            _, budget_errors = _policy_budget_binding_errors(
                policy=policy,
                receipt_budget=normalized["trajectory_budget"],
                prefix=f"pin[{index}]",
            )
            errors.extend(budget_errors)
            if errors:
                break
        errors.extend(
            _session_accounting_errors(
                session_initial_state=dict(normalized["session_initial_state"]),
                summary={
                    "final_state": dict(normalized["final_state"]),
                    "trajectory_used_final": dict(normalized["trajectory_used_final"]),
                    "trajectory_budget": dict(normalized["trajectory_budget"]),
                },
                previous_used=dict(previous["trajectory_used_final"])
                if previous
                else {},
                prefix=f"pin[{index}]",
            )
        )
        if errors:
            break

        if replay_mode:
            receipt = receipt_list[index]
            receipt_verification = _VERIFY_TRAJECTORY(receipt=receipt, policy=policy)
            if receipt_verification.get("ok") is not True or not isinstance(
                receipt, Mapping
            ):
                errors.append(f"pin[{index}]:session_pin_receipt_unverified")
                errors.extend(
                    f"pin[{index}]:receipt:{error}"
                    for error in receipt_verification.get("errors", ())
                )
                break
            summary_errors: list[str] = []
            summary = _receipt_summary(
                receipt, summary_errors, prefix=f"pin[{index}]:session_receipt"
            )
            if summary_errors:
                errors.extend(summary_errors)
                break
            errors.extend(
                _pin_receipt_binding_errors(
                    normalized, summary, prefix=f"pin[{index}]"
                )
            )
            if index == 0:
                errors.extend(
                    f"pin[{index}]:{error}"
                    for error in _genesis_freshness_errors(receipt)
                )
            elif previous_receipt is not None:
                errors.extend(
                    _boundary_errors(
                        head=previous,
                        receipt=receipt,
                        summary=summary,
                        prefix=f"pin[{index}]:session_receipt",
                    )
                )
            if errors:
                break
            previous_receipt = receipt

        previous = normalized
        head_hash = str(normalized["pin_hash"])

    ok = not errors
    return {
        "ok": ok,
        "scope": scope,
        "authenticity_verified": bool(replay_mode and ok),
        "errors": tuple(errors),
        "length": len(pins),
        "head_pin_hash": head_hash if ok else "",
        "session_genesis_pin_hash": str(genesis.get("pin_hash", ""))
        if genesis and ok
        else "",
    }

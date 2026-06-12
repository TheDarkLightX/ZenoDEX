"""Quorum-gated policy-pin lineage for the autonomous-governance brain.

The trajectory runner refuses to run unpinned (`expected_policy_hash` is
required), but nothing governed which hash an operator pins: whoever calls the
runner chooses the brain. This module closes that gap. A policy pin is a
hash-chained record of which frozen policy artifact is authorized, and every
pin, including genesis, exists only if a signature quorum approved exactly that
rotation through `evaluate_governance_authority_v0` (quorum + timelock + Tau
policy receipt + backend evidence).

Design points:

- Rotation does not accept a pre-made authority receipt. A receipt hash is
  integrity, not authority. Anyone can mint an internally consistent receipt
  claiming ok=True. Rotation calls the import-bound authority evaluator inline
  against the caller-supplied registry and signature envelopes, so the quorum
  is actually verified on the rotation path.
- The signed payload binds: the new policy hash, the predecessor pin hash, the
  rotation index, the signer-registry hash, and the proposal epoch. A quorum
  approval for one rotation cannot be replayed for a different policy, a
  different predecessor, or under a different registry.
- The new policy itself must be runnable by the trajectory runner: it must
  normalize cleanly and declare a complete safety envelope. The pin refuses to
  bless a malformed brain.
- Pins chain by hash (`previous_pin_hash`, `rotation_index`). Consumers must
  accept a new pin only when its `previous_pin_hash` equals their current
  head's `pin_hash`; `verify_policy_pin_chain_v1` checks a full lineage.
- Registry rotation is out of scope for v1: a rotation must present the same
  registry the current pin was created under (`registry_rotation_not_supported`
  otherwise).

Honest boundaries: a pin proves that a quorum under the pinned registry
approved this exact brain lineage. Re-verifying the underlying BLS signatures
later requires the archived envelopes (the receipt embeds the quorum report,
not the envelopes). Distributing the current head pin is the ordering/DA
layer's job.
"""

from __future__ import annotations

from typing import Any, Callable, Mapping, Sequence

from src.integration.autonomous_governance_hostile_input import (
    is_canonically_encodable,
)
from src.integration.autonomous_governance_q_policy import (
    SURFACE_PARAMETER_NAMES_V1,
    _normalize_policy,
    _policy_content_hash_for_receipt,
)
from src.integration.autonomous_governance_trajectory import (
    _validate_safety_envelope,
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

AUTONOMOUS_GOVERNANCE_POLICY_PIN_SCHEMA_V1 = (
    "zenodex.autonomous_governance.policy_pin.v1"
)
AUTONOMOUS_GOVERNANCE_POLICY_ROTATION_SCHEMA_V1 = (
    "zenodex.autonomous_governance.policy_pin_rotation.v1"
)
ROTATION_ACTION_ID_V1 = "gov:rotate-autonomous-governance-policy"
ROTATION_ACTION_KIND_V1 = "autonomous_governance_policy_rotation_v1"

_PIN_HASH_TAG = "autonomous_governance_policy_pin_v1"
_ROTATION_HASH_TAG = "autonomous_governance_policy_pin_rotation_v1"
_REGISTRY_HASH_TAG = "autonomous_governance_signer_registry_pin_v1"

GENESIS_PREVIOUS_PIN_HASH = ""

_PIN_FIELDS_V1 = (
    "schema",
    "policy_id",
    "policy_hash",
    "registry_hash",
    "previous_pin_hash",
    "rotation_index",
    "approved_at_epoch",
    "authority_receipt_hash",
    "pin_hash",
)


def _is_plain_int(value: object) -> bool:
    return type(value) is int


def signer_registry_hash_v1(registry: object) -> str:
    """Canonical hash that pins which signer registry authorizes rotations."""

    if not isinstance(registry, Mapping):
        raise TypeError("registry must be a JSON object")
    return _HASH_V0(_REGISTRY_HASH_TAG, dict(registry))


def rotation_action_payload_v1(
    *,
    new_policy_hash: str,
    previous_pin_hash: str,
    rotation_index: int,
    registry_hash: str,
    proposal_epoch: int,
) -> dict[str, Any]:
    """The exact governance-action payload a rotation quorum signs."""

    return {
        "action_id": ROTATION_ACTION_ID_V1,
        "kind": ROTATION_ACTION_KIND_V1,
        "new_policy_hash": new_policy_hash,
        "previous_pin_hash": previous_pin_hash,
        "rotation_index": rotation_index,
        "registry_hash": registry_hash,
        "proposal_epoch": proposal_epoch,
    }


def _pin_body_hash(pin_body: Mapping[str, Any]) -> str:
    return _HASH_V0(_PIN_HASH_TAG, dict(pin_body))


def _validate_pin(pin: object) -> tuple[dict[str, Any], list[str]]:
    """Exact-shape, hash-recomputed validation of a policy pin record."""

    if not isinstance(pin, Mapping):
        return {}, ["pin_must_be_object"]
    # A pin whose field names/values cannot be canonically encoded (a surrogate
    # key, a recursion-bomb value) is refused before any label quotes a key:
    # the refusal receipt must hash, and a self-hashed pin can never have been
    # minted with such a field anyway.
    if not is_canonically_encodable(pin):
        return {}, ["pin_not_canonically_encodable"]
    errors: list[str] = []
    for key in pin:
        if key not in _PIN_FIELDS_V1:
            errors.append(f"pin_unknown_field:{key}")
    for key in _PIN_FIELDS_V1:
        if key not in pin:
            errors.append(f"pin_missing_field:{key}")
    if errors:
        return {}, errors
    if pin.get("schema") != AUTONOMOUS_GOVERNANCE_POLICY_PIN_SCHEMA_V1:
        errors.append("pin_schema_invalid")
    for key in ("policy_id", "policy_hash", "registry_hash", "authority_receipt_hash", "pin_hash"):
        if not isinstance(pin.get(key), str):
            errors.append(f"pin_field_must_be_string:{key}")
    if not isinstance(pin.get("previous_pin_hash"), str):
        errors.append("pin_field_must_be_string:previous_pin_hash")
    for key in ("rotation_index", "approved_at_epoch"):
        if not _is_plain_int(pin.get(key)) or int(pin.get(key, -1)) < 0:
            errors.append(f"pin_field_must_be_nonnegative_int:{key}")
    if errors:
        return {}, errors
    normalized = {key: pin[key] for key in _PIN_FIELDS_V1}
    body = dict(normalized)
    claimed = body.pop("pin_hash")
    if _pin_body_hash(body) != claimed:
        errors.append("pin_hash_mismatch")
        return {}, errors
    return normalized, []


def verify_policy_pin_v1(
    *,
    pin: object,
    policy: object = None,
    registry: object = None,
) -> dict[str, Any]:
    """Verify a pin record's integrity and optional policy/registry binding."""

    normalized, errors = _validate_pin(pin)
    policy_bound = False
    if not errors and policy is not None:
        if not is_canonically_encodable(policy):
            errors.append("policy_not_canonically_encodable")
        else:
            hash_errors: list[str] = []
            policy_hash = _policy_content_hash_for_receipt(policy, hash_errors)
            errors.extend(hash_errors)
            if policy_hash and policy_hash == normalized.get("policy_hash"):
                policy_bound = True
            else:
                errors.append("pin_policy_hash_mismatch")
    registry_bound = False
    if not errors and registry is not None:
        if not is_canonically_encodable(registry):
            errors.append("registry_not_canonically_encodable")
        else:
            try:
                if signer_registry_hash_v1(registry) == normalized.get("registry_hash"):
                    registry_bound = True
                else:
                    errors.append("pin_registry_hash_mismatch")
            except TypeError:
                errors.append("registry_must_be_object")
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_POLICY_PIN_SCHEMA_V1 + ".verification",
        "ok": not errors,
        "errors": tuple(errors),
        "pin_hash": str(normalized.get("pin_hash", "")) if normalized else "",
        "policy_bound": policy_bound,
        "registry_bound": registry_bound,
    }
    return body


def verify_policy_pin_chain_v1(pins: Sequence[object]) -> dict[str, Any]:
    """Verify a full pin lineage: genesis anchor, hash links, index continuity.

    Consumers tracking a head pin accept a successor only when its
    `previous_pin_hash` equals the head's `pin_hash`; this function checks an
    entire archived lineage at once (fork/rollback detection is the comparison
    of two claimed lineages' heads).
    """

    errors: list[str] = []
    if not isinstance(pins, Sequence) or isinstance(pins, (str, bytes, bytearray)):
        return {"ok": False, "errors": ("pin_chain_must_be_sequence",), "length": 0}
    if not pins:
        return {"ok": False, "errors": ("pin_chain_empty",), "length": 0}
    previous_hash = GENESIS_PREVIOUS_PIN_HASH
    for index, pin in enumerate(pins):
        normalized, pin_errors = _validate_pin(pin)
        if pin_errors:
            errors.extend(f"pin[{index}]:{error}" for error in pin_errors)
            break
        if normalized["rotation_index"] != index:
            errors.append(f"pin[{index}]:rotation_index_mismatch")
            break
        if normalized["previous_pin_hash"] != previous_hash:
            errors.append(f"pin[{index}]:chain_link_mismatch")
            break
        previous_hash = str(normalized["pin_hash"])
    return {
        "ok": not errors,
        "errors": tuple(errors),
        "length": len(pins),
        "head_pin_hash": previous_hash if not errors else "",
    }


def _execute_rotation(
    *,
    current_pin: object,
    policy: object,
    registry: object,
    signature_envelopes: Sequence[Mapping[str, Any]],
    current_epoch: int,
    proposal_epoch: int,
    min_delay_epochs: int,
    tau_policy_receipt: Mapping[str, Any],
    backend_descriptors: Sequence[KeyBackendDescriptor | Mapping[str, Any]],
    evidence_claims: Sequence[Mapping[str, Any]],
    required_evidence_claims: Sequence[str],
    production_mode: bool,
) -> dict[str, Any]:
    errors: list[str] = []

    # Refuse inputs hostile to the rotation receipt's own hashing before they
    # reach `_normalize_policy` (which would quote a surrogate key) or the
    # policy/registry content hashes (which would recurse on a nesting bomb).
    # `current_pin` is guarded by `_validate_pin` below; the typed descriptor
    # inputs are validated by the authority evaluator, not hashed raw here.
    if policy is not None and not is_canonically_encodable(policy):
        errors.append("policy_not_canonically_encodable")
        policy = {}
    if registry is not None and not is_canonically_encodable(registry):
        errors.append("registry_not_canonically_encodable")
        registry = {}
    if not is_canonically_encodable(evidence_claims):
        errors.append("evidence_claims_not_canonically_encodable")
        evidence_claims = ()
    if not is_canonically_encodable(required_evidence_claims):
        errors.append("required_evidence_claims_not_canonically_encodable")
        required_evidence_claims = ()

    previous_pin_hash = GENESIS_PREVIOUS_PIN_HASH
    rotation_index = 0
    expected_registry_hash: str | None = None
    if current_pin is not None:
        normalized_pin, pin_errors = _validate_pin(current_pin)
        errors.extend(f"current_{error}" for error in pin_errors)
        if not pin_errors:
            previous_pin_hash = str(normalized_pin["pin_hash"])
            rotation_index = int(normalized_pin["rotation_index"]) + 1
            expected_registry_hash = str(normalized_pin["registry_hash"])

    normalized_policy, policy_errors = _normalize_policy(
        policy if isinstance(policy, Mapping) else {},
        parameter_names=SURFACE_PARAMETER_NAMES_V1,
    )
    if not isinstance(policy, Mapping):
        errors.append("policy_must_be_object")
    else:
        errors.extend(policy_errors)
        errors.extend(_validate_safety_envelope(normalized_policy))
    policy_hash = _policy_content_hash_for_receipt(policy, errors)

    registry_hash = ""
    try:
        registry_hash = signer_registry_hash_v1(registry)
    except TypeError:
        errors.append("registry_must_be_object")
    if expected_registry_hash is not None and registry_hash != expected_registry_hash:
        errors.append("registry_rotation_not_supported")

    normalized_proposal_epoch = proposal_epoch if _is_plain_int(proposal_epoch) else -1
    if normalized_proposal_epoch < 0:
        errors.append("proposal_epoch must be a non-negative int")
        normalized_proposal_epoch = 0

    payload = rotation_action_payload_v1(
        new_policy_hash=policy_hash,
        previous_pin_hash=previous_pin_hash,
        rotation_index=rotation_index,
        registry_hash=registry_hash,
        proposal_epoch=normalized_proposal_epoch,
    )
    payload_hash = _PAYLOAD_HASH(payload)

    authority_receipt = _EVALUATE_AUTHORITY(
        action_id=ROTATION_ACTION_ID_V1,
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
        # Redundant with the authority gate's own fail-closed rule, kept as a
        # local tripwire: a pin must never exist without a verified quorum.
        if "authority_rejected" not in errors:
            errors.append("authority_quorum_missing")

    pin: dict[str, Any] = {}
    if not errors:
        pin_body = {
            "schema": AUTONOMOUS_GOVERNANCE_POLICY_PIN_SCHEMA_V1,
            "policy_id": str(normalized_policy.get("policy_id", "")),
            "policy_hash": policy_hash,
            "registry_hash": registry_hash,
            "previous_pin_hash": previous_pin_hash,
            "rotation_index": rotation_index,
            "approved_at_epoch": int(authority_receipt.get("current_epoch", 0)),
            "authority_receipt_hash": str(authority_receipt.get("receipt_hash", "")),
        }
        pin = {**pin_body, "pin_hash": _pin_body_hash(pin_body)}

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_POLICY_ROTATION_SCHEMA_V1,
        "rotation_index": rotation_index,
        "previous_pin_hash": previous_pin_hash,
        "rotation_payload": payload,
        "rotation_payload_hash": payload_hash,
        "authority_receipt": authority_receipt,
        "pin": pin,
        "ok": not errors,
        "errors": tuple(errors),
        "not_claimed": (
            "does_not_verify_archived_signatures_later",
            "does_not_distribute_the_head_pin",
        ),
    }
    return {**body, "rotation_hash": _HASH_V0(_ROTATION_HASH_TAG, body)}


def build_genesis_policy_pin_v1(
    *,
    policy: object,
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
    """Create the genesis pin. The first brain needs a quorum too."""

    return _execute_rotation(
        current_pin=None,
        policy=policy,
        registry=registry,
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


def rotate_policy_pin_v1(
    *,
    current_pin: Mapping[str, Any],
    policy: object,
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
    """Rotate the pinned policy to a new artifact under quorum authority."""

    return _execute_rotation(
        current_pin=current_pin,
        policy=policy,
        registry=registry,
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

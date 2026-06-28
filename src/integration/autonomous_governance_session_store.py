"""Single-live-head admission store: the deployed flow the lineage stack feeds.

The verification stack so far is advisory: receipts, sessions, and pins all
verify, but nothing operational owns the head. An operator holding two
verified continuations of the same parent can apply either (equivocation), or
re-apply an already-consumed receipt from a stale head (rollback). The
adversarial bench measures exactly that: storeless operation admits every
individually-verified forgery, both fork branches, and replayed segments.

This module is the admission boundary that closes it:

```text
initialize_autonomous_governance_session_store_v1(... authority inputs ...)
  -> store state anchored at a quorum-authorized genesis head
admit_autonomous_governance_session_continuation_v1(store, receipt, policy)
  -> the only way the head moves: a full v5 advance (receipt re-verified,
     every boundary-carry rule re-derived, session accounting) against the
     store's current head. Fork branches and rollback replays fail the
     chain-head/epoch checks by construction. Refusal returns the store
     unchanged.
verify_autonomous_governance_session_store_v1(store, policy)
  -> full receipts-replayed authenticity audit of the archived lineage
current_session_store_head_v1(store)
  -> the head pin + final surface state (what a deployed flow reads)
```

The store state is a plain JSON-serializable dict that archives the pin chain
and the trajectory receipts (one per pin), so its own audit runs in the
strong `receipts_replayed` scope. The store never asks anyone to trust an
integrity-only lineage.

Trust model, stated plainly: the store state is deployment state. Its
`store_hash` makes accidental corruption and casual tampering loud, and any
hash-consistent state is still re-checkable end to end via the receipts
audit; but an adversary who can replace the deployment's state blob does not
need to forge anything. Protecting the blob (and serving one head, not two)
is the deployed store / ordering-DA layer's job. This module guarantees that
through the admission API the head only ever moves on a verified continuation
of itself: equivocation and rollback are refusals, not states.
The genesis pin's quorum provenance is `open_autonomous_governance_session_v1`'s
job; the store validates the record and binds it to the genesis receipt.
"""

from __future__ import annotations

import copy
from typing import Any, Callable, Mapping, Sequence

from src.integration.autonomous_governance_hostile_input import (
    is_canonically_encodable,
    safe_field_label,
)
from src.integration.autonomous_governance_q_policy import (
    _policy_content_hash_for_receipt,
)
from src.integration.autonomous_governance_session_pin import (
    PIN_KIND_GENESIS,
    _genesis_freshness_errors,
    _pin_receipt_binding_errors,
    _receipt_summary,
    _validate_session_pin,
    advance_autonomous_governance_session_v1,
    open_autonomous_governance_session_v1,
    verify_session_pin_chain_v1,
)
from src.integration.autonomous_governance_trajectory import (
    verify_autonomous_governance_surface_trajectory_v1,
)
from src.integration.zeno_ledger_v0 import hash_v0

_HASH_V0: Callable[[str, object], str] = hash_v0
_ADVANCE_SESSION = advance_autonomous_governance_session_v1
_VERIFY_PIN_CHAIN = verify_session_pin_chain_v1
_VERIFY_TRAJECTORY = verify_autonomous_governance_surface_trajectory_v1
_OPEN_SESSION = open_autonomous_governance_session_v1

AUTONOMOUS_GOVERNANCE_SESSION_STORE_SCHEMA_V1 = (
    "zenodex.autonomous_governance.session_store.v1"
)
AUTONOMOUS_GOVERNANCE_SESSION_STORE_INIT_SCHEMA_V1 = (
    "zenodex.autonomous_governance.session_store_init.v1"
)
AUTONOMOUS_GOVERNANCE_SESSION_STORE_ADMISSION_SCHEMA_V1 = (
    "zenodex.autonomous_governance.session_store_admission.v1"
)
AUTONOMOUS_GOVERNANCE_SESSION_STORE_VERIFICATION_SCHEMA_V1 = (
    "zenodex.autonomous_governance.session_store_verification.v1"
)

_STORE_HASH_TAG = "autonomous_governance_session_store_v1"
_INIT_HASH_TAG = "autonomous_governance_session_store_init_v1"
_ADMISSION_HASH_TAG = "autonomous_governance_session_store_admission_v1"
_VERIFICATION_HASH_TAG = "autonomous_governance_session_store_verification_v1"

MAX_SESSION_STORE_SEGMENTS_V1 = 4096


def _store_body_hash(body: Mapping[str, Any]) -> str:
    return _HASH_V0(_STORE_HASH_TAG, dict(body))


def _safe_field_label(key: object) -> str:
    """Total, canonical-safe label for a (possibly hostile) field name.

    Canonical JSON rejects unpaired surrogates and a refusal that quotes a raw
    hostile key would crash its own response hashing; a name whose __str__
    raises would crash error formatting. Delegates to the shared guard, which
    handles both. Benign names pass through unchanged.
    """

    return safe_field_label(key)


def _build_store_state(
    *,
    policy_hash: str,
    pin_chain: Sequence[Mapping[str, Any]],
    receipt_archive: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    # The archive must OWN detached copies: a shallow copy would share nested
    # maps with caller-held receipt/pin objects, letting later caller-side
    # mutation change store contents underneath the already-computed hash.
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SESSION_STORE_SCHEMA_V1,
        "policy_hash": policy_hash,
        "pin_chain": tuple(copy.deepcopy(dict(pin)) for pin in pin_chain),
        "receipt_archive": tuple(
            copy.deepcopy(dict(receipt)) for receipt in receipt_archive
        ),
        "segment_count": len(pin_chain),
    }
    return {**body, "store_hash": _store_body_hash(body)}


def _validate_store_state(store: object) -> tuple[dict[str, Any], list[str]]:
    """Shape + self-hash + head-pin validation of a store state blob."""

    if not isinstance(store, Mapping):
        return {}, ["session_store_must_be_object"]
    errors: list[str] = []
    expected_fields = {
        "schema",
        "policy_hash",
        "pin_chain",
        "receipt_archive",
        "segment_count",
        "store_hash",
    }
    for key in store:
        if key not in expected_fields:
            errors.append(f"session_store_unknown_field:{_safe_field_label(key)}")
    for key in expected_fields:
        if key not in store:
            errors.append(f"session_store_missing_field:{key}")
    if errors:
        return {}, errors
    if store.get("schema") != AUTONOMOUS_GOVERNANCE_SESSION_STORE_SCHEMA_V1:
        errors.append("session_store_schema_invalid")
    pin_chain_raw = store.get("pin_chain")
    receipt_archive_raw = store.get("receipt_archive")
    if (
        not isinstance(pin_chain_raw, Sequence)
        or isinstance(pin_chain_raw, (str, bytes, bytearray))
        or not pin_chain_raw
    ):
        errors.append("session_store_pin_chain_invalid")
        return {}, errors
    if not isinstance(receipt_archive_raw, Sequence) or isinstance(
        receipt_archive_raw, (str, bytes, bytearray)
    ):
        errors.append("session_store_receipt_archive_invalid")
        return {}, errors
    if errors:
        return {}, errors
    if len(pin_chain_raw) != len(receipt_archive_raw):
        errors.append("session_store_archive_count_mismatch")
    segment_count_raw = store.get("segment_count")
    if type(segment_count_raw) is not int:
        # Exact type: True == 1 must not satisfy the count equality below.
        errors.append("session_store_segment_count_invalid")
    elif segment_count_raw != len(pin_chain_raw):
        errors.append("session_store_segment_count_mismatch")
    if len(pin_chain_raw) > MAX_SESSION_STORE_SEGMENTS_V1:
        errors.append("session_store_segments_exceed_max")
    if errors:
        # Fail fast: a hostile oversized or count-broken blob must not buy
        # CPU/memory proportional to its size from the copies below.
        return {}, errors

    # Materialize-once: every archive entry must be a mapping BEFORE anything
    # is hashed, and the hash is computed over exactly the materialized copies
    # this function returns. A hash-consistent blob with a list-of-pairs entry
    # must be refused here, never transformed post-hash into data the hash did
    # not commit to.
    pin_chain: list[dict[str, Any]] = []
    for index, pin in enumerate(pin_chain_raw):
        if not isinstance(pin, Mapping):
            errors.append(f"session_store_pin_entry_invalid:{index}")
        else:
            pin_chain.append(dict(pin))
    receipt_archive: list[dict[str, Any]] = []
    for index, receipt in enumerate(receipt_archive_raw):
        if not isinstance(receipt, Mapping):
            errors.append(f"session_store_receipt_entry_invalid:{index}")
        else:
            receipt_archive.append(dict(receipt))
    if errors:
        return {}, errors

    body = {
        "schema": store["schema"],
        "policy_hash": store["policy_hash"],
        "pin_chain": tuple(pin_chain),
        "receipt_archive": tuple(receipt_archive),
        "segment_count": store["segment_count"],
    }
    if not is_canonically_encodable(body):
        # Canonical-JSON-rejected values (floats, non-string keys, surrogates)
        # OR a recursion-bomb nesting inside an archived pin/receipt must fail
        # closed here, never crash (or recurse) the admission boundary's own
        # hashing. The depth-bounded probe bails before the encoder would.
        errors.append("session_store_unhashable")
        return {}, errors
    recomputed_hash = _store_body_hash(body)
    if recomputed_hash != store.get("store_hash"):
        errors.append("session_store_hash_mismatch")
        return {}, errors

    head, head_errors = _validate_session_pin(pin_chain[-1])
    errors.extend(f"session_store_head_{error}" for error in head_errors)
    if not errors and str(store.get("policy_hash", "")) != str(head["policy_hash"]):
        errors.append("session_store_head_policy_hash_mismatch")
    if errors:
        return {}, errors
    return {
        "schema": str(store["schema"]),
        "policy_hash": str(store["policy_hash"]),
        "pin_chain": [dict(pin) for pin in pin_chain],
        "receipt_archive": [dict(receipt) for receipt in receipt_archive],
        "segment_count": int(store["segment_count"]),
        "store_hash": str(store["store_hash"]),
        "head": head,
    }, []



def _plain_nonnegative_int(value: object) -> int | None:
    """DbC: accept exact non-negative ints only; bool is not an epoch."""

    if type(value) is not int:
        return None
    if value < 0:
        return None
    return int(value)


def _verify_genesis_open_authority(
    *,
    expected_pin: Mapping[str, Any],
    genesis_receipt: object,
    policy: object,
    policy_pin: object,
    registry: object,
    signature_envelopes: object,
    current_epoch: object,
    proposal_epoch: object,
    min_delay_epochs: object,
    tau_policy_receipt: object,
    backend_descriptors: object,
    evidence_claims: object,
    required_evidence_claims: object,
    production_mode: bool,
) -> list[str]:
    """Verify the quorum-gated session-open path produced the genesis pin.

    Preconditions: caller supplies the same authority artifacts required by
    open_autonomous_governance_session_v1.
    Invariant: store genesis admission is authorized only when replaying that
    path yields exactly the supplied genesis pin.
    Postcondition: a self-hashed pin with a forged authority hash is refused.
    """

    current = _plain_nonnegative_int(current_epoch)
    proposal = _plain_nonnegative_int(proposal_epoch)
    delay = _plain_nonnegative_int(min_delay_epochs)
    if current is None or proposal is None or delay is None:
        return ["session_store_genesis_authority_context_required"]
    if not isinstance(registry, Mapping):
        return ["session_store_genesis_registry_required"]
    if not isinstance(signature_envelopes, Sequence) or isinstance(
        signature_envelopes, (str, bytes, bytearray)
    ):
        return ["session_store_genesis_signature_envelopes_required"]
    if not isinstance(backend_descriptors, Sequence) or isinstance(
        backend_descriptors, (str, bytes, bytearray)
    ):
        return ["session_store_genesis_backend_descriptors_required"]

    opened = _OPEN_SESSION(
        policy=policy,
        policy_pin=policy_pin,
        genesis_receipt=genesis_receipt,
        registry=registry,
        signature_envelopes=signature_envelopes,
        current_epoch=current,
        proposal_epoch=proposal,
        min_delay_epochs=delay,
        tau_policy_receipt=tau_policy_receipt,
        backend_descriptors=backend_descriptors,
        evidence_claims=evidence_claims if isinstance(evidence_claims, Sequence) else (),
        required_evidence_claims=required_evidence_claims
        if isinstance(required_evidence_claims, Sequence)
        else (),
        production_mode=production_mode,
    )
    if opened.get("ok") is not True:
        return [
            "session_store_genesis_authority_unverified",
            *(f"session_open:{error}" for error in opened.get("errors", ())),
        ]
    if dict(opened.get("pin", {})) != dict(expected_pin):
        return ["session_store_genesis_authority_pin_mismatch"]
    return []

def initialize_autonomous_governance_session_store_v1(
    *,
    genesis_pin: object,
    genesis_receipt: object,
    policy: object,
    policy_pin: object = None,
    registry: object = None,
    signature_envelopes: object = None,
    current_epoch: object = None,
    proposal_epoch: object = None,
    min_delay_epochs: object = None,
    tau_policy_receipt: object = None,
    backend_descriptors: object = None,
    evidence_claims: object = (),
    required_evidence_claims: object = (),
    production_mode: bool = True,
) -> dict[str, Any]:
    """Anchor a store at a validated genesis head bound to its receipt.

    The genesis pin's quorum provenance is established by
    `open_autonomous_governance_session_v1` (deployment passes
    `open_result["pin"]` here); this function re-validates the record, binds
    it field-by-field to the genesis receipt, re-verifies the receipt against
    the policy, and re-checks session freshness. Any defect fails closed.
    """

    errors: list[str] = []
    pin, pin_errors = _validate_session_pin(genesis_pin)
    errors.extend(f"genesis_{error}" for error in pin_errors)
    if pin and pin.get("kind") != PIN_KIND_GENESIS:
        errors.append("session_store_genesis_pin_kind_invalid")

    authority = _verify_genesis_open_authority(
        expected_pin=pin,
        genesis_receipt=genesis_receipt,
        policy=policy,
        policy_pin=policy_pin,
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
    errors.extend(authority)

    # A policy hostile to canonical hashing would crash the genesis content
    # hash (and the receipt verification) before the store could refuse it.
    if policy is not None and not is_canonically_encodable(policy):
        errors.append("policy_not_canonically_encodable")
        policy = {}
    policy_hash = _policy_content_hash_for_receipt(policy, errors)
    if pin and policy_hash and policy_hash != pin.get("policy_hash"):
        errors.append("session_store_policy_hash_mismatch")

    receipt_verification = _VERIFY_TRAJECTORY(receipt=genesis_receipt, policy=policy)
    if receipt_verification.get("ok") is not True or not isinstance(
        genesis_receipt, Mapping
    ):
        errors.append("session_store_genesis_receipt_unverified")
        errors.extend(
            f"genesis_receipt:{error}"
            for error in receipt_verification.get("errors", ())
        )
    elif pin:
        summary_errors: list[str] = []
        summary = _receipt_summary(
            genesis_receipt, summary_errors, prefix="session_store_genesis"
        )
        errors.extend(summary_errors)
        if not summary_errors:
            errors.extend(
                _pin_receipt_binding_errors(pin, summary, prefix="session_store_genesis")
            )
        errors.extend(_genesis_freshness_errors(genesis_receipt))

    store: dict[str, Any] = {}
    if not errors and isinstance(genesis_receipt, Mapping):
        store = _build_store_state(
            policy_hash=policy_hash,
            pin_chain=[pin],
            receipt_archive=[dict(genesis_receipt)],
        )

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SESSION_STORE_INIT_SCHEMA_V1,
        "ok": not errors,
        "errors": tuple(errors),
        "store": store,
    }
    return {**body, "init_hash": _HASH_V0(_INIT_HASH_TAG, body)}


def admit_autonomous_governance_session_continuation_v1(
    *,
    store: object,
    receipt: object,
    policy: object,
) -> dict[str, Any]:
    """The only way the head moves. Refusal returns the store unchanged.

    Admission is exactly a v5 advance against the store's current head: the
    receipt is fully re-verified and every boundary-carry rule re-derived. A
    fork branch (the head already moved past its parent) fails the chain-head
    check; a rollback replay (an already-consumed segment) fails the
    chain-head and epoch checks. Both are refusals with named errors, never
    alternative heads.
    """

    errors: list[str] = []
    state, state_errors = _validate_store_state(store)
    errors.extend(state_errors)

    # Gate the policy before its content hash (recursion-bomb nesting would
    # otherwise crash the admission boundary). The receipt is gated by the
    # trajectory verifier inside the advance below.
    if policy is not None and not is_canonically_encodable(policy):
        errors.append("policy_not_canonically_encodable")
        policy = {}
    policy_hash = _policy_content_hash_for_receipt(policy, errors)
    if state and policy_hash and policy_hash != state["policy_hash"]:
        errors.append("session_store_policy_hash_mismatch")

    # Refuse BEFORE the append would cross the cap: a refusal returns the
    # store unchanged and still serviceable; admitting and then failing every
    # later validation would brick the session at the boundary.
    if state and int(state["segment_count"]) >= MAX_SESSION_STORE_SEGMENTS_V1:
        errors.append("session_store_segments_at_max")

    advance: dict[str, Any] = {}
    if not errors:
        advance = _ADVANCE_SESSION(
            current_pin=state["head"], receipt=receipt, policy=policy
        )
        if advance.get("ok") is not True:
            errors.append("session_store_admission_refused")
            errors.extend(str(error) for error in advance.get("errors", ()))

    admitted = not errors
    new_store: dict[str, Any]
    if admitted and isinstance(receipt, Mapping):
        new_store = _build_store_state(
            policy_hash=state["policy_hash"],
            pin_chain=[*state["pin_chain"], dict(advance["pin"])],
            receipt_archive=[*state["receipt_archive"], dict(receipt)],
        )
    else:
        admitted = False
        # Echo the unchanged store only when it VALIDATED (and is therefore
        # canonically hashable); a malformed blob must not ride into the
        # admission body where hashing it would crash the refusal path.
        new_store = (
            dict(store) if state and isinstance(store, Mapping) else {}
        )

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SESSION_STORE_ADMISSION_SCHEMA_V1,
        "admitted": admitted,
        "head_pin_hash": str(dict(advance.get("pin", {})).get("pin_hash", ""))
        if admitted
        else "",
        "advance": advance,
        "store": new_store,
        "ok": admitted,
        "errors": tuple(errors),
    }
    return {**body, "admission_hash": _HASH_V0(_ADMISSION_HASH_TAG, body)}


def verify_autonomous_governance_session_store_v1(
    *,
    store: object,
    policy: object,
) -> dict[str, Any]:
    """Full receipts-replayed authenticity audit of a store's archived lineage."""

    errors: list[str] = []
    state, state_errors = _validate_store_state(store)
    errors.extend(state_errors)

    chain: dict[str, Any] = {}
    if not errors:
        chain = _VERIFY_PIN_CHAIN(
            state["pin_chain"],
            policy=policy,
            receipts=state["receipt_archive"],
        )
        if chain.get("ok") is not True:
            errors.append("session_store_lineage_unverified")
            errors.extend(str(error) for error in chain.get("errors", ()))

    ok = not errors
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SESSION_STORE_VERIFICATION_SCHEMA_V1,
        "ok": ok,
        "authenticity_verified": bool(ok and chain.get("authenticity_verified") is True),
        "scope": str(chain.get("scope", "")),
        "errors": tuple(errors),
        "segment_count": int(state.get("segment_count", 0)) if state else 0,
        "head_pin_hash": str(chain.get("head_pin_hash", "")),
        "session_genesis_pin_hash": str(chain.get("session_genesis_pin_hash", "")),
    }
    return {**body, "verification_hash": _HASH_V0(_VERIFICATION_HASH_TAG, body)}


def current_session_store_head_v1(store: object) -> dict[str, Any]:
    """What a deployed flow reads: the head pin and its final surface state."""

    state, state_errors = _validate_store_state(store)
    if state_errors:
        return {
            "ok": False,
            "errors": tuple(state_errors),
            "head_pin": {},
            "surface_state": {},
            "segment_count": 0,
        }
    # Detached snapshot: a shallow copy would alias nested maps in the
    # validated store data, letting a reader's mutation corrupt the store
    # past its own hash.
    head = copy.deepcopy(dict(state["head"]))
    return {
        "ok": True,
        "errors": (),
        "head_pin": head,
        "surface_state": dict(head["final_state"]),
        "segment_count": int(state["segment_count"]),
    }

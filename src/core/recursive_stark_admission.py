"""Deterministic exact-once admission for authenticated recursive STARK roots.

``RecursiveStarkRootFacts`` validates public shape only. The private governed
marker and admission transition are reserved for the pinned verifier
adapter after receipt verification. The transition checks trusted policy
bindings and cross-root replay state; it does not establish proof authority.
"""

from __future__ import annotations

import hashlib
from bisect import bisect_left
from dataclasses import dataclass
from enum import Enum
from typing import NoReturn, TypeVar, final

from ..state.canonical import canonical_hex_fixed_allow_0x

HASH_BYTES = 32
MAX_CHAIN_ID_BYTES = 128
MAX_PROOF_PROFILE_BYTES = 128
MAX_CHILD_VERIFICATION_CLAIMS_PER_ROOT = 4_096
MAX_ACCEPTED_RECEIPT_IDS_PER_ROOT = 65_536
MAX_CROSS_SHARD_MESSAGE_IDS_PER_ROOT = 65_536
MAX_ADMISSION_INDEX_ENTRIES = 1_048_576
MAX_EPOCH_ID = (1 << 64) - 1

_ZERO_HASH = "0x" + "00" * HASH_BYTES
_TOKEN_CHARS = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._:-")
_CHILD_CLAIMS_ROOT_DOMAIN = b"zenodex.risc0.recursive.child_verification_claims_root.v1"
_RECEIPT_IDS_ROOT_DOMAIN = b"zenodex.risc0.recursive.receipt_ids_root.v1"
_MESSAGE_IDS_ROOT_DOMAIN = b"zenodex.risc0.recursive.message_ids_root.v1"


class RecursiveStarkAdmissionRejectReason(str, Enum):
    """Stable fail-closed reasons emitted by exact-once admission."""

    CHAIN_ID_MISMATCH = "recursive_stark.chain_id_mismatch"
    EPOCH_ID_MISMATCH = "recursive_stark.epoch_id_mismatch"
    PROOF_PROFILE_MISMATCH = "recursive_stark.proof_profile_mismatch"
    VERIFIER_SET_ROOT_MISMATCH = "recursive_stark.verifier_set_root_mismatch"
    PUBLIC_POLICY_HASH_MISMATCH = "recursive_stark.public_policy_hash_mismatch"
    STATE_CHAIN_ID_MISMATCH = "recursive_stark.state_chain_id_mismatch"
    DUPLICATE_ROOT_JOURNAL = "recursive_stark.duplicate_root_journal"
    DUPLICATE_ADMISSION_SLOT = "recursive_stark.duplicate_admission_slot"
    DUPLICATE_CHILD_VERIFICATION_CLAIM = "recursive_stark.duplicate_child_verification_claim"
    DUPLICATE_ACCEPTED_RECEIPT = "recursive_stark.duplicate_accepted_receipt"
    DUPLICATE_CROSS_SHARD_MESSAGE = "recursive_stark.duplicate_cross_shard_message"
    ADMISSION_INDEX_CAPACITY_EXCEEDED = "recursive_stark.admission_index_capacity_exceeded"
    DURABLE_CURSOR_MISMATCH = "recursive_stark.durable_cursor_mismatch"


@dataclass(frozen=True, order=True)
class RecursiveStarkAdmissionSlot:
    """One exact-once root slot, ordered by chain, epoch, and proof profile."""

    chain_id: str
    epoch_id: int
    proof_profile: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="slot.chain_id", max_bytes=MAX_CHAIN_ID_BYTES)
        _require_epoch_id(self.epoch_id, name="slot.epoch_id")
        _require_token(
            self.proof_profile,
            name="slot.proof_profile",
            max_bytes=MAX_PROOF_PROFILE_BYTES,
        )


@dataclass(frozen=True)
class TrustedRecursiveStarkAdmissionPolicy:
    """Ledger-owned bindings for the root currently eligible for admission."""

    expected_chain_id: str
    expected_epoch_id: int
    expected_proof_profile: str
    expected_verifier_set_root: str
    expected_public_policy_hash: str

    def __post_init__(self) -> None:
        _require_token(
            self.expected_chain_id,
            name="policy.expected_chain_id",
            max_bytes=MAX_CHAIN_ID_BYTES,
        )
        _require_epoch_id(
            self.expected_epoch_id,
            name="policy.expected_epoch_id",
        )
        _require_token(
            self.expected_proof_profile,
            name="policy.expected_proof_profile",
            max_bytes=MAX_PROOF_PROFILE_BYTES,
        )
        _require_nonzero_hash(
            self.expected_verifier_set_root,
            name="policy.expected_verifier_set_root",
        )
        _require_nonzero_hash(
            self.expected_public_policy_hash,
            name="policy.expected_public_policy_hash",
        )


@dataclass(frozen=True)
class RecursiveStarkRootFacts:
    """Canonical journal-fact shape without cryptographic authority.

    Construction validates only shape and canonical form.  It does not verify a
    RISC0 receipt and cannot enter the private admission transition directly.
    """

    chain_id: str
    epoch_id: int
    proof_profile: str
    root_journal_hash: str
    verifier_set_root: str
    public_policy_hash: str
    child_verification_claim_hashes: tuple[str, ...]
    child_verification_claims_root: str
    accepted_receipt_ids: tuple[str, ...]
    accepted_receipts_root: str
    cross_shard_message_ids: tuple[str, ...]
    cross_shard_message_ids_root: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="facts.chain_id", max_bytes=MAX_CHAIN_ID_BYTES)
        _require_epoch_id(self.epoch_id, name="facts.epoch_id")
        _require_token(
            self.proof_profile,
            name="facts.proof_profile",
            max_bytes=MAX_PROOF_PROFILE_BYTES,
        )
        _require_nonzero_hash(self.root_journal_hash, name="facts.root_journal_hash")
        _require_nonzero_hash(self.verifier_set_root, name="facts.verifier_set_root")
        _require_nonzero_hash(self.public_policy_hash, name="facts.public_policy_hash")
        _require_bounded_unique_hashes(
            self.child_verification_claim_hashes,
            name="facts.child_verification_claim_hashes",
            max_items=MAX_CHILD_VERIFICATION_CLAIMS_PER_ROOT,
            allow_empty=False,
        )
        _require_sorted_unique_hashes(
            self.accepted_receipt_ids,
            name="facts.accepted_receipt_ids",
            max_items=MAX_ACCEPTED_RECEIPT_IDS_PER_ROOT,
            allow_empty=True,
        )
        _require_sorted_unique_hashes(
            self.cross_shard_message_ids,
            name="facts.cross_shard_message_ids",
            max_items=MAX_CROSS_SHARD_MESSAGE_IDS_PER_ROOT,
            allow_empty=True,
        )
        _require_committed_root(
            self.child_verification_claims_root,
            recursive_child_verification_claims_root_v1(self.child_verification_claim_hashes),
            name="facts.child_verification_claims_root",
        )
        _require_committed_root(
            self.accepted_receipts_root,
            recursive_receipt_ids_root_v1(self.accepted_receipt_ids),
            name="facts.accepted_receipts_root",
        )
        _require_committed_root(
            self.cross_shard_message_ids_root,
            recursive_message_ids_root_v1(self.cross_shard_message_ids),
            name="facts.cross_shard_message_ids_root",
        )

    @property
    def slot(self) -> RecursiveStarkAdmissionSlot:
        return RecursiveStarkAdmissionSlot(
            chain_id=self.chain_id,
            epoch_id=self.epoch_id,
            proof_profile=self.proof_profile,
        )


_AUTHENTICATED_FACTS_SEAL = object()


@dataclass(frozen=True, slots=True)
class _RecursiveStarkVerificationProvenance:
    """Exact governed inputs retained across verification and durable commit."""

    authority_manifest_sha256: str
    verifier_executable_sha256: str
    verification_request_sha256: str
    release_binding_config_digest: str | None = None
    replay_manifest_sha256: str | None = None

    def __post_init__(self) -> None:
        _require_bare_sha256(
            self.authority_manifest_sha256,
            name="provenance.authority_manifest_sha256",
        )
        _require_bare_sha256(
            self.verifier_executable_sha256,
            name="provenance.verifier_executable_sha256",
        )
        _require_bare_sha256(
            self.verification_request_sha256,
            name="provenance.verification_request_sha256",
        )
        if self.release_binding_config_digest is not None:
            _require_prefixed_sha256(
                self.release_binding_config_digest,
                prefix="0x",
                name="provenance.release_binding_config_digest",
            )
        if self.replay_manifest_sha256 is not None:
            _require_prefixed_sha256(
                self.replay_manifest_sha256,
                prefix="sha256:",
                name="provenance.replay_manifest_sha256",
            )


@final
class _AuthenticatedRecursiveStarkRootFacts:
    """Governed-source post-verification marker for the pinned adapter.

    Python module privacy is not a same-interpreter security boundary. The
    required architecture gate limits construction and consumption to the
    reviewed adapter path; hostile private-symbol access remains a non-claim.
    """

    __slots__ = ("_facts", "_provenance", "_trusted_policy", "_seal")
    _facts: RecursiveStarkRootFacts
    _provenance: _RecursiveStarkVerificationProvenance
    _trusted_policy: TrustedRecursiveStarkAdmissionPolicy

    def __init__(
        self,
        facts: RecursiveStarkRootFacts,
        trusted_policy: TrustedRecursiveStarkAdmissionPolicy,
        provenance: _RecursiveStarkVerificationProvenance,
        *,
        seal: object,
    ) -> None:
        if seal is not _AUTHENTICATED_FACTS_SEAL:
            raise TypeError("authenticated recursive facts require the private seal")
        if type(facts) is not RecursiveStarkRootFacts:
            raise TypeError("facts must be exactly RecursiveStarkRootFacts")
        if type(trusted_policy) is not TrustedRecursiveStarkAdmissionPolicy:
            raise TypeError("trusted_policy must be exactly TrustedRecursiveStarkAdmissionPolicy")
        if type(provenance) is not _RecursiveStarkVerificationProvenance:
            raise TypeError("provenance must be exactly _RecursiveStarkVerificationProvenance")
        object.__setattr__(self, "_facts", facts)
        object.__setattr__(self, "_trusted_policy", trusted_policy)
        object.__setattr__(self, "_provenance", provenance)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> None:
        raise TypeError("authenticated recursive facts cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> None:
        raise AttributeError("authenticated recursive facts are immutable")

    def __copy__(self) -> None:
        raise TypeError("authenticated recursive facts cannot be copied")

    def __deepcopy__(self, _memo: object) -> None:
        raise TypeError("authenticated recursive facts cannot be copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated recursive facts cannot be serialized")

    @property
    def facts(self) -> RecursiveStarkRootFacts:
        return self._facts

    @property
    def trusted_policy(self) -> TrustedRecursiveStarkAdmissionPolicy:
        return self._trusted_policy

    @property
    def provenance(self) -> _RecursiveStarkVerificationProvenance:
        return self._provenance

    def _has_private_seal(self) -> bool:
        try:
            return object.__getattribute__(self, "_seal") is _AUTHENTICATED_FACTS_SEAL
        except AttributeError:
            return False


def _mint_recursive_stark_root_facts_after_verification(
    facts: RecursiveStarkRootFacts,
    trusted_policy: TrustedRecursiveStarkAdmissionPolicy,
    provenance: _RecursiveStarkVerificationProvenance,
) -> _AuthenticatedRecursiveStarkRootFacts:
    """Mint the private marker on the governed post-verification path."""

    if type(facts) is not RecursiveStarkRootFacts:
        raise TypeError("facts must be exactly RecursiveStarkRootFacts")
    if type(trusted_policy) is not TrustedRecursiveStarkAdmissionPolicy:
        raise TypeError("trusted_policy must be exactly TrustedRecursiveStarkAdmissionPolicy")
    if type(provenance) is not _RecursiveStarkVerificationProvenance:
        raise TypeError("provenance must be exactly _RecursiveStarkVerificationProvenance")
    return _AuthenticatedRecursiveStarkRootFacts(
        facts,
        trusted_policy,
        provenance,
        seal=_AUTHENTICATED_FACTS_SEAL,
    )


@dataclass(frozen=True, slots=True)
class _RecursiveStarkAdmissionIndexSnapshot:
    """Minimal replay-index view consumed by the shared admission planner."""

    chain_id: str | None
    root_seen: bool
    root_is_idempotent_outcome: bool
    slot_seen: bool
    child_claim_overlap: bool
    receipt_overlap: bool
    message_overlap: bool
    root_count: int
    slot_count: int
    child_claim_count: int
    receipt_count: int
    message_count: int

    def __post_init__(self) -> None:
        if self.chain_id is not None:
            _require_token(
                self.chain_id,
                name="snapshot.chain_id",
                max_bytes=MAX_CHAIN_ID_BYTES,
            )
        for name in (
            "root_seen",
            "root_is_idempotent_outcome",
            "slot_seen",
            "child_claim_overlap",
            "receipt_overlap",
            "message_overlap",
        ):
            if type(getattr(self, name)) is not bool:
                raise TypeError(f"snapshot.{name} must be a bool")
        if self.root_is_idempotent_outcome and not self.root_seen:
            raise ValueError("idempotent root outcome requires root_seen")
        for name in (
            "root_count",
            "slot_count",
            "child_claim_count",
            "receipt_count",
            "message_count",
        ):
            value = getattr(self, name)
            if type(value) is not int:
                raise TypeError(f"snapshot.{name} must be an int")
            if value < 0 or value > MAX_ADMISSION_INDEX_ENTRIES:
                raise ValueError(f"snapshot.{name} must be in 0..{MAX_ADMISSION_INDEX_ENTRIES}")
        if self.root_count != self.slot_count:
            raise ValueError("snapshot root and slot counts must match")


@dataclass(frozen=True, slots=True)
class _RecursiveStarkAdmissionPlan:
    """Private deterministic decision shared by memory and durable stores."""

    reject_reason: RecursiveStarkAdmissionRejectReason | None
    idempotent_replay: bool = False

    def __post_init__(self) -> None:
        if self.idempotent_replay and self.reject_reason is not None:
            raise ValueError("idempotent replay cannot include a reject reason")

    @property
    def accepted(self) -> bool:
        return self.reject_reason is None


@dataclass(frozen=True)
class RecursiveStarkAdmissionState:
    """Canonical in-memory replay indexes proposed by successful evaluation."""

    chain_id: str | None = None
    accepted_root_journal_hashes: tuple[str, ...] = ()
    accepted_slots: tuple[RecursiveStarkAdmissionSlot, ...] = ()
    accepted_child_verification_claim_hashes: tuple[str, ...] = ()
    accepted_receipt_ids: tuple[str, ...] = ()
    accepted_cross_shard_message_ids: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if self.chain_id is not None:
            _require_token(
                self.chain_id,
                name="state.chain_id",
                max_bytes=MAX_CHAIN_ID_BYTES,
            )
        _require_sorted_unique_hashes(
            self.accepted_root_journal_hashes,
            name="state.accepted_root_journal_hashes",
            max_items=MAX_ADMISSION_INDEX_ENTRIES,
            allow_empty=True,
        )
        _require_sorted_unique_slots(self.accepted_slots)
        _require_sorted_unique_hashes(
            self.accepted_child_verification_claim_hashes,
            name="state.accepted_child_verification_claim_hashes",
            max_items=MAX_ADMISSION_INDEX_ENTRIES,
            allow_empty=True,
        )
        _require_sorted_unique_hashes(
            self.accepted_receipt_ids,
            name="state.accepted_receipt_ids",
            max_items=MAX_ADMISSION_INDEX_ENTRIES,
            allow_empty=True,
        )
        _require_sorted_unique_hashes(
            self.accepted_cross_shard_message_ids,
            name="state.accepted_cross_shard_message_ids",
            max_items=MAX_ADMISSION_INDEX_ENTRIES,
            allow_empty=True,
        )
        if len(self.accepted_root_journal_hashes) != len(self.accepted_slots):
            raise ValueError("state root and admission slot counts must match")
        has_indexes = any(
            (
                self.accepted_root_journal_hashes,
                self.accepted_slots,
                self.accepted_child_verification_claim_hashes,
                self.accepted_receipt_ids,
                self.accepted_cross_shard_message_ids,
            )
        )
        if has_indexes and self.chain_id is None:
            raise ValueError("non-empty admission state must be chain-scoped")


@dataclass(frozen=True)
class RecursiveStarkAdmissionResult:
    """Data-only decision; never an authority token for durable persistence."""

    accepted: bool
    state: RecursiveStarkAdmissionState
    reject_reason: RecursiveStarkAdmissionRejectReason | None

    def __post_init__(self) -> None:
        if not isinstance(self.accepted, bool):
            raise TypeError("accepted must be a bool")
        if not isinstance(self.state, RecursiveStarkAdmissionState):
            raise TypeError("state must be a RecursiveStarkAdmissionState")
        if self.accepted and self.reject_reason is not None:
            raise ValueError("accepted admission cannot include a reject reason")
        if not self.accepted and not isinstance(
            self.reject_reason,
            RecursiveStarkAdmissionRejectReason,
        ):
            raise ValueError("rejected admission must include a typed reject reason")


def _admit_authenticated_recursive_stark_root(
    state: RecursiveStarkAdmissionState,
    authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
) -> RecursiveStarkAdmissionResult:
    """Evaluate one authenticated root against exact-once replay state.

    Reject precedence is trusted policy, root, slot, child claim, accepted
    receipt, cross-shard message, then state capacity.  Every reject returns the
    exact input state object.  Candidate indexes are built only after all checks
    succeed. Durable atomic commit remains an external obligation.
    """

    _require_transition_types(state, authenticated_root)
    facts = authenticated_root.facts
    plan = _plan_authenticated_recursive_stark_root(
        authenticated_root,
        _index_snapshot_from_memory(state, facts),
    )
    if not plan.accepted:
        return RecursiveStarkAdmissionResult(
            accepted=False,
            state=state,
            reject_reason=plan.reject_reason,
        )

    staged_state = _stage_admission(state, facts)
    return RecursiveStarkAdmissionResult(
        accepted=True,
        state=staged_state,
        reject_reason=None,
    )


def _require_transition_types(
    state: object,
    authenticated_root: object,
) -> None:
    if not isinstance(state, RecursiveStarkAdmissionState):
        raise TypeError("state must be a RecursiveStarkAdmissionState")
    if type(authenticated_root) is not _AuthenticatedRecursiveStarkRootFacts:
        raise TypeError("authenticated_root must be _AuthenticatedRecursiveStarkRootFacts")
    if not authenticated_root._has_private_seal():
        raise TypeError("authenticated_root lacks the private seal")


def _plan_authenticated_recursive_stark_root(
    authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
    snapshot: _RecursiveStarkAdmissionIndexSnapshot,
) -> _RecursiveStarkAdmissionPlan:
    """Plan one admission without accepting caller-projected next state."""

    if type(authenticated_root) is not _AuthenticatedRecursiveStarkRootFacts:
        raise TypeError("authenticated_root must be _AuthenticatedRecursiveStarkRootFacts")
    if not authenticated_root._has_private_seal():
        raise TypeError("authenticated_root lacks the private seal")
    if type(snapshot) is not _RecursiveStarkAdmissionIndexSnapshot:
        raise TypeError("snapshot must be exactly _RecursiveStarkAdmissionIndexSnapshot")

    facts = authenticated_root.facts
    reject_reason = _policy_reject_reason(facts, authenticated_root.trusted_policy)
    if reject_reason is None and snapshot.chain_id not in (None, facts.chain_id):
        reject_reason = RecursiveStarkAdmissionRejectReason.STATE_CHAIN_ID_MISMATCH
    if reject_reason is None and snapshot.root_is_idempotent_outcome:
        return _RecursiveStarkAdmissionPlan(
            reject_reason=None,
            idempotent_replay=True,
        )
    if reject_reason is None:
        reject_reason = _snapshot_replay_reject_reason(snapshot)
    if reject_reason is None:
        reject_reason = _snapshot_capacity_reject_reason(snapshot, facts)
    return _RecursiveStarkAdmissionPlan(reject_reason=reject_reason)


def _index_snapshot_from_memory(
    state: RecursiveStarkAdmissionState,
    facts: RecursiveStarkRootFacts,
) -> _RecursiveStarkAdmissionIndexSnapshot:
    return _RecursiveStarkAdmissionIndexSnapshot(
        chain_id=state.chain_id,
        root_seen=_contains_sorted(
            state.accepted_root_journal_hashes,
            facts.root_journal_hash,
        ),
        root_is_idempotent_outcome=False,
        slot_seen=_contains_sorted(state.accepted_slots, facts.slot),
        child_claim_overlap=_any_overlap_sorted(
            state.accepted_child_verification_claim_hashes,
            facts.child_verification_claim_hashes,
        ),
        receipt_overlap=_any_overlap_sorted(
            state.accepted_receipt_ids,
            facts.accepted_receipt_ids,
        ),
        message_overlap=_any_overlap_sorted(
            state.accepted_cross_shard_message_ids,
            facts.cross_shard_message_ids,
        ),
        root_count=len(state.accepted_root_journal_hashes),
        slot_count=len(state.accepted_slots),
        child_claim_count=len(state.accepted_child_verification_claim_hashes),
        receipt_count=len(state.accepted_receipt_ids),
        message_count=len(state.accepted_cross_shard_message_ids),
    )


def _policy_reject_reason(
    facts: RecursiveStarkRootFacts,
    policy: TrustedRecursiveStarkAdmissionPolicy,
) -> RecursiveStarkAdmissionRejectReason | None:
    if facts.chain_id != policy.expected_chain_id:
        return RecursiveStarkAdmissionRejectReason.CHAIN_ID_MISMATCH
    if facts.epoch_id != policy.expected_epoch_id:
        return RecursiveStarkAdmissionRejectReason.EPOCH_ID_MISMATCH
    if facts.proof_profile != policy.expected_proof_profile:
        return RecursiveStarkAdmissionRejectReason.PROOF_PROFILE_MISMATCH
    if facts.verifier_set_root != policy.expected_verifier_set_root:
        return RecursiveStarkAdmissionRejectReason.VERIFIER_SET_ROOT_MISMATCH
    if facts.public_policy_hash != policy.expected_public_policy_hash:
        return RecursiveStarkAdmissionRejectReason.PUBLIC_POLICY_HASH_MISMATCH
    return None


def _snapshot_replay_reject_reason(
    snapshot: _RecursiveStarkAdmissionIndexSnapshot,
) -> RecursiveStarkAdmissionRejectReason | None:
    if snapshot.root_seen:
        return RecursiveStarkAdmissionRejectReason.DUPLICATE_ROOT_JOURNAL
    if snapshot.slot_seen:
        return RecursiveStarkAdmissionRejectReason.DUPLICATE_ADMISSION_SLOT
    if snapshot.child_claim_overlap:
        return RecursiveStarkAdmissionRejectReason.DUPLICATE_CHILD_VERIFICATION_CLAIM
    if snapshot.receipt_overlap:
        return RecursiveStarkAdmissionRejectReason.DUPLICATE_ACCEPTED_RECEIPT
    if snapshot.message_overlap:
        return RecursiveStarkAdmissionRejectReason.DUPLICATE_CROSS_SHARD_MESSAGE
    return None


def _snapshot_capacity_reject_reason(
    snapshot: _RecursiveStarkAdmissionIndexSnapshot,
    facts: RecursiveStarkRootFacts,
) -> RecursiveStarkAdmissionRejectReason | None:
    proposed_lengths = (
        snapshot.root_count + 1,
        snapshot.slot_count + 1,
        snapshot.child_claim_count + len(facts.child_verification_claim_hashes),
        snapshot.receipt_count + len(facts.accepted_receipt_ids),
        snapshot.message_count + len(facts.cross_shard_message_ids),
    )
    if any(length > MAX_ADMISSION_INDEX_ENTRIES for length in proposed_lengths):
        return RecursiveStarkAdmissionRejectReason.ADMISSION_INDEX_CAPACITY_EXCEEDED
    return None


def _stage_admission(
    state: RecursiveStarkAdmissionState,
    facts: RecursiveStarkRootFacts,
) -> RecursiveStarkAdmissionState:
    return RecursiveStarkAdmissionState(
        chain_id=facts.chain_id,
        accepted_root_journal_hashes=_insert_sorted(
            state.accepted_root_journal_hashes,
            facts.root_journal_hash,
        ),
        accepted_slots=_insert_sorted(state.accepted_slots, facts.slot),
        accepted_child_verification_claim_hashes=_merge_disjoint_sorted(
            state.accepted_child_verification_claim_hashes,
            facts.child_verification_claim_hashes,
        ),
        accepted_receipt_ids=_merge_disjoint_sorted(
            state.accepted_receipt_ids,
            facts.accepted_receipt_ids,
        ),
        accepted_cross_shard_message_ids=_merge_disjoint_sorted(
            state.accepted_cross_shard_message_ids,
            facts.cross_shard_message_ids,
        ),
    )


def _require_token(value: object, *, name: str, max_bytes: int) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if len(value.encode("utf-8")) > max_bytes:
        raise ValueError(f"{name} exceeds {max_bytes} bytes")
    if any(character not in _TOKEN_CHARS for character in value):
        raise ValueError(f"{name} must use canonical ASCII token characters")
    return value


def _require_epoch_id(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < 0 or value > MAX_EPOCH_ID:
        raise ValueError(f"{name} must be in the unsigned 64-bit range")
    return value


def _require_nonzero_hash(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=HASH_BYTES, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    if canonical == _ZERO_HASH:
        raise ValueError(f"{name} must be nonzero")
    return canonical


def _require_bare_sha256(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if len(value) != 64 or any(character not in "0123456789abcdef" for character in value):
        raise ValueError(f"{name} must be lowercase 64-character hex")
    return value


def _require_prefixed_sha256(value: object, *, prefix: str, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value.startswith(prefix):
        raise ValueError(f"{name} must start with {prefix}")
    _require_bare_sha256(value[len(prefix) :], name=name)
    return value


def _require_sorted_unique_hashes(
    values: object,
    *,
    name: str,
    max_items: int,
    allow_empty: bool,
) -> tuple[str, ...]:
    if not isinstance(values, tuple):
        raise TypeError(f"{name} must be a tuple")
    if not allow_empty and not values:
        raise ValueError(f"{name} must be non-empty")
    if len(values) > max_items:
        raise ValueError(f"{name} exceeds {max_items} items")
    previous: str | None = None
    for index, value in enumerate(values):
        checked = _require_nonzero_hash(value, name=f"{name}[{index}]")
        if previous is not None and checked <= previous:
            raise ValueError(f"{name} must be strictly sorted and unique")
        previous = checked
    return values


def _require_bounded_unique_hashes(
    values: object,
    *,
    name: str,
    max_items: int,
    allow_empty: bool,
) -> tuple[str, ...]:
    if not isinstance(values, tuple):
        raise TypeError(f"{name} must be a tuple")
    if not allow_empty and not values:
        raise ValueError(f"{name} must be non-empty")
    if len(values) > max_items:
        raise ValueError(f"{name} exceeds {max_items} items")
    seen: set[str] = set()
    for index, value in enumerate(values):
        checked = _require_nonzero_hash(value, name=f"{name}[{index}]")
        if checked in seen:
            raise ValueError(f"{name} must be unique")
        seen.add(checked)
    return values


def recursive_child_verification_claims_root_v1(ids: tuple[str, ...]) -> str:
    """Recompute the Rust journal root over lane-ordered child claim hashes."""

    _require_bounded_unique_hashes(
        ids,
        name="child_verification_claim_hashes",
        max_items=MAX_CHILD_VERIFICATION_CLAIMS_PER_ROOT,
        allow_empty=False,
    )
    return _recursive_identifier_root_v1(_CHILD_CLAIMS_ROOT_DOMAIN, ids)


def recursive_receipt_ids_root_v1(ids: tuple[str, ...]) -> str:
    """Recompute the Rust journal root over sorted accepted receipt IDs."""

    _require_sorted_unique_hashes(
        ids,
        name="accepted_receipt_ids",
        max_items=MAX_ACCEPTED_RECEIPT_IDS_PER_ROOT,
        allow_empty=True,
    )
    return _recursive_identifier_root_v1(_RECEIPT_IDS_ROOT_DOMAIN, ids)


def recursive_message_ids_root_v1(ids: tuple[str, ...]) -> str:
    """Recompute the Rust journal root over sorted cross-shard message IDs."""

    _require_sorted_unique_hashes(
        ids,
        name="cross_shard_message_ids",
        max_items=MAX_CROSS_SHARD_MESSAGE_IDS_PER_ROOT,
        allow_empty=True,
    )
    return _recursive_identifier_root_v1(_MESSAGE_IDS_ROOT_DOMAIN, ids)


def _recursive_identifier_root_v1(domain: bytes, ids: tuple[str, ...]) -> str:
    digest = hashlib.sha256()
    digest.update(domain)
    digest.update(len(ids).to_bytes(4, byteorder="big", signed=False))
    for identifier in ids:
        digest.update(bytes.fromhex(identifier.removeprefix("0x")))
    return "0x" + digest.hexdigest()


def _require_committed_root(value: object, expected: str, *, name: str) -> None:
    canonical = _require_nonzero_hash(value, name=name)
    if canonical != expected:
        raise ValueError(f"{name} mismatch")


def _require_sorted_unique_slots(values: object) -> tuple[RecursiveStarkAdmissionSlot, ...]:
    name = "state.accepted_slots"
    if not isinstance(values, tuple):
        raise TypeError(f"{name} must be a tuple")
    if len(values) > MAX_ADMISSION_INDEX_ENTRIES:
        raise ValueError(f"{name} exceeds {MAX_ADMISSION_INDEX_ENTRIES} items")
    previous: RecursiveStarkAdmissionSlot | None = None
    for value in values:
        if not isinstance(value, RecursiveStarkAdmissionSlot):
            raise TypeError(f"{name} must contain RecursiveStarkAdmissionSlot values")
        if previous is not None and value <= previous:
            raise ValueError(f"{name} must be strictly sorted and unique")
        previous = value
    return values


_OrderedValue = TypeVar("_OrderedValue", str, RecursiveStarkAdmissionSlot)


def _contains_sorted(values: tuple[_OrderedValue, ...], value: _OrderedValue) -> bool:
    index = bisect_left(values, value)
    return index < len(values) and values[index] == value


def _any_overlap_sorted(
    existing: tuple[_OrderedValue, ...],
    incoming: tuple[_OrderedValue, ...],
) -> bool:
    return any(_contains_sorted(existing, value) for value in incoming)


def _insert_sorted(
    values: tuple[_OrderedValue, ...],
    value: _OrderedValue,
) -> tuple[_OrderedValue, ...]:
    index = bisect_left(values, value)
    return values[:index] + (value,) + values[index:]


def _merge_disjoint_sorted(
    existing: tuple[_OrderedValue, ...],
    incoming: tuple[_OrderedValue, ...],
) -> tuple[_OrderedValue, ...]:
    if not incoming:
        return existing
    return tuple(sorted(existing + incoming))

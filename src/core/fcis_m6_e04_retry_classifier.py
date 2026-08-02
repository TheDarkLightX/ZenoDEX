"""Typed total durable-state retry classification for FCIS M6 E04.

E04 separates four values that are often accidentally conflated:

* a verifier-owned request/publication attempt;
* a verifier-owned structurally canonical stored-state view;
* a verifier-owned receipt for the fresh reopen subject;
* client transport knowledge about the response.

The classifier is pure.  It performs no datastore read or write and has no
authority to commit a transition.  A shell or a later datastore adapter must
first produce the verifier-owned state view and matching reopen receipt from a
successful canonical reopen.  The exact precedence is the E04 contract:

    same commit and same fingerprint -> ALREADY_COMMITTED
    same commit and different fingerprint -> DEFINITE_REJECTION
    consumed nullifier by another commit -> DEFINITE_REJECTION
    different current state root -> STALE_STATE
    different head/authority context -> DEFINITE_REJECTION
    otherwise -> ABSENT_RETRYABLE

``NEWLY_COMMITTED`` is retained in the durable outcome enum for the complete
R05 algebra.  E04 classifies a retry against already-stored state; the
linearizing publication operation that produces ``NEWLY_COMMITTED`` belongs
to E05.

This remains research-only, unmounted, and non-promotable.  The private
construction tokens and registries are model provenance guards.  They do not
implement cryptographic authentication or production datastore trust.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import Final, TypeAlias
from weakref import WeakValueDictionary

from src.core.fcis_m6_e01_request_identity import (
    E01Error,
    E01RequestIdentityV1,
    same_request_identity_v1,
)
from src.core.fcis_m6_e03_unique_commit_port import (
    E03CommitIdentityV1,
    E03Error,
    is_verified_e03_commit_identity_v1,
)
from src.state.canonical import canonical_json_bytes

FCIS_M6_E04_SCHEMA_V1: Final = "zenodex/fcis/m6/e04/retry-classifier/v1"
FCIS_M6_E04_ATTEMPT_ROOT_SCHEMA_V1: Final = "zenodex/fcis/m6/e04/attempt-root/v1"
FCIS_M6_E04_SNAPSHOT_ROOT_SCHEMA_V1: Final = "zenodex/fcis/m6/e04/stored-state-root/v1"
FCIS_M6_E04_SEQUENCE_BINDING_SCHEMA_V1: Final = "zenodex/fcis/m6/e04/sequence-binding/v1"
FCIS_M6_E04_REOPEN_RECEIPT_SCHEMA_V1: Final = "zenodex/fcis/m6/e04/reopen-receipt/v1"
MAX_E04_COMMITS_V1: Final = 128
MAX_E04_WRITERS_V1: Final = 128
MAX_E04_U32_V1: Final = (1 << 32) - 1
MAX_E04_REJECT_PATH_ITEMS_V1: Final = 8
E04_SEQUENCE_REQUEST_DOMAIN_V1: Final = "request_context_sequence"
E04_SEQUENCE_PUBLICATION_DOMAIN_V1: Final = "publication_history_sequence"
E04_SEQUENCE_MAPPING_PROFILE_ROOT_V1: Final = sha256(
    b"zenodex/fcis/m6/e04/sequence-mapping-profile/v1"
).hexdigest()
_HEX_DIGITS = frozenset("0123456789abcdef")

_E04_ATTEMPT_CONSTRUCTION_TOKEN_V1 = object()
_E04_SEQUENCE_BINDING_CONSTRUCTION_TOKEN_V1 = object()
_E04_STORED_COMMIT_CONSTRUCTION_TOKEN_V1 = object()
_E04_STATE_CONSTRUCTION_TOKEN_V1 = object()
_E04_REOPEN_RECEIPT_CONSTRUCTION_TOKEN_V1 = object()

_E04_ATTEMPT_REGISTRY_V1: WeakValueDictionary[int, E04AttemptV1] = WeakValueDictionary()
_E04_ATTEMPT_SNAPSHOTS_V1: dict[int, bytes] = {}
_E04_SEQUENCE_BINDING_REGISTRY_V1: WeakValueDictionary[int, E04SequenceBindingV1] = (
    WeakValueDictionary()
)
_E04_SEQUENCE_BINDING_SNAPSHOTS_V1: dict[int, bytes] = {}
_E04_STORED_COMMIT_REGISTRY_V1: WeakValueDictionary[int, E04StoredCommitV1] = WeakValueDictionary()
_E04_STORED_COMMIT_SNAPSHOTS_V1: dict[int, bytes] = {}
_E04_STATE_REGISTRY_V1: WeakValueDictionary[int, E04StoredStateV1] = WeakValueDictionary()
_E04_STATE_SNAPSHOTS_V1: dict[int, bytes] = {}
_E04_REOPEN_RECEIPT_REGISTRY_V1: WeakValueDictionary[int, E04ReopenReceiptV1] = (
    WeakValueDictionary()
)
_E04_REOPEN_RECEIPT_SNAPSHOTS_V1: dict[int, bytes] = {}


class E04Error(ValueError):
    """Raised when an E04 value is outside its closed research domain."""


class E04DurableOutcomeV1(Enum):
    """Durable outcomes in the complete R05 commit algebra."""

    NEWLY_COMMITTED = "newly_committed"
    ALREADY_COMMITTED = "already_committed"
    ABSENT_RETRYABLE = "absent_retryable"
    STALE_STATE = "stale_state"
    DEFINITE_REJECTION = "definite_rejection"


class E04ClientKnowledgeV1(Enum):
    """Client knowledge is transport state, never a durable outcome."""

    CONFIRMED = "confirmed"
    INDETERMINATE = "indeterminate"


class E04RejectCodeV1(Enum):
    """Typed failures before a valid total-classification input exists."""

    WRONG_ATTEMPT_TYPE = "wrong_attempt_type"
    UNVERIFIED_ATTEMPT = "unverified_attempt"
    WRONG_STATE_TYPE = "wrong_state_type"
    UNVERIFIED_STATE = "unverified_state"
    WRONG_KNOWLEDGE_TYPE = "wrong_knowledge_type"
    WRONG_REOPEN_RECEIPT_TYPE = "wrong_reopen_receipt_type"
    UNVERIFIED_REOPEN_RECEIPT = "unverified_reopen_receipt"
    REOPEN_SUBJECT_MISMATCH = "reopen_subject_mismatch"


@dataclass(frozen=True, slots=True)
class E04RejectV1:
    """Fail-closed classifier rejection with a stable semantic path."""

    code: E04RejectCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not E04RejectCodeV1:
            raise E04Error("E04 rejection code has the wrong exact type")
        if type(self.path) is not tuple or not self.path:
            raise E04Error("E04 rejection path must be a nonempty exact tuple")
        if len(self.path) > MAX_E04_REJECT_PATH_ITEMS_V1:
            raise E04Error("E04 rejection path exceeds the closed bound")
        if any(type(item) is not str or not item for item in self.path):
            raise E04Error("E04 rejection path contains an invalid item")


def _digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in _HEX_DIGITS for character in value)
    ):
        raise E04Error(f"{name} must be a lowercase SHA-256 digest")
    return value


def _u32(value: object, name: str, *, minimum: int = 0) -> int:
    if type(value) is not int or value < minimum or value > MAX_E04_U32_V1:
        raise E04Error(f"{name} is outside its closed u32 domain")
    return value


def _sequence_binding_body(value: E04SequenceBindingV1) -> dict[str, object]:
    return {
        "schema": FCIS_M6_E04_SEQUENCE_BINDING_SCHEMA_V1,
        "request_domain": E04_SEQUENCE_REQUEST_DOMAIN_V1,
        "publication_domain": E04_SEQUENCE_PUBLICATION_DOMAIN_V1,
        "request_expected_sequence": value.request_expected_sequence,
        "publication_sequence": value.publication_sequence,
        "mapping_profile_root": value.mapping_profile_root,
    }


def _sequence_binding_root(value: E04SequenceBindingV1) -> str:
    return sha256(
        FCIS_M6_E04_SEQUENCE_BINDING_SCHEMA_V1.encode("ascii")
        + b"\x00"
        + canonical_json_bytes(_sequence_binding_body(value))
    ).hexdigest()


@dataclass(frozen=True, slots=True, weakref_slot=True)
class E04SequenceBindingV1:
    """Verifier-owned relation between request and publication sequences.

    The two integers intentionally live in different domains.  The mapping
    profile and the checked projections make that distinction explicit and
    prevent two co-hashed fields from being mistaken for an equality proof.
    """

    request_expected_sequence: int
    publication_sequence: int
    mapping_profile_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _E04_SEQUENCE_BINDING_CONSTRUCTION_TOKEN_V1:
            raise E04Error("E04 sequence binding construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        _u32(self.request_expected_sequence, "request_expected_sequence", minimum=1)
        _u32(self.publication_sequence, "publication_sequence", minimum=1)
        if self.mapping_profile_root != E04_SEQUENCE_MAPPING_PROFILE_ROOT_V1:
            raise E04Error("sequence mapping profile is outside the closed registry")
        _digest(self.mapping_profile_root, "mapping_profile_root")

    def to_wire(self) -> dict[str, object]:
        self._validate_fields()
        return {
            **_sequence_binding_body(self),
            "binding_root": _sequence_binding_root(self),
        }


def _register_sequence_binding_v1(value: E04SequenceBindingV1) -> E04SequenceBindingV1:
    key = id(value)
    _E04_SEQUENCE_BINDING_REGISTRY_V1[key] = value
    _E04_SEQUENCE_BINDING_SNAPSHOTS_V1[key] = canonical_json_bytes(value.to_wire())
    return value


def _mint_e04_sequence_binding_v1(
    *, request_expected_sequence: int, publication_sequence: int
) -> E04SequenceBindingV1:
    return _register_sequence_binding_v1(
        E04SequenceBindingV1(
            request_expected_sequence=request_expected_sequence,
            publication_sequence=publication_sequence,
            mapping_profile_root=E04_SEQUENCE_MAPPING_PROFILE_ROOT_V1,
            _construction_token=_E04_SEQUENCE_BINDING_CONSTRUCTION_TOKEN_V1,
        )
    )


def is_verified_e04_sequence_binding_v1(value: object) -> bool:
    """Return true only for an unchanged verifier-derived sequence relation."""

    if type(value) is not E04SequenceBindingV1:
        return False
    binding = value
    if _E04_SEQUENCE_BINDING_REGISTRY_V1.get(id(binding)) is not binding:
        return False
    try:
        binding._validate_fields()
        expected = _E04_SEQUENCE_BINDING_SNAPSHOTS_V1.get(id(binding))
        return expected is not None and expected == canonical_json_bytes(binding.to_wire())
    except (AttributeError, E04Error, TypeError, ValueError, ArithmeticError):
        return False


def _attempt_body(value: E04AttemptV1) -> dict[str, object]:
    return {
        "schema": FCIS_M6_E04_SCHEMA_V1,
        "request_identity": value.request_identity.to_wire(),
        "commit": value.commit.to_wire(),
        "expected_pre_root": value.expected_pre_root,
        "writer_profile_root": value.writer_profile_root,
        "authority_state_root": value.authority_state_root,
        "verifier_profile_root": value.verifier_profile_root,
        "sequence_binding": value.sequence_binding.to_wire(),
    }


def _attempt_root(value: E04AttemptV1) -> str:
    return sha256(
        FCIS_M6_E04_ATTEMPT_ROOT_SCHEMA_V1.encode("ascii")
        + b"\x00"
        + canonical_json_bytes(_attempt_body(value))
    ).hexdigest()


@dataclass(frozen=True, slots=True, weakref_slot=True)
class E04AttemptV1:
    """Verifier-owned complete retry/publication attempt lineage."""

    request_identity: E01RequestIdentityV1
    commit: E03CommitIdentityV1
    expected_pre_root: str
    writer_profile_root: str
    authority_state_root: str
    verifier_profile_root: str
    sequence_binding: E04SequenceBindingV1
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _E04_ATTEMPT_CONSTRUCTION_TOKEN_V1:
            raise E04Error("E04 attempt construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        if type(self.request_identity) is not E01RequestIdentityV1:
            raise E04Error("request identity has the wrong exact type")
        try:
            same_request_identity_v1(self.request_identity, self.request_identity)
        except (E01Error, TypeError, ValueError, ArithmeticError, OverflowError) as exc:
            raise E04Error("request identity lacks verifier provenance") from exc
        if type(self.commit) is not E03CommitIdentityV1:
            raise E04Error("commit has the wrong exact type")
        if not is_verified_e03_commit_identity_v1(self.commit):
            raise E04Error("commit lacks verifier provenance")
        self.commit._validate_fields()
        if type(self.sequence_binding) is not E04SequenceBindingV1:
            raise E04Error("sequence binding has the wrong exact type")
        if not is_verified_e04_sequence_binding_v1(self.sequence_binding):
            raise E04Error("sequence binding lacks verifier provenance")
        if (
            self.sequence_binding.request_expected_sequence
            != self.request_identity.expected_sequence
            or self.sequence_binding.publication_sequence != self.commit.sequence
        ):
            raise E04Error("sequence binding is crossed with its source values")
        nullifier = self.commit.nullifier
        if (
            nullifier.request_identity_root != self.request_identity.request_identity_root
            or nullifier.deployment_config_root != self.request_identity.deployment_config_root
            or nullifier.sender_id != self.request_identity.sender_id
            or nullifier.command_family != self.request_identity.command_family
            or nullifier.nonce != self.request_identity.nonce
        ):
            raise E04Error("commit nullifier is crossed with the request identity")
        _digest(self.expected_pre_root, "expected_pre_root")
        _digest(self.writer_profile_root, "writer_profile_root")
        _digest(self.authority_state_root, "authority_state_root")
        _digest(self.verifier_profile_root, "verifier_profile_root")
        for effect in self.commit.effects:
            if effect.writer_profile_root != self.writer_profile_root:
                raise E04Error("commit effect writer profile is crossed with the attempt")

    @property
    def publication_sequence(self) -> int:
        self._validate_fields()
        return self.sequence_binding.publication_sequence

    @property
    def attempt_root(self) -> str:
        self._validate_fields()
        return _attempt_root(self)

    @property
    def fingerprint(self) -> str:
        """Fingerprint of the complete attempt, including request context."""

        return self.attempt_root

    def to_wire(self) -> dict[str, object]:
        self._validate_fields()
        return {
            **_attempt_body(self),
            "attempt_root": self.attempt_root,
            "publication_sequence": self.publication_sequence,
        }


def _register_attempt_v1(value: E04AttemptV1) -> E04AttemptV1:
    key = id(value)
    _E04_ATTEMPT_REGISTRY_V1[key] = value
    _E04_ATTEMPT_SNAPSHOTS_V1[key] = canonical_json_bytes(value.to_wire())
    return value


def _mint_e04_attempt_v1(
    *,
    request_identity: E01RequestIdentityV1,
    commit: E03CommitIdentityV1,
    expected_pre_root: str,
    writer_profile_root: str,
    authority_state_root: str,
    verifier_profile_root: str,
) -> E04AttemptV1:
    """Mint an E04 attempt from the preceding verifier-owned values."""

    return _register_attempt_v1(
        E04AttemptV1(
            request_identity=request_identity,
            commit=commit,
            expected_pre_root=expected_pre_root,
            writer_profile_root=writer_profile_root,
            authority_state_root=authority_state_root,
            verifier_profile_root=verifier_profile_root,
            sequence_binding=_mint_e04_sequence_binding_v1(
                request_expected_sequence=request_identity.expected_sequence,
                publication_sequence=commit.sequence,
            ),
            _construction_token=_E04_ATTEMPT_CONSTRUCTION_TOKEN_V1,
        )
    )


def is_verified_e04_attempt_v1(value: object) -> bool:
    """Return true only for an unchanged verifier-derived attempt."""

    if type(value) is not E04AttemptV1:
        return False
    attempt = value
    if _E04_ATTEMPT_REGISTRY_V1.get(id(attempt)) is not attempt:
        return False
    try:
        attempt._validate_fields()
        expected = _E04_ATTEMPT_SNAPSHOTS_V1.get(id(attempt))
        return expected is not None and expected == canonical_json_bytes(attempt.to_wire())
    except (AttributeError, E01Error, E03Error, E04Error, TypeError, ValueError, ArithmeticError):
        return False


@dataclass(frozen=True, slots=True, weakref_slot=True)
class E04StoredCommitV1:
    """One complete committed attempt in the canonical stored-state view."""

    attempt: E04AttemptV1
    post_state_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _E04_STORED_COMMIT_CONSTRUCTION_TOKEN_V1:
            raise E04Error("stored commit construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        if not is_verified_e04_attempt_v1(self.attempt):
            raise E04Error("stored commit attempt lacks verifier provenance")
        _digest(self.post_state_root, "post_state_root")

    def to_wire(self) -> dict[str, object]:
        self._validate_fields()
        return {
            "attempt": self.attempt.to_wire(),
            "post_state_root": self.post_state_root,
        }


def _register_stored_commit_v1(value: E04StoredCommitV1) -> E04StoredCommitV1:
    key = id(value)
    _E04_STORED_COMMIT_REGISTRY_V1[key] = value
    _E04_STORED_COMMIT_SNAPSHOTS_V1[key] = canonical_json_bytes(value.to_wire())
    return value


def _mint_e04_stored_commit_v1(*, attempt: E04AttemptV1, post_state_root: str) -> E04StoredCommitV1:
    return _register_stored_commit_v1(
        E04StoredCommitV1(
            attempt=attempt,
            post_state_root=post_state_root,
            _construction_token=_E04_STORED_COMMIT_CONSTRUCTION_TOKEN_V1,
        )
    )


def is_verified_e04_stored_commit_v1(value: object) -> bool:
    """Return true only for an unchanged verifier-derived stored commit."""

    if type(value) is not E04StoredCommitV1:
        return False
    stored = value
    if _E04_STORED_COMMIT_REGISTRY_V1.get(id(stored)) is not stored:
        return False
    try:
        stored._validate_fields()
        expected = _E04_STORED_COMMIT_SNAPSHOTS_V1.get(id(stored))
        return expected is not None and expected == canonical_json_bytes(stored.to_wire())
    except (AttributeError, E04Error, TypeError, ValueError, ArithmeticError):
        return False


def _state_body(value: E04StoredStateV1) -> dict[str, object]:
    return {
        "schema": FCIS_M6_E04_SCHEMA_V1,
        "genesis_state_root": value.genesis_state_root,
        "current_state_root": value.current_state_root,
        "authority_epoch_index": value.authority_epoch_index,
        "authority_state_root": value.authority_state_root,
        "allowed_writer_roots": list(value.allowed_writer_roots),
        "deployment_config_root": value.deployment_config_root,
        "verifier_profile_root": value.verifier_profile_root,
        "commits": [commit.to_wire() for commit in value.commits],
    }


def _state_root(value: E04StoredStateV1) -> str:
    return sha256(
        FCIS_M6_E04_SNAPSHOT_ROOT_SCHEMA_V1.encode("ascii")
        + b"\x00"
        + canonical_json_bytes(_state_body(value))
    ).hexdigest()


@dataclass(frozen=True, slots=True, weakref_slot=True)
class E04StoredStateV1:
    """Verifier-owned canonical state view used by the pure classifier."""

    genesis_state_root: str
    current_state_root: str
    authority_epoch_index: int
    authority_state_root: str
    allowed_writer_roots: tuple[str, ...]
    deployment_config_root: str
    verifier_profile_root: str
    commits: tuple[E04StoredCommitV1, ...]
    snapshot_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _E04_STATE_CONSTRUCTION_TOKEN_V1:
            raise E04Error("stored-state construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        _digest(self.genesis_state_root, "genesis_state_root")
        _digest(self.current_state_root, "current_state_root")
        _u32(self.authority_epoch_index, "authority_epoch_index")
        _digest(self.authority_state_root, "authority_state_root")
        _digest(self.deployment_config_root, "deployment_config_root")
        _digest(self.verifier_profile_root, "verifier_profile_root")
        _digest(self.snapshot_root, "snapshot_root")
        if type(self.allowed_writer_roots) is not tuple:
            raise E04Error("allowed_writer_roots must be an exact tuple")
        if len(self.allowed_writer_roots) > MAX_E04_WRITERS_V1:
            raise E04Error("allowed_writer_roots exceed the closed bound")
        for writer in self.allowed_writer_roots:
            _digest(writer, "allowed_writer_root")
        if tuple(sorted(self.allowed_writer_roots)) != self.allowed_writer_roots:
            raise E04Error("allowed_writer_roots must be canonically ordered")
        if len(set(self.allowed_writer_roots)) != len(self.allowed_writer_roots):
            raise E04Error("allowed_writer_roots must be unique")
        if type(self.commits) is not tuple:
            raise E04Error("commits must be an exact tuple")
        if len(self.commits) > MAX_E04_COMMITS_V1:
            raise E04Error("commits exceed the closed transition bound")
        expected_pre = self.genesis_state_root
        commit_ids: set[str] = set()
        nullifiers: set[str] = set()
        for sequence, stored in enumerate(self.commits, start=1):
            if type(stored) is not E04StoredCommitV1:
                raise E04Error("commits contain the wrong exact type")
            if not is_verified_e04_stored_commit_v1(stored):
                raise E04Error("commits contain an unverified stored value")
            attempt = stored.attempt
            if attempt.publication_sequence != sequence:
                raise E04Error("publication sequence is not contiguous")
            if attempt.expected_pre_root != expected_pre:
                raise E04Error("stored commits do not form a state chain")
            if attempt.commit.commit_id in commit_ids:
                raise E04Error("stored commit IDs must be unique")
            if attempt.commit.nullifier.nullifier_root in nullifiers:
                raise E04Error("stored nullifiers must be unique")
            if (
                attempt.request_identity.deployment_config_root != self.deployment_config_root
                or attempt.verifier_profile_root != self.verifier_profile_root
            ):
                raise E04Error("stored commit is crossed with its state context")
            if attempt.request_identity.authority_epoch_index > self.authority_epoch_index:
                raise E04Error("stored commit names a future authority epoch")
            commit_ids.add(attempt.commit.commit_id)
            nullifiers.add(attempt.commit.nullifier.nullifier_root)
            expected_pre = stored.post_state_root
        if self.current_state_root != expected_pre:
            raise E04Error("current_state_root is not the exact stored head")
        if self.snapshot_root != _state_root(self):
            raise E04Error("snapshot_root is not canonically bound")

    def to_wire(self) -> dict[str, object]:
        self._validate_fields()
        return {**_state_body(self), "snapshot_root": self.snapshot_root}


def _register_state_v1(value: E04StoredStateV1) -> E04StoredStateV1:
    key = id(value)
    _E04_STATE_REGISTRY_V1[key] = value
    _E04_STATE_SNAPSHOTS_V1[key] = canonical_json_bytes(value.to_wire())
    return value


def _mint_e04_stored_state_v1(
    *,
    genesis_state_root: str,
    current_state_root: str,
    authority_epoch_index: int,
    authority_state_root: str,
    allowed_writer_roots: tuple[str, ...],
    deployment_config_root: str,
    verifier_profile_root: str,
    commits: tuple[E04StoredCommitV1, ...],
) -> E04StoredStateV1:
    provisional = object.__new__(E04StoredStateV1)
    object.__setattr__(provisional, "genesis_state_root", genesis_state_root)
    object.__setattr__(provisional, "current_state_root", current_state_root)
    object.__setattr__(provisional, "authority_epoch_index", authority_epoch_index)
    object.__setattr__(provisional, "authority_state_root", authority_state_root)
    object.__setattr__(provisional, "allowed_writer_roots", allowed_writer_roots)
    object.__setattr__(provisional, "deployment_config_root", deployment_config_root)
    object.__setattr__(provisional, "verifier_profile_root", verifier_profile_root)
    object.__setattr__(provisional, "commits", commits)
    object.__setattr__(provisional, "snapshot_root", "0" * 64)
    return _register_state_v1(
        E04StoredStateV1(
            genesis_state_root=provisional.genesis_state_root,
            current_state_root=provisional.current_state_root,
            authority_epoch_index=provisional.authority_epoch_index,
            authority_state_root=provisional.authority_state_root,
            allowed_writer_roots=provisional.allowed_writer_roots,
            deployment_config_root=provisional.deployment_config_root,
            verifier_profile_root=provisional.verifier_profile_root,
            commits=provisional.commits,
            snapshot_root=_state_root(provisional),
            _construction_token=_E04_STATE_CONSTRUCTION_TOKEN_V1,
        )
    )


def is_verified_e04_stored_state_v1(value: object) -> bool:
    """Return true only for an unchanged canonical state view."""

    if type(value) is not E04StoredStateV1:
        return False
    state = value
    if _E04_STATE_REGISTRY_V1.get(id(state)) is not state:
        return False
    try:
        state._validate_fields()
        expected = _E04_STATE_SNAPSHOTS_V1.get(id(state))
        return expected is not None and expected == canonical_json_bytes(state.to_wire())
    except (AttributeError, E04Error, TypeError, ValueError, ArithmeticError):
        return False


def _reopen_receipt_body(value: E04ReopenReceiptV1) -> dict[str, object]:
    return {
        "schema": FCIS_M6_E04_REOPEN_RECEIPT_SCHEMA_V1,
        "snapshot_root": value.snapshot_root,
        "current_state_root": value.current_state_root,
        "authority_epoch_index": value.authority_epoch_index,
        "authority_state_root": value.authority_state_root,
        "deployment_config_root": value.deployment_config_root,
        "verifier_profile_root": value.verifier_profile_root,
        "datastore_profile_root": value.datastore_profile_root,
        "read_version": value.read_version,
        "freshness_epoch": value.freshness_epoch,
    }


def _reopen_receipt_root(value: E04ReopenReceiptV1) -> str:
    return sha256(
        FCIS_M6_E04_REOPEN_RECEIPT_SCHEMA_V1.encode("ascii")
        + b"\x00"
        + canonical_json_bytes(_reopen_receipt_body(value))
    ).hexdigest()


@dataclass(frozen=True, slots=True, weakref_slot=True)
class E04ReopenReceiptV1:
    """Verifier-owned subject for a fresh canonical-reopen observation.

    The receipt is a typed model port.  A production datastore adapter must
    supply the actual canonical-reopen and freshness proof represented by
    these fields before this port may be used for runtime authorization.
    """

    snapshot_root: str
    current_state_root: str
    authority_epoch_index: int
    authority_state_root: str
    deployment_config_root: str
    verifier_profile_root: str
    datastore_profile_root: str
    read_version: int
    freshness_epoch: int
    receipt_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _E04_REOPEN_RECEIPT_CONSTRUCTION_TOKEN_V1:
            raise E04Error("E04 reopen receipt construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        _digest(self.snapshot_root, "snapshot_root")
        _digest(self.current_state_root, "current_state_root")
        _u32(self.authority_epoch_index, "authority_epoch_index")
        _digest(self.authority_state_root, "authority_state_root")
        _digest(self.deployment_config_root, "deployment_config_root")
        _digest(self.verifier_profile_root, "verifier_profile_root")
        _digest(self.datastore_profile_root, "datastore_profile_root")
        _u32(self.read_version, "read_version", minimum=1)
        _u32(self.freshness_epoch, "freshness_epoch", minimum=1)
        _digest(self.receipt_root, "receipt_root")
        if self.receipt_root != _reopen_receipt_root(self):
            raise E04Error("reopen receipt root is not canonically bound")

    def to_wire(self) -> dict[str, object]:
        self._validate_fields()
        return {**_reopen_receipt_body(self), "receipt_root": self.receipt_root}


def _register_reopen_receipt_v1(value: E04ReopenReceiptV1) -> E04ReopenReceiptV1:
    key = id(value)
    _E04_REOPEN_RECEIPT_REGISTRY_V1[key] = value
    _E04_REOPEN_RECEIPT_SNAPSHOTS_V1[key] = canonical_json_bytes(value.to_wire())
    return value


def _mint_e04_reopen_receipt_v1(
    *,
    state: E04StoredStateV1,
    datastore_profile_root: str,
    read_version: int,
    freshness_epoch: int,
) -> E04ReopenReceiptV1:
    """Mint the model port after an external reopen verifier has succeeded."""

    if not is_verified_e04_stored_state_v1(state):
        raise E04Error("reopen receipt subject must be a verified stored state")
    _digest(datastore_profile_root, "datastore_profile_root")
    _u32(read_version, "read_version", minimum=1)
    _u32(freshness_epoch, "freshness_epoch", minimum=1)
    provisional = object.__new__(E04ReopenReceiptV1)
    object.__setattr__(provisional, "snapshot_root", state.snapshot_root)
    object.__setattr__(provisional, "current_state_root", state.current_state_root)
    object.__setattr__(provisional, "authority_epoch_index", state.authority_epoch_index)
    object.__setattr__(provisional, "authority_state_root", state.authority_state_root)
    object.__setattr__(provisional, "deployment_config_root", state.deployment_config_root)
    object.__setattr__(provisional, "verifier_profile_root", state.verifier_profile_root)
    object.__setattr__(provisional, "datastore_profile_root", datastore_profile_root)
    object.__setattr__(provisional, "read_version", read_version)
    object.__setattr__(provisional, "freshness_epoch", freshness_epoch)
    object.__setattr__(provisional, "receipt_root", "0" * 64)
    return _register_reopen_receipt_v1(
        E04ReopenReceiptV1(
            snapshot_root=provisional.snapshot_root,
            current_state_root=provisional.current_state_root,
            authority_epoch_index=provisional.authority_epoch_index,
            authority_state_root=provisional.authority_state_root,
            deployment_config_root=provisional.deployment_config_root,
            verifier_profile_root=provisional.verifier_profile_root,
            datastore_profile_root=provisional.datastore_profile_root,
            read_version=provisional.read_version,
            freshness_epoch=provisional.freshness_epoch,
            receipt_root=_reopen_receipt_root(provisional),
            _construction_token=_E04_REOPEN_RECEIPT_CONSTRUCTION_TOKEN_V1,
        )
    )


def is_verified_e04_reopen_receipt_v1(value: object) -> bool:
    """Return true only for an unchanged verifier-derived reopen receipt."""

    if type(value) is not E04ReopenReceiptV1:
        return False
    receipt = value
    if _E04_REOPEN_RECEIPT_REGISTRY_V1.get(id(receipt)) is not receipt:
        return False
    try:
        receipt._validate_fields()
        expected = _E04_REOPEN_RECEIPT_SNAPSHOTS_V1.get(id(receipt))
        return expected is not None and expected == canonical_json_bytes(receipt.to_wire())
    except (AttributeError, E04Error, TypeError, ValueError, ArithmeticError):
        return False


@dataclass(frozen=True, slots=True)
class E04RetryResolutionV1:
    """Total classification plus the client knowledge dimension."""

    outcome: E04DurableOutcomeV1
    client_knowledge: E04ClientKnowledgeV1
    attempt_root: str
    snapshot_root: str
    matched_commit_id: str | None

    def __post_init__(self) -> None:
        if type(self.outcome) is not E04DurableOutcomeV1:
            raise E04Error("resolution outcome has the wrong exact type")
        if type(self.client_knowledge) is not E04ClientKnowledgeV1:
            raise E04Error("resolution knowledge has the wrong exact type")
        _digest(self.attempt_root, "attempt_root")
        _digest(self.snapshot_root, "snapshot_root")
        if self.matched_commit_id is not None:
            _digest(self.matched_commit_id, "matched_commit_id")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": FCIS_M6_E04_SCHEMA_V1,
            "outcome": self.outcome.value,
            "client_knowledge": self.client_knowledge.value,
            "attempt_root": self.attempt_root,
            "snapshot_root": self.snapshot_root,
            "matched_commit_id": self.matched_commit_id,
        }


E04ClassificationV1: TypeAlias = E04RetryResolutionV1 | E04RejectV1


def _reject(code: E04RejectCodeV1, path: str) -> E04RejectV1:
    return E04RejectV1(code=code, path=(path,))


def _resolution(
    *,
    outcome: E04DurableOutcomeV1,
    knowledge: E04ClientKnowledgeV1,
    attempt: E04AttemptV1,
    state: E04StoredStateV1,
    matched_commit_id: str | None,
) -> E04RetryResolutionV1:
    return E04RetryResolutionV1(
        outcome=outcome,
        client_knowledge=knowledge,
        attempt_root=attempt.attempt_root,
        snapshot_root=state.snapshot_root,
        matched_commit_id=matched_commit_id,
    )


def classify_e04_retry(
    attempt: object,
    state: object,
    client_knowledge: object,
    reopen_receipt: object,
) -> E04ClassificationV1:
    """Classify a retry against one state view and its fresh-reopen subject.

    The receipt is required so an in-memory structural state view cannot be
    treated as a fresh durable read without an explicit verifier-port value.
    """

    if type(attempt) is not E04AttemptV1:
        return _reject(E04RejectCodeV1.WRONG_ATTEMPT_TYPE, "attempt")
    if not is_verified_e04_attempt_v1(attempt):
        return _reject(E04RejectCodeV1.UNVERIFIED_ATTEMPT, "attempt")
    if type(state) is not E04StoredStateV1:
        return _reject(E04RejectCodeV1.WRONG_STATE_TYPE, "state")
    if not is_verified_e04_stored_state_v1(state):
        return _reject(E04RejectCodeV1.UNVERIFIED_STATE, "state")
    if type(reopen_receipt) is not E04ReopenReceiptV1:
        return _reject(E04RejectCodeV1.WRONG_REOPEN_RECEIPT_TYPE, "reopen_receipt")
    if not is_verified_e04_reopen_receipt_v1(reopen_receipt):
        return _reject(E04RejectCodeV1.UNVERIFIED_REOPEN_RECEIPT, "reopen_receipt")
    if type(client_knowledge) is not E04ClientKnowledgeV1:
        return _reject(E04RejectCodeV1.WRONG_KNOWLEDGE_TYPE, "client_knowledge")
    checked_attempt = attempt
    checked_state = state
    checked_receipt = reopen_receipt
    knowledge = client_knowledge
    if (
        checked_receipt.snapshot_root != checked_state.snapshot_root
        or checked_receipt.current_state_root != checked_state.current_state_root
        or checked_receipt.authority_epoch_index != checked_state.authority_epoch_index
        or checked_receipt.authority_state_root != checked_state.authority_state_root
        or checked_receipt.deployment_config_root != checked_state.deployment_config_root
        or checked_receipt.verifier_profile_root != checked_state.verifier_profile_root
    ):
        return _reject(E04RejectCodeV1.REOPEN_SUBJECT_MISMATCH, "reopen_receipt")

    for stored in checked_state.commits:
        stored_attempt = stored.attempt
        if stored_attempt.commit.commit_id == checked_attempt.commit.commit_id:
            outcome = (
                E04DurableOutcomeV1.ALREADY_COMMITTED
                if stored_attempt.fingerprint == checked_attempt.fingerprint
                else E04DurableOutcomeV1.DEFINITE_REJECTION
            )
            return _resolution(
                outcome=outcome,
                knowledge=knowledge,
                attempt=checked_attempt,
                state=checked_state,
                matched_commit_id=stored_attempt.commit.commit_id
                if outcome is E04DurableOutcomeV1.ALREADY_COMMITTED
                else None,
            )
        if (
            stored_attempt.commit.nullifier.nullifier_root
            == checked_attempt.commit.nullifier.nullifier_root
        ):
            return _resolution(
                outcome=E04DurableOutcomeV1.DEFINITE_REJECTION,
                knowledge=knowledge,
                attempt=checked_attempt,
                state=checked_state,
                matched_commit_id=None,
            )

    if checked_state.current_state_root != checked_attempt.expected_pre_root:
        return _resolution(
            outcome=E04DurableOutcomeV1.STALE_STATE,
            knowledge=knowledge,
            attempt=checked_attempt,
            state=checked_state,
            matched_commit_id=None,
        )

    head_matches = (
        checked_attempt.publication_sequence == len(checked_state.commits) + 1
        and checked_attempt.request_identity.authority_epoch_index
        == checked_state.authority_epoch_index
        and checked_attempt.authority_state_root == checked_state.authority_state_root
        and checked_attempt.writer_profile_root in checked_state.allowed_writer_roots
        and checked_attempt.request_identity.deployment_config_root
        == checked_state.deployment_config_root
        and checked_attempt.verifier_profile_root == checked_state.verifier_profile_root
    )
    outcome = (
        E04DurableOutcomeV1.ABSENT_RETRYABLE
        if head_matches
        else E04DurableOutcomeV1.DEFINITE_REJECTION
    )
    return _resolution(
        outcome=outcome,
        knowledge=knowledge,
        attempt=checked_attempt,
        state=checked_state,
        matched_commit_id=None,
    )


__all__ = (
    "E04AttemptV1",
    "E04ClassificationV1",
    "E04ClientKnowledgeV1",
    "E04DurableOutcomeV1",
    "E04Error",
    "E04ReopenReceiptV1",
    "E04RejectCodeV1",
    "E04RejectV1",
    "E04RetryResolutionV1",
    "E04_SEQUENCE_MAPPING_PROFILE_ROOT_V1",
    "E04_SEQUENCE_PUBLICATION_DOMAIN_V1",
    "E04_SEQUENCE_REQUEST_DOMAIN_V1",
    "E04SequenceBindingV1",
    "E04StoredCommitV1",
    "E04StoredStateV1",
    "FCIS_M6_E04_ATTEMPT_ROOT_SCHEMA_V1",
    "FCIS_M6_E04_REOPEN_RECEIPT_SCHEMA_V1",
    "FCIS_M6_E04_SCHEMA_V1",
    "FCIS_M6_E04_SEQUENCE_BINDING_SCHEMA_V1",
    "FCIS_M6_E04_SNAPSHOT_ROOT_SCHEMA_V1",
    "MAX_E04_COMMITS_V1",
    "MAX_E04_REJECT_PATH_ITEMS_V1",
    "MAX_E04_U32_V1",
    "MAX_E04_WRITERS_V1",
    "classify_e04_retry",
    "is_verified_e04_attempt_v1",
    "is_verified_e04_reopen_receipt_v1",
    "is_verified_e04_sequence_binding_v1",
    "is_verified_e04_stored_commit_v1",
    "is_verified_e04_stored_state_v1",
)

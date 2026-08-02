"""Research-only unique publication capability for FCIS M6 K02.

The port is a pure capability boundary. It accepts an exact D08 verifier
acceptance witness, an immutable publication request, and an immutable current
port state. It returns a new state, a retry classification, or a typed reject.
No database, network, filesystem, process, clock, random source, or logging
adapter is imported here.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from src.core import fcis_m6_d08_combined_anf as d08
from src.core.fcis_durable_retraction import (
    DurableRetractionError,
    OutboxEffectV1,
    PublicationAtomV1,
    outbox_root,
    tagged_digest,
)

K02_COMMIT_PORT_SCHEMA_V1: Final = "zenodex/fcis/m6/k02/unique-commit-port/v1"
K02_UNIQUE_PORT_ID_V1: Final = "fcis/m6/unique-atomic-commit-port/v1"
U32_MAX: Final = (1 << 32) - 1
_HEX: Final = frozenset("0123456789abcdef")
_PORT_CONSTRUCTION_TOKEN_V1: Final = object()


class K02Error(ValueError):
    """Typed construction or transition failure in the K02 model."""


class K02CommitResolutionV1(Enum):
    """The only successful durable classifications exposed by the port."""

    NEWLY_COMMITTED = "newly_committed"
    ALREADY_COMMITTED = "already_committed"


class K02RejectCodeV1(Enum):
    """Fail-closed port rejection classes."""

    WRONG_CAPABILITY = "wrong_capability"
    WRONG_STATE = "wrong_state"
    WRONG_REQUEST = "wrong_request"
    ANF_WITNESS_REJECTED = "anf_witness_rejected"
    SEQUENCE_MISMATCH = "sequence_mismatch"
    STALE_HEAD = "stale_head"
    COMMIT_COLLISION = "commit_collision"


def _digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or value != value.lower()
        or any(character not in _HEX for character in value)
    ):
        raise K02Error(f"{name} must be 64 lowercase hexadecimal characters")
    return value


def _text(value: object, name: str) -> str:
    if type(value) is not str or not value:
        raise K02Error(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise K02Error(f"{name} must be valid UTF-8") from exc
    if len(encoded) > 512:
        raise K02Error(f"{name} exceeds its byte bound")
    return value


def _u32(value: object, name: str) -> int:
    if type(value) is not int or value < 0 or value > U32_MAX:
        raise K02Error(f"{name} must be an exact u32")
    return value


@dataclass(frozen=True, slots=True)
class K02PublicationRequestV1:
    """One request whose publication fields are owned by the D08 witness."""

    anf_accept: object

    def __post_init__(self) -> None:
        self.publication_atom.__post_init__()

    @property
    def publication_atom(self) -> PublicationAtomV1:
        """Return the complete publication aggregate owned by D08."""

        if not d08.is_verified_combined_anf_accept_v1(self.anf_accept):
            raise K02Error("publication request lacks a verified D08 acceptance witness")
        try:
            return d08.authorized_publication_atom_v1(self.anf_accept)
        except (
            d08.D08CombinedANFError,
            DurableRetractionError,
            AttributeError,
            TypeError,
            ValueError,
            ArithmeticError,
            OverflowError,
        ) as exc:
            raise K02Error("D08 publication aggregate is invalid") from exc

    @property
    def commit_id(self) -> str:
        return cast(str, self.publication_atom.commit_id)

    @property
    def expected_pre_state_root(self) -> str:
        return cast(str, self.publication_atom.expected_pre_root)

    @property
    def post_state_root(self) -> str:
        return cast(str, self.publication_atom.post_state_root)

    @property
    def authority_epoch_root(self) -> str:
        return cast(str, self.publication_atom.authority_state_root)

    @property
    def effect_root(self) -> str:
        return cast(
            str,
            outbox_root(cast(tuple[OutboxEffectV1, ...], self.publication_atom.outbox)),
        )

    @property
    def sequence(self) -> int:
        return cast(int, self.publication_atom.sequence)


@dataclass(frozen=True, slots=True, order=True)
class K02CommitRecordV1:
    """The minimal immutable record needed for same-commit retry detection."""

    sequence: int
    commit_id: str
    fingerprint_root: str
    post_state_root: str
    response_root: str

    def __post_init__(self) -> None:
        _u32(self.sequence, "record.sequence")
        _digest(self.commit_id, "record.commit_id")
        _digest(self.fingerprint_root, "record.fingerprint_root")
        _digest(self.post_state_root, "record.post_state_root")
        _digest(self.response_root, "record.response_root")


@dataclass(frozen=True, slots=True)
class K02PortStateV1:
    """Immutable state owned by the unique port transition."""

    head_root: str
    next_sequence: int
    records: tuple[K02CommitRecordV1, ...]

    def __post_init__(self) -> None:
        _digest(self.head_root, "state.head_root")
        _u32(self.next_sequence, "state.next_sequence")
        if type(self.records) is not tuple:
            raise K02Error("state.records must be an exact tuple")
        if len(self.records) > U32_MAX:
            raise K02Error("state.records exceeds its closed bound")
        for record in self.records:
            if type(record) is not K02CommitRecordV1:
                raise K02Error("state record has the wrong exact type")
            record.__post_init__()
        if tuple(record.sequence for record in self.records) != tuple(
            range(1, len(self.records) + 1)
        ):
            raise K02Error("state record sequence is not contiguous")
        if self.next_sequence != len(self.records) + 1:
            raise K02Error("state next_sequence does not match record count")
        commit_ids = tuple(record.commit_id for record in self.records)
        if len(set(commit_ids)) != len(commit_ids):
            raise K02Error("state records contain duplicate commit IDs")


@dataclass(frozen=True, slots=True)
class K02CommitTransitionV1:
    """A successful result from the only publication edge."""

    resolution: K02CommitResolutionV1
    state: K02PortStateV1
    commit_id: str
    response_root: str

    def __post_init__(self) -> None:
        if type(self.resolution) is not K02CommitResolutionV1:
            raise K02Error("transition resolution has the wrong exact type")
        if type(self.state) is not K02PortStateV1:
            raise K02Error("transition state has the wrong exact type")
        _digest(self.commit_id, "transition.commit_id")
        _digest(self.response_root, "transition.response_root")
        if not any(
            record.commit_id == self.commit_id and record.response_root == self.response_root
            for record in self.state.records
        ):
            raise K02Error("transition response is absent from port state")


@dataclass(frozen=True, slots=True)
class K02RejectV1:
    """A typed rejection that carries no publication authority."""

    code: K02RejectCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not K02RejectCodeV1:
            raise K02Error("reject code has the wrong exact type")
        if (
            type(self.path) is not tuple
            or not self.path
            or any(type(item) is not str or not item for item in self.path)
        ):
            raise K02Error("reject path has the wrong exact type")


K02ResultV1: TypeAlias = K02CommitTransitionV1 | K02RejectV1


@dataclass(frozen=True, slots=True)
class K02CommitPortV1:
    """Opaque singleton publication capability.

    The construction token is intentionally absent from the public API. The
    only returned instance is the module-owned singleton below.
    """

    port_id: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _PORT_CONSTRUCTION_TOKEN_V1:
            raise TypeError("K02 commit port requires controlled construction")
        if self.port_id != K02_UNIQUE_PORT_ID_V1:
            raise K02Error("K02 commit port ID is not the unique declared port")

    def publish(self, state: object, request: object) -> K02ResultV1:
        """Use the singleton port without exposing a second publication path."""

        return publish_v1(self, state, request)


_UNIQUE_COMMIT_PORT_V1 = K02CommitPortV1(
    port_id=K02_UNIQUE_PORT_ID_V1,
    _construction_token=_PORT_CONSTRUCTION_TOKEN_V1,
)


def unique_commit_port_v1() -> K02CommitPortV1:
    """Return the one process-local capability object for this research model."""

    return _UNIQUE_COMMIT_PORT_V1


def initial_port_state_v1(head_root: object) -> K02PortStateV1:
    """Create an authority-free initial state for a bounded model run."""

    try:
        return K02PortStateV1(
            head_root=_digest(head_root, "head_root"), next_sequence=1, records=()
        )
    except (K02Error, TypeError, ValueError, ArithmeticError, OverflowError) as exc:
        raise K02Error("invalid initial port state") from exc


def request_fingerprint_root_v1(request: K02PublicationRequestV1) -> str:
    """Derive the exact retry identity from all publication-relevant fields."""

    request.__post_init__()
    exact_anf = cast(d08.D08CombinedANFAcceptV1, request.anf_accept)
    exact_atom = request.publication_atom
    return cast(
        str,
        tagged_digest(
            "k02/request/v1/"
            f"{request.commit_id}/{request.expected_pre_state_root}/"
            f"{request.post_state_root}/{request.authority_epoch_root}/"
            f"{request.effect_root}/{request.sequence}/{exact_anf.anf_root}/"
            f"{exact_atom.atom_root}"
        ),
    )


def _response_root(request: K02PublicationRequestV1, fingerprint_root: str) -> str:
    return cast(
        str,
        tagged_digest(
            f"k02/response/v1/{request.commit_id}/{fingerprint_root}/{request.post_state_root}"
        ),
    )


def _next_head_root(state: K02PortStateV1, request: K02PublicationRequestV1) -> str:
    return cast(
        str,
        tagged_digest(
            "k02/head/v1/"
            f"{state.head_root}/{request.commit_id}/{request.post_state_root}/"
            f"{request.authority_epoch_root}/{request.effect_root}/{request.sequence}"
        ),
    )


def _reject(code: K02RejectCodeV1, *path: str) -> K02RejectV1:
    return K02RejectV1(code=code, path=tuple(path))


def publish_v1(port: object, state: object, request: object) -> K02ResultV1:
    """Publish one verified request through the singleton capability only."""

    if type(port) is not K02CommitPortV1 or port is not _UNIQUE_COMMIT_PORT_V1:
        return _reject(K02RejectCodeV1.WRONG_CAPABILITY, "port")
    if type(state) is not K02PortStateV1:
        return _reject(K02RejectCodeV1.WRONG_STATE, "state")
    if type(request) is not K02PublicationRequestV1:
        return _reject(K02RejectCodeV1.WRONG_REQUEST, "request")
    exact_state = state
    exact_request = request
    try:
        exact_state.__post_init__()
        exact_request.__post_init__()
    except (
        AttributeError,
        K02Error,
        TypeError,
        ValueError,
        ArithmeticError,
        OverflowError,
    ):
        return _reject(K02RejectCodeV1.WRONG_REQUEST, "typed_fields")
    if not d08.is_verified_combined_anf_accept_v1(exact_request.anf_accept):
        return _reject(K02RejectCodeV1.ANF_WITNESS_REJECTED, "anf_accept")
    fingerprint_root = request_fingerprint_root_v1(exact_request)
    for record in exact_state.records:
        if record.commit_id != exact_request.commit_id:
            continue
        if record.fingerprint_root != fingerprint_root:
            return _reject(K02RejectCodeV1.COMMIT_COLLISION, "commit_id")
        return K02CommitTransitionV1(
            resolution=K02CommitResolutionV1.ALREADY_COMMITTED,
            state=exact_state,
            commit_id=record.commit_id,
            response_root=record.response_root,
        )
    if exact_request.sequence != exact_state.next_sequence:
        return _reject(K02RejectCodeV1.SEQUENCE_MISMATCH, "sequence")
    if exact_request.expected_pre_state_root != exact_state.head_root:
        return _reject(K02RejectCodeV1.STALE_HEAD, "expected_pre_state_root")
    response_root = _response_root(exact_request, fingerprint_root)
    next_record = K02CommitRecordV1(
        sequence=exact_request.sequence,
        commit_id=exact_request.commit_id,
        fingerprint_root=fingerprint_root,
        post_state_root=exact_request.post_state_root,
        response_root=response_root,
    )
    next_state = K02PortStateV1(
        head_root=_next_head_root(exact_state, exact_request),
        next_sequence=exact_state.next_sequence + 1,
        records=(*exact_state.records, next_record),
    )
    return K02CommitTransitionV1(
        resolution=K02CommitResolutionV1.NEWLY_COMMITTED,
        state=next_state,
        commit_id=exact_request.commit_id,
        response_root=response_root,
    )


__all__ = [
    "K02_COMMIT_PORT_SCHEMA_V1",
    "K02_UNIQUE_PORT_ID_V1",
    "K02CommitPortV1",
    "K02CommitRecordV1",
    "K02CommitResolutionV1",
    "K02CommitTransitionV1",
    "K02Error",
    "K02PortStateV1",
    "K02PublicationRequestV1",
    "K02RejectCodeV1",
    "K02RejectV1",
    "K02ResultV1",
    "initial_port_state_v1",
    "publish_v1",
    "request_fingerprint_root_v1",
    "unique_commit_port_v1",
]

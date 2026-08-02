"""Canonical source-owned history encoder for FCIS M6 F02.

F02 refines one complete F01 history into a durable-layout value.  The public
``encode_history`` function is the only materialization entry point.  It emits
all row families from the same owned history and checks exact counts, order,
lineage, and layout-root recomputation before returning the layout.

This is a research adapter contract.  It does not perform a database write,
authenticate a caller, reopen a physical store, or grant runtime authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, cast

from ..state.canonical import (
    bounded_json_utf8_size,
    canonical_json_bytes,
    domain_sep_bytes,
    hex_to_bytes_fixed,
    sha256_hex,
)
from .fcis_durable_retraction import MigrationPhaseV1, derive_destination_idempotency_root
from .fcis_m6_f01_history_atom import (
    FCIS_M6_F01_MAX_ATOM_BYTES_V1,
    F01HistoryAtomV1,
    F01HistoryNullifierV1,
    F01HistoryOutboxRecordV1,
    decode_history_atom_v1,
    encode_history_atom_v1,
)

FCIS_M6_F02_HISTORY_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/f02/authorized-history/v1"
FCIS_M6_F02_LAYOUT_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/f02/durable-layout/v1"
FCIS_M6_F02_MAX_ATOMS_V1: Final[int] = 128
FCIS_M6_F02_MAX_AUTHORITY_EPOCHS_V1: Final[int] = 129
FCIS_M6_F02_MAX_ACKS_V1: Final[int] = 8_192
FCIS_M6_F02_MAX_TEXT_BYTES_V1: Final[int] = 512 * 1024
FCIS_M6_F02_MAX_LAYOUT_BYTES_V1: Final[int] = 8 * 1024 * 1024
FCIS_M6_F02_MAX_WRITERS_PER_EPOCH_V1: Final[int] = 8

_HEX_DIGITS: Final[frozenset[str]] = frozenset("0123456789abcdef")


class F02HistoryEncoderError(ValueError):
    """Raised when an F02 history or durable layout is malformed."""


class F02EvidenceKindV1(Enum):
    """Closed evidence rows emitted for every publication atom."""

    ANF = "anf"
    PROOF_CONTEXT = "proof_context"
    RESPONSE = "response"
    RECEIPT = "receipt"
    DECISION = "decision"
    BUNDLE = "bundle"
    REPLAY = "replay"
    OUTBOX = "outbox"


_EVIDENCE_ORDER: Final[tuple[F02EvidenceKindV1, ...]] = (
    F02EvidenceKindV1.ANF,
    F02EvidenceKindV1.PROOF_CONTEXT,
    F02EvidenceKindV1.RESPONSE,
    F02EvidenceKindV1.RECEIPT,
    F02EvidenceKindV1.DECISION,
    F02EvidenceKindV1.BUNDLE,
    F02EvidenceKindV1.REPLAY,
    F02EvidenceKindV1.OUTBOX,
)


def _root(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value != value.lower()
        or any(character not in _HEX_DIGITS for character in value[2:])
    ):
        raise F02HistoryEncoderError(f"{name} must be a lowercase 0x digest")
    try:
        hex_to_bytes_fixed(value, nbytes=32, name=name)
    except (TypeError, ValueError) as exc:
        raise F02HistoryEncoderError(f"{name} must be a 32-byte digest") from exc
    return value


def _text(value: object, name: str, *, maximum_bytes: int = FCIS_M6_F02_MAX_TEXT_BYTES_V1) -> str:
    if type(value) is not str or not value:
        raise F02HistoryEncoderError(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise F02HistoryEncoderError(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise F02HistoryEncoderError(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise F02HistoryEncoderError(f"{name} contains a control character")
    return value


def _u32(value: object, name: str, *, positive: bool = False) -> int:
    minimum = 1 if positive else 0
    if type(value) is not int or value < minimum or value >= (1 << 32):
        raise F02HistoryEncoderError(f"{name} is outside its closed u32 domain")
    return value


def _hash_projection(domain: str, value: object) -> str:
    try:
        encoded = canonical_json_bytes(value)
    except (TypeError, ValueError) as exc:
        raise F02HistoryEncoderError(f"{domain} projection is not canonical") from exc
    return cast(str, sha256_hex(domain_sep_bytes(domain, version=1) + encoded))


@dataclass(frozen=True, slots=True)
class F02AuthorityEpochV1:
    """One ordered authority header row."""

    epoch_index: int
    phase: MigrationPhaseV1
    authority_state_root: str
    allowed_writer_roots: tuple[str, ...]
    transition_root: str

    def __post_init__(self) -> None:
        _u32(self.epoch_index, "authority.epoch_index")
        if type(self.phase) is not MigrationPhaseV1:
            raise F02HistoryEncoderError("authority phase has the wrong exact type")
        _root(self.authority_state_root, "authority.authority_state_root")
        _root(self.transition_root, "authority.transition_root")
        if type(self.allowed_writer_roots) is not tuple:
            raise F02HistoryEncoderError("authority writers must be an exact tuple")
        if len(self.allowed_writer_roots) > FCIS_M6_F02_MAX_WRITERS_PER_EPOCH_V1:
            raise F02HistoryEncoderError("authority writers exceed their bound")
        for writer in self.allowed_writer_roots:
            _root(writer, "authority.allowed_writer_root")
        if tuple(sorted(self.allowed_writer_roots)) != self.allowed_writer_roots:
            raise F02HistoryEncoderError("authority writers must be ordered")
        if len(set(self.allowed_writer_roots)) != len(self.allowed_writer_roots):
            raise F02HistoryEncoderError("authority writers must be unique")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "epoch_index": self.epoch_index,
            "phase": self.phase.value,
            "authority_state_root": self.authority_state_root,
            "allowed_writer_roots": list(self.allowed_writer_roots),
            "transition_root": self.transition_root,
        }


@dataclass(frozen=True, slots=True)
class F02AckRowV1:
    """Durable acknowledgment row with effect provenance."""

    effect_id: str
    commit_id: str
    destination: str
    payload_root: str
    destination_receipt_root: str
    adapter_profile_root: str
    idempotency_root: str
    response_root: str

    def __post_init__(self) -> None:
        for name in (
            "effect_id",
            "commit_id",
            "payload_root",
            "destination_receipt_root",
            "adapter_profile_root",
            "idempotency_root",
            "response_root",
        ):
            _root(object.__getattribute__(self, name), f"ack.{name}")
        _text(self.destination, "ack.destination")
        expected = derive_destination_idempotency_root(self.effect_id[2:])
        if self.idempotency_root != f"0x{expected}":
            raise F02HistoryEncoderError("ack idempotency root does not rederive")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "effect_id": self.effect_id,
            "commit_id": self.commit_id,
            "destination": self.destination,
            "payload_root": self.payload_root,
            "destination_receipt_root": self.destination_receipt_root,
            "adapter_profile_root": self.adapter_profile_root,
            "idempotency_root": self.idempotency_root,
            "response_root": self.response_root,
        }


def _validate_authority_epochs(epochs: tuple[F02AuthorityEpochV1, ...]) -> None:
    if type(epochs) is not tuple or not epochs:
        raise F02HistoryEncoderError("authority epochs must be a nonempty tuple")
    if len(epochs) > FCIS_M6_F02_MAX_AUTHORITY_EPOCHS_V1:
        raise F02HistoryEncoderError("authority epochs exceed their bound")
    for index, epoch in enumerate(epochs):
        if type(epoch) is not F02AuthorityEpochV1:
            raise F02HistoryEncoderError("authority epoch has the wrong exact type")
        epoch.__post_init__()
        if epoch.epoch_index != index:
            raise F02HistoryEncoderError("authority epoch indices must be contiguous")


def _all_effects(
    atoms: tuple[F01HistoryAtomV1, ...],
) -> dict[str, tuple[F01HistoryAtomV1, F01HistoryOutboxRecordV1]]:
    effects: dict[str, tuple[F01HistoryAtomV1, F01HistoryOutboxRecordV1]] = {}
    for atom in atoms:
        for record in atom.outbox:
            if record.effect_id in effects:
                raise F02HistoryEncoderError("effect identities must be globally unique")
            effects[record.effect_id] = (atom, record)
    return effects


def _validate_atoms(
    atoms: tuple[F01HistoryAtomV1, ...],
    *,
    genesis_state_root: str,
    deployment_config_root: str,
    verifier_profile_root: str,
    authority_epochs: tuple[F02AuthorityEpochV1, ...],
) -> None:
    if type(atoms) is not tuple:
        raise F02HistoryEncoderError("atoms must be an exact tuple")
    if len(atoms) > FCIS_M6_F02_MAX_ATOMS_V1:
        raise F02HistoryEncoderError("atoms exceed their bound")
    expected_pre = genesis_state_root
    commit_ids: set[str] = set()
    nullifiers: set[str] = set()
    for index, atom in enumerate(atoms, start=1):
        if type(atom) is not F01HistoryAtomV1:
            raise F02HistoryEncoderError("atom has the wrong exact type")
        atom.__post_init__()
        if atom.sequence != index:
            raise F02HistoryEncoderError("atom sequences must be contiguous")
        if atom.expected_pre_state_root != expected_pre:
            raise F02HistoryEncoderError("atoms do not form a state chain")
        if atom.commit_id in commit_ids:
            raise F02HistoryEncoderError("commit IDs must be unique")
        if atom.nullifier.nullifier_root in nullifiers:
            raise F02HistoryEncoderError("nullifier roots must be unique")
        if atom.deployment_config_root != deployment_config_root:
            raise F02HistoryEncoderError("atom deployment context is crossed")
        if atom.verifier_profile_root != verifier_profile_root:
            raise F02HistoryEncoderError("atom verifier context is crossed")
        if atom.authority_epoch_index >= len(authority_epochs):
            raise F02HistoryEncoderError("atom names an unknown authority epoch")
        authority = authority_epochs[atom.authority_epoch_index]
        if atom.authority_state_root != authority.authority_state_root:
            raise F02HistoryEncoderError("atom authority root is crossed")
        if atom.writer_profile_root not in authority.allowed_writer_roots:
            raise F02HistoryEncoderError("atom uses a writer outside its authority row")
        commit_ids.add(atom.commit_id)
        nullifiers.add(atom.nullifier.nullifier_root)
        expected_pre = atom.post_state_root
    _all_effects(atoms)


@dataclass(frozen=True, slots=True)
class F02AuthorizedHistoryV1:
    """Complete source value consumed by the sole F02 encoder."""

    genesis_state_root: str
    deployment_config_root: str
    verifier_profile_root: str
    authority_epochs: tuple[F02AuthorityEpochV1, ...]
    atoms: tuple[F01HistoryAtomV1, ...]
    acks: tuple[F02AckRowV1, ...]

    def __post_init__(self) -> None:
        _root(self.genesis_state_root, "genesis_state_root")
        _root(self.deployment_config_root, "deployment_config_root")
        _root(self.verifier_profile_root, "verifier_profile_root")
        _validate_authority_epochs(self.authority_epochs)
        _validate_atoms(
            self.atoms,
            genesis_state_root=self.genesis_state_root,
            deployment_config_root=self.deployment_config_root,
            verifier_profile_root=self.verifier_profile_root,
            authority_epochs=self.authority_epochs,
        )
        if type(self.acks) is not tuple:
            raise F02HistoryEncoderError("acks must be an exact tuple")
        if len(self.acks) > FCIS_M6_F02_MAX_ACKS_V1:
            raise F02HistoryEncoderError("acks exceed their bound")
        if tuple(sorted(self.acks, key=lambda row: row.effect_id)) != self.acks:
            raise F02HistoryEncoderError("acks must be ordered by effect ID")
        effect_map = _all_effects(self.atoms)
        seen: set[str] = set()
        for ack in self.acks:
            if type(ack) is not F02AckRowV1:
                raise F02HistoryEncoderError("ack has the wrong exact type")
            ack.__post_init__()
            if ack.effect_id in seen:
                raise F02HistoryEncoderError("ack effect IDs must be unique")
            effect = effect_map.get(ack.effect_id)
            if effect is None:
                raise F02HistoryEncoderError("ack has no committed outbox ancestor")
            atom, record = effect
            if (
                ack.commit_id != atom.commit_id
                or ack.destination != record.destination
                or ack.payload_root != record.payload_root
                or ack.adapter_profile_root != record.adapter_profile_root
                or ack.response_root != atom.response_root
            ):
                raise F02HistoryEncoderError("ack provenance is crossed")
            seen.add(ack.effect_id)

    @property
    def current_state_root(self) -> str:
        if not self.atoms:
            return self.genesis_state_root
        return self.atoms[-1].post_state_root

    @property
    def current_authority(self) -> F02AuthorityEpochV1:
        return self.authority_epochs[-1]


@dataclass(frozen=True, slots=True)
class F02StateHeaderV1:
    """Singleton state/header row emitted by ``encode_history``."""

    genesis_state_root: str
    current_state_root: str
    deployment_config_root: str
    verifier_profile_root: str
    current_authority_state_root: str
    current_authority_epoch_index: int
    history_count: int
    evidence_count: int
    nullifier_count: int
    outbox_count: int
    authority_count: int
    ack_count: int

    def __post_init__(self) -> None:
        for name in (
            "genesis_state_root",
            "current_state_root",
            "deployment_config_root",
            "verifier_profile_root",
            "current_authority_state_root",
        ):
            _root(object.__getattribute__(self, name), f"header.{name}")
        _u32(self.current_authority_epoch_index, "header.current_authority_epoch_index")
        for name in (
            "history_count",
            "evidence_count",
            "nullifier_count",
            "outbox_count",
            "authority_count",
            "ack_count",
        ):
            _u32(object.__getattribute__(self, name), f"header.{name}")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "genesis_state_root": self.genesis_state_root,
            "current_state_root": self.current_state_root,
            "deployment_config_root": self.deployment_config_root,
            "verifier_profile_root": self.verifier_profile_root,
            "current_authority_state_root": self.current_authority_state_root,
            "current_authority_epoch_index": self.current_authority_epoch_index,
            "history_count": self.history_count,
            "evidence_count": self.evidence_count,
            "nullifier_count": self.nullifier_count,
            "outbox_count": self.outbox_count,
            "authority_count": self.authority_count,
            "ack_count": self.ack_count,
        }


@dataclass(frozen=True, slots=True)
class F02HistoryRowV1:
    """Complete canonical F01 atom bytes plus its derived root."""

    sequence: int
    atom_root: str
    atom_bytes_utf8: str

    def __post_init__(self) -> None:
        _u32(self.sequence, "history.sequence", positive=True)
        _root(self.atom_root, "history.atom_root")
        _text(
            self.atom_bytes_utf8,
            "history.atom_bytes_utf8",
            maximum_bytes=FCIS_M6_F01_MAX_ATOM_BYTES_V1,
        )
        decoded = decode_history_atom_v1(self.atom_bytes_utf8.encode("utf-8"))
        if type(decoded) is not F01HistoryAtomV1:
            raise F02HistoryEncoderError("history row does not contain a complete F01 atom")
        if decoded.sequence != self.sequence or decoded.atom_root != self.atom_root:
            raise F02HistoryEncoderError("history row root or sequence is crossed")

    @property
    def atom(self) -> F01HistoryAtomV1:
        decoded = decode_history_atom_v1(self.atom_bytes_utf8.encode("utf-8"))
        if type(decoded) is not F01HistoryAtomV1:
            raise F02HistoryEncoderError("history row atom is no longer complete")
        return decoded

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "sequence": self.sequence,
            "atom_root": self.atom_root,
            "atom_bytes_utf8": self.atom_bytes_utf8,
        }


@dataclass(frozen=True, slots=True)
class F02EvidenceRowV1:
    sequence: int
    commit_id: str
    kind: F02EvidenceKindV1
    value_root: str

    def __post_init__(self) -> None:
        _u32(self.sequence, "evidence.sequence", positive=True)
        _root(self.commit_id, "evidence.commit_id")
        if type(self.kind) is not F02EvidenceKindV1:
            raise F02HistoryEncoderError("evidence kind has the wrong exact type")
        _root(self.value_root, "evidence.value_root")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "sequence": self.sequence,
            "commit_id": self.commit_id,
            "kind": self.kind.value,
            "value_root": self.value_root,
        }


@dataclass(frozen=True, slots=True)
class F02NullifierRowV1:
    sequence: int
    commit_id: str
    nullifier: F01HistoryNullifierV1

    def __post_init__(self) -> None:
        _u32(self.sequence, "nullifier.sequence", positive=True)
        _root(self.commit_id, "nullifier.commit_id")
        if type(self.nullifier) is not F01HistoryNullifierV1:
            raise F02HistoryEncoderError("nullifier row has the wrong exact type")
        self.nullifier.__post_init__()

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "sequence": self.sequence,
            "commit_id": self.commit_id,
            "nullifier": self.nullifier.to_wire(),
        }


@dataclass(frozen=True, slots=True)
class F02OutboxRowV1:
    sequence: int
    commit_id: str
    record: F01HistoryOutboxRecordV1

    def __post_init__(self) -> None:
        _u32(self.sequence, "outbox.sequence", positive=True)
        _root(self.commit_id, "outbox.commit_id")
        if type(self.record) is not F01HistoryOutboxRecordV1:
            raise F02HistoryEncoderError("outbox row has the wrong exact type")
        self.record.__post_init__()

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "sequence": self.sequence,
            "commit_id": self.commit_id,
            "record": self.record.to_wire(),
        }


def _outbox_root(atom: F01HistoryAtomV1) -> str:
    return _hash_projection(
        "zenodex/fcis/m6/f02/outbox-projection",
        [record.to_wire() for record in atom.outbox],
    )


def _history_rows(atoms: tuple[F01HistoryAtomV1, ...]) -> tuple[F02HistoryRowV1, ...]:
    return tuple(
        F02HistoryRowV1(
            sequence=atom.sequence,
            atom_root=atom.atom_root,
            atom_bytes_utf8=encode_history_atom_v1(atom).decode("utf-8"),
        )
        for atom in atoms
    )


def _evidence_rows(atoms: tuple[F01HistoryAtomV1, ...]) -> tuple[F02EvidenceRowV1, ...]:
    rows: list[F02EvidenceRowV1] = []
    for atom in atoms:
        roots = (
            (F02EvidenceKindV1.ANF, atom.anf_root),
            (F02EvidenceKindV1.PROOF_CONTEXT, atom.proof_context_root),
            (F02EvidenceKindV1.RESPONSE, atom.response_root),
            (F02EvidenceKindV1.RECEIPT, atom.receipt_root),
            (F02EvidenceKindV1.DECISION, atom.decision_root),
            (F02EvidenceKindV1.BUNDLE, atom.bundle_root),
            (F02EvidenceKindV1.REPLAY, atom.replay_root),
            (F02EvidenceKindV1.OUTBOX, _outbox_root(atom)),
        )
        rows.extend(
            F02EvidenceRowV1(
                sequence=atom.sequence,
                commit_id=atom.commit_id,
                kind=kind,
                value_root=value_root,
            )
            for kind, value_root in roots
        )
    return tuple(rows)


def _nullifier_rows(atoms: tuple[F01HistoryAtomV1, ...]) -> tuple[F02NullifierRowV1, ...]:
    return tuple(
        F02NullifierRowV1(
            sequence=atom.sequence,
            commit_id=atom.commit_id,
            nullifier=atom.nullifier,
        )
        for atom in atoms
    )


def _outbox_rows(atoms: tuple[F01HistoryAtomV1, ...]) -> tuple[F02OutboxRowV1, ...]:
    return tuple(
        F02OutboxRowV1(
            sequence=atom.sequence,
            commit_id=atom.commit_id,
            record=record,
        )
        for atom in atoms
        for record in atom.outbox
    )


def _validate_row_order(
    history_rows: tuple[F02HistoryRowV1, ...],
    evidence_rows: tuple[F02EvidenceRowV1, ...],
    nullifier_rows: tuple[F02NullifierRowV1, ...],
    outbox_rows: tuple[F02OutboxRowV1, ...],
) -> None:
    if tuple(row.sequence for row in history_rows) != tuple(range(1, len(history_rows) + 1)):
        raise F02HistoryEncoderError("history rows must be sequence ordered")
    expected_evidence_keys = tuple(
        (row.sequence, index) for row in history_rows for index in range(len(_EVIDENCE_ORDER))
    )
    actual_evidence_keys = tuple(
        (row.sequence, _EVIDENCE_ORDER.index(row.kind)) for row in evidence_rows
    )
    if actual_evidence_keys != expected_evidence_keys:
        raise F02HistoryEncoderError("evidence rows must use exact atom/kind order")
    if tuple(row.sequence for row in nullifier_rows) != tuple(range(1, len(history_rows) + 1)):
        raise F02HistoryEncoderError("nullifier rows must be sequence ordered")
    actual_outbox_keys = tuple((row.sequence, row.record.ordinal) for row in outbox_rows)
    expected_outbox_keys = tuple(
        (atom.sequence, record.ordinal)
        for atom in (row.atom for row in history_rows)
        for record in atom.outbox
    )
    if actual_outbox_keys != expected_outbox_keys:
        raise F02HistoryEncoderError("outbox rows must use exact atom/ordinal order")


def _layout_projection(
    header: F02StateHeaderV1,
    authority_rows: tuple[F02AuthorityEpochV1, ...],
    history_rows: tuple[F02HistoryRowV1, ...],
    evidence_rows: tuple[F02EvidenceRowV1, ...],
    nullifier_rows: tuple[F02NullifierRowV1, ...],
    outbox_rows: tuple[F02OutboxRowV1, ...],
    ack_rows: tuple[F02AckRowV1, ...],
) -> dict[str, object]:
    return {
        "header": header.to_wire(),
        "authority_rows": [row.to_wire() for row in authority_rows],
        "history_rows": [row.to_wire() for row in history_rows],
        "evidence_rows": [row.to_wire() for row in evidence_rows],
        "nullifier_rows": [row.to_wire() for row in nullifier_rows],
        "outbox_rows": [row.to_wire() for row in outbox_rows],
        "ack_rows": [row.to_wire() for row in ack_rows],
    }


@dataclass(frozen=True, slots=True)
class F02DurableLayoutV1:
    """Complete canonical layout produced by the F02 encoder."""

    header: F02StateHeaderV1
    authority_rows: tuple[F02AuthorityEpochV1, ...]
    history_rows: tuple[F02HistoryRowV1, ...]
    evidence_rows: tuple[F02EvidenceRowV1, ...]
    nullifier_rows: tuple[F02NullifierRowV1, ...]
    outbox_rows: tuple[F02OutboxRowV1, ...]
    ack_rows: tuple[F02AckRowV1, ...]
    layout_root: str

    def __post_init__(self) -> None:
        if type(self.header) is not F02StateHeaderV1:
            raise F02HistoryEncoderError("layout header has the wrong exact type")
        self.header.__post_init__()
        collections = (
            ("authority_rows", self.authority_rows, F02AuthorityEpochV1),
            ("history_rows", self.history_rows, F02HistoryRowV1),
            ("evidence_rows", self.evidence_rows, F02EvidenceRowV1),
            ("nullifier_rows", self.nullifier_rows, F02NullifierRowV1),
            ("outbox_rows", self.outbox_rows, F02OutboxRowV1),
            ("ack_rows", self.ack_rows, F02AckRowV1),
        )
        for name, rows, row_type in collections:
            if type(rows) is not tuple:
                raise F02HistoryEncoderError(f"{name} must be an exact tuple")
            for row in rows:
                if type(row) is not row_type:
                    raise F02HistoryEncoderError(f"{name} contains the wrong exact type")
                row.__post_init__()
        _validate_authority_epochs(self.authority_rows)
        _validate_row_order(
            self.history_rows,
            self.evidence_rows,
            self.nullifier_rows,
            self.outbox_rows,
        )
        atoms = tuple(row.atom for row in self.history_rows)
        _validate_atoms(
            atoms,
            genesis_state_root=self.header.genesis_state_root,
            deployment_config_root=self.header.deployment_config_root,
            verifier_profile_root=self.header.verifier_profile_root,
            authority_epochs=self.authority_rows,
        )
        if len(self.history_rows) != self.header.history_count:
            raise F02HistoryEncoderError("header history count differs")
        if len(self.evidence_rows) != self.header.evidence_count:
            raise F02HistoryEncoderError("header evidence count differs")
        if len(self.nullifier_rows) != self.header.nullifier_count:
            raise F02HistoryEncoderError("header nullifier count differs")
        if len(self.outbox_rows) != self.header.outbox_count:
            raise F02HistoryEncoderError("header outbox count differs")
        if len(self.authority_rows) != self.header.authority_count:
            raise F02HistoryEncoderError("header authority count differs")
        if len(self.ack_rows) != self.header.ack_count:
            raise F02HistoryEncoderError("header ack count differs")
        if self.header.current_state_root != (
            atoms[-1].post_state_root if atoms else self.header.genesis_state_root
        ):
            raise F02HistoryEncoderError("header current state root differs")
        if self.header.current_authority_state_root != self.authority_rows[-1].authority_state_root:
            raise F02HistoryEncoderError("header authority root differs")
        if self.header.current_authority_epoch_index != self.authority_rows[-1].epoch_index:
            raise F02HistoryEncoderError("header authority epoch differs")
        if tuple(sorted(self.ack_rows, key=lambda row: row.effect_id)) != self.ack_rows:
            raise F02HistoryEncoderError("layout acknowledgments must be effect ordered")
        if len({row.effect_id for row in self.ack_rows}) != len(self.ack_rows):
            raise F02HistoryEncoderError("layout acknowledgment effect IDs must be unique")
        if self.evidence_rows != _evidence_rows(atoms):
            raise F02HistoryEncoderError("evidence rows are not canonical projections")
        if self.nullifier_rows != _nullifier_rows(atoms):
            raise F02HistoryEncoderError("nullifier rows are not canonical projections")
        if self.outbox_rows != _outbox_rows(atoms):
            raise F02HistoryEncoderError("outbox rows are not canonical projections")
        effect_map = _all_effects(atoms)
        for ack in self.ack_rows:
            effect = effect_map.get(ack.effect_id)
            if effect is None:
                raise F02HistoryEncoderError("layout ack has no outbox ancestor")
            atom, record = effect
            if (
                ack.commit_id != atom.commit_id
                or ack.destination != record.destination
                or ack.payload_root != record.payload_root
                or ack.adapter_profile_root != record.adapter_profile_root
                or ack.response_root != atom.response_root
            ):
                raise F02HistoryEncoderError("layout ack provenance is crossed")
        _root(self.layout_root, "layout_root")
        expected_root = _hash_projection(
            "zenodex/fcis/m6/f02/layout-root",
            _layout_projection(
                self.header,
                self.authority_rows,
                self.history_rows,
                self.evidence_rows,
                self.nullifier_rows,
                self.outbox_rows,
                self.ack_rows,
            ),
        )
        if self.layout_root != expected_root:
            raise F02HistoryEncoderError("layout root does not rederive")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        value = _layout_projection(
            self.header,
            self.authority_rows,
            self.history_rows,
            self.evidence_rows,
            self.nullifier_rows,
            self.outbox_rows,
            self.ack_rows,
        )
        value["layout_root"] = self.layout_root
        return {"schema": FCIS_M6_F02_LAYOUT_SCHEMA_V1, "value": value}


def encode_history(history: object) -> F02DurableLayoutV1:
    """Materialize every authoritative row from one exact complete history."""

    if type(history) is not F02AuthorizedHistoryV1:
        raise F02HistoryEncoderError("encode_history requires an exact F02 history")
    value = history
    value.__post_init__()
    authority_rows = value.authority_epochs
    history_rows = _history_rows(value.atoms)
    evidence_rows = _evidence_rows(value.atoms)
    nullifier_rows = _nullifier_rows(value.atoms)
    outbox_rows = _outbox_rows(value.atoms)
    ack_rows = value.acks
    header = F02StateHeaderV1(
        genesis_state_root=value.genesis_state_root,
        current_state_root=value.current_state_root,
        deployment_config_root=value.deployment_config_root,
        verifier_profile_root=value.verifier_profile_root,
        current_authority_state_root=value.current_authority.authority_state_root,
        current_authority_epoch_index=value.current_authority.epoch_index,
        history_count=len(history_rows),
        evidence_count=len(evidence_rows),
        nullifier_count=len(nullifier_rows),
        outbox_count=len(outbox_rows),
        authority_count=len(authority_rows),
        ack_count=len(ack_rows),
    )
    projection = _layout_projection(
        header,
        authority_rows,
        history_rows,
        evidence_rows,
        nullifier_rows,
        outbox_rows,
        ack_rows,
    )
    return F02DurableLayoutV1(
        header=header,
        authority_rows=authority_rows,
        history_rows=history_rows,
        evidence_rows=evidence_rows,
        nullifier_rows=nullifier_rows,
        outbox_rows=outbox_rows,
        ack_rows=ack_rows,
        layout_root=_hash_projection("zenodex/fcis/m6/f02/layout-root", projection),
    )


def encode_layout_v1(layout: object) -> bytes:
    """Encode one already-produced layout for hashing/replay evidence."""

    if type(layout) is not F02DurableLayoutV1:
        raise F02HistoryEncoderError("layout codec requires an exact F02 layout")
    payload = layout.to_wire()
    try:
        bounded_json_utf8_size(
            payload,
            max_bytes=FCIS_M6_F02_MAX_LAYOUT_BYTES_V1,
            max_depth=12,
            max_items=100_000,
        )
        return cast(bytes, canonical_json_bytes(payload))
    except (TypeError, ValueError) as exc:
        raise F02HistoryEncoderError("layout exceeds canonical codec bounds") from exc


__all__ = (
    "FCIS_M6_F02_HISTORY_SCHEMA_V1",
    "FCIS_M6_F02_LAYOUT_SCHEMA_V1",
    "F02AckRowV1",
    "F02AuthorityEpochV1",
    "F02AuthorizedHistoryV1",
    "F02DurableLayoutV1",
    "F02EvidenceKindV1",
    "F02EvidenceRowV1",
    "F02HistoryEncoderError",
    "F02HistoryRowV1",
    "F02NullifierRowV1",
    "F02OutboxRowV1",
    "F02StateHeaderV1",
    "encode_history",
    "encode_layout_v1",
)

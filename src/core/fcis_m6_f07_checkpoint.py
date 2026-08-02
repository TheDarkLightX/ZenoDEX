"""Checkpoint and full-tip compaction semantics for the unmounted FCIS M6 lane.

F07 makes history truncation explicit.  The only compaction operation admitted
by this research contract removes a complete history at its current tip and
replaces it with a checkpoint certificate that acts as a new authenticated
genesis-like object.  A partial-prefix truncation is rejected until a later
schema can carry the retained suffix's sequence and state ancestry.

The certificate is source-derived from an F04 fixed point and an accepted F05
genesis relation.  Its constructor is an ordinary value constructor; the
``validate_f07_checkpoint_v1`` relation must be used at the consumption
boundary.  This module does not authorize a datastore deletion, authenticate a
snapshot signer, or mount a runtime compaction path.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .fcis_m6_f01_history_atom import (
    FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1,
    F01HistoryOutboxRecordV1,
)
from .fcis_m6_f02_history_encoder import (
    FCIS_M6_F02_HISTORY_SCHEMA_V1,
    F02AuthorizedHistoryV1,
    F02DurableLayoutV1,
    encode_layout_v1,
)
from .fcis_m6_f04_fixed_point import (
    F04FixedPointSuccessV1,
)
from .fcis_m6_f05_authenticated_genesis import (
    F05GenesisAcceptanceV1,
)

FCIS_M6_F07_CHECKPOINT_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/f07/checkpoint/v1"
FCIS_M6_F07_COMPACTED_SNAPSHOT_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/f07/compacted-snapshot/v1"
FCIS_M6_F07_MAX_U32_V1: Final[int] = (1 << 32) - 1
_ROOT_HEX: Final[frozenset[str]] = frozenset("0123456789abcdef")


class F07CheckpointCodeV1(Enum):
    """Stable fail-closed outcomes for checkpoint construction and use."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    SOURCE_REJECTED = "source_rejected"
    GENESIS_REJECTED = "genesis_rejected"
    GENESIS_MISMATCH = "genesis_mismatch"
    EMPTY_HISTORY = "empty_history"
    INVALID_CHECKPOINT = "invalid_checkpoint"
    UNSUPPORTED_PROOF = "unsupported_proof"
    CHECKPOINT_MISMATCH = "checkpoint_mismatch"
    PENDING_OUTBOX_MISMATCH = "pending_outbox_mismatch"


class F07ProofKindV1(Enum):
    """Closed proof modes; only deterministic replay is admitted in F07-v1."""

    REPLAY = "replay"
    APPROVED_SNAPSHOT = "approved_snapshot"


class F07CheckpointError(ValueError):
    """Raised when a checkpoint value is outside its closed schema."""


def _root(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value != value.lower()
        or any(character not in _ROOT_HEX for character in value[2:])
    ):
        raise F07CheckpointError(f"{name} must be a lowercase 32-byte root")
    return value


def _u32(value: object, name: str, *, positive: bool = False) -> int:
    minimum = 1 if positive else 0
    if type(value) is not int or value < minimum or value > FCIS_M6_F07_MAX_U32_V1:
        raise F07CheckpointError(f"{name} is outside its closed u32 domain")
    return value


def _derive_root(domain: str, payload: dict[str, object]) -> str:
    return cast(
        str,
        sha256_hex(domain_sep_bytes(domain, version=1) + canonical_json_bytes(payload)),
    )


def _pending_wire(rows: tuple["F07PendingOutboxV1", ...]) -> list[dict[str, object]]:
    return [row.to_wire() for row in rows]


@dataclass(frozen=True, slots=True)
class F07PendingOutboxV1:
    """Complete identity needed to deliver an effect after history compaction."""

    sequence: int
    commit_id: str
    writer_profile_root: str
    record: F01HistoryOutboxRecordV1

    def __post_init__(self) -> None:
        _u32(self.sequence, "pending_outbox.sequence", positive=True)
        _root(self.commit_id, "pending_outbox.commit_id")
        _root(self.writer_profile_root, "pending_outbox.writer_profile_root")
        if type(self.record) is not F01HistoryOutboxRecordV1:
            raise F07CheckpointError("pending outbox record has the wrong exact type")
        self.record.__post_init__()
        self.record.validate_for_atom(
            commit_id=self.commit_id,
            writer_profile_root=self.writer_profile_root,
        )

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "sequence": self.sequence,
            "commit_id": self.commit_id,
            "writer_profile_root": self.writer_profile_root,
            "record": self.record.to_wire(),
        }


def _checkpoint_payload(value: "F07CheckpointV1") -> dict[str, object]:
    return {
        "schema": FCIS_M6_F07_CHECKPOINT_SCHEMA_V1,
        "checkpoint_sequence": value.checkpoint_sequence,
        "prior_layout_root": value.prior_layout_root,
        "prior_history_root": value.prior_history_root,
        "checkpoint_state_root": value.checkpoint_state_root,
        "deployment_config_root": value.deployment_config_root,
        "verifier_profile_root": value.verifier_profile_root,
        "genesis_admission_root": value.genesis_admission_root,
        "nullifier_accumulator_root": value.nullifier_accumulator_root,
        "authority_epoch_summary_root": value.authority_epoch_summary_root,
        "outbox_accumulator_root": value.outbox_accumulator_root,
        "pending_outbox": _pending_wire(value.pending_outbox),
        "proof_kind": value.proof_kind.value,
        "proof_root": value.proof_root,
    }


@dataclass(frozen=True, slots=True)
class F07CheckpointV1:
    """New authenticated-genesis-like value for a complete tip checkpoint."""

    checkpoint_sequence: int
    prior_layout_root: str
    prior_history_root: str
    checkpoint_state_root: str
    deployment_config_root: str
    verifier_profile_root: str
    genesis_admission_root: str
    nullifier_accumulator_root: str
    authority_epoch_summary_root: str
    outbox_accumulator_root: str
    pending_outbox: tuple[F07PendingOutboxV1, ...]
    proof_kind: F07ProofKindV1
    proof_root: str
    checkpoint_genesis_root: str

    def __post_init__(self) -> None:
        _u32(self.checkpoint_sequence, "checkpoint_sequence", positive=True)
        for name in (
            "prior_layout_root",
            "prior_history_root",
            "checkpoint_state_root",
            "deployment_config_root",
            "verifier_profile_root",
            "genesis_admission_root",
            "nullifier_accumulator_root",
            "authority_epoch_summary_root",
            "outbox_accumulator_root",
            "proof_root",
            "checkpoint_genesis_root",
        ):
            _root(object.__getattribute__(self, name), name)
        if type(self.pending_outbox) is not tuple:
            raise F07CheckpointError("pending_outbox must be an exact tuple")
        for row in self.pending_outbox:
            if type(row) is not F07PendingOutboxV1:
                raise F07CheckpointError("pending_outbox contains the wrong exact type")
            row.__post_init__()
            if row.sequence > self.checkpoint_sequence:
                raise F07CheckpointError("pending outbox is outside the checkpoint history")
        if tuple(sorted(self.pending_outbox, key=lambda row: row.record.effect_id)) != (
            self.pending_outbox
        ):
            raise F07CheckpointError("pending_outbox must be ordered by effect ID")
        effect_ids = tuple(row.record.effect_id for row in self.pending_outbox)
        if len(effect_ids) != len(set(effect_ids)):
            raise F07CheckpointError("pending outbox effect IDs must be unique")
        if type(self.proof_kind) is not F07ProofKindV1:
            raise F07CheckpointError("proof_kind has the wrong exact type")
        expected = _derive_root(
            "zenodex/fcis/m6/f07/checkpoint-genesis",
            _checkpoint_payload(self),
        )
        if self.checkpoint_genesis_root != expected:
            raise F07CheckpointError("checkpoint_genesis_root does not rederive")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            **_checkpoint_payload(self),
            "checkpoint_genesis_root": self.checkpoint_genesis_root,
        }


def _compacted_snapshot_root(checkpoint: F07CheckpointV1) -> str:
    return _derive_root(
        "zenodex/fcis/m6/f07/compacted-snapshot",
        {
            "schema": FCIS_M6_F07_COMPACTED_SNAPSHOT_SCHEMA_V1,
            "checkpoint_genesis_root": checkpoint.checkpoint_genesis_root,
            "checkpoint_state_root": checkpoint.checkpoint_state_root,
            "pending_outbox": _pending_wire(checkpoint.pending_outbox),
        },
    )


@dataclass(frozen=True, slots=True)
class F07CompactedSnapshotV1:
    """Exact replacement snapshot exposed by the value-level compaction model."""

    checkpoint: F07CheckpointV1
    snapshot_root: str

    def __post_init__(self) -> None:
        if type(self.checkpoint) is not F07CheckpointV1:
            raise F07CheckpointError("compacted snapshot checkpoint has the wrong exact type")
        self.checkpoint.__post_init__()
        _root(self.snapshot_root, "snapshot_root")
        if self.snapshot_root != _compacted_snapshot_root(self.checkpoint):
            raise F07CheckpointError("compacted snapshot root does not rederive")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": FCIS_M6_F07_COMPACTED_SNAPSHOT_SCHEMA_V1,
            "checkpoint": self.checkpoint.to_wire(),
            "snapshot_root": self.snapshot_root,
        }


@dataclass(frozen=True, slots=True)
class F07CheckpointAcceptanceV1:
    """Source-checked compaction result; it grants no datastore authority."""

    checkpoint: F07CheckpointV1
    compacted_snapshot: F07CompactedSnapshotV1
    removed_history_count: int
    removed_nullifier_count: int
    removed_outbox_count: int

    def __post_init__(self) -> None:
        if type(self.checkpoint) is not F07CheckpointV1:
            raise F07CheckpointError("accepted checkpoint has the wrong exact type")
        if type(self.compacted_snapshot) is not F07CompactedSnapshotV1:
            raise F07CheckpointError("accepted snapshot has the wrong exact type")
        self.checkpoint.__post_init__()
        self.compacted_snapshot.__post_init__()
        if self.compacted_snapshot.checkpoint != self.checkpoint:
            raise F07CheckpointError("accepted snapshot is crossed with checkpoint")
        _u32(self.removed_history_count, "removed_history_count", positive=True)
        _u32(self.removed_nullifier_count, "removed_nullifier_count")
        _u32(self.removed_outbox_count, "removed_outbox_count")
        if self.removed_nullifier_count != self.removed_history_count:
            raise F07CheckpointError("removed nullifier count is not bijective")
        if self.removed_outbox_count < len(self.checkpoint.pending_outbox):
            raise F07CheckpointError("removed outbox count loses pending identities")


@dataclass(frozen=True, slots=True)
class F07CheckpointRejectV1:
    """Typed failure with no replacement snapshot."""

    code: F07CheckpointCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not F07CheckpointCodeV1:
            raise F07CheckpointError("F07 code has the wrong exact type")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise F07CheckpointError("F07 path must be an exact string tuple")


F07CheckpointResultV1: TypeAlias = F07CheckpointAcceptanceV1 | F07CheckpointRejectV1


def _reject(code: F07CheckpointCodeV1, *path: str) -> F07CheckpointRejectV1:
    return F07CheckpointRejectV1(code, path)


def _history_root(history: F02AuthorizedHistoryV1) -> str:
    return _derive_root(
        "zenodex/fcis/m6/f07/prior-history",
        {
            "schema": FCIS_M6_F02_HISTORY_SCHEMA_V1,
            "genesis_state_root": history.genesis_state_root,
            "deployment_config_root": history.deployment_config_root,
            "verifier_profile_root": history.verifier_profile_root,
            "atoms": [
                {
                    "sequence": atom.sequence,
                    "atom_root": atom.atom_root,
                }
                for atom in history.atoms
            ],
        },
    )


def _nullifier_accumulator_root(layout: F02DurableLayoutV1) -> str:
    return _derive_root(
        "zenodex/fcis/m6/f07/nullifier-accumulator",
        {
            "rows": [row.to_wire() for row in layout.nullifier_rows],
        },
    )


def _authority_epoch_summary_root(layout: F02DurableLayoutV1) -> str:
    return _derive_root(
        "zenodex/fcis/m6/f07/authority-epoch-summary",
        {
            "rows": [row.to_wire() for row in layout.authority_rows],
        },
    )


def _outbox_accumulator_root(layout: F02DurableLayoutV1) -> str:
    return _derive_root(
        "zenodex/fcis/m6/f07/outbox-accumulator",
        {
            "rows": [row.to_wire() for row in layout.outbox_rows],
        },
    )


def _pending_outbox(
    history: F02AuthorizedHistoryV1,
    layout: F02DurableLayoutV1,
) -> tuple[F07PendingOutboxV1, ...]:
    acknowledged = {row.effect_id for row in history.acks}
    atom_by_sequence = {atom.sequence: atom for atom in history.atoms}
    pending: list[F07PendingOutboxV1] = []
    for row in layout.outbox_rows:
        if row.record.effect_id in acknowledged:
            continue
        atom = atom_by_sequence.get(row.sequence)
        if atom is None:
            raise F07CheckpointError("outbox row has no atom ancestor")
        pending.append(
            F07PendingOutboxV1(
                sequence=row.sequence,
                commit_id=row.commit_id,
                writer_profile_root=atom.writer_profile_root,
                record=row.record,
            )
        )
    pending.sort(key=lambda row: row.record.effect_id)
    return tuple(pending)


def _replay_proof_root(
    *,
    prior_layout_root: str,
    prior_history_root: str,
    checkpoint_state_root: str,
    nullifier_accumulator_root: str,
    authority_epoch_summary_root: str,
    outbox_accumulator_root: str,
    pending_outbox: tuple[F07PendingOutboxV1, ...],
) -> str:
    return _derive_root(
        "zenodex/fcis/m6/f07/replay-proof",
        {
            "schema": FCIS_M6_F07_CHECKPOINT_SCHEMA_V1,
            "proof_kind": F07ProofKindV1.REPLAY.value,
            "prior_layout_root": prior_layout_root,
            "prior_history_root": prior_history_root,
            "checkpoint_state_root": checkpoint_state_root,
            "nullifier_accumulator_root": nullifier_accumulator_root,
            "authority_epoch_summary_root": authority_epoch_summary_root,
            "outbox_accumulator_root": outbox_accumulator_root,
            "pending_outbox": _pending_wire(pending_outbox),
        },
    )


def _build_expected_checkpoint(
    source: F04FixedPointSuccessV1,
    genesis: F05GenesisAcceptanceV1,
) -> tuple[F07CheckpointV1, int, int, int]:
    history = source.history
    layout = source.layout
    if not history.atoms:
        raise F07CheckpointError("F07 requires a nonempty history tip")
    if history.genesis_state_root != genesis.genesis.initial_state_root:
        raise F07CheckpointError("history genesis state differs from F05 genesis")
    if history.deployment_config_root != genesis.genesis.initial_configuration_root:
        raise F07CheckpointError("history configuration differs from F05 genesis")
    if history.authority_epochs[0].authority_state_root != (
        genesis.genesis.initial_authority_profile_root
    ):
        raise F07CheckpointError("history initial authority differs from F05 genesis")
    if genesis.genesis.history_schema != FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1:
        raise F07CheckpointError("F05 history schema is foreign to F01")

    pending = _pending_outbox(history, layout)
    prior_history_root = _history_root(history)
    nullifier_root = _nullifier_accumulator_root(layout)
    authority_root = _authority_epoch_summary_root(layout)
    outbox_root = _outbox_accumulator_root(layout)
    proof_root = _replay_proof_root(
        prior_layout_root=layout.layout_root,
        prior_history_root=prior_history_root,
        checkpoint_state_root=history.current_state_root,
        nullifier_accumulator_root=nullifier_root,
        authority_epoch_summary_root=authority_root,
        outbox_accumulator_root=outbox_root,
        pending_outbox=pending,
    )
    checkpoint_fields = {
        "schema": FCIS_M6_F07_CHECKPOINT_SCHEMA_V1,
        "checkpoint_sequence": len(history.atoms),
        "prior_layout_root": layout.layout_root,
        "prior_history_root": prior_history_root,
        "checkpoint_state_root": history.current_state_root,
        "deployment_config_root": history.deployment_config_root,
        "verifier_profile_root": history.verifier_profile_root,
        "genesis_admission_root": genesis.admission_root,
        "nullifier_accumulator_root": nullifier_root,
        "authority_epoch_summary_root": authority_root,
        "outbox_accumulator_root": outbox_root,
        "pending_outbox": _pending_wire(pending),
        "proof_kind": F07ProofKindV1.REPLAY.value,
        "proof_root": proof_root,
    }
    checkpoint_root = _derive_root(
        "zenodex/fcis/m6/f07/checkpoint-genesis",
        checkpoint_fields,
    )
    checkpoint = F07CheckpointV1(
        checkpoint_sequence=len(history.atoms),
        prior_layout_root=layout.layout_root,
        prior_history_root=prior_history_root,
        checkpoint_state_root=history.current_state_root,
        deployment_config_root=history.deployment_config_root,
        verifier_profile_root=history.verifier_profile_root,
        genesis_admission_root=genesis.admission_root,
        nullifier_accumulator_root=nullifier_root,
        authority_epoch_summary_root=authority_root,
        outbox_accumulator_root=outbox_root,
        pending_outbox=pending,
        proof_kind=F07ProofKindV1.REPLAY,
        proof_root=proof_root,
        checkpoint_genesis_root=checkpoint_root,
    )
    return checkpoint, len(history.atoms), len(layout.nullifier_rows), len(layout.outbox_rows)


def _accept(
    checkpoint: F07CheckpointV1,
    removed_history_count: int,
    removed_nullifier_count: int,
    removed_outbox_count: int,
) -> F07CheckpointAcceptanceV1:
    snapshot = F07CompactedSnapshotV1(
        checkpoint=checkpoint,
        snapshot_root=_compacted_snapshot_root(checkpoint),
    )
    return F07CheckpointAcceptanceV1(
        checkpoint=checkpoint,
        compacted_snapshot=snapshot,
        removed_history_count=removed_history_count,
        removed_nullifier_count=removed_nullifier_count,
        removed_outbox_count=removed_outbox_count,
    )


def _checked_source(
    source: object,
) -> F04FixedPointSuccessV1 | F07CheckpointRejectV1:
    if type(source) is not F04FixedPointSuccessV1:
        return _reject(F07CheckpointCodeV1.WRONG_EXACT_TYPE, "source")
    checked = cast(F04FixedPointSuccessV1, source)
    try:
        checked.__post_init__()
        if checked.canonical_layout_bytes != encode_layout_v1(checked.layout):
            return _reject(F07CheckpointCodeV1.SOURCE_REJECTED, "source")
    except (AttributeError, TypeError, ValueError, ArithmeticError, RecursionError):
        return _reject(F07CheckpointCodeV1.SOURCE_REJECTED, "source")
    return checked


def _checked_genesis(
    genesis: object,
) -> F05GenesisAcceptanceV1 | F07CheckpointRejectV1:
    if type(genesis) is not F05GenesisAcceptanceV1:
        return _reject(F07CheckpointCodeV1.GENESIS_REJECTED, "genesis")
    checked = cast(F05GenesisAcceptanceV1, genesis)
    try:
        checked.__post_init__()
    except (AttributeError, TypeError, ValueError, ArithmeticError, RecursionError):
        return _reject(F07CheckpointCodeV1.GENESIS_REJECTED, "genesis")
    return checked


def build_f07_checkpoint_v1(
    source: object,
    *,
    genesis: object,
) -> F07CheckpointResultV1:
    """Derive a full-tip replay checkpoint from two checked predecessor values."""

    checked_source = _checked_source(source)
    if type(checked_source) is F07CheckpointRejectV1:
        return checked_source
    checked_genesis = _checked_genesis(genesis)
    if type(checked_genesis) is F07CheckpointRejectV1:
        return checked_genesis
    try:
        checkpoint, history_count, nullifier_count, outbox_count = _build_expected_checkpoint(
            checked_source,
            checked_genesis,
        )
        return _accept(checkpoint, history_count, nullifier_count, outbox_count)
    except F07CheckpointError as exc:
        message = str(exc)
        if "nonempty" in message:
            return _reject(F07CheckpointCodeV1.EMPTY_HISTORY, "source", "history")
        if "genesis" in message:
            return _reject(F07CheckpointCodeV1.GENESIS_MISMATCH, "genesis")
        return _reject(F07CheckpointCodeV1.SOURCE_REJECTED, "source")
    except (AttributeError, TypeError, ValueError, ArithmeticError, RecursionError):
        return _reject(F07CheckpointCodeV1.SOURCE_REJECTED, "source")


def validate_f07_checkpoint_v1(
    source: object,
    *,
    genesis: object,
    checkpoint: object,
) -> F07CheckpointResultV1:
    """Recompute and compare a checkpoint at the intended consumption boundary."""

    checked_source = _checked_source(source)
    if type(checked_source) is F07CheckpointRejectV1:
        return checked_source
    checked_genesis = _checked_genesis(genesis)
    if type(checked_genesis) is F07CheckpointRejectV1:
        return checked_genesis
    if type(checkpoint) is not F07CheckpointV1:
        return _reject(F07CheckpointCodeV1.WRONG_EXACT_TYPE, "checkpoint")
    checked_checkpoint = checkpoint
    try:
        checked_checkpoint.__post_init__()
    except (AttributeError, TypeError, ValueError, ArithmeticError, RecursionError):
        return _reject(F07CheckpointCodeV1.INVALID_CHECKPOINT, "checkpoint")
    if checked_checkpoint.proof_kind is not F07ProofKindV1.REPLAY:
        return _reject(F07CheckpointCodeV1.UNSUPPORTED_PROOF, "checkpoint", "proof_kind")
    try:
        expected, history_count, nullifier_count, outbox_count = _build_expected_checkpoint(
            checked_source,
            checked_genesis,
        )
    except F07CheckpointError as exc:
        message = str(exc)
        if "nonempty" in message:
            return _reject(F07CheckpointCodeV1.EMPTY_HISTORY, "source", "history")
        if "genesis" in message:
            return _reject(F07CheckpointCodeV1.GENESIS_MISMATCH, "genesis")
        return _reject(F07CheckpointCodeV1.SOURCE_REJECTED, "source")
    except (AttributeError, TypeError, ValueError, ArithmeticError, RecursionError):
        return _reject(F07CheckpointCodeV1.SOURCE_REJECTED, "source")
    if checked_checkpoint != expected:
        if checked_checkpoint.pending_outbox != expected.pending_outbox:
            return _reject(
                F07CheckpointCodeV1.PENDING_OUTBOX_MISMATCH, "checkpoint", "pending_outbox"
            )
        return _reject(F07CheckpointCodeV1.CHECKPOINT_MISMATCH, "checkpoint")
    try:
        return _accept(expected, history_count, nullifier_count, outbox_count)
    except (AttributeError, TypeError, ValueError, ArithmeticError, RecursionError):
        return _reject(F07CheckpointCodeV1.INVALID_CHECKPOINT, "checkpoint")


__all__ = (
    "FCIS_M6_F07_CHECKPOINT_SCHEMA_V1",
    "FCIS_M6_F07_COMPACTED_SNAPSHOT_SCHEMA_V1",
    "F07CheckpointAcceptanceV1",
    "F07CheckpointCodeV1",
    "F07CheckpointError",
    "F07CheckpointRejectV1",
    "F07CheckpointResultV1",
    "F07CheckpointV1",
    "F07CompactedSnapshotV1",
    "F07PendingOutboxV1",
    "F07ProofKindV1",
    "build_f07_checkpoint_v1",
    "validate_f07_checkpoint_v1",
)

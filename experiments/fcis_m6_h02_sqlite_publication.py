"""Research-only SQLite refinement of the FCIS M6 publication atom.

This module is an isolated database adapter experiment. It maps the H01
logical tables to SQLite, uses one BEGIN IMMEDIATE transaction for a complete
publication, performs expected snapshot/state/authority CAS inside that
transaction, and reopens the resulting rows through the canonical durable
retraction model.

It also exposes deterministic H03 logical fault hooks for the later crash and
reopen harness. It is not a production adapter. It does not establish
filesystem durability, WAL/fsync semantics, process-crash recovery, concurrent
linearization across deployment settings, runtime caller coverage, or value
movement.
"""

from __future__ import annotations

import hashlib
import sqlite3
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Final, TypeAlias, cast

from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_d08_combined_anf import (
    D08CombinedANFAcceptV1,
    D08CombinedANFInstanceV1,
    verify_combined_anf_v1,
)
from src.core.fcis_m6_profile_ids import ANF_VERSION_V1

MAX_TRANSITIONS: Final = dra.MAX_TRANSITIONS
MAX_OUTBOX_PER_TRANSITION: Final = dra.MAX_OUTBOX_PER_TRANSITION
U32_MAX: Final = dra.U32_MAX
MAX_TEXT_BYTES: Final = dra.MAX_TEXT_BYTES


class H02Error(ValueError):
    """Typed validation failure in the isolated H02 adapter."""


class H02StorageError(H02Error):
    """The SQLite layout is not a canonical H02 state."""


class H03CrashPointV1(Enum):
    """Named logical boundaries for deterministic H03 fault injection."""

    BEFORE_BEGIN = "before_begin"
    AFTER_BEGIN = "after_begin"
    BEFORE_CAS = "before_cas"
    AFTER_CAS_CHECK = "after_cas_check"
    BEFORE_AUTHORITY_EPOCH_INSERT = "before_authority_epoch_insert"
    AFTER_AUTHORITY_EPOCH_INSERT = "after_authority_epoch_insert"
    BEFORE_AUTHORITY_WRITER_INSERT = "before_authority_writer_insert"
    AFTER_AUTHORITY_WRITER_INSERT = "after_authority_writer_insert"
    BEFORE_ATOM_INSERT = "before_atom_insert"
    AFTER_ATOM_INSERT = "after_atom_insert"
    BEFORE_EVIDENCE_INSERT = "before_evidence_insert"
    AFTER_EVIDENCE_INSERT = "after_evidence_insert"
    BEFORE_NULLIFIER_INSERT = "before_nullifier_insert"
    AFTER_NULLIFIER_INSERT = "after_nullifier_insert"
    BEFORE_OUTBOX_INSERT = "before_outbox_insert"
    AFTER_OUTBOX_INSERT = "after_outbox_insert"
    BEFORE_ANF_INSERT = "before_anf_insert"
    AFTER_ANF_INSERT = "after_anf_insert"
    BEFORE_COMMIT = "before_commit"
    AFTER_COMMIT_BEFORE_RESPONSE = "after_commit_before_response"


H03_CRASH_MANIFEST_V1: Final[tuple[H03CrashPointV1, ...]] = tuple(H03CrashPointV1)


class H03InjectedCrash(RuntimeError):
    """Deterministic process-fault surrogate; the publish path must not catch it."""

    def __init__(self, point: H03CrashPointV1) -> None:
        self.point = point
        super().__init__(f"H03 injected crash at {point.value}")


@dataclass(frozen=True, slots=True)
class H03FaultHookV1:
    """One-shot logical fault hook selected only by the research harness."""

    point: H03CrashPointV1 | None = None

    def __post_init__(self) -> None:
        if self.point is not None and type(self.point) is not H03CrashPointV1:
            raise H02Error("H03 fault point has the wrong exact type")

    def checkpoint(self, point: H03CrashPointV1) -> None:
        if type(point) is not H03CrashPointV1:
            raise H02Error("H03 checkpoint has the wrong exact type")
        if self.point is point:
            raise H03InjectedCrash(point)


class H02CodeV1(Enum):
    COMMITTED = "committed"
    INVALID_REQUEST = "invalid_request"
    STALE_SNAPSHOT_CAS = "stale_snapshot_cas"
    STALE_STATE_CAS = "stale_state_cas"
    STALE_AUTHORITY_CAS = "stale_authority_cas"
    REOPEN_REJECTED = "reopen_rejected"
    SQL_ROLLBACK = "sql_rollback"


@dataclass(frozen=True, slots=True)
class H02RejectV1:
    code: H02CodeV1
    path: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class H02CommitV1:
    post_snapshot: dra.DurableSnapshotV1
    anf_root: str
    publication_root: str


H02ResultV1: TypeAlias = H02CommitV1 | H02RejectV1


def _digest(value: object, label: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise H02Error(f"{label} must be 64 lowercase hexadecimal characters")
    return value


def _anf_digest(value: object, label: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or any(character not in "0123456789abcdef" for character in value[2:])
    ):
        raise H02Error(f"{label} must be a 0x-prefixed lowercase digest")
    return value


def _exact_u32(value: object, label: str) -> int:
    if type(value) is not int or value < 0 or value > U32_MAX:
        raise H02Error(f"{label} must fit the u32 domain")
    return value


def _bounded_text(value: object, label: str) -> str:
    if type(value) is not str:
        raise H02Error(f"{label} must be an exact string")
    if not value or len(value.encode("utf-8")) > MAX_TEXT_BYTES:
        raise H02Error(f"{label} is empty or exceeds its byte bound")
    return value


def _framed_hash(domain: str, fields: tuple[bytes, ...]) -> str:
    digest = hashlib.sha256()
    domain_bytes = domain.encode("ascii")
    digest.update(len(domain_bytes).to_bytes(8, "big"))
    digest.update(domain_bytes)
    digest.update(len(fields).to_bytes(4, "big"))
    for field in fields:
        digest.update(len(field).to_bytes(8, "big"))
        digest.update(field)
    return digest.hexdigest()


@dataclass(frozen=True, slots=True)
class ANFPublicationWitnessV1:
    """Verifier-minted D08 acceptance bound to one exact publication fixture."""

    instance: D08CombinedANFInstanceV1
    acceptance: D08CombinedANFAcceptV1

    def __post_init__(self) -> None:
        if type(self.instance) is not D08CombinedANFInstanceV1:
            raise H02Error("ANF witness instance has the wrong exact type")
        if type(self.acceptance) is not D08CombinedANFAcceptV1:
            raise H02Error("ANF witness acceptance has the wrong exact type")
        try:
            verified = verify_combined_anf_v1(self.instance)
        except (
            AttributeError,
            dra.DurableRetractionError,
            TypeError,
            ValueError,
            ArithmeticError,
            OverflowError,
            RecursionError,
        ) as exc:
            raise H02Error("ANF witness verification failed") from exc
        if type(verified) is not D08CombinedANFAcceptV1 or verified != self.acceptance:
            raise H02Error("ANF witness is not the verifier result for its instance")
        _anf_digest(self.acceptance.anf_root, "anf_root")

    @property
    def atom(self) -> dra.PublicationAtomV1:
        return self.instance.publication_atom

    @property
    def anf_root(self) -> str:
        return cast(str, self.acceptance.anf_root[2:])


@dataclass(frozen=True, slots=True)
class ANFPublicationRowV1:
    """Durable ANF relation added to the DRA snapshot by H02."""

    commit_id: str
    atom_root: str
    anf_root: str
    anf_version: str = ANF_VERSION_V1

    def __post_init__(self) -> None:
        _digest(self.commit_id, "commit_id")
        _digest(self.atom_root, "atom_root")
        _digest(self.anf_root, "anf_root")
        if self.anf_version != ANF_VERSION_V1:
            raise H02Error("anf_version is not the pinned profile")


def _anf_set_root(rows: tuple[ANFPublicationRowV1, ...]) -> str:
    if type(rows) is not tuple:
        raise H02Error("ANF rows must be an exact tuple")
    canonical = tuple(sorted(rows, key=lambda row: row.commit_id))
    if canonical != rows:
        raise H02Error("ANF rows must be in commit-id order")
    fields: list[bytes] = []
    for row in rows:
        row.__post_init__()
        fields.extend(
            (
                bytes.fromhex(row.commit_id),
                bytes.fromhex(row.atom_root),
                bytes.fromhex(row.anf_root),
                row.anf_version.encode("ascii"),
            )
        )
    return _framed_hash("zenodex/fcis/m6/h02/anf-set/v1", tuple(fields))


def _publication_root(snapshot_root: str, anf_set_root: str) -> str:
    _digest(snapshot_root, "snapshot_root")
    _digest(anf_set_root, "anf_set_root")
    return _framed_hash(
        "zenodex/fcis/m6/h02/publication-state/v1",
        (bytes.fromhex(snapshot_root), bytes.fromhex(anf_set_root)),
    )


@dataclass(frozen=True, slots=True)
class SQLiteStateV1:
    """DRA snapshot plus the atom-to-ANF relation required by H02."""

    snapshot: dra.DurableSnapshotV1
    anf_rows: tuple[ANFPublicationRowV1, ...]
    anf_set_root: str
    publication_root: str

    def __post_init__(self) -> None:
        if type(self.snapshot) is not dra.DurableSnapshotV1:
            raise H02Error("snapshot has the wrong exact type")
        self.snapshot.__post_init__()
        if type(self.anf_rows) is not tuple:
            raise H02Error("ANF rows must be an exact tuple")
        if tuple(sorted(self.anf_rows, key=lambda row: row.commit_id)) != self.anf_rows:
            raise H02Error("ANF rows must be canonically ordered")
        commit_to_atom = {atom.commit_id: atom for atom in self.snapshot.atom_rows}
        if len(self.anf_rows) != len(commit_to_atom):
            raise H02Error("ANF row cardinality does not match atom cardinality")
        seen: set[str] = set()
        for row in self.anf_rows:
            row.__post_init__()
            if row.commit_id in seen:
                raise H02Error("ANF commit identities must be unique")
            seen.add(row.commit_id)
            atom = commit_to_atom.get(row.commit_id)
            if atom is None or atom.atom_root != row.atom_root:
                raise H02Error("ANF row is not bound to its exact atom")
        expected_anf_set_root = _anf_set_root(self.anf_rows)
        if self.anf_set_root != expected_anf_set_root:
            raise H02Error("ANF set root does not rederive")
        expected_publication_root = _publication_root(
            self.snapshot.snapshot_root,
            expected_anf_set_root,
        )
        if self.publication_root != expected_publication_root:
            raise H02Error("publication root does not rederive")


@dataclass(frozen=True, slots=True)
class SQLitePublicationRequestV1:
    """One H02 request with caller-observed roots and verifier-minted ANF."""

    atom: dra.PublicationAtomV1
    anf_witness: ANFPublicationWitnessV1
    expected_snapshot_root: str
    expected_publication_root: str
    expected_state_root: str
    expected_authority_epoch: int
    expected_authority_root: str
    next_authority: dra.AuthorityStateV1 | None = None

    def __post_init__(self) -> None:
        if type(self.atom) is not dra.PublicationAtomV1:
            raise H02Error("atom has the wrong exact type")
        self.atom.__post_init__()
        if type(self.anf_witness) is not ANFPublicationWitnessV1:
            raise H02Error("ANF witness has the wrong exact type")
        self.anf_witness.__post_init__()
        if self.anf_witness.atom != self.atom:
            raise H02Error("ANF witness is crossed with a different atom")
        for name in (
            "expected_snapshot_root",
            "expected_publication_root",
            "expected_state_root",
            "expected_authority_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        _exact_u32(self.expected_authority_epoch, "expected_authority_epoch")
        if self.next_authority is not None:
            if type(self.next_authority) is not dra.AuthorityStateV1:
                raise H02Error("next authority has the wrong exact type")
            self.next_authority.__post_init__()


def _root_column(name: str) -> str:
    return f"{name} TEXT NOT NULL CHECK(length({name}) = 64 AND {name} NOT GLOB '*[^0-9a-f]*')"


def _text_column(name: str) -> str:
    return (
        f"{name} TEXT NOT NULL CHECK(length(CAST({name} AS BLOB)) BETWEEN 1 AND {MAX_TEXT_BYTES})"
    )


def _schema_sql() -> str:
    return f"""
CREATE TABLE IF NOT EXISTS snapshot_meta (
    singleton INTEGER PRIMARY KEY CHECK(singleton = 1),
    {_root_column("genesis_state_root")},
    {_root_column("current_state_root")},
    {_root_column("snapshot_root")},
    {_root_column("deployment_config_root")},
    {_root_column("verifier_profile_root")},
    authority_head_epoch INTEGER NOT NULL CHECK(
        authority_head_epoch BETWEEN 0 AND {U32_MAX}
    ),
    {_root_column("authority_head_root")},
    {_root_column("anf_set_root")},
    {_root_column("publication_root")}
);

CREATE TABLE IF NOT EXISTS authority_epochs (
    epoch_index INTEGER PRIMARY KEY CHECK(
        epoch_index BETWEEN 0 AND {U32_MAX}
    ),
    phase TEXT NOT NULL CHECK(
        phase IN (
            'LEGACY',
            'SHADOW_REPLAY',
            'DUAL_CHECK',
            'QUIESCED',
            'AUTHORITY_SWITCH',
            'POST_SWITCH_VALIDATION',
            'LEGACY_DISABLED'
        )
    ),
    {_root_column("legacy_profile_root")},
    {_root_column("target_profile_root")},
    {_root_column("active_profile_root")},
    {_root_column("transport_root")},
    {_root_column("transition_root")}
);

CREATE TABLE IF NOT EXISTS authority_allowed_writers (
    epoch_index INTEGER NOT NULL REFERENCES authority_epochs(epoch_index),
    writer_profile_root TEXT NOT NULL CHECK(
        length(writer_profile_root) = 64
        AND writer_profile_root NOT GLOB '*[^0-9a-f]*'
    ),
    PRIMARY KEY(epoch_index, writer_profile_root)
);

CREATE TABLE IF NOT EXISTS publication_atoms (
    sequence INTEGER PRIMARY KEY CHECK(
        sequence BETWEEN 1 AND {MAX_TRANSITIONS}
    ),
    {_root_column("commit_id")} UNIQUE,
    {_root_column("command_root")},
    {_root_column("expected_pre_root")},
    {_root_column("post_state_root")},
    {_root_column("writer_profile_root")},
    authority_epoch_index INTEGER NOT NULL REFERENCES authority_epochs(epoch_index)
        CHECK(authority_epoch_index BETWEEN 0 AND {U32_MAX}),
    {_root_column("authority_state_root")},
    {_root_column("nullifier_root")} UNIQUE,
    {_root_column("response_root")},
    {_root_column("receipt_root")},
    {_root_column("decision_root")},
    {_root_column("bundle_root")},
    {_root_column("replay_root")},
    {_root_column("deployment_config_root")},
    {_root_column("verifier_profile_root")}
);

CREATE TABLE IF NOT EXISTS publication_evidence (
    commit_id TEXT NOT NULL REFERENCES publication_atoms(commit_id),
    kind TEXT NOT NULL CHECK(
        kind IN ('command', 'response', 'receipt', 'decision', 'bundle', 'replay', 'authority')
    ),
    {_root_column("value_root")},
    PRIMARY KEY(commit_id, kind)
);

CREATE TABLE IF NOT EXISTS publication_nullifiers (
    {_root_column("nullifier_root")} PRIMARY KEY,
    commit_id TEXT NOT NULL REFERENCES publication_atoms(commit_id),
    {_root_column("fingerprint")}
);

CREATE TABLE IF NOT EXISTS publication_outbox (
    {_root_column("effect_id")} PRIMARY KEY,
    commit_id TEXT NOT NULL REFERENCES publication_atoms(commit_id),
    ordinal INTEGER NOT NULL CHECK(
        ordinal BETWEEN 0 AND {MAX_OUTBOX_PER_TRANSITION - 1}
    ),
    {_text_column("destination")},
    {_root_column("payload_root")},
    {_root_column("adapter_profile_root")},
    UNIQUE(commit_id, ordinal)
);

CREATE TABLE IF NOT EXISTS anf_publications (
    commit_id TEXT PRIMARY KEY REFERENCES publication_atoms(commit_id),
    {_root_column("atom_root")},
    {_root_column("anf_root")},
    anf_version TEXT NOT NULL CHECK(anf_version = '{ANF_VERSION_V1}')
);

CREATE TABLE IF NOT EXISTS delivery_acks (
    {_root_column("effect_id")} PRIMARY KEY,
    {_text_column("destination")},
    {_root_column("payload_root")},
    {_root_column("destination_receipt_root")},
    {_root_column("adapter_profile_root")},
    {_root_column("idempotency_root")},
    {_root_column("response_root")}
);
"""


def create_connection(path: str | Path = ":memory:") -> sqlite3.Connection:
    connection = sqlite3.connect(str(path), isolation_level=None)
    connection.execute("PRAGMA foreign_keys = ON")
    connection.executescript(_schema_sql())
    return connection


def _checkpoint(
    fault_hook: H03FaultHookV1 | None,
    point: H03CrashPointV1,
) -> None:
    if fault_hook is not None:
        fault_hook.checkpoint(point)


def _insert_authority(
    connection: sqlite3.Connection,
    authority: dra.AuthorityStateV1,
    fault_hook: H03FaultHookV1 | None = None,
) -> None:
    _checkpoint(fault_hook, H03CrashPointV1.BEFORE_AUTHORITY_EPOCH_INSERT)
    connection.execute(
        """
        INSERT INTO authority_epochs(
            epoch_index, phase, legacy_profile_root, target_profile_root,
            active_profile_root, transport_root, transition_root
        ) VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (
            authority.epoch_index,
            authority.phase.value,
            authority.legacy_profile_root,
            authority.target_profile_root,
            authority.active_profile_root,
            authority.transport_root,
            authority.transition_root,
        ),
    )
    _checkpoint(fault_hook, H03CrashPointV1.AFTER_AUTHORITY_EPOCH_INSERT)
    _checkpoint(fault_hook, H03CrashPointV1.BEFORE_AUTHORITY_WRITER_INSERT)
    connection.executemany(
        """
        INSERT INTO authority_allowed_writers(epoch_index, writer_profile_root)
        VALUES (?, ?)
        """,
        ((authority.epoch_index, writer) for writer in authority.allowed_writer_roots),
    )
    _checkpoint(fault_hook, H03CrashPointV1.AFTER_AUTHORITY_WRITER_INSERT)


def _insert_atom(
    connection: sqlite3.Connection,
    atom: dra.PublicationAtomV1,
    fault_hook: H03FaultHookV1 | None = None,
) -> None:
    _checkpoint(fault_hook, H03CrashPointV1.BEFORE_ATOM_INSERT)
    connection.execute(
        """
        INSERT INTO publication_atoms(
            sequence, commit_id, command_root, expected_pre_root,
            post_state_root, writer_profile_root, authority_epoch_index,
            authority_state_root, nullifier_root, response_root, receipt_root,
            decision_root, bundle_root, replay_root,
            deployment_config_root, verifier_profile_root
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            atom.sequence,
            atom.commit_id,
            atom.command_root,
            atom.expected_pre_root,
            atom.post_state_root,
            atom.writer_profile_root,
            atom.authority_epoch_index,
            atom.authority_state_root,
            atom.nullifier_root,
            atom.response_root,
            atom.receipt_root,
            atom.decision_root,
            atom.bundle_root,
            atom.replay_root,
            atom.deployment_config_root,
            atom.verifier_profile_root,
        ),
    )
    _checkpoint(fault_hook, H03CrashPointV1.AFTER_ATOM_INSERT)
    _checkpoint(fault_hook, H03CrashPointV1.BEFORE_EVIDENCE_INSERT)
    connection.executemany(
        """
        INSERT INTO publication_evidence(commit_id, kind, value_root)
        VALUES (?, ?, ?)
        """,
        ((row.commit_id, row.kind, row.value_root) for row in dra._evidence_rows((atom,))),
    )
    _checkpoint(fault_hook, H03CrashPointV1.AFTER_EVIDENCE_INSERT)
    _checkpoint(fault_hook, H03CrashPointV1.BEFORE_NULLIFIER_INSERT)
    connection.execute(
        """
        INSERT INTO publication_nullifiers(nullifier_root, commit_id, fingerprint)
        VALUES (?, ?, ?)
        """,
        (atom.nullifier_root, atom.commit_id, atom.fingerprint),
    )
    _checkpoint(fault_hook, H03CrashPointV1.AFTER_NULLIFIER_INSERT)
    _checkpoint(fault_hook, H03CrashPointV1.BEFORE_OUTBOX_INSERT)
    connection.executemany(
        """
        INSERT INTO publication_outbox(
            effect_id, commit_id, ordinal, destination,
            payload_root, adapter_profile_root
        ) VALUES (?, ?, ?, ?, ?, ?)
        """,
        (
            (
                effect.effect_id,
                atom.commit_id,
                effect.ordinal,
                effect.destination,
                effect.payload_root,
                effect.adapter_profile_root,
            )
            for effect in atom.outbox
        ),
    )
    _checkpoint(fault_hook, H03CrashPointV1.AFTER_OUTBOX_INSERT)


def _insert_ack(
    connection: sqlite3.Connection,
    ack: dra.DeliveryAckV1,
) -> None:
    connection.execute(
        """
        INSERT INTO delivery_acks(
            effect_id, destination, payload_root, destination_receipt_root,
            adapter_profile_root, idempotency_root, response_root
        ) VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (
            ack.effect_id,
            ack.destination,
            ack.payload_root,
            ack.destination_receipt_root,
            ack.adapter_profile_root,
            ack.idempotency_root,
            ack.response_root,
        ),
    )


def _insert_anf_row(
    connection: sqlite3.Connection,
    row: ANFPublicationRowV1,
    fault_hook: H03FaultHookV1 | None = None,
) -> None:
    _checkpoint(fault_hook, H03CrashPointV1.BEFORE_ANF_INSERT)
    connection.execute(
        """
        INSERT INTO anf_publications(commit_id, atom_root, anf_root, anf_version)
        VALUES (?, ?, ?, ?)
        """,
        (row.commit_id, row.atom_root, row.anf_root, row.anf_version),
    )
    _checkpoint(fault_hook, H03CrashPointV1.AFTER_ANF_INSERT)


def _insert_snapshot_meta(
    connection: sqlite3.Connection,
    state: SQLiteStateV1,
) -> None:
    authority = state.snapshot.authority_epochs[-1]
    connection.execute(
        """
        INSERT INTO snapshot_meta(
            singleton, genesis_state_root, current_state_root, snapshot_root,
            deployment_config_root, verifier_profile_root,
            authority_head_epoch, authority_head_root, anf_set_root,
            publication_root
        ) VALUES (1, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            state.snapshot.genesis_state_root,
            state.snapshot.current_state_root,
            state.snapshot.snapshot_root,
            state.snapshot.deployment_config_root,
            state.snapshot.verifier_profile_root,
            authority.epoch_index,
            authority.root,
            state.anf_set_root,
            state.publication_root,
        ),
    )


def _insert_state_rows(
    connection: sqlite3.Connection,
    state: SQLiteStateV1,
) -> None:
    for authority in state.snapshot.authority_epochs:
        _insert_authority(connection, authority)
    for atom in state.snapshot.atom_rows:
        _insert_atom(connection, atom)
    for ack in state.snapshot.ack_rows:
        _insert_ack(connection, ack)
    for row in state.anf_rows:
        _insert_anf_row(connection, row)


def initialize_database(
    connection: sqlite3.Connection,
    snapshot: dra.DurableSnapshotV1,
    anf_rows: tuple[ANFPublicationRowV1, ...] = (),
) -> None:
    if type(connection) is not sqlite3.Connection:
        raise H02Error("connection has the wrong exact type")
    if type(snapshot) is not dra.DurableSnapshotV1:
        raise H02Error("snapshot has the wrong exact type")
    reopened = dra.reopen_snapshot(snapshot)
    if type(reopened) is not dra.AuthorizedHistoryV1:
        raise H02Error("initial snapshot is not a canonical fixed point")
    state = SQLiteStateV1(
        snapshot=snapshot,
        anf_rows=anf_rows,
        anf_set_root=_anf_set_root(anf_rows),
        publication_root=_publication_root(
            snapshot.snapshot_root,
            _anf_set_root(anf_rows),
        ),
    )
    try:
        connection.execute("BEGIN")
        if connection.execute("SELECT 1 FROM snapshot_meta").fetchone() is not None:
            raise H02Error("database is already initialized")
        _insert_snapshot_meta(connection, state)
        _insert_state_rows(connection, state)
        connection.commit()
    except (H02Error, sqlite3.Error):
        connection.rollback()
        raise
    if read_state(connection) != state:
        raise H02StorageError("initialized database does not reopen to its seed state")


def create_database(
    snapshot: dra.DurableSnapshotV1,
    anf_rows: tuple[ANFPublicationRowV1, ...] = (),
) -> sqlite3.Connection:
    connection = create_connection()
    initialize_database(connection, snapshot, anf_rows)
    return connection


def _read_snapshot(connection: sqlite3.Connection) -> dra.DurableSnapshotV1:
    meta = connection.execute(
        """
        SELECT genesis_state_root, current_state_root, snapshot_root,
               deployment_config_root, verifier_profile_root,
               authority_head_epoch, authority_head_root, anf_set_root,
               publication_root
        FROM snapshot_meta WHERE singleton = 1
        """
    ).fetchone()
    if meta is None:
        raise H02StorageError("snapshot metadata is absent")

    authorities: list[dra.AuthorityStateV1] = []
    for row in connection.execute(
        """
        SELECT epoch_index, phase, legacy_profile_root, target_profile_root,
               active_profile_root, transport_root, transition_root
        FROM authority_epochs ORDER BY epoch_index
        """
    ):
        writers = tuple(
            writer_row[0]
            for writer_row in connection.execute(
                """
                SELECT writer_profile_root
                FROM authority_allowed_writers
                WHERE epoch_index = ? ORDER BY writer_profile_root
                """,
                (row[0],),
            )
        )
        authorities.append(
            dra.AuthorityStateV1(
                epoch_index=row[0],
                phase=dra.MigrationPhaseV1(row[1]),
                legacy_profile_root=row[2],
                target_profile_root=row[3],
                active_profile_root=row[4],
                allowed_writer_roots=writers,
                transport_root=row[5],
                transition_root=row[6],
            )
        )

    atoms: list[dra.PublicationAtomV1] = []
    for row in connection.execute(
        """
        SELECT sequence, commit_id, command_root, expected_pre_root,
               post_state_root, writer_profile_root, authority_epoch_index,
               authority_state_root, nullifier_root, response_root, receipt_root,
               decision_root, bundle_root, replay_root,
               deployment_config_root, verifier_profile_root
        FROM publication_atoms ORDER BY sequence
        """
    ):
        effects = tuple(
            dra.OutboxEffectV1(
                effect_id=effect_row[0],
                ordinal=effect_row[1],
                destination=effect_row[2],
                payload_root=effect_row[3],
                adapter_profile_root=effect_row[4],
            )
            for effect_row in connection.execute(
                """
                SELECT effect_id, ordinal, destination, payload_root,
                       adapter_profile_root
                FROM publication_outbox
                WHERE commit_id = ? ORDER BY ordinal
                """,
                (row[1],),
            )
        )
        atoms.append(
            dra.PublicationAtomV1(
                sequence=row[0],
                commit_id=row[1],
                command_root=row[2],
                expected_pre_root=row[3],
                post_state_root=row[4],
                writer_profile_root=row[5],
                authority_epoch_index=row[6],
                authority_state_root=row[7],
                nullifier_root=row[8],
                response_root=row[9],
                receipt_root=row[10],
                decision_root=row[11],
                bundle_root=row[12],
                replay_root=row[13],
                outbox=effects,
                deployment_config_root=row[14],
                verifier_profile_root=row[15],
            )
        )

    evidence_rows = tuple(
        dra.EvidenceRowV1(commit_id=row[0], kind=row[1], value_root=row[2])
        for row in connection.execute(
            """
            SELECT commit_id, kind, value_root
            FROM publication_evidence ORDER BY commit_id, kind, value_root
            """
        )
    )
    nullifier_rows = tuple(
        dra.NullifierRowV1(
            nullifier_root=row[0],
            commit_id=row[1],
            fingerprint=row[2],
        )
        for row in connection.execute(
            """
            SELECT nullifier_root, commit_id, fingerprint
            FROM publication_nullifiers
            ORDER BY nullifier_root, commit_id, fingerprint
            """
        )
    )
    outbox_rows = tuple(
        dra.OutboxRowV1(
            effect_id=row[0],
            commit_id=row[1],
            ordinal=row[2],
            destination=row[3],
            payload_root=row[4],
            adapter_profile_root=row[5],
        )
        for row in connection.execute(
            """
            SELECT effect_id, commit_id, ordinal, destination, payload_root,
                   adapter_profile_root
            FROM publication_outbox
            ORDER BY effect_id, commit_id, ordinal
            """
        )
    )
    ack_rows = tuple(
        dra.DeliveryAckV1(
            effect_id=row[0],
            destination=row[1],
            payload_root=row[2],
            destination_receipt_root=row[3],
            adapter_profile_root=row[4],
            idempotency_root=row[5],
            response_root=row[6],
        )
        for row in connection.execute(
            """
            SELECT effect_id, destination, payload_root,
                   destination_receipt_root, adapter_profile_root,
                   idempotency_root, response_root
            FROM delivery_acks ORDER BY effect_id
            """
        )
    )
    snapshot = dra.DurableSnapshotV1(
        genesis_state_root=meta[0],
        authority_epochs=tuple(authorities),
        current_state_root=meta[1],
        atom_rows=tuple(atoms),
        evidence_rows=evidence_rows,
        nullifier_rows=nullifier_rows,
        outbox_rows=outbox_rows,
        ack_rows=ack_rows,
        snapshot_root=meta[2],
        deployment_config_root=meta[3],
        verifier_profile_root=meta[4],
    )
    authority = snapshot.authority_epochs[-1]
    if meta[5] != authority.epoch_index or meta[6] != authority.root:
        raise H02StorageError("authority head cache does not rederive")
    return snapshot


def _read_anf_rows(connection: sqlite3.Connection) -> tuple[ANFPublicationRowV1, ...]:
    return tuple(
        ANFPublicationRowV1(
            commit_id=row[0],
            atom_root=row[1],
            anf_root=row[2],
            anf_version=row[3],
        )
        for row in connection.execute(
            """
            SELECT commit_id, atom_root, anf_root, anf_version
            FROM anf_publications ORDER BY commit_id
            """
        )
    )


def read_state(connection: sqlite3.Connection) -> SQLiteStateV1:
    if type(connection) is not sqlite3.Connection:
        raise H02Error("connection has the wrong exact type")
    snapshot = _read_snapshot(connection)
    reopened = dra.reopen_snapshot(snapshot)
    if type(reopened) is not dra.AuthorizedHistoryV1:
        raise H02StorageError("durable snapshot is not a canonical fixed point")
    anf_rows = _read_anf_rows(connection)
    meta = connection.execute(
        "SELECT anf_set_root, publication_root FROM snapshot_meta WHERE singleton = 1"
    ).fetchone()
    if meta is None:
        raise H02StorageError("snapshot metadata is absent")
    state = SQLiteStateV1(
        snapshot=snapshot,
        anf_rows=anf_rows,
        anf_set_root=meta[0],
        publication_root=meta[1],
    )
    if reopened.current_state_root != snapshot.current_state_root:
        raise H02StorageError("reopened state root disagrees with snapshot")
    return state


def _reject(code: H02CodeV1, *path: str) -> H02RejectV1:
    return H02RejectV1(code=code, path=tuple(path))


def _rollback(connection: sqlite3.Connection, code: H02CodeV1, *path: str) -> H02RejectV1:
    connection.rollback()
    return _reject(code, *path)


def _post_authorities(
    pre_history: dra.AuthorizedHistoryV1,
    request: SQLitePublicationRequestV1,
) -> tuple[dra.AuthorityStateV1, ...]:
    if request.next_authority is None:
        if request.atom.authority_epoch_index != pre_history.authority.epoch_index:
            raise H02Error("ordinary publication names a non-head authority epoch")
        return cast(tuple[dra.AuthorityStateV1, ...], pre_history.authority_epochs)
    next_authority = request.next_authority
    if next_authority.epoch_index != len(pre_history.authority_epochs):
        raise H02Error("authority transition must append exactly one epoch")
    if request.atom.authority_epoch_index != next_authority.epoch_index:
        raise H02Error("atom is not bound to the appended authority epoch")
    return cast(tuple[dra.AuthorityStateV1, ...], pre_history.authority_epochs + (next_authority,))


def publish_atom(
    connection: sqlite3.Connection,
    request: object,
    fault_hook: object = None,
) -> H02ResultV1:
    if type(connection) is not sqlite3.Connection:
        return _reject(H02CodeV1.INVALID_REQUEST, "connection")
    if type(request) is not SQLitePublicationRequestV1:
        return _reject(H02CodeV1.INVALID_REQUEST, "request")
    if fault_hook is not None and type(fault_hook) is not H03FaultHookV1:
        return _reject(H02CodeV1.INVALID_REQUEST, "fault_hook")
    exact_request = request
    exact_fault_hook = fault_hook
    if exact_fault_hook is None:
        exact_fault_hook = H03FaultHookV1()
    try:
        exact_request.__post_init__()
        exact_fault_hook.__post_init__()
    except (
        AttributeError,
        H02Error,
        TypeError,
        ValueError,
        ArithmeticError,
        OverflowError,
        RecursionError,
    ):
        return _reject(H02CodeV1.INVALID_REQUEST, "request")

    exact_fault_hook.checkpoint(H03CrashPointV1.BEFORE_BEGIN)
    try:
        connection.execute("BEGIN IMMEDIATE")
    except sqlite3.Error:
        return _reject(H02CodeV1.SQL_ROLLBACK, "begin")
    exact_fault_hook.checkpoint(H03CrashPointV1.AFTER_BEGIN)

    try:
        pre_state = read_state(connection)
        pre_snapshot = pre_state.snapshot
        pre_history_result = dra.reopen_snapshot(pre_snapshot)
        if type(pre_history_result) is not dra.AuthorizedHistoryV1:
            return _rollback(connection, H02CodeV1.REOPEN_REJECTED, "pre")
        pre_history = pre_history_result

        if pre_snapshot.snapshot_root != exact_request.expected_snapshot_root:
            return _rollback(connection, H02CodeV1.STALE_SNAPSHOT_CAS, "snapshot_root")
        if pre_state.publication_root != exact_request.expected_publication_root:
            return _rollback(connection, H02CodeV1.STALE_SNAPSHOT_CAS, "publication_root")
        if pre_snapshot.current_state_root != exact_request.expected_state_root:
            return _rollback(connection, H02CodeV1.STALE_STATE_CAS, "state_root")
        if pre_history.authority.epoch_index != exact_request.expected_authority_epoch:
            return _rollback(connection, H02CodeV1.STALE_AUTHORITY_CAS, "epoch")
        if pre_history.authority.root != exact_request.expected_authority_root:
            return _rollback(connection, H02CodeV1.STALE_AUTHORITY_CAS, "authority_root")
        if exact_request.anf_witness.instance.pre_snapshot != pre_snapshot:
            return _rollback(connection, H02CodeV1.INVALID_REQUEST, "anf_pre_snapshot")

        authorities = _post_authorities(pre_history, exact_request)
        post_history = dra.AuthorizedHistoryV1(
            genesis_state_root=pre_history.genesis_state_root,
            authority_epochs=authorities,
            atoms=pre_history.atoms + (exact_request.atom,),
            acks=pre_history.acks,
            deployment_config_root=pre_history.deployment_config_root,
            verifier_profile_root=pre_history.verifier_profile_root,
        )
        post_snapshot = dra.encode_history(post_history)
        if exact_request.anf_witness.instance.post_snapshot != post_snapshot:
            return _rollback(connection, H02CodeV1.INVALID_REQUEST, "anf_post_snapshot")

        new_anf_row = ANFPublicationRowV1(
            commit_id=exact_request.atom.commit_id,
            atom_root=exact_request.atom.atom_root,
            anf_root=exact_request.anf_witness.anf_root,
        )
        post_anf_rows = tuple(
            sorted(pre_state.anf_rows + (new_anf_row,), key=lambda row: row.commit_id)
        )
        post_state = SQLiteStateV1(
            snapshot=post_snapshot,
            anf_rows=post_anf_rows,
            anf_set_root=_anf_set_root(post_anf_rows),
            publication_root=_publication_root(
                post_snapshot.snapshot_root,
                _anf_set_root(post_anf_rows),
            ),
        )
        authority = post_snapshot.authority_epochs[-1]
        exact_fault_hook.checkpoint(H03CrashPointV1.BEFORE_CAS)
        cursor = connection.execute(
            """
            UPDATE snapshot_meta
            SET current_state_root = ?, snapshot_root = ?,
                deployment_config_root = ?, verifier_profile_root = ?,
                authority_head_epoch = ?, authority_head_root = ?,
                anf_set_root = ?, publication_root = ?
            WHERE singleton = 1
              AND current_state_root = ?
              AND snapshot_root = ?
              AND authority_head_epoch = ?
              AND authority_head_root = ?
              AND publication_root = ?
            """,
            (
                post_snapshot.current_state_root,
                post_snapshot.snapshot_root,
                post_snapshot.deployment_config_root,
                post_snapshot.verifier_profile_root,
                authority.epoch_index,
                authority.root,
                post_state.anf_set_root,
                post_state.publication_root,
                exact_request.expected_state_root,
                exact_request.expected_snapshot_root,
                exact_request.expected_authority_epoch,
                exact_request.expected_authority_root,
                exact_request.expected_publication_root,
            ),
        )
        if cursor.rowcount != 1:
            return _rollback(connection, H02CodeV1.STALE_SNAPSHOT_CAS, "sql_cas")
        exact_fault_hook.checkpoint(H03CrashPointV1.AFTER_CAS_CHECK)

        if exact_request.next_authority is not None:
            _insert_authority(connection, exact_request.next_authority, exact_fault_hook)
        _insert_atom(connection, exact_request.atom, exact_fault_hook)
        _insert_anf_row(connection, new_anf_row, exact_fault_hook)
        actual_state = read_state(connection)
        if actual_state != post_state:
            raise H02StorageError("transaction rows do not equal complete POST")
        exact_fault_hook.checkpoint(H03CrashPointV1.BEFORE_COMMIT)
        connection.commit()
        exact_fault_hook.checkpoint(H03CrashPointV1.AFTER_COMMIT_BEFORE_RESPONSE)
        return H02CommitV1(
            post_snapshot=post_snapshot,
            anf_root=new_anf_row.anf_root,
            publication_root=post_state.publication_root,
        )
    except (
        H02Error,
        dra.DurableRetractionError,
        AttributeError,
        TypeError,
        ValueError,
        ArithmeticError,
        OverflowError,
        IndexError,
        sqlite3.IntegrityError,
    ):
        connection.rollback()
        return _reject(H02CodeV1.SQL_ROLLBACK, "transaction")
    except sqlite3.Error:
        connection.rollback()
        return _reject(H02CodeV1.SQL_ROLLBACK, "sqlite")


__all__ = (
    "ANFPublicationRowV1",
    "ANFPublicationWitnessV1",
    "H03CrashPointV1",
    "H03FaultHookV1",
    "H03InjectedCrash",
    "H03_CRASH_MANIFEST_V1",
    "H02CodeV1",
    "H02CommitV1",
    "H02Error",
    "H02RejectV1",
    "H02ResultV1",
    "SQLitePublicationRequestV1",
    "SQLiteStateV1",
    "create_connection",
    "create_database",
    "initialize_database",
    "publish_atom",
    "read_state",
)

"""Research-only SQLite refinement of the E05 expected-root CAS.

The adapter deliberately starts ``BEGIN IMMEDIATE`` before reading the
datastore head.  It then checks the E04 classifier, compares the complete
verifier-owned predecessor layout, performs one SQL head CAS containing the
state and authority guards, inserts the publication/nullifier/effect rows,
reopens the staged layout, and commits.  Any failure rolls the whole attempt
back to the predecessor.

The adapter is an isolated model port.  It does not prove production
authentication, filesystem durability, concurrent linearizability under a
production configuration, crash recovery, or value movement.
"""

from __future__ import annotations

import json
import sqlite3
from dataclasses import dataclass
from pathlib import Path
from typing import Final, TypeAlias, cast

from src.core.fcis_m6_e03_unique_commit_port import E03EffectSpecV1
from src.core.fcis_m6_e04_retry_classifier import (
    E04AttemptV1,
    E04ClientKnowledgeV1,
    E04DurableOutcomeV1,
    E04Error,
    E04StoredStateV1,
    classify_e04_retry,
    is_verified_e04_stored_state_v1,
)
from src.core.fcis_m6_e05_expected_root_cas import (
    E05CodeV1,
    E05CommitReceiptV1,
    E05Error,
    E05PublicationRequestV1,
    E05RejectV1,
    E05ResultV1,
    e05_publication_set_root,
)
from src.state.canonical import canonical_json_bytes

MAX_E05_TRANSITIONS_V1: Final = 128
MAX_E05_EFFECTS_V1: Final = 128
MAX_E05_U32_V1: Final = (1 << 32) - 1
MAX_E05_TEXT_BYTES_V1: Final = 4096
MAX_E05_ATTEMPT_BYTES_V1: Final = 2 * 1024 * 1024
_ROOT_HEX = frozenset("0123456789abcdef")
_ROOT = Path(__file__).resolve().parents[1]


class E05StorageError(E05Error):
    """The SQLite layout is not a canonical E05 state."""


@dataclass(frozen=True, slots=True)
class E05EffectRowV1:
    """One normalized effect projection owned by one E05 publication."""

    effect_id: str
    commit_id: str
    ordinal: int
    destination: str
    payload_root: str
    writer_profile_root: str
    adapter_profile_root: str

    def __post_init__(self) -> None:
        _digest(self.effect_id, "effect_id")
        _digest(self.commit_id, "commit_id")
        _u32(self.ordinal, "ordinal")
        if self.ordinal >= MAX_E05_EFFECTS_V1:
            raise E05Error("effect ordinal exceeds the closed bound")
        _text(self.destination, "destination")
        for name in ("payload_root", "writer_profile_root", "adapter_profile_root"):
            _digest(getattr(self, name), name)

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "effect_id": self.effect_id,
            "commit_id": self.commit_id,
            "ordinal": self.ordinal,
            "destination": self.destination,
            "payload_root": self.payload_root,
            "writer_profile_root": self.writer_profile_root,
            "adapter_profile_root": self.adapter_profile_root,
        }


@dataclass(frozen=True, slots=True)
class E05PublicationRowV1:
    """Complete durable projection for one verified E04 attempt."""

    sequence: int
    attempt_root: str
    fingerprint: str
    commit_id: str
    nullifier_root: str
    request_identity_root: str
    expected_pre_root: str
    post_state_root: str
    writer_profile_root: str
    authority_epoch_index: int
    authority_state_root: str
    deployment_config_root: str
    verifier_profile_root: str
    attempt_wire: bytes
    effects: tuple[E05EffectRowV1, ...]

    def __post_init__(self) -> None:
        if type(self.sequence) is not int or not 1 <= self.sequence <= MAX_E05_TRANSITIONS_V1:
            raise E05Error("publication sequence is outside the closed bound")
        for name in (
            "attempt_root",
            "fingerprint",
            "commit_id",
            "nullifier_root",
            "request_identity_root",
            "expected_pre_root",
            "post_state_root",
            "writer_profile_root",
            "authority_state_root",
            "deployment_config_root",
            "verifier_profile_root",
        ):
            _digest(getattr(self, name), name)
        if type(self.attempt_wire) is not bytes:
            raise E05Error("attempt_wire must be an exact bytes value")
        if not self.attempt_wire or len(self.attempt_wire) > MAX_E05_ATTEMPT_BYTES_V1:
            raise E05Error("attempt_wire is outside the closed byte bound")
        try:
            decoded = json.loads(self.attempt_wire)
        except (UnicodeDecodeError, json.JSONDecodeError, TypeError) as exc:
            raise E05Error("attempt_wire is not canonical JSON") from exc
        if type(decoded) is not dict or canonical_json_bytes(decoded) != self.attempt_wire:
            raise E05Error("attempt_wire is not a canonical object")
        body = cast(dict[str, object], decoded)
        if set(body) != {
            "attempt_root",
            "authority_state_root",
            "commit",
            "expected_pre_root",
            "publication_sequence",
            "request_identity",
            "schema",
            "sequence_binding",
            "verifier_profile_root",
            "writer_profile_root",
        }:
            raise E05Error("attempt_wire has an unexpected field set")
        if (
            body["attempt_root"] != self.attempt_root
            or body["expected_pre_root"] != self.expected_pre_root
            or body["publication_sequence"] != self.sequence
            or body["authority_state_root"] != self.authority_state_root
            or body["writer_profile_root"] != self.writer_profile_root
            or body["verifier_profile_root"] != self.verifier_profile_root
        ):
            raise E05Error("attempt_wire header is crossed with the publication row")
        identity = body["request_identity"]
        if type(identity) is not dict:
            raise E05Error("attempt_wire request identity is not an object")
        identity_map = cast(dict[str, object], identity)
        if (
            identity_map.get("request_identity_root") != self.request_identity_root
            or identity_map.get("authority_epoch_index") != self.authority_epoch_index
            or identity_map.get("deployment_config_root") != self.deployment_config_root
        ):
            raise E05Error("attempt_wire request identity is crossed with the row")
        commit = body["commit"]
        if type(commit) is not dict:
            raise E05Error("attempt_wire commit is not an object")
        commit_map = cast(dict[str, object], commit)
        if (
            commit_map.get("commit_id") != self.commit_id
            or commit_map.get("nullifier_root") != self.nullifier_root
            or commit_map.get("request_identity_root") != self.request_identity_root
            or commit_map.get("sequence") != self.sequence
        ):
            raise E05Error("attempt_wire commit is crossed with the row")
        raw_effects = commit_map.get("effects")
        if type(raw_effects) is not list or len(raw_effects) != len(self.effects):
            raise E05Error("attempt_wire effect cardinality differs from the row")
        for raw_effect, effect in zip(raw_effects, self.effects, strict=True):
            if type(raw_effect) is not dict:
                raise E05Error("attempt_wire effect is not an object")
            effect_map = cast(dict[str, object], raw_effect)
            if (
                effect_map.get("effect_id") != effect.effect_id
                or effect_map.get("ordinal") != effect.ordinal
                or effect_map.get("destination") != effect.destination
                or effect_map.get("payload_root") != effect.payload_root
                or effect_map.get("writer_profile_root") != effect.writer_profile_root
                or effect_map.get("adapter_profile_root") != effect.adapter_profile_root
            ):
                raise E05Error("attempt_wire effect is crossed with the row")
        if (
            type(self.authority_epoch_index) is not int
            or not 0 <= self.authority_epoch_index <= MAX_E05_U32_V1
        ):
            raise E05Error("authority_epoch_index is outside the closed u32 domain")
        if type(self.effects) is not tuple:
            raise E05Error("effects must be an exact tuple")
        if len(self.effects) > MAX_E05_EFFECTS_V1:
            raise E05Error("effects exceed the closed bound")
        if tuple(effect.ordinal for effect in self.effects) != tuple(range(len(self.effects))):
            raise E05Error("effects must be contiguous and canonically ordered")
        if any(effect.commit_id != self.commit_id for effect in self.effects):
            raise E05Error("effect is crossed with its publication")
        if len({effect.effect_id for effect in self.effects}) != len(self.effects):
            raise E05Error("effect IDs must be unique")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "sequence": self.sequence,
            "attempt_root": self.attempt_root,
            "fingerprint": self.fingerprint,
            "commit_id": self.commit_id,
            "nullifier_root": self.nullifier_root,
            "request_identity_root": self.request_identity_root,
            "expected_pre_root": self.expected_pre_root,
            "post_state_root": self.post_state_root,
            "writer_profile_root": self.writer_profile_root,
            "authority_epoch_index": self.authority_epoch_index,
            "authority_state_root": self.authority_state_root,
            "deployment_config_root": self.deployment_config_root,
            "verifier_profile_root": self.verifier_profile_root,
            "attempt_wire_hex": self.attempt_wire.hex(),
            "effects": [effect.to_wire() for effect in self.effects],
        }


@dataclass(frozen=True, slots=True)
class E05DurableStateV1:
    """Canonical SQLite head plus its complete publication projections."""

    current_state_root: str
    snapshot_root: str
    authority_epoch_index: int
    authority_state_root: str
    deployment_config_root: str
    verifier_profile_root: str
    next_publication_sequence: int
    publication_set_root: str
    publications: tuple[E05PublicationRowV1, ...]

    def __post_init__(self) -> None:
        for name in (
            "current_state_root",
            "snapshot_root",
            "authority_state_root",
            "deployment_config_root",
            "verifier_profile_root",
            "publication_set_root",
        ):
            _digest(getattr(self, name), name)
        if (
            type(self.authority_epoch_index) is not int
            or not 0 <= self.authority_epoch_index <= MAX_E05_U32_V1
        ):
            raise E05Error("authority_epoch_index is outside the closed u32 domain")
        if (
            type(self.next_publication_sequence) is not int
            or not 1 <= self.next_publication_sequence <= MAX_E05_TRANSITIONS_V1 + 1
        ):
            raise E05Error("next_publication_sequence is outside the closed bound")
        if type(self.publications) is not tuple:
            raise E05Error("publications must be an exact tuple")
        if len(self.publications) >= MAX_E05_TRANSITIONS_V1 + 1:
            raise E05Error("publications exceed the closed bound")
        if tuple(row.sequence for row in self.publications) != tuple(
            range(1, len(self.publications) + 1)
        ):
            raise E05Error("publication sequences are not contiguous")
        expected_root = e05_publication_set_root(tuple(row.to_wire() for row in self.publications))
        if expected_root != self.publication_set_root:
            raise E05Error("publication_set_root does not rederive")
        if self.publications and self.publications[-1].post_state_root != self.current_state_root:
            raise E05Error("head state root is not the last publication successor")
        if self.next_publication_sequence != len(self.publications) + 1:
            raise E05Error("next publication sequence does not match row count")


E05StoredResultV1: TypeAlias = E05DurableStateV1


def _digest(value: object, name: str) -> None:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in _ROOT_HEX for character in value)
    ):
        raise E05Error(f"{name} must be a lowercase SHA-256 digest")


def _u32(value: object, name: str) -> None:
    if type(value) is not int or value < 0 or value > MAX_E05_U32_V1:
        raise E05Error(f"{name} is outside the closed u32 domain")


def _text(value: object, name: str) -> None:
    if type(value) is not str or not value:
        raise E05Error(f"{name} must be a nonempty exact string")
    encoded = value.encode("utf-8")
    if len(encoded) > MAX_E05_TEXT_BYTES_V1:
        raise E05Error(f"{name} exceeds the closed byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise E05Error(f"{name} contains a control character")


def _empty_publication_set_root() -> str:
    return e05_publication_set_root(())


def _effect_row(commit_id: str, effect: E03EffectSpecV1) -> E05EffectRowV1:
    return E05EffectRowV1(
        effect_id=effect.derive_effect_id(commit_id),
        commit_id=commit_id,
        ordinal=effect.ordinal,
        destination=effect.destination,
        payload_root=effect.payload_root,
        writer_profile_root=effect.writer_profile_root,
        adapter_profile_root=effect.adapter_profile_root,
    )


def _row_from_attempt(attempt: object, post_state_root: str) -> E05PublicationRowV1:
    if not hasattr(attempt, "commit") or not hasattr(attempt, "attempt_root"):
        raise E05Error("attempt has no E04 publication surface")
    exact = cast(E04AttemptV1, attempt)
    exact._validate_fields()
    _digest(post_state_root, "post_state_root")
    commit = exact.commit
    return E05PublicationRowV1(
        sequence=exact.publication_sequence,
        attempt_root=exact.attempt_root,
        fingerprint=exact.fingerprint,
        commit_id=commit.commit_id,
        nullifier_root=commit.nullifier.nullifier_root,
        request_identity_root=exact.request_identity.request_identity_root,
        expected_pre_root=exact.expected_pre_root,
        post_state_root=post_state_root,
        writer_profile_root=exact.writer_profile_root,
        authority_epoch_index=exact.request_identity.authority_epoch_index,
        authority_state_root=exact.authority_state_root,
        deployment_config_root=exact.request_identity.deployment_config_root,
        verifier_profile_root=exact.verifier_profile_root,
        attempt_wire=canonical_json_bytes(exact.to_wire()),
        effects=tuple(_effect_row(commit.commit_id, effect) for effect in commit.effects),
    )


def _rows_from_state(state: E04StoredStateV1) -> tuple[E05PublicationRowV1, ...]:
    if not is_verified_e04_stored_state_v1(state):
        raise E05Error("state lacks E04 verifier provenance")
    return tuple(_row_from_attempt(item.attempt, item.post_state_root) for item in state.commits)


def _head_for_state(
    state: E04StoredStateV1,
    publications: tuple[E05PublicationRowV1, ...],
) -> E05DurableStateV1:
    return E05DurableStateV1(
        current_state_root=state.current_state_root,
        snapshot_root=state.snapshot_root,
        authority_epoch_index=state.authority_epoch_index,
        authority_state_root=state.authority_state_root,
        deployment_config_root=state.deployment_config_root,
        verifier_profile_root=state.verifier_profile_root,
        next_publication_sequence=len(publications) + 1,
        publication_set_root=e05_publication_set_root(tuple(row.to_wire() for row in publications)),
        publications=publications,
    )


def _reject(code: E05CodeV1, *path: str) -> E05RejectV1:
    return E05RejectV1(code=code, path=tuple(path))


def _is_constraint_error(error: sqlite3.IntegrityError) -> bool:
    message = str(error)
    return any(
        marker in message
        for marker in (
            "UNIQUE constraint failed",
            "CHECK constraint failed",
            "NOT NULL constraint failed",
            "FOREIGN KEY constraint failed",
        )
    )


def _schema_sql() -> str:
    return f"""
CREATE TABLE IF NOT EXISTS e05_head (
    singleton INTEGER PRIMARY KEY CHECK(singleton = 1),
    current_state_root TEXT NOT NULL CHECK(length(current_state_root) = 64 AND current_state_root NOT GLOB '*[^0-9a-f]*'),
    snapshot_root TEXT NOT NULL CHECK(length(snapshot_root) = 64 AND snapshot_root NOT GLOB '*[^0-9a-f]*'),
    authority_epoch_index INTEGER NOT NULL CHECK(authority_epoch_index BETWEEN 0 AND {MAX_E05_U32_V1}),
    authority_state_root TEXT NOT NULL CHECK(length(authority_state_root) = 64 AND authority_state_root NOT GLOB '*[^0-9a-f]*'),
    deployment_config_root TEXT NOT NULL CHECK(length(deployment_config_root) = 64 AND deployment_config_root NOT GLOB '*[^0-9a-f]*'),
    verifier_profile_root TEXT NOT NULL CHECK(length(verifier_profile_root) = 64 AND verifier_profile_root NOT GLOB '*[^0-9a-f]*'),
    next_publication_sequence INTEGER NOT NULL CHECK(next_publication_sequence BETWEEN 1 AND {MAX_E05_TRANSITIONS_V1 + 1}),
    publication_set_root TEXT NOT NULL CHECK(length(publication_set_root) = 64 AND publication_set_root NOT GLOB '*[^0-9a-f]*')
);

CREATE TABLE IF NOT EXISTS e05_publications (
    sequence INTEGER PRIMARY KEY CHECK(sequence BETWEEN 1 AND {MAX_E05_TRANSITIONS_V1}),
    attempt_root TEXT NOT NULL UNIQUE CHECK(length(attempt_root) = 64 AND attempt_root NOT GLOB '*[^0-9a-f]*'),
    fingerprint TEXT NOT NULL CHECK(length(fingerprint) = 64 AND fingerprint NOT GLOB '*[^0-9a-f]*'),
    commit_id TEXT NOT NULL UNIQUE CHECK(length(commit_id) = 64 AND commit_id NOT GLOB '*[^0-9a-f]*'),
    nullifier_root TEXT NOT NULL CHECK(length(nullifier_root) = 64 AND nullifier_root NOT GLOB '*[^0-9a-f]*'),
    request_identity_root TEXT NOT NULL CHECK(length(request_identity_root) = 64 AND request_identity_root NOT GLOB '*[^0-9a-f]*'),
    expected_pre_root TEXT NOT NULL CHECK(length(expected_pre_root) = 64 AND expected_pre_root NOT GLOB '*[^0-9a-f]*'),
    post_state_root TEXT NOT NULL CHECK(length(post_state_root) = 64 AND post_state_root NOT GLOB '*[^0-9a-f]*'),
    writer_profile_root TEXT NOT NULL CHECK(length(writer_profile_root) = 64 AND writer_profile_root NOT GLOB '*[^0-9a-f]*'),
    authority_epoch_index INTEGER NOT NULL CHECK(authority_epoch_index BETWEEN 0 AND {MAX_E05_U32_V1}),
    authority_state_root TEXT NOT NULL CHECK(length(authority_state_root) = 64 AND authority_state_root NOT GLOB '*[^0-9a-f]*'),
    deployment_config_root TEXT NOT NULL CHECK(length(deployment_config_root) = 64 AND deployment_config_root NOT GLOB '*[^0-9a-f]*'),
    verifier_profile_root TEXT NOT NULL CHECK(length(verifier_profile_root) = 64 AND verifier_profile_root NOT GLOB '*[^0-9a-f]*'),
    attempt_wire BLOB NOT NULL CHECK(length(attempt_wire) BETWEEN 1 AND {MAX_E05_ATTEMPT_BYTES_V1}),
    UNIQUE(nullifier_root)
);

CREATE TABLE IF NOT EXISTS e05_nullifiers (
    nullifier_root TEXT PRIMARY KEY CHECK(length(nullifier_root) = 64 AND nullifier_root NOT GLOB '*[^0-9a-f]*'),
    commit_id TEXT NOT NULL REFERENCES e05_publications(commit_id),
    fingerprint TEXT NOT NULL CHECK(length(fingerprint) = 64 AND fingerprint NOT GLOB '*[^0-9a-f]*'),
    UNIQUE(commit_id)
);

CREATE TABLE IF NOT EXISTS e05_effects (
    effect_id TEXT PRIMARY KEY CHECK(length(effect_id) = 64 AND effect_id NOT GLOB '*[^0-9a-f]*'),
    commit_id TEXT NOT NULL REFERENCES e05_publications(commit_id),
    ordinal INTEGER NOT NULL CHECK(ordinal BETWEEN 0 AND {MAX_E05_EFFECTS_V1 - 1}),
    destination TEXT NOT NULL CHECK(length(CAST(destination AS BLOB)) BETWEEN 1 AND {MAX_E05_TEXT_BYTES_V1}),
    payload_root TEXT NOT NULL CHECK(length(payload_root) = 64 AND payload_root NOT GLOB '*[^0-9a-f]*'),
    writer_profile_root TEXT NOT NULL CHECK(length(writer_profile_root) = 64 AND writer_profile_root NOT GLOB '*[^0-9a-f]*'),
    adapter_profile_root TEXT NOT NULL CHECK(length(adapter_profile_root) = 64 AND adapter_profile_root NOT GLOB '*[^0-9a-f]*'),
    UNIQUE(commit_id, ordinal)
);
"""


def create_connection(path: str | Path = ":memory:") -> sqlite3.Connection:
    connection = sqlite3.connect(str(path), isolation_level=None, timeout=5.0)
    connection.execute("PRAGMA foreign_keys = ON")
    connection.executescript(_schema_sql())
    return connection


def _insert_row(connection: sqlite3.Connection, row: E05PublicationRowV1) -> None:
    row.__post_init__()
    connection.execute(
        """
        INSERT INTO e05_publications(
            sequence, attempt_root, fingerprint, commit_id, nullifier_root,
            request_identity_root, expected_pre_root, post_state_root,
            writer_profile_root, authority_epoch_index, authority_state_root,
            deployment_config_root, verifier_profile_root, attempt_wire
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            row.sequence,
            row.attempt_root,
            row.fingerprint,
            row.commit_id,
            row.nullifier_root,
            row.request_identity_root,
            row.expected_pre_root,
            row.post_state_root,
            row.writer_profile_root,
            row.authority_epoch_index,
            row.authority_state_root,
            row.deployment_config_root,
            row.verifier_profile_root,
            row.attempt_wire,
        ),
    )
    connection.execute(
        "INSERT INTO e05_nullifiers(nullifier_root, commit_id, fingerprint) VALUES (?, ?, ?)",
        (row.nullifier_root, row.commit_id, row.fingerprint),
    )
    connection.executemany(
        """
        INSERT INTO e05_effects(
            effect_id, commit_id, ordinal, destination, payload_root,
            writer_profile_root, adapter_profile_root
        ) VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (
            (
                effect.effect_id,
                effect.commit_id,
                effect.ordinal,
                effect.destination,
                effect.payload_root,
                effect.writer_profile_root,
                effect.adapter_profile_root,
            )
            for effect in row.effects
        ),
    )


def _insert_head(connection: sqlite3.Connection, state: E05DurableStateV1) -> None:
    connection.execute(
        """
        INSERT INTO e05_head(
            singleton, current_state_root, snapshot_root,
            authority_epoch_index, authority_state_root,
            deployment_config_root, verifier_profile_root,
            next_publication_sequence, publication_set_root
        ) VALUES (1, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            state.current_state_root,
            state.snapshot_root,
            state.authority_epoch_index,
            state.authority_state_root,
            state.deployment_config_root,
            state.verifier_profile_root,
            state.next_publication_sequence,
            state.publication_set_root,
        ),
    )


def _read_row(connection: sqlite3.Connection, commit_id: str) -> E05PublicationRowV1:
    row = connection.execute(
        """
        SELECT sequence, attempt_root, fingerprint, commit_id, nullifier_root,
               request_identity_root, expected_pre_root, post_state_root,
               writer_profile_root, authority_epoch_index, authority_state_root,
               deployment_config_root, verifier_profile_root, attempt_wire
        FROM e05_publications WHERE commit_id = ?
        """,
        (commit_id,),
    ).fetchone()
    if row is None:
        raise E05StorageError("publication row is absent")
    if type(row[13]) is not bytes:
        raise E05StorageError("attempt_wire is not stored as BLOB bytes")
    effects = tuple(
        E05EffectRowV1(
            effect_id=effect[0],
            commit_id=effect[1],
            ordinal=effect[2],
            destination=effect[3],
            payload_root=effect[4],
            writer_profile_root=effect[5],
            adapter_profile_root=effect[6],
        )
        for effect in connection.execute(
            """
            SELECT effect_id, commit_id, ordinal, destination, payload_root,
                   writer_profile_root, adapter_profile_root
            FROM e05_effects WHERE commit_id = ? ORDER BY ordinal
            """,
            (commit_id,),
        )
    )
    return E05PublicationRowV1(
        sequence=row[0],
        attempt_root=row[1],
        fingerprint=row[2],
        commit_id=row[3],
        nullifier_root=row[4],
        request_identity_root=row[5],
        expected_pre_root=row[6],
        post_state_root=row[7],
        writer_profile_root=row[8],
        authority_epoch_index=row[9],
        authority_state_root=row[10],
        deployment_config_root=row[11],
        verifier_profile_root=row[12],
        attempt_wire=row[13],
        effects=effects,
    )


def read_state(connection: sqlite3.Connection) -> E05DurableStateV1:
    """Reconstruct and validate the complete E05 durable projection."""

    if type(connection) is not sqlite3.Connection:
        raise E05Error("connection has the wrong exact type")
    try:
        head = connection.execute(
            """
            SELECT current_state_root, snapshot_root, authority_epoch_index,
                   authority_state_root, deployment_config_root,
                   verifier_profile_root, next_publication_sequence,
                   publication_set_root
            FROM e05_head WHERE singleton = 1
            """
        ).fetchone()
        if head is None:
            raise E05StorageError("E05 head is absent")
        commit_ids = tuple(
            row[0]
            for row in connection.execute(
                "SELECT commit_id FROM e05_publications ORDER BY sequence"
            )
        )
        publications = tuple(_read_row(connection, commit_id) for commit_id in commit_ids)
        state = E05DurableStateV1(
            current_state_root=head[0],
            snapshot_root=head[1],
            authority_epoch_index=head[2],
            authority_state_root=head[3],
            deployment_config_root=head[4],
            verifier_profile_root=head[5],
            next_publication_sequence=head[6],
            publication_set_root=head[7],
            publications=publications,
        )
        expected_nullifiers = tuple(
            sorted((row.nullifier_root, row.commit_id, row.fingerprint) for row in publications)
        )
        actual_nullifiers = tuple(
            connection.execute(
                "SELECT nullifier_root, commit_id, fingerprint FROM e05_nullifiers "
                "ORDER BY nullifier_root"
            )
        )
        if actual_nullifiers != expected_nullifiers:
            raise E05StorageError("nullifier projections differ from publications")
        expected_effects = tuple(
            sorted(
                (
                    effect.effect_id,
                    effect.commit_id,
                    effect.ordinal,
                    effect.destination,
                    effect.payload_root,
                    effect.writer_profile_root,
                    effect.adapter_profile_root,
                )
                for row in publications
                for effect in row.effects
            )
        )
        actual_effects = tuple(
            connection.execute(
                "SELECT effect_id, commit_id, ordinal, destination, payload_root, "
                "writer_profile_root, adapter_profile_root FROM e05_effects "
                "ORDER BY effect_id"
            )
        )
        if actual_effects != expected_effects:
            raise E05StorageError("effect projections differ from publications")
        return state
    except E05StorageError:
        raise
    except E05Error as exc:
        raise E05StorageError(f"E05 durable state is malformed: {exc}") from exc
    except (TypeError, ValueError, sqlite3.Error) as exc:
        raise E05StorageError("E05 durable state is malformed") from exc


def initialize_database(
    connection: sqlite3.Connection,
    state: E04StoredStateV1,
) -> None:
    """Seed one canonical E04 state as the E05 predecessor layout."""

    if type(connection) is not sqlite3.Connection:
        raise E05Error("connection has the wrong exact type")
    if type(state) is not E04StoredStateV1 or not is_verified_e04_stored_state_v1(state):
        raise E05Error("initial state lacks E04 verifier provenance")
    rows = _rows_from_state(state)
    expected = _head_for_state(state, rows)
    try:
        connection.execute("BEGIN")
        if connection.execute("SELECT 1 FROM e05_head LIMIT 1").fetchone() is not None:
            raise E05StorageError("E05 database is not empty")
        _insert_head(connection, expected)
        for row in rows:
            _insert_row(connection, row)
        if read_state(connection) != expected:
            raise E05StorageError("seed rows do not reopen to the exact seed state")
        connection.commit()
    except (E05Error, sqlite3.Error):
        connection.rollback()
        raise


def create_database(state: E04StoredStateV1) -> sqlite3.Connection:
    connection = create_connection()
    initialize_database(connection, state)
    return connection


def _same_head(left: E05DurableStateV1, right: E05DurableStateV1) -> bool:
    return (
        left.current_state_root == right.current_state_root
        and left.snapshot_root == right.snapshot_root
        and left.authority_epoch_index == right.authority_epoch_index
        and left.authority_state_root == right.authority_state_root
        and left.deployment_config_root == right.deployment_config_root
        and left.verifier_profile_root == right.verifier_profile_root
        and left.next_publication_sequence == right.next_publication_sequence
        and left.publication_set_root == right.publication_set_root
    )


def _cas_update(
    connection: sqlite3.Connection,
    before: E05DurableStateV1,
    after: E05DurableStateV1,
) -> bool:
    cursor = connection.execute(
        """
        UPDATE e05_head
        SET current_state_root = ?, snapshot_root = ?,
            authority_epoch_index = ?, authority_state_root = ?,
            deployment_config_root = ?, verifier_profile_root = ?,
            next_publication_sequence = ?, publication_set_root = ?
        WHERE singleton = 1
          AND current_state_root = ?
          AND snapshot_root = ?
          AND authority_epoch_index = ?
          AND authority_state_root = ?
          AND deployment_config_root = ?
          AND verifier_profile_root = ?
          AND next_publication_sequence = ?
          AND publication_set_root = ?
        """,
        (
            after.current_state_root,
            after.snapshot_root,
            after.authority_epoch_index,
            after.authority_state_root,
            after.deployment_config_root,
            after.verifier_profile_root,
            after.next_publication_sequence,
            after.publication_set_root,
            before.current_state_root,
            before.snapshot_root,
            before.authority_epoch_index,
            before.authority_state_root,
            before.deployment_config_root,
            before.verifier_profile_root,
            before.next_publication_sequence,
            before.publication_set_root,
        ),
    )
    return cursor.rowcount == 1


def publish(
    connection: sqlite3.Connection,
    request: object,
) -> E05ResultV1:
    """Publish one E04 successor through the expected-root atomic CAS."""

    if type(connection) is not sqlite3.Connection:
        return _reject(E05CodeV1.INVALID_REQUEST, "connection")
    if type(request) is not E05PublicationRequestV1:
        return _reject(E05CodeV1.INVALID_REQUEST, "request")
    exact_request = request
    try:
        exact_request.__post_init__()
    except (AttributeError, E04Error, E05Error, TypeError, ValueError, ArithmeticError):
        return _reject(E05CodeV1.INVALID_REQUEST, "request")

    try:
        connection.execute("BEGIN IMMEDIATE")
        classification = classify_e04_retry(
            exact_request.attempt,
            exact_request.pre_state,
            E04ClientKnowledgeV1.CONFIRMED,
            exact_request.reopen_receipt,
        )
        if getattr(classification, "outcome", None) is not E04DurableOutcomeV1.ABSENT_RETRYABLE:
            connection.rollback()
            return _reject(E05CodeV1.CLASSIFIER_REJECTED, "e04_classifier")

        actual_before = read_state(connection)
        expected_before = _head_for_state(
            exact_request.pre_state,
            _rows_from_state(exact_request.pre_state),
        )
        if actual_before.snapshot_root != expected_before.snapshot_root:
            connection.rollback()
            return _reject(E05CodeV1.STALE_SNAPSHOT_CAS, "snapshot_root")
        if actual_before.current_state_root != expected_before.current_state_root:
            connection.rollback()
            return _reject(E05CodeV1.STALE_STATE_CAS, "current_state_root")
        if (
            actual_before.authority_epoch_index != expected_before.authority_epoch_index
            or actual_before.authority_state_root != expected_before.authority_state_root
            or actual_before.deployment_config_root != expected_before.deployment_config_root
            or actual_before.verifier_profile_root != expected_before.verifier_profile_root
        ):
            connection.rollback()
            return _reject(E05CodeV1.STALE_AUTHORITY_CAS, "authority_context")
        if actual_before.publications != expected_before.publications:
            connection.rollback()
            return _reject(E05CodeV1.STALE_SNAPSHOT_CAS, "publication_rows")

        new_row = _row_from_attempt(
            exact_request.attempt,
            exact_request.post_state.current_state_root,
        )
        expected_after = _head_for_state(
            exact_request.post_state,
            expected_before.publications + (new_row,),
        )
        if not _cas_update(connection, expected_before, expected_after):
            connection.rollback()
            return _reject(E05CodeV1.STALE_STATE_CAS, "sql_cas")
        _insert_row(connection, new_row)
        actual_after = read_state(connection)
        if (
            not _same_head(actual_after, expected_after)
            or actual_after.publications != expected_after.publications
        ):
            raise E05StorageError("staged E05 rows differ from the exact successor")
        connection.commit()
        return E05CommitReceiptV1(
            attempt_root=new_row.attempt_root,
            post_snapshot_root=expected_after.snapshot_root,
            post_state_root=expected_after.current_state_root,
            authority_epoch_index=expected_after.authority_epoch_index,
            publication_sequence=new_row.sequence,
            publication_set_root=expected_after.publication_set_root,
        )
    except sqlite3.IntegrityError as exc:
        connection.rollback()
        if _is_constraint_error(exc):
            return _reject(E05CodeV1.CONSTRAINT_COLLISION, "uniqueness")
        return _reject(E05CodeV1.SQL_ROLLBACK, "transaction")
    except (E05Error, E04Error, TypeError, ValueError, ArithmeticError, sqlite3.Error):
        connection.rollback()
        return _reject(E05CodeV1.SQL_ROLLBACK, "transaction")


__all__ = (
    "E05DurableStateV1",
    "E05EffectRowV1",
    "E05PublicationRowV1",
    "E05StorageError",
    "MAX_E05_ATTEMPT_BYTES_V1",
    "MAX_E05_EFFECTS_V1",
    "MAX_E05_TRANSITIONS_V1",
    "create_connection",
    "create_database",
    "initialize_database",
    "publish",
    "read_state",
)

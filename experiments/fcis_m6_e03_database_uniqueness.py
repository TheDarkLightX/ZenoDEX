"""Research-only SQLite shell for the FCIS M6 E03 uniqueness contract.

The adapter publishes one E03 identity aggregate in one transaction.  SQLite
primary keys, unique constraints, and foreign keys own the final collision
decision; the Python pre-checker never substitutes for those constraints.
This module does not provide production durability, authentication, runtime
reachability, or value movement.
"""

from __future__ import annotations

import sqlite3
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Final, TypeAlias, cast

from src.core.fcis_m6_e03_unique_commit_port import (
    E03CommitIdentityV1,
    E03Error,
    is_verified_e03_commit_identity_v1,
)

_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MIGRATION_PATH: Final = Path("config/deploy/fcis_m6_e03_uniqueness_v1.sql")
SQLITE_TIMEOUT_SECONDS: Final = 5.0


class E03DatabaseCodeV1(Enum):
    """Typed outcomes of the isolated unique-commit persistence port."""

    COMMITTED = "committed"
    INVALID_REQUEST = "invalid_request"
    CONSTRAINT_COLLISION = "constraint_collision"
    SQL_ROLLBACK = "sql_rollback"


@dataclass(frozen=True, slots=True)
class E03CommitV1:
    """Immutable receipt for one successful E03 identity insertion."""

    commit_id: str
    fingerprint: str
    nullifier_root: str
    effect_ids: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class E03RejectV1:
    """Typed failure with a stable reason and semantic path."""

    code: E03DatabaseCodeV1
    path: tuple[str, ...]


E03ResultV1: TypeAlias = E03CommitV1 | E03RejectV1


def migration_sql(path: Path = _ROOT / DEFAULT_MIGRATION_PATH) -> str:
    """Load the source-pinned migration used by the research adapter."""

    try:
        value = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise E03Error("E03 migration SQL cannot be read") from exc
    if not value or not value.endswith("\n"):
        raise E03Error("E03 migration SQL must be nonempty and newline terminated")
    return value


def create_e03_connection(path: str | Path = ":memory:") -> sqlite3.Connection:
    """Create a research connection and apply the exact E03 migration."""

    connection = sqlite3.connect(
        str(path),
        isolation_level=None,
        timeout=SQLITE_TIMEOUT_SECONDS,
    )
    connection.execute("PRAGMA foreign_keys = ON")
    connection.executescript(migration_sql())
    return connection


def _reject(code: E03DatabaseCodeV1, *path: str) -> E03RejectV1:
    return E03RejectV1(code=code, path=tuple(path))


def _is_constraint_error(error: sqlite3.IntegrityError) -> bool:
    message = str(error)
    return any(
        marker in message
        for marker in (
            "UNIQUE constraint failed",
            "FOREIGN KEY constraint failed",
            "CHECK constraint failed",
            "NOT NULL constraint failed",
        )
    )


def _effect_rows(identity: E03CommitIdentityV1) -> tuple[tuple[object, ...], ...]:
    return tuple(
        (
            effect.derive_effect_id(identity.commit_id),
            identity.commit_id,
            effect.ordinal,
            effect.destination,
            effect.payload_root,
            effect.writer_profile_root,
            effect.adapter_profile_root,
        )
        for effect in identity.effects
    )


def _read_counts(connection: sqlite3.Connection) -> tuple[int, int, int]:
    commits = int(connection.execute("SELECT COUNT(*) FROM e03_publication_commits").fetchone()[0])
    nullifiers = int(
        connection.execute("SELECT COUNT(*) FROM e03_publication_nullifiers").fetchone()[0]
    )
    effects = int(connection.execute("SELECT COUNT(*) FROM e03_publication_effects").fetchone()[0])
    return commits, nullifiers, effects


def read_e03_counts(connection: sqlite3.Connection) -> tuple[int, int, int]:
    """Return commit, nullifier, and effect row counts for test inspection."""

    if type(connection) is not sqlite3.Connection:
        raise E03Error("connection has the wrong exact type")
    try:
        return _read_counts(connection)
    except sqlite3.Error as exc:
        raise E03Error("E03 table counts cannot be read") from exc


def _verify_staged_rows(
    connection: sqlite3.Connection,
    identity: E03CommitIdentityV1,
) -> None:
    expected_commit = (
        identity.sequence,
        identity.commit_id,
        identity.fingerprint,
        identity.nullifier.nullifier_root,
        identity.nullifier.request_identity_root,
    )
    actual_commit = connection.execute(
        """
        SELECT sequence, commit_id, fingerprint, nullifier_root,
               request_identity_root
        FROM e03_publication_commits WHERE commit_id = ?
        """,
        (identity.commit_id,),
    ).fetchone()
    if actual_commit != expected_commit:
        raise E03Error("staged commit row differs from the canonical identity")

    actual_nullifier = connection.execute(
        """
        SELECT nullifier_root, commit_id, fingerprint
        FROM e03_publication_nullifiers WHERE nullifier_root = ?
        """,
        (identity.nullifier.nullifier_root,),
    ).fetchone()
    if actual_nullifier != (
        identity.nullifier.nullifier_root,
        identity.commit_id,
        identity.fingerprint,
    ):
        raise E03Error("staged nullifier row differs from the canonical identity")

    actual_effects = tuple(
        connection.execute(
            """
            SELECT effect_id, commit_id, ordinal, destination, payload_root,
                   writer_profile_root, adapter_profile_root
            FROM e03_publication_effects
            WHERE commit_id = ? ORDER BY ordinal
            """,
            (identity.commit_id,),
        )
    )
    if actual_effects != _effect_rows(identity):
        raise E03Error("staged effect rows differ from the canonical identity")


def persist_e03_commit(
    connection: sqlite3.Connection,
    candidate: object,
) -> E03ResultV1:
    """Atomically insert one verified identity or return a typed rejection."""

    if type(connection) is not sqlite3.Connection:
        return _reject(E03DatabaseCodeV1.INVALID_REQUEST, "connection")
    if not is_verified_e03_commit_identity_v1(candidate):
        return _reject(E03DatabaseCodeV1.INVALID_REQUEST, "candidate")
    identity = cast(E03CommitIdentityV1, candidate)
    try:
        identity._validate_fields()
    except (AttributeError, E03Error, TypeError, ValueError, ArithmeticError):
        return _reject(E03DatabaseCodeV1.INVALID_REQUEST, "candidate")

    try:
        connection.execute("BEGIN IMMEDIATE")
        connection.execute(
            """
            INSERT INTO e03_publication_commits(
                sequence, commit_id, fingerprint, nullifier_root,
                request_identity_root
            ) VALUES (?, ?, ?, ?, ?)
            """,
            (
                identity.sequence,
                identity.commit_id,
                identity.fingerprint,
                identity.nullifier.nullifier_root,
                identity.nullifier.request_identity_root,
            ),
        )
        connection.execute(
            """
            INSERT INTO e03_publication_nullifiers(
                nullifier_root, commit_id, fingerprint
            ) VALUES (?, ?, ?)
            """,
            (
                identity.nullifier.nullifier_root,
                identity.commit_id,
                identity.fingerprint,
            ),
        )
        connection.executemany(
            """
            INSERT INTO e03_publication_effects(
                effect_id, commit_id, ordinal, destination, payload_root,
                writer_profile_root, adapter_profile_root
            ) VALUES (?, ?, ?, ?, ?, ?, ?)
            """,
            _effect_rows(identity),
        )
        _verify_staged_rows(connection, identity)
        connection.commit()
        return E03CommitV1(
            commit_id=identity.commit_id,
            fingerprint=identity.fingerprint,
            nullifier_root=identity.nullifier.nullifier_root,
            effect_ids=tuple(
                effect.derive_effect_id(identity.commit_id) for effect in identity.effects
            ),
        )
    except E03Error:
        connection.rollback()
        return _reject(E03DatabaseCodeV1.SQL_ROLLBACK, "staged_rows")
    except sqlite3.IntegrityError as exc:
        connection.rollback()
        if _is_constraint_error(exc):
            return _reject(E03DatabaseCodeV1.CONSTRAINT_COLLISION, "constraint")
        return _reject(E03DatabaseCodeV1.SQL_ROLLBACK, "integrity")
    except sqlite3.Error:
        connection.rollback()
        return _reject(E03DatabaseCodeV1.SQL_ROLLBACK, "sqlite")


__all__ = (
    "DEFAULT_MIGRATION_PATH",
    "E03CommitV1",
    "E03DatabaseCodeV1",
    "E03RejectV1",
    "E03ResultV1",
    "SQLITE_TIMEOUT_SECONDS",
    "create_e03_connection",
    "migration_sql",
    "persist_e03_commit",
    "read_e03_counts",
)

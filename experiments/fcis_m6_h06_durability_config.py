"""Fail-closed SQLite durability-profile checks for the isolated M6 harness.

The checker treats the durability assumptions as configuration evidence. It
does not claim that a local SQLite process or filesystem provides production
power-loss durability, and it does not silently repair a weak deployment
profile. The required profile is closed in this module:

    file-backed main database
    journal_mode = WAL
    synchronous = FULL (SQLite numeric value 2)
    foreign_keys = ON
    busy_timeout >= 5000 ms
    locking_mode = NORMAL
"""

from __future__ import annotations

import sqlite3
from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias

H06_REQUIRED_BUSY_TIMEOUT_MS: Final[int] = 5_000
H06_REQUIRED_SYNCHRONOUS: Final[int] = 2
H06_REQUIRED_FOREIGN_KEYS: Final[int] = 1
H06_REQUIRED_JOURNAL_MODE: Final[str] = "wal"
H06_REQUIRED_LOCKING_MODE: Final[str] = "normal"


class H06Error(ValueError):
    """Typed validation failure in the isolated H06 checker."""


class H06CodeV1(Enum):
    ACCEPTED = "accepted"
    INVALID_CONNECTION = "invalid_connection"
    TRANSACTION_OPEN = "transaction_open"
    NOT_FILE_BACKED = "not_file_backed"
    JOURNAL_MODE_MISMATCH = "journal_mode_mismatch"
    SYNCHRONOUS_MISMATCH = "synchronous_mismatch"
    FOREIGN_KEYS_DISABLED = "foreign_keys_disabled"
    BUSY_TIMEOUT_TOO_LOW = "busy_timeout_too_low"
    LOCKING_MODE_MISMATCH = "locking_mode_mismatch"
    SQL_ERROR = "sql_error"


@dataclass(frozen=True, slots=True)
class H06SQLiteObservationV1:
    database_path: str
    journal_mode: str
    synchronous: int
    foreign_keys: int
    busy_timeout_ms: int
    locking_mode: str

    def __post_init__(self) -> None:
        if type(self.database_path) is not str or not self.database_path:
            raise H06Error("database_path must be a nonempty string")
        if type(self.journal_mode) is not str:
            raise H06Error("journal_mode must be an exact string")
        if type(self.synchronous) is not int or self.synchronous < 0:
            raise H06Error("synchronous must be a nonnegative exact integer")
        if type(self.foreign_keys) is not int or self.foreign_keys not in (0, 1):
            raise H06Error("foreign_keys must be the SQLite 0/1 integer")
        if type(self.busy_timeout_ms) is not int or self.busy_timeout_ms < 0:
            raise H06Error("busy_timeout_ms must be a nonnegative exact integer")
        if type(self.locking_mode) is not str:
            raise H06Error("locking_mode must be an exact string")


@dataclass(frozen=True, slots=True)
class H06AcceptV1:
    observation: H06SQLiteObservationV1


@dataclass(frozen=True, slots=True)
class H06RejectV1:
    code: H06CodeV1
    path: tuple[str, ...]


H06ResultV1: TypeAlias = H06AcceptV1 | H06RejectV1


def _reject(code: H06CodeV1, *path: str) -> H06RejectV1:
    return H06RejectV1(code=code, path=tuple(path))


def _pragma_value(
    connection: sqlite3.Connection,
    statement: str,
    label: str,
) -> object:
    row = connection.execute(statement).fetchone()
    if row is None or len(row) != 1:
        raise H06Error(f"{label} pragma returned no scalar")
    return row[0]


def _read_observation(connection: sqlite3.Connection) -> H06SQLiteObservationV1:
    database_row = connection.execute("PRAGMA database_list").fetchone()
    if database_row is None or len(database_row) != 3:
        raise H06Error("main database identity is absent")
    database_path = database_row[2]
    if type(database_path) is not str or not database_path:
        raise H06Error("main database is not file-backed")
    journal_mode = _pragma_value(connection, "PRAGMA journal_mode", "journal_mode")
    synchronous = _pragma_value(connection, "PRAGMA synchronous", "synchronous")
    foreign_keys = _pragma_value(connection, "PRAGMA foreign_keys", "foreign_keys")
    busy_timeout_ms = _pragma_value(connection, "PRAGMA busy_timeout", "busy_timeout")
    locking_mode = _pragma_value(connection, "PRAGMA locking_mode", "locking_mode")
    if type(journal_mode) is not str:
        raise H06Error("journal_mode pragma is not a string")
    if type(synchronous) is not int:
        raise H06Error("synchronous pragma is not an exact integer")
    if type(foreign_keys) is not int:
        raise H06Error("foreign_keys pragma is not an exact integer")
    if type(busy_timeout_ms) is not int:
        raise H06Error("busy_timeout pragma is not an exact integer")
    if type(locking_mode) is not str:
        raise H06Error("locking_mode pragma is not a string")
    return H06SQLiteObservationV1(
        database_path=database_path,
        journal_mode=journal_mode.lower(),
        synchronous=synchronous,
        foreign_keys=foreign_keys,
        busy_timeout_ms=busy_timeout_ms,
        locking_mode=locking_mode.lower(),
    )


def check_sqlite_durability(connection: object) -> H06ResultV1:
    """Inspect the closed required profile without mutating the connection."""

    if type(connection) is not sqlite3.Connection:
        return _reject(H06CodeV1.INVALID_CONNECTION, "connection")
    exact_connection = connection
    if exact_connection.in_transaction:
        return _reject(H06CodeV1.TRANSACTION_OPEN, "transaction")
    try:
        observation = _read_observation(exact_connection)
    except H06Error as exc:
        message = str(exc)
        if "file-backed" in message:
            return _reject(H06CodeV1.NOT_FILE_BACKED, "database_path")
        return _reject(H06CodeV1.SQL_ERROR, "observation")
    except sqlite3.Error:
        return _reject(H06CodeV1.SQL_ERROR, "observation")
    if observation.journal_mode != H06_REQUIRED_JOURNAL_MODE:
        return _reject(H06CodeV1.JOURNAL_MODE_MISMATCH, "journal_mode")
    if observation.synchronous != H06_REQUIRED_SYNCHRONOUS:
        return _reject(H06CodeV1.SYNCHRONOUS_MISMATCH, "synchronous")
    if observation.foreign_keys != H06_REQUIRED_FOREIGN_KEYS:
        return _reject(H06CodeV1.FOREIGN_KEYS_DISABLED, "foreign_keys")
    if observation.busy_timeout_ms < H06_REQUIRED_BUSY_TIMEOUT_MS:
        return _reject(H06CodeV1.BUSY_TIMEOUT_TOO_LOW, "busy_timeout")
    if observation.locking_mode != H06_REQUIRED_LOCKING_MODE:
        return _reject(H06CodeV1.LOCKING_MODE_MISMATCH, "locking_mode")
    return H06AcceptV1(observation=observation)


def configure_sqlite_durability(connection: object) -> H06ResultV1:
    """Apply the closed research profile, then verify it through the checker."""

    if type(connection) is not sqlite3.Connection:
        return _reject(H06CodeV1.INVALID_CONNECTION, "connection")
    exact_connection = connection
    if exact_connection.in_transaction:
        return _reject(H06CodeV1.TRANSACTION_OPEN, "transaction")
    try:
        exact_connection.execute("PRAGMA journal_mode = WAL").fetchone()
        exact_connection.execute("PRAGMA synchronous = FULL")
        exact_connection.execute("PRAGMA foreign_keys = ON")
        exact_connection.execute(f"PRAGMA busy_timeout = {H06_REQUIRED_BUSY_TIMEOUT_MS}")
        exact_connection.execute("PRAGMA locking_mode = NORMAL")
    except sqlite3.Error:
        return _reject(H06CodeV1.SQL_ERROR, "configure")
    return check_sqlite_durability(exact_connection)


__all__ = (
    "H06AcceptV1",
    "H06CodeV1",
    "H06Error",
    "H06RejectV1",
    "H06ResultV1",
    "H06SQLiteObservationV1",
    "H06_REQUIRED_BUSY_TIMEOUT_MS",
    "H06_REQUIRED_FOREIGN_KEYS",
    "H06_REQUIRED_JOURNAL_MODE",
    "H06_REQUIRED_LOCKING_MODE",
    "H06_REQUIRED_SYNCHRONOUS",
    "check_sqlite_durability",
    "configure_sqlite_durability",
)

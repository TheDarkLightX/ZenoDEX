"""Shared durable current-authority head for global economic publication.

The journal is an unmounted reference control plane.  It supplies monotone,
content-addressed authority generations that ordinary epoch stores can attach
and recheck inside their SQLite commit transaction.  It does not authenticate
governance or migration decisions and therefore grants no production authority.
"""

from __future__ import annotations

import errno
import fcntl
import os
import sqlite3
import stat
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from threading import Lock
from typing import Final
from weakref import WeakKeyDictionary

from ..core.global_economic_authority_head_v1 import (
    GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V1,
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
    decode_global_economic_authority_head_v1,
    require_global_economic_authority_successor_v1,
)
from ..core.global_settlement_types_v1 import hash_global_v1

_MAX_AUTHORITY_GENERATIONS_V1: Final = 256
_MAX_AUTHORITY_STORE_BYTES_V1: Final = 2 * 1024 * 1024
_MAX_OUTSTANDING_AUTHORITY_CAS_TOKENS_V1: Final = 1024
_CAS_TOKEN_MINT_V1: Final = object()
_ATTACHED_DATABASE_V1: Final = "economic_authority"
_CREATE_METADATA_SQL_V1: Final = (
    "CREATE TABLE metadata ("
    "singleton INTEGER PRIMARY KEY CHECK (singleton = 1), "
    "schema_name TEXT NOT NULL"
    ") STRICT"
)
_CREATE_HISTORY_SQL_V1: Final = (
    "CREATE TABLE authority_history ("
    "authority_root TEXT PRIMARY KEY NOT NULL, "
    "generation_decimal TEXT NOT NULL UNIQUE, "
    "head_bytes BLOB NOT NULL"
    ") STRICT"
)
_CREATE_CURRENT_SQL_V1: Final = (
    "CREATE TABLE current_authority ("
    "singleton INTEGER PRIMARY KEY CHECK (singleton = 1), "
    "authority_root TEXT NOT NULL, "
    "FOREIGN KEY (authority_root) REFERENCES authority_history (authority_root)"
    ") STRICT"
)
_EXPECTED_TABLE_SQL_V1: Final = (
    ("authority_history", _CREATE_HISTORY_SQL_V1),
    ("current_authority", _CREATE_CURRENT_SQL_V1),
    ("metadata", _CREATE_METADATA_SQL_V1),
)
_EXPECTED_COLUMNS_V1: Final = (
    (
        "metadata",
        (
            (0, "singleton", "INTEGER", 0, None, 1),
            (1, "schema_name", "TEXT", 1, None, 0),
        ),
    ),
    (
        "authority_history",
        (
            (0, "authority_root", "TEXT", 1, None, 1),
            (1, "generation_decimal", "TEXT", 1, None, 0),
            (2, "head_bytes", "BLOB", 1, None, 0),
        ),
    ),
    (
        "current_authority",
        (
            (0, "singleton", "INTEGER", 0, None, 1),
            (1, "authority_root", "TEXT", 1, None, 0),
        ),
    ),
)


class GlobalEconomicAuthorityCommitStatusV1(str, Enum):
    COMMITTED = "COMMITTED"
    ALREADY_COMMITTED = "ALREADY_COMMITTED"
    STALE_HEAD = "STALE_HEAD"
    CAPACITY_EXCEEDED = "CAPACITY_EXCEEDED"


class GlobalEconomicAuthorityBootstrapBusyV1(RuntimeError):
    """Another cooperating installer owns the directory bootstrap lock."""


class GlobalEconomicAuthorityLegacyStoreMigrationRequiredV1(PermissionError):
    """A valid-looking legacy mode requires an explicit validated migration."""


class GlobalEconomicAuthorityBootstrapPlatformUnsupportedV1(RuntimeError):
    """Descriptor-bound recovery requires Linux O_PATH and usable procfs."""


@dataclass(frozen=True, slots=True)
class GlobalEconomicAuthorityCommitOutcomeV1:
    status: GlobalEconomicAuthorityCommitStatusV1
    head: GlobalEconomicAuthorityHeadV1
    committed_authority: GlobalEconomicAuthorityHeadV1 | None = None

    def __post_init__(self) -> None:
        if type(self.status) is not GlobalEconomicAuthorityCommitStatusV1:
            raise TypeError("global economic authority outcome status is not closed")
        if type(self.head) is not GlobalEconomicAuthorityHeadV1:
            raise TypeError("global economic authority outcome head is not closed")
        successful = {
            GlobalEconomicAuthorityCommitStatusV1.COMMITTED,
            GlobalEconomicAuthorityCommitStatusV1.ALREADY_COMMITTED,
        }
        if self.status in successful:
            if type(self.committed_authority) is not GlobalEconomicAuthorityHeadV1:
                raise TypeError("global economic authority success lacks committed head")
        elif self.committed_authority is not None:
            raise ValueError("global economic authority no-op declares a committed head")


class GlobalEconomicAuthorityCasTokenV1:
    """Process-local snapshot token; it grants no governance authorization."""

    __slots__ = ("__authority_root", "__generation", "__sealed", "__weakref__")

    def __init__(self, mint: object, authority_root: str, generation: int) -> None:
        if mint is not _CAS_TOKEN_MINT_V1:
            raise TypeError("global economic authority CAS tokens are journal-minted")
        object.__setattr__(self, "_GlobalEconomicAuthorityCasTokenV1__authority_root", authority_root)
        object.__setattr__(self, "_GlobalEconomicAuthorityCasTokenV1__generation", generation)
        object.__setattr__(self, "_GlobalEconomicAuthorityCasTokenV1__sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_GlobalEconomicAuthorityCasTokenV1__sealed", False):
            raise TypeError("global economic authority CAS tokens are immutable")
        object.__setattr__(self, name, value)


def authority_journal_path_for_epoch_v1(epoch_path: str | Path) -> Path:
    """Derive one directory-scoped authority file shared by all epoch stores."""

    normalized = _normalize_path_v1(epoch_path, name="economic epoch path")
    return normalized.parent / ".global-economic-authority-v1.sqlite"


def economic_epoch_store_root_v1(
    epoch_path: str | Path,
) -> str:
    """Bind one directory-local authority head to one named epoch store.

    The binding prevents two differently named epoch databases in one authority
    directory from each advancing an independent publication head.  It is not a
    host, backup, or rollback identity and carries no such claim.
    """

    normalized = _normalize_path_v1(epoch_path, name="economic epoch path")
    return hash_global_v1(
        "global-economic-epoch-store-v1",
        {"epoch_file_name": normalized.name},
    )


def _normalize_path_v1(path: str | Path, *, name: str) -> Path:
    if type(path) is str:
        candidate = Path(path)
    elif type(path) is type(Path()):
        candidate = Path(str(path))
    else:
        raise TypeError(f"{name} must be exact str or platform Path")
    if not candidate.name:
        raise ValueError(f"{name} must name a file")
    return candidate.absolute()


def _require_owned_regular_store_v1(path: Path, *, name: str) -> None:
    try:
        metadata = path.lstat()
    except FileNotFoundError:
        raise FileNotFoundError(f"{name} file is absent") from None
    if not stat.S_ISREG(metadata.st_mode):
        raise ValueError(f"{name} must be a regular file")
    if metadata.st_uid != os.geteuid():
        raise PermissionError(f"{name} owner does not match the current process")
    mode = stat.S_IMODE(metadata.st_mode)
    if mode == 0o644 and metadata.st_nlink == 1:
        raise GlobalEconomicAuthorityLegacyStoreMigrationRequiredV1(
            f"{name} uses legacy mode 0644; explicit validated migration is required"
        )
    if mode != 0o600:
        raise PermissionError(f"{name} mode must be exactly 0600")
    if metadata.st_nlink != 1:
        raise PermissionError(f"{name} must have exactly one filesystem link")


def _acquire_authority_bootstrap_lock_v1(path: Path) -> int:
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC
    directory_fd = os.open(path.parent, flags)
    try:
        fcntl.flock(directory_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError as exc:
        os.close(directory_fd)
        if exc.errno in {errno.EACCES, errno.EAGAIN}:
            raise GlobalEconomicAuthorityBootstrapBusyV1(
                "global economic authority bootstrap is busy"
            ) from exc
        raise
    return directory_fd


def _release_authority_bootstrap_lock_v1(directory_fd: int) -> None:
    try:
        fcntl.flock(directory_fd, fcntl.LOCK_UN)
    finally:
        os.close(directory_fd)


def _authority_bootstrap_candidate_path_v1(path: Path) -> Path:
    return path.parent / ".global-economic-authority-bootstrap-v1.sqlite"


def _require_descriptor_recovery_platform_v1() -> None:
    if not hasattr(os, "O_PATH") or not Path("/proc/self/fd").is_dir():
        raise GlobalEconomicAuthorityBootstrapPlatformUnsupportedV1(
            "global economic authority bootstrap recovery requires Linux O_PATH "
            "and /proc/self/fd"
        )


def _open_identity_descriptor_v1(path: Path) -> int:
    _require_descriptor_recovery_platform_v1()
    return os.open(path, os.O_PATH | os.O_NOFOLLOW | os.O_CLOEXEC)


def _open_readable_identity_descriptor_v1(identity_fd: int) -> int:
    try:
        readable_fd = os.open(
            Path(f"/proc/self/fd/{identity_fd}"),
            os.O_RDONLY | os.O_CLOEXEC,
        )
    except OSError as exc:
        raise GlobalEconomicAuthorityBootstrapPlatformUnsupportedV1(
            "global economic authority cannot reopen its procfs descriptor"
        ) from exc
    if not _same_inode_v1(os.fstat(identity_fd), os.fstat(readable_fd)):
        os.close(readable_fd)
        raise RuntimeError(
            "global economic authority readable recovery descriptor changed inode"
        )
    return readable_fd


def _require_linked_private_inode_v1(
    metadata: os.stat_result,
    *,
    name: str,
) -> None:
    if not stat.S_ISREG(metadata.st_mode):
        raise RuntimeError(f"{name} is not a regular file")
    if metadata.st_uid != os.geteuid():
        raise RuntimeError(f"{name} owner does not match the current process")
    if stat.S_IMODE(metadata.st_mode) != 0o600:
        raise RuntimeError(f"{name} mode is not exactly 0600")
    if metadata.st_nlink != 2:
        raise RuntimeError(f"{name} does not have the exact post-link count")


def _same_inode_v1(left: os.stat_result, right: os.stat_result) -> bool:
    return left.st_dev == right.st_dev and left.st_ino == right.st_ino


def _require_path_matches_fd_v1(
    path: Path,
    file_descriptor: int,
    *,
    name: str,
) -> None:
    try:
        path_metadata = path.lstat()
    except FileNotFoundError:
        raise RuntimeError(f"{name} disappeared during bootstrap recovery") from None
    descriptor_metadata = os.fstat(file_descriptor)
    if not _same_inode_v1(path_metadata, descriptor_metadata):
        raise RuntimeError(f"{name} changed inode during bootstrap recovery")


def _connect_descriptor_for_validation_v1(
    file_descriptor: int,
) -> sqlite3.Connection:
    _require_descriptor_recovery_platform_v1()
    descriptor_path = Path(f"/proc/self/fd/{file_descriptor}")
    try:
        connection = sqlite3.connect(
            f"{descriptor_path.as_uri()}?mode=ro&immutable=1",
            uri=True,
            timeout=5.0,
            isolation_level=None,
            check_same_thread=False,
        )
    except (OSError, sqlite3.Error) as exc:
        raise GlobalEconomicAuthorityBootstrapPlatformUnsupportedV1(
            "global economic authority cannot open SQLite through procfs"
        ) from exc
    try:
        connection.execute("PRAGMA foreign_keys = ON")
        connection.execute("PRAGMA trusted_schema = OFF")
        mode = connection.execute("PRAGMA journal_mode").fetchone()
        if mode is None or str(mode[0]).lower() != "delete":
            raise RuntimeError("global economic authority requires DELETE journal mode")
    except BaseException:
        connection.close()
        raise
    return connection


def _reject_recovery_wal_artifacts_v1(
    final_path: Path,
    candidate_path: Path,
    readable_fd: int,
) -> None:
    for path in (final_path, candidate_path):
        for suffix in ("-wal", "-shm"):
            try:
                Path(f"{path}{suffix}").lstat()
            except FileNotFoundError:
                continue
            raise RuntimeError(
                "global economic authority journal rejects WAL artifacts"
            )
    try:
        header = os.pread(readable_fd, 100, 0)
    except OSError as exc:
        raise RuntimeError(
            "global economic authority recovery header cannot be read"
        ) from exc
    if (
        len(header) >= 20
        and header[:16] == b"SQLite format 3\x00"
        and (header[18] == 2 or header[19] == 2)
    ):
        raise RuntimeError("global economic authority journal rejects WAL mode")


def _reject_wal_artifacts_v1(path: Path) -> None:
    for suffix in ("-wal", "-shm"):
        sidecar = Path(f"{path}{suffix}")
        try:
            sidecar.lstat()
        except FileNotFoundError:
            continue
        raise RuntimeError("global economic authority journal rejects WAL artifacts")
    try:
        with path.open("rb") as store:
            header = store.read(100)
    except OSError as exc:
        raise RuntimeError("global economic authority header cannot be read") from exc
    if (
        len(header) >= 20
        and header[:16] == b"SQLite format 3\x00"
        and (header[18] == 2 or header[19] == 2)
    ):
        raise RuntimeError("global economic authority journal rejects WAL mode")


def _configure_connection_v1(connection: sqlite3.Connection) -> None:
    connection.execute("PRAGMA foreign_keys = ON")
    if connection.execute("PRAGMA foreign_keys").fetchone() != (1,):
        raise RuntimeError("global economic authority could not enable foreign keys")
    mode = connection.execute("PRAGMA journal_mode = DELETE").fetchone()
    if mode is None or str(mode[0]).lower() != "delete":
        raise RuntimeError("global economic authority requires DELETE journal mode")
    connection.execute("PRAGMA synchronous = FULL")
    if connection.execute("PRAGMA synchronous").fetchone() != (2,):
        raise RuntimeError("global economic authority requires FULL synchronization")
    connection.execute("PRAGMA trusted_schema = OFF")
    connection.execute("PRAGMA busy_timeout = 5000")


def _connect_v1(path: Path) -> sqlite3.Connection:
    connection = sqlite3.connect(
        path,
        timeout=5.0,
        isolation_level=None,
        check_same_thread=False,
    )
    try:
        _configure_connection_v1(connection)
    except BaseException:
        connection.close()
        raise
    return connection


def _connect_existing_for_validation_v1(path: Path) -> sqlite3.Connection:
    _reject_wal_artifacts_v1(path)
    connection = sqlite3.connect(
        f"{path.as_uri()}?mode=ro&immutable=1",
        uri=True,
        timeout=5.0,
        isolation_level=None,
        check_same_thread=False,
    )
    try:
        connection.execute("PRAGMA foreign_keys = ON")
        connection.execute("PRAGMA trusted_schema = OFF")
        mode = connection.execute("PRAGMA journal_mode").fetchone()
        if mode is None or str(mode[0]).lower() != "delete":
            raise RuntimeError("global economic authority requires DELETE journal mode")
    except BaseException:
        connection.close()
        raise
    return connection


def _rollback_v1(connection: sqlite3.Connection) -> None:
    if connection.in_transaction:
        connection.execute("ROLLBACK")


def _canonical_decimal_v1(value: object, *, name: str) -> int:
    if type(value) is not str:
        raise TypeError(f"{name} must be exact str")
    if (
        not value
        or not value.isascii()
        or not value.isdecimal()
        or (len(value) > 1 and value.startswith("0"))
    ):
        raise ValueError(f"{name} is not canonical decimal")
    result = int(value)
    if result > (1 << 64) - 1:
        raise ValueError(f"{name} exceeds unsigned 64-bit range")
    return result


def _qualified_v1(database: str, table: str) -> str:
    if database not in {"main", _ATTACHED_DATABASE_V1}:
        raise ValueError("global economic authority database name is not closed")
    return f"{database}.{table}"


def _validate_authority_store_on_connection_v1(
    connection: sqlite3.Connection,
    *,
    database: str,
) -> GlobalEconomicAuthorityHeadV1:
    """Validate one exact authority history inside the caller's transaction."""

    if not connection.in_transaction:
        raise RuntimeError("global economic authority validation requires one snapshot")
    _validate_authority_schema_v1(connection, database=database)
    history = _read_authority_history_v1(connection, database=database)
    current_rows = connection.execute(
        f"SELECT singleton, authority_root FROM "
        f"{_qualified_v1(database, 'current_authority')} ORDER BY singleton"
    ).fetchall()
    if len(current_rows) != 1 or current_rows[0][0] != 1:
        raise RuntimeError("global economic current-authority row mismatch")
    if current_rows[0][1] != history[-1].authority_root:
        raise ValueError("global economic current authority is not the history tip")
    return history[-1]


def _validate_authority_schema_v1(
    connection: sqlite3.Connection,
    *,
    database: str,
) -> None:
    master = _qualified_v1(database, "sqlite_master")
    objects = connection.execute(
        f"SELECT name, sql FROM {master} "
        "WHERE name NOT LIKE 'sqlite_%' ORDER BY name"
    ).fetchall()
    if tuple(objects) != _EXPECTED_TABLE_SQL_V1:
        raise RuntimeError("global economic authority exact schema mismatch")
    strict_by_name = {
        row[1]: row[5]
        for row in connection.execute(
            f"PRAGMA {database}.table_list"
        ).fetchall()
        if len(row) == 6
        and row[1] in {name for name, _ in _EXPECTED_TABLE_SQL_V1}
    }
    if strict_by_name != {
        "authority_history": 1,
        "current_authority": 1,
        "metadata": 1,
    }:
        raise RuntimeError("global economic authority STRICT schema mismatch")
    for table, expected_columns in _EXPECTED_COLUMNS_V1:
        columns = connection.execute(
            f"PRAGMA {database}.table_info({table})"
        ).fetchall()
        if tuple(columns) != expected_columns:
            raise RuntimeError(
                f"global economic authority {table} column mismatch"
            )
    foreign_keys = connection.execute(
        f"PRAGMA {database}.foreign_key_list(current_authority)"
    ).fetchall()
    if len(foreign_keys) != 1 or (
        foreign_keys[0][2],
        foreign_keys[0][3],
        foreign_keys[0][4],
        foreign_keys[0][5],
        foreign_keys[0][6],
    ) != (
        "authority_history",
        "authority_root",
        "authority_root",
        "NO ACTION",
        "NO ACTION",
    ):
        raise RuntimeError("global economic authority foreign-key mismatch")
    if connection.execute(f"PRAGMA {database}.foreign_key_check").fetchall():
        raise RuntimeError("global economic authority foreign-key check failed")
    index_rows = connection.execute(
        f"PRAGMA {database}.index_list(authority_history)"
    ).fetchall()
    index_contracts = {(row[2], row[3], row[4]) for row in index_rows}
    if index_contracts != {(1, "pk", 0), (1, "u", 0)}:
        raise RuntimeError("global economic authority unique-index mismatch")
    if connection.execute("PRAGMA trusted_schema").fetchone() != (0,):
        raise RuntimeError("global economic authority trusted schema must be disabled")
    if connection.execute(f"PRAGMA {database}.integrity_check").fetchall() != [
        ("ok",)
    ]:
        raise RuntimeError("global economic authority integrity check failed")


def _read_authority_history_v1(
    connection: sqlite3.Connection,
    *,
    database: str,
) -> tuple[GlobalEconomicAuthorityHeadV1, ...]:
    metadata = connection.execute(
        f"SELECT singleton, schema_name FROM {_qualified_v1(database, 'metadata')} "
        "ORDER BY singleton"
    ).fetchall()
    if metadata != [(1, GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V1)]:
        raise RuntimeError("global economic authority metadata mismatch")
    row_count, byte_count = _read_authority_history_bounds_v1(
        connection,
        database=database,
    )
    history = _decode_authority_history_rows_v1(
        connection,
        database=database,
        expected_count=row_count,
    )
    if history[0].generation != 0:
        raise ValueError("global economic authority history lacks generation zero")
    for current, successor in zip(history, history[1:], strict=False):
        require_global_economic_authority_successor_v1(current, successor)
    _require_authority_revocation_reserve_v1(
        history[-1],
        row_count=row_count,
        byte_count=byte_count,
    )
    return history


def _read_authority_history_bounds_v1(
    connection: sqlite3.Connection,
    *,
    database: str,
) -> tuple[int, int]:
    bounds = connection.execute(
        f"SELECT COUNT(*), COALESCE(SUM(length(head_bytes)), 0) FROM "
        f"{_qualified_v1(database, 'authority_history')}"
    ).fetchone()
    if (
        bounds is None
        or type(bounds[0]) is not int
        or type(bounds[1]) is not int
    ):
        raise RuntimeError("global economic authority history bounds query failed")
    row_count, byte_count = bounds
    if not 1 <= row_count <= _MAX_AUTHORITY_GENERATIONS_V1:
        raise ValueError("global economic authority history exceeds row capacity")
    if not 1 <= byte_count <= _MAX_AUTHORITY_STORE_BYTES_V1:
        raise ValueError("global economic authority history exceeds byte capacity")
    return row_count, byte_count


def _decode_authority_history_rows_v1(
    connection: sqlite3.Connection,
    *,
    database: str,
    expected_count: int,
) -> tuple[GlobalEconomicAuthorityHeadV1, ...]:
    rows = connection.execute(
        f"SELECT authority_root, generation_decimal, head_bytes FROM "
        f"{_qualified_v1(database, 'authority_history')}"
    ).fetchall()
    if len(rows) != expected_count:
        raise RuntimeError("global economic authority history count changed")
    decoded: list[GlobalEconomicAuthorityHeadV1] = []
    for authority_root, generation_decimal, head_bytes in rows:
        if type(authority_root) is not str or type(head_bytes) is not bytes:
            raise TypeError("global economic authority row types are invalid")
        generation = _canonical_decimal_v1(
            generation_decimal,
            name="global economic authority row generation",
        )
        head = decode_global_economic_authority_head_v1(head_bytes)
        if head.authority_root != authority_root or head.generation != generation:
            raise ValueError("global economic authority row binding mismatch")
        decoded.append(head)
    return tuple(sorted(decoded, key=lambda head: head.generation))


def _require_authority_revocation_reserve_v1(
    tip: GlobalEconomicAuthorityHeadV1,
    *,
    row_count: int,
    byte_count: int,
) -> None:
    if tip.status is GlobalEconomicAuthorityStatusV1.ACTIVE:
        revocation = tip.revoked_successor()
        if row_count + 1 > _MAX_AUTHORITY_GENERATIONS_V1:
            raise ValueError(
                "global economic authority history lacks revocation row reserve"
            )
        if byte_count + len(revocation.canonical_bytes) > (
            _MAX_AUTHORITY_STORE_BYTES_V1
        ):
            raise ValueError(
                "global economic authority history lacks revocation byte reserve"
            )


def _existing_successor_status_v1(
    connection: sqlite3.Connection,
    current: GlobalEconomicAuthorityHeadV1,
    successor: GlobalEconomicAuthorityHeadV1,
) -> GlobalEconomicAuthorityCommitStatusV1 | None:
    row = connection.execute(
        "SELECT head_bytes FROM authority_history WHERE authority_root = ?",
        (successor.authority_root,),
    ).fetchone()
    if row is None:
        return None
    if row != (successor.canonical_bytes,):
        raise RuntimeError("global economic authority root collision")
    if successor.authority_root == current.authority_root:
        return GlobalEconomicAuthorityCommitStatusV1.ALREADY_COMMITTED
    return GlobalEconomicAuthorityCommitStatusV1.STALE_HEAD


def _authority_capacity_available_v1(
    connection: sqlite3.Connection,
    successor: GlobalEconomicAuthorityHeadV1,
) -> bool:
    bounds = connection.execute(
        "SELECT COUNT(*), COALESCE(SUM(length(head_bytes)), 0) "
        "FROM authority_history"
    ).fetchone()
    if bounds is None or type(bounds[0]) is not int or type(bounds[1]) is not int:
        raise RuntimeError("global economic authority capacity query failed")
    required_rows = 1
    required_bytes = len(successor.canonical_bytes)
    if successor.status is GlobalEconomicAuthorityStatusV1.ACTIVE:
        reserved_revocation = successor.revoked_successor()
        required_rows += 1
        required_bytes += len(reserved_revocation.canonical_bytes)
    return (
        bounds[0] + required_rows <= _MAX_AUTHORITY_GENERATIONS_V1
        and bounds[1] + required_bytes <= _MAX_AUTHORITY_STORE_BYTES_V1
    )


def _insert_authority_successor_v1(
    connection: sqlite3.Connection,
    current: GlobalEconomicAuthorityHeadV1,
    successor: GlobalEconomicAuthorityHeadV1,
) -> None:
    connection.execute(
        "INSERT INTO authority_history(authority_root, generation_decimal, head_bytes) "
        "VALUES (?, ?, ?)",
        (
            successor.authority_root,
            str(successor.generation),
            successor.canonical_bytes,
        ),
    )
    cursor = connection.execute(
        "UPDATE current_authority SET authority_root = ? "
        "WHERE singleton = 1 AND authority_root = ?",
        (successor.authority_root, current.authority_root),
    )
    if cursor.rowcount != 1:
        raise RuntimeError("global economic authority CAS changed in transaction")


def _attach_authority_store_v1(
    connection: sqlite3.Connection,
    authority_path: Path,
    *,
    immutable: bool,
) -> None:
    _require_owned_regular_store_v1(
        authority_path,
        name="global economic authority journal",
    )
    _reject_wal_artifacts_v1(authority_path)
    target = (
        f"{authority_path.as_uri()}?mode=ro&immutable=1"
        if immutable
        else str(authority_path)
    )
    connection.execute(
        f"ATTACH DATABASE ? AS {_ATTACHED_DATABASE_V1}",
        (target,),
    )
    mode = connection.execute(
        f"PRAGMA {_ATTACHED_DATABASE_V1}.journal_mode"
    ).fetchone()
    if mode is None or str(mode[0]).lower() != "delete":
        raise RuntimeError("attached global economic authority requires DELETE mode")
    if not immutable:
        connection.execute(f"PRAGMA {_ATTACHED_DATABASE_V1}.synchronous = FULL")
        if connection.execute(
            f"PRAGMA {_ATTACHED_DATABASE_V1}.synchronous"
        ).fetchone() != (2,):
            raise RuntimeError(
                "attached global economic authority requires FULL synchronization"
            )


class GlobalEconomicAuthorityJournalV1:
    """Bounded monotone durable authority history."""

    def __init__(self, path: Path, connection: sqlite3.Connection) -> None:
        self._path = path
        self._connection = connection
        self._lock = Lock()
        self._instance_token = object()
        self._cas_tokens: WeakKeyDictionary[
            GlobalEconomicAuthorityCasTokenV1,
            tuple[object, str, int],
        ] = WeakKeyDictionary()
        self._closed = False

    @classmethod
    def create(
        cls,
        path: str | Path,
        initial_head: GlobalEconomicAuthorityHeadV1,
    ) -> GlobalEconomicAuthorityJournalV1:
        normalized = _normalize_path_v1(path, name="global economic authority path")
        owned = decode_global_economic_authority_head_v1(initial_head.canonical_bytes)
        if owned.generation != 0:
            raise ValueError("global economic authority journal must begin at generation zero")
        if owned.status.value != "ACTIVE":
            raise ValueError("global economic authority journal must begin active")
        if not normalized.parent.is_dir():
            raise FileNotFoundError("global economic authority parent directory is absent")
        _install_authority_store_no_replace_v1(normalized, owned)
        return cls.open(normalized)

    @classmethod
    def open(cls, path: str | Path) -> GlobalEconomicAuthorityJournalV1:
        normalized = _normalize_path_v1(path, name="global economic authority path")
        _require_owned_regular_store_v1(
            normalized,
            name="global economic authority journal",
        )
        validation = cls(normalized, _connect_existing_for_validation_v1(normalized))
        try:
            validation._read_snapshot_v1()
        finally:
            validation.close()
        journal = cls(normalized, _connect_v1(normalized))
        try:
            journal._read_snapshot_v1()
        except BaseException:
            journal.close()
            raise
        return journal

    def __enter__(self) -> GlobalEconomicAuthorityJournalV1:
        self._require_open_v1()
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()

    @property
    def path(self) -> Path:
        return self._path

    @property
    def head(self) -> GlobalEconomicAuthorityHeadV1:
        with self._lock:
            self._require_open_v1()
            return self._read_snapshot_v1()

    def _require_open_v1(self) -> None:
        if self._closed:
            raise RuntimeError("global economic authority journal is closed")

    def close(self) -> None:
        with self._lock:
            if self._closed:
                return
            self._connection.close()
            self._cas_tokens.clear()
            self._closed = True

    def _acquire_cas_head_token_for_unmounted_control_plane_v1(
        self,
    ) -> GlobalEconomicAuthorityCasTokenV1:
        with self._lock:
            self._require_open_v1()
            if len(self._cas_tokens) >= _MAX_OUTSTANDING_AUTHORITY_CAS_TOKENS_V1:
                raise RuntimeError(
                    "global economic authority CAS token capacity exceeded"
                )
            head = self._read_snapshot_v1()
            token = GlobalEconomicAuthorityCasTokenV1(
                _CAS_TOKEN_MINT_V1,
                head.authority_root,
                head.generation,
            )
            self._cas_tokens[token] = (
                self._instance_token,
                head.authority_root,
                head.generation,
            )
            return token

    def _commit_successor_for_unmounted_control_plane_v1(
        self,
        successor: GlobalEconomicAuthorityHeadV1,
        cas_token: GlobalEconomicAuthorityCasTokenV1,
    ) -> GlobalEconomicAuthorityCommitOutcomeV1:
        owned = decode_global_economic_authority_head_v1(successor.canonical_bytes)
        if type(cas_token) is not GlobalEconomicAuthorityCasTokenV1:
            raise TypeError("global economic authority commit requires exact CAS token")
        with self._lock:
            self._require_open_v1()
            binding = self._cas_tokens.get(cas_token)
            if binding is None or binding[0] is not self._instance_token:
                raise ValueError("global economic authority CAS token is foreign or forged")
            try:
                return self._commit_under_lock_v1(
                    owned,
                    expected_root=binding[1],
                    expected_generation=binding[2],
                )
            finally:
                self._cas_tokens.pop(cas_token, None)

    def _create_store_v1(self, initial_head: GlobalEconomicAuthorityHeadV1) -> None:
        connection = self._connection
        try:
            connection.execute("BEGIN IMMEDIATE")
            existing = connection.execute(
                "SELECT 1 FROM sqlite_master WHERE name NOT LIKE 'sqlite_%' LIMIT 1"
            ).fetchone()
            if existing is not None:
                raise RuntimeError("authority bootstrap candidate is not empty")
            connection.execute(_CREATE_METADATA_SQL_V1)
            connection.execute(_CREATE_HISTORY_SQL_V1)
            connection.execute(_CREATE_CURRENT_SQL_V1)
            connection.execute(
                "INSERT INTO metadata(singleton, schema_name) VALUES (1, ?)",
                (GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V1,),
            )
            connection.execute(
                "INSERT INTO authority_history(authority_root, generation_decimal, head_bytes) "
                "VALUES (?, '0', ?)",
                (initial_head.authority_root, initial_head.canonical_bytes),
            )
            connection.execute(
                "INSERT INTO current_authority(singleton, authority_root) VALUES (1, ?)",
                (initial_head.authority_root,),
            )
            connection.execute("COMMIT")
        except BaseException:
            _rollback_v1(connection)
            raise

    def _read_snapshot_v1(self) -> GlobalEconomicAuthorityHeadV1:
        if self._connection.in_transaction:
            return _validate_authority_store_on_connection_v1(
                self._connection,
                database="main",
            )
        self._connection.execute("BEGIN")
        try:
            head = _validate_authority_store_on_connection_v1(
                self._connection,
                database="main",
            )
            self._connection.execute("COMMIT")
            return head
        except BaseException:
            _rollback_v1(self._connection)
            raise

    def _commit_under_lock_v1(
        self,
        successor: GlobalEconomicAuthorityHeadV1,
        *,
        expected_root: str,
        expected_generation: int,
    ) -> GlobalEconomicAuthorityCommitOutcomeV1:
        connection = self._connection
        connection.execute("BEGIN IMMEDIATE")
        try:
            current = _validate_authority_store_on_connection_v1(
                connection,
                database="main",
            )
            existing_status = _existing_successor_status_v1(
                connection,
                current,
                successor,
            )
            if existing_status is GlobalEconomicAuthorityCommitStatusV1.ALREADY_COMMITTED:
                connection.execute("COMMIT")
                return GlobalEconomicAuthorityCommitOutcomeV1(
                    existing_status,
                    current,
                    successor,
                )
            if existing_status is GlobalEconomicAuthorityCommitStatusV1.STALE_HEAD:
                connection.execute("ROLLBACK")
                return GlobalEconomicAuthorityCommitOutcomeV1(
                    existing_status,
                    current,
                )
            if (
                current.authority_root != expected_root
                or current.generation != expected_generation
            ):
                connection.execute("ROLLBACK")
                return GlobalEconomicAuthorityCommitOutcomeV1(
                    GlobalEconomicAuthorityCommitStatusV1.STALE_HEAD,
                    current,
                )
            require_global_economic_authority_successor_v1(current, successor)
            if not _authority_capacity_available_v1(connection, successor):
                connection.execute("ROLLBACK")
                return GlobalEconomicAuthorityCommitOutcomeV1(
                    GlobalEconomicAuthorityCommitStatusV1.CAPACITY_EXCEEDED,
                    current,
                )
            _insert_authority_successor_v1(connection, current, successor)
            connection.execute("COMMIT")
            return GlobalEconomicAuthorityCommitOutcomeV1(
                GlobalEconomicAuthorityCommitStatusV1.COMMITTED,
                successor,
                successor,
            )
        except BaseException:
            _rollback_v1(connection)
            raise


def _path_entry_exists_v1(path: Path) -> bool:
    try:
        path.lstat()
    except FileNotFoundError:
        return False
    return True


def _initialize_authority_candidate_v1(
    candidate_path: Path,
    initial_head: GlobalEconomicAuthorityHeadV1,
) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW
    try:
        candidate_fd = os.open(candidate_path, flags, 0o600)
    except FileExistsError:
        raise RuntimeError(
            "global economic authority crash-left bootstrap candidate exists"
        ) from None
    os.close(candidate_fd)
    candidate = GlobalEconomicAuthorityJournalV1(
        candidate_path,
        _connect_v1(candidate_path),
    )
    try:
        candidate._create_store_v1(initial_head)
        candidate._read_snapshot_v1()
    finally:
        candidate.close()
    _require_owned_regular_store_v1(
        candidate_path,
        name="global economic authority bootstrap candidate",
    )
    fsync_fd = os.open(
        candidate_path,
        os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
    )
    try:
        os.fsync(fsync_fd)
    finally:
        os.close(fsync_fd)


def _recover_linked_authority_install_v1(
    path: Path,
    candidate_path: Path,
    initial_head: GlobalEconomicAuthorityHeadV1,
    directory_fd: int,
) -> None:
    """Complete only the exact validated two-name post-link crash state."""

    final_fd = _open_identity_descriptor_v1(path)
    try:
        candidate_fd = _open_identity_descriptor_v1(candidate_path)
        try:
            final_metadata = os.fstat(final_fd)
            candidate_metadata = os.fstat(candidate_fd)
            _require_linked_private_inode_v1(
                final_metadata,
                name="global economic authority final store",
            )
            _require_linked_private_inode_v1(
                candidate_metadata,
                name="global economic authority bootstrap candidate",
            )
            if not _same_inode_v1(final_metadata, candidate_metadata):
                raise RuntimeError(
                    "global economic authority bootstrap names do not share one inode"
                )
            readable_fd = _open_readable_identity_descriptor_v1(final_fd)
            try:
                _reject_recovery_wal_artifacts_v1(
                    path,
                    candidate_path,
                    readable_fd,
                )
                validation = GlobalEconomicAuthorityJournalV1(
                    path,
                    _connect_descriptor_for_validation_v1(readable_fd),
                )
                try:
                    if validation._read_snapshot_v1() != initial_head:
                        raise RuntimeError(
                            "global economic authority bootstrap recovery head mismatch"
                        )
                finally:
                    validation.close()
            finally:
                os.close(readable_fd)
            _require_path_matches_fd_v1(
                path,
                final_fd,
                name="global economic authority final store",
            )
            _require_path_matches_fd_v1(
                candidate_path,
                candidate_fd,
                name="global economic authority bootstrap candidate",
            )
            os.unlink(candidate_path.name, dir_fd=directory_fd)
            os.fsync(directory_fd)
            _require_path_matches_fd_v1(
                path,
                final_fd,
                name="global economic authority final store",
            )
            if os.fstat(final_fd).st_nlink != 1:
                raise RuntimeError(
                    "global economic authority recovery did not restore one link"
                )
        finally:
            os.close(candidate_fd)
    finally:
        os.close(final_fd)


def _install_authority_store_no_replace_v1(
    path: Path,
    initial_head: GlobalEconomicAuthorityHeadV1,
) -> None:
    directory_fd = _acquire_authority_bootstrap_lock_v1(path)
    try:
        candidate_path = _authority_bootstrap_candidate_path_v1(path)
        if candidate_path == path:
            raise ValueError("global economic authority path uses a reserved name")
        final_exists = _path_entry_exists_v1(path)
        candidate_exists = _path_entry_exists_v1(candidate_path)
        if final_exists and candidate_exists:
            _recover_linked_authority_install_v1(
                path,
                candidate_path,
                initial_head,
                directory_fd,
            )
            return
        if final_exists:
            raise FileExistsError(
                "global economic authority journal path already exists"
            )
        if candidate_exists:
            raise RuntimeError(
                "global economic authority crash-left bootstrap candidate exists"
            )
        _initialize_authority_candidate_v1(candidate_path, initial_head)
        try:
            os.link(candidate_path, path, follow_symlinks=False)
        except FileExistsError:
            raise FileExistsError(
                "global economic authority journal path already exists"
            ) from None
        os.fsync(directory_fd)
        os.unlink(candidate_path)
        os.fsync(directory_fd)
    finally:
        _release_authority_bootstrap_lock_v1(directory_fd)


def _create_or_recover_authority_for_publisher_v1(
    authority_path: Path,
    expected_head: GlobalEconomicAuthorityHeadV1,
) -> None:
    """Install generation zero or require an exact already-current authority."""

    try:
        journal = GlobalEconomicAuthorityJournalV1.create(
            authority_path,
            expected_head,
        )
    except FileExistsError:
        journal = GlobalEconomicAuthorityJournalV1.open(authority_path)
        if journal.head != expected_head:
            journal.close()
            raise ValueError(
                "global economic durable publisher current authority mismatch"
            ) from None
    journal.close()


__all__ = [
    "GlobalEconomicAuthorityBootstrapBusyV1",
    "GlobalEconomicAuthorityBootstrapPlatformUnsupportedV1",
    "GlobalEconomicAuthorityLegacyStoreMigrationRequiredV1",
    "GlobalEconomicAuthorityCasTokenV1",
    "GlobalEconomicAuthorityCommitOutcomeV1",
    "GlobalEconomicAuthorityCommitStatusV1",
    "GlobalEconomicAuthorityJournalV1",
    "authority_journal_path_for_epoch_v1",
    "economic_epoch_store_root_v1",
]

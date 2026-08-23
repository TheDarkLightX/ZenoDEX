"""Atomic SQLite journal for complete ordinary economic epoch bundles.

This adapter is deliberately unmounted.  It offers bounded durability, CAS,
exact retry, and coherent recovery.  It does not verify proof receipts or grant
settlement, finality, consensus, or production writer authority.
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
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
)
from ..core.global_economic_durable_activation_v1 import (
    DurableEconomicComponentKindV1,
    DurableEconomicInitialStateBundleV1,
    _decode_exact_canonical_json_v1,
    decode_durable_economic_initial_state_bundle_v1,
)
from ..core.global_settlement_types_v1 import _require_root, hash_global_v1
from .global_economic_authority_journal_v1 import (
    _attach_authority_store_v1,
    _validate_authority_store_on_connection_v1,
)
from .global_economic_durable_epoch_v1 import (
    DURABLE_ECONOMIC_EPOCH_SCHEMA_V1,
    DurableEconomicEpochBundleV1,
    DurableEconomicPublicationHeadV1,
    decode_durable_economic_epoch_bundle_v1,
)

_MAX_EPOCH_HISTORY_V1: Final = 4096
_MAX_EPOCH_STORE_BYTES_V1: Final = 512 * 1024 * 1024
_CAS_TOKEN_MINT_V1: Final = object()
_WRITE_CAPABILITY_MINT_V1: Final = object()
_CREATE_METADATA_SQL_V1: Final = (
    "CREATE TABLE metadata ("
    "singleton INTEGER PRIMARY KEY CHECK (singleton = 1), "
    "schema_name TEXT NOT NULL, "
    "activation_id TEXT NOT NULL, "
    "activation_bundle BLOB NOT NULL"
    ") STRICT"
)
_CREATE_EPOCHS_SQL_V1: Final = (
    "CREATE TABLE economic_epochs ("
    "publication_id TEXT PRIMARY KEY NOT NULL, "
    "commit_id TEXT NOT NULL UNIQUE, "
    "sequence_decimal TEXT NOT NULL UNIQUE, "
    "bundle_bytes BLOB NOT NULL"
    ") STRICT"
)
_CREATE_CURRENT_HEAD_SQL_V1: Final = (
    "CREATE TABLE current_head ("
    "singleton INTEGER PRIMARY KEY CHECK (singleton = 1), "
    "publication_id TEXT NOT NULL, "
    "sequence_decimal TEXT NOT NULL"
    ") STRICT"
)
_EXPECTED_TABLE_SQL_V1: Final = (
    ("current_head", _CREATE_CURRENT_HEAD_SQL_V1),
    ("economic_epochs", _CREATE_EPOCHS_SQL_V1),
    ("metadata", _CREATE_METADATA_SQL_V1),
)


class DurableEconomicEpochCommitStatusV1(str, Enum):
    COMMITTED = "COMMITTED"
    ALREADY_COMMITTED = "ALREADY_COMMITTED"
    STALE_HEAD = "STALE_HEAD"
    CAPACITY_EXCEEDED = "CAPACITY_EXCEEDED"
    AUTHORITY_STALE = "AUTHORITY_STALE"


@dataclass(frozen=True, slots=True)
class DurableEconomicEpochCommitOutcomeV1:
    status: DurableEconomicEpochCommitStatusV1
    head: DurableEconomicPublicationHeadV1
    committed_epoch: DurableEconomicPublicationHeadV1 | None = None

    def __post_init__(self) -> None:
        if type(self.status) is not DurableEconomicEpochCommitStatusV1:
            raise TypeError("durable epoch commit status is not closed")
        if type(self.head) is not DurableEconomicPublicationHeadV1:
            raise TypeError("durable epoch outcome head is not closed")
        successful = {
            DurableEconomicEpochCommitStatusV1.COMMITTED,
            DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED,
        }
        if self.status in successful:
            if type(self.committed_epoch) is not DurableEconomicPublicationHeadV1:
                raise TypeError("durable epoch successful outcome lacks committed epoch")
        elif self.committed_epoch is not None:
            raise ValueError("durable epoch no-effect outcome declares committed epoch")


class DurableEconomicEpochCasTokenV1:
    """Process-local source snapshot; it grants no writer authorization."""

    __slots__ = (
        "__authority_generation",
        "__authority_root",
        "__publication_id",
        "__sequence",
        "__sealed",
        "__weakref__",
    )
    __publication_id: str
    __sequence: int
    __sealed: bool

    def __init__(
        self,
        mint: object,
        publication_id: str,
        sequence: int,
        authority_root: str | None,
        authority_generation: int | None,
    ) -> None:
        if mint is not _CAS_TOKEN_MINT_V1:
            raise TypeError("durable epoch CAS tokens are journal-minted")
        object.__setattr__(self, "_DurableEconomicEpochCasTokenV1__publication_id", publication_id)
        object.__setattr__(self, "_DurableEconomicEpochCasTokenV1__sequence", sequence)
        object.__setattr__(
            self,
            "_DurableEconomicEpochCasTokenV1__authority_root",
            authority_root,
        )
        object.__setattr__(
            self,
            "_DurableEconomicEpochCasTokenV1__authority_generation",
            authority_generation,
        )
        object.__setattr__(self, "_DurableEconomicEpochCasTokenV1__sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_DurableEconomicEpochCasTokenV1__sealed", False):
            raise TypeError("durable epoch CAS tokens are immutable")
        object.__setattr__(self, name, value)

    @property
    def publication_id(self) -> str:
        return self.__publication_id

    @property
    def sequence(self) -> int:
        return self.__sequence


class DurableEconomicEpochWriteCapabilityV1:
    """Data-slot-free handle bound to one journal instance."""

    __slots__ = ("__weakref__",)

    def __init__(self, mint: object, journal: object) -> None:
        if mint is not _WRITE_CAPABILITY_MINT_V1:
            raise TypeError("durable epoch write capability is publisher-minted")
        _register_write_capability_v1(self, journal)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("durable epoch write capability is immutable")


_WRITE_CAPABILITY_LOCK_V1 = Lock()
_WRITE_CAPABILITY_AUTHORITIES_V1: WeakKeyDictionary[
    DurableEconomicEpochWriteCapabilityV1,
    object,
] = WeakKeyDictionary()


def _register_write_capability_v1(
    capability: DurableEconomicEpochWriteCapabilityV1,
    journal: object,
) -> None:
    with _WRITE_CAPABILITY_LOCK_V1:
        if capability in _WRITE_CAPABILITY_AUTHORITIES_V1:
            raise TypeError("durable epoch write capability is already registered")
        _WRITE_CAPABILITY_AUTHORITIES_V1[capability] = journal


def _require_write_capability_v1(
    journal: object,
    capability: DurableEconomicEpochWriteCapabilityV1,
) -> None:
    if type(capability) is not DurableEconomicEpochWriteCapabilityV1:
        raise TypeError("durable epoch commit requires exact write capability")
    with _WRITE_CAPABILITY_LOCK_V1:
        authority = _WRITE_CAPABILITY_AUTHORITIES_V1.get(capability)
    if authority is not journal:
        raise ValueError("durable epoch write capability is foreign or forged")


class _DurableEconomicEpochCommitFaultV1(str, Enum):
    AFTER_BEGIN = "AFTER_BEGIN"
    AFTER_INSERT = "AFTER_INSERT"
    AFTER_HEAD_UPDATE_BEFORE_COMMIT = "AFTER_HEAD_UPDATE_BEFORE_COMMIT"
    AFTER_COMMIT_BEFORE_ACK = "AFTER_COMMIT_BEFORE_ACK"


class _SimulatedDurableEconomicEpochCrashV1(RuntimeError):
    pass


class DurableEconomicEpochBootstrapBusyV1(RuntimeError):
    """Another cooperating installer owns the directory bootstrap lock."""


class DurableEconomicEpochLegacyStoreMigrationRequiredV1(PermissionError):
    """A valid-looking legacy mode requires an explicit validated migration."""


def _normalize_path_v1(path: str | Path) -> Path:
    if type(path) is str:
        candidate = Path(path)
    elif type(path) is type(Path()):
        candidate = Path(str(path))
    else:
        raise TypeError(
            "durable epoch journal path must be exact str or platform Path"
        )
    if not candidate.name:
        raise ValueError("durable epoch journal path must name a file")
    return candidate.absolute()


def _require_owned_regular_epoch_store_v1(path: Path, *, name: str) -> None:
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
        raise DurableEconomicEpochLegacyStoreMigrationRequiredV1(
            f"{name} uses legacy mode 0644; explicit validated migration is required"
        )
    if mode != 0o600:
        raise PermissionError(f"{name} mode must be exactly 0600")
    if metadata.st_nlink != 1:
        raise PermissionError(f"{name} must have exactly one filesystem link")


def _acquire_epoch_bootstrap_lock_v1(path: Path) -> int:
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC
    directory_fd = os.open(path.parent, flags)
    try:
        fcntl.flock(directory_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError as exc:
        os.close(directory_fd)
        if exc.errno in {errno.EACCES, errno.EAGAIN}:
            raise DurableEconomicEpochBootstrapBusyV1(
                "durable epoch bootstrap is busy"
            ) from exc
        raise
    return directory_fd


def _release_epoch_bootstrap_lock_v1(directory_fd: int) -> None:
    try:
        fcntl.flock(directory_fd, fcntl.LOCK_UN)
    finally:
        os.close(directory_fd)


def _epoch_bootstrap_candidate_path_v1(path: Path) -> Path:
    return path.parent / ".global-economic-epoch-bootstrap-v1.sqlite"


def _require_linked_private_epoch_inode_v1(
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


def _same_epoch_inode_v1(left: os.stat_result, right: os.stat_result) -> bool:
    return left.st_dev == right.st_dev and left.st_ino == right.st_ino


def _require_epoch_path_matches_fd_v1(
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
    if not _same_epoch_inode_v1(path_metadata, descriptor_metadata):
        raise RuntimeError(f"{name} changed inode during bootstrap recovery")


def _connect_epoch_descriptor_for_validation_v1(
    file_descriptor: int,
    authority_path: Path | None,
) -> sqlite3.Connection:
    descriptor_path = Path(f"/proc/self/fd/{file_descriptor}")
    connection = sqlite3.connect(
        f"{descriptor_path.as_uri()}?mode=ro&immutable=1",
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
            raise RuntimeError("durable epoch journal requires DELETE journal mode")
        if authority_path is not None:
            _attach_authority_store_v1(
                connection,
                authority_path,
                immutable=True,
            )
    except BaseException:
        connection.close()
        raise
    return connection


def _configure_connection_v1(connection: sqlite3.Connection) -> None:
    connection.execute("PRAGMA foreign_keys = ON")
    if connection.execute("PRAGMA foreign_keys").fetchone() != (1,):
        raise RuntimeError("durable epoch journal could not enable foreign keys")
    mode = connection.execute("PRAGMA journal_mode = DELETE").fetchone()
    if mode is None or str(mode[0]).lower() != "delete":
        raise RuntimeError("durable epoch journal requires DELETE journal mode")
    connection.execute("PRAGMA synchronous = FULL")
    if connection.execute("PRAGMA synchronous").fetchone() != (2,):
        raise RuntimeError("durable epoch journal requires FULL synchronization")
    connection.execute("PRAGMA trusted_schema = OFF")
    connection.execute("PRAGMA busy_timeout = 5000")


def _connect_v1(
    path: Path,
    authority_path: Path | None = None,
) -> sqlite3.Connection:
    connection = sqlite3.connect(
        path,
        timeout=5.0,
        isolation_level=None,
        check_same_thread=False,
    )
    try:
        _configure_connection_v1(connection)
        if authority_path is not None:
            _attach_authority_store_v1(
                connection,
                authority_path,
                immutable=False,
            )
    except BaseException:
        connection.close()
        raise
    return connection


def _connect_existing_for_validation_v1(
    path: Path,
    authority_path: Path | None = None,
) -> sqlite3.Connection:
    """Open an existing store without changing its persistent journal mode."""

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
        connection.execute("PRAGMA busy_timeout = 5000")
        mode = connection.execute("PRAGMA journal_mode").fetchone()
        if mode is None or str(mode[0]).lower() != "delete":
            raise RuntimeError("durable epoch journal requires DELETE journal mode")
        if authority_path is not None:
            _attach_authority_store_v1(
                connection,
                authority_path,
                immutable=True,
            )
    except BaseException:
        connection.close()
        raise
    return connection


def _reject_wal_artifacts_v1(path: Path) -> None:
    """Reject crash-left WAL state before SQLite can checkpoint or unlink it."""

    for suffix in ("-wal", "-shm"):
        sidecar = Path(f"{path}{suffix}")
        try:
            sidecar.lstat()
        except FileNotFoundError:
            continue
        raise RuntimeError("durable epoch journal rejects existing WAL artifacts")
    try:
        with path.open("rb") as store:
            header = store.read(100)
    except OSError as exc:
        raise RuntimeError("durable epoch journal header cannot be read") from exc
    if (
        len(header) >= 20
        and header[:16] == b"SQLite format 3\x00"
        and (header[18] == 2 or header[19] == 2)
    ):
        raise RuntimeError("durable epoch journal rejects WAL artifacts or mode")


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


def _snapshot_activation_v1(
    activation: DurableEconomicInitialStateBundleV1,
) -> DurableEconomicInitialStateBundleV1:
    if type(activation) is not DurableEconomicInitialStateBundleV1:
        raise TypeError("durable epoch journal activation type is not closed")
    return decode_durable_economic_initial_state_bundle_v1(activation.canonical_bytes)


def _snapshot_epoch_v1(epoch: DurableEconomicEpochBundleV1) -> DurableEconomicEpochBundleV1:
    if type(epoch) is not DurableEconomicEpochBundleV1:
        raise TypeError("durable epoch journal bundle type is not closed")
    return decode_durable_economic_epoch_bundle_v1(epoch.canonical_bytes)


def _activation_release_observation_root_v1(
    activation: DurableEconomicInitialStateBundleV1,
) -> str:
    profile_component = next(
        component
        for component in activation.components
        if component.kind is DurableEconomicComponentKindV1.PROFILE
    )
    envelope = _decode_exact_canonical_json_v1(
        profile_component.payload,
        name="durable epoch base profile",
    )
    if type(envelope) is not dict or type(envelope.get("profile")) is not dict:
        raise ValueError("durable epoch base profile envelope is malformed")
    profile = envelope["profile"]
    required = ("profile_id", "lane_registry_root", "route_registry_root")
    if any(type(profile.get(field)) is not str for field in required):
        raise TypeError("durable epoch base profile roots must be exact str")
    return hash_global_v1(
        "global-economic-release-observation-v1",
        {
            "profile_root": profile["profile_id"],
            "lane_registry_root": profile["lane_registry_root"],
            "route_registry_root": profile["route_registry_root"],
        },
    )


class GlobalEconomicEpochJournalV1:
    """Bounded atomic history for one activation and its ordinary epochs."""

    def __init__(
        self,
        path: Path,
        connection: sqlite3.Connection,
        *,
        expected_authority: GlobalEconomicAuthorityHeadV1 | None = None,
    ) -> None:
        self._path = path
        self._connection = connection
        self._lock = Lock()
        self._instance_token = object()
        self._expected_authority = expected_authority
        self._cas_tokens: WeakKeyDictionary[
            DurableEconomicEpochCasTokenV1,
            tuple[object, str, int, str | None, int | None],
        ] = WeakKeyDictionary()
        self._closed = False

    @classmethod
    def create(
        cls,
        path: str | Path,
        activation: DurableEconomicInitialStateBundleV1,
    ) -> GlobalEconomicEpochJournalV1:
        normalized = _normalize_path_v1(path)
        owned_activation = _snapshot_activation_v1(activation)
        if not normalized.parent.is_dir():
            raise FileNotFoundError("durable epoch journal parent directory is absent")
        _install_epoch_store_no_replace_v1(
            normalized,
            owned_activation,
            authority_path=None,
            expected_authority=None,
        )
        return cls.open(normalized)

    @classmethod
    def open(cls, path: str | Path) -> GlobalEconomicEpochJournalV1:
        normalized = _normalize_path_v1(path)
        _require_owned_regular_epoch_store_v1(
            normalized,
            name="durable epoch journal",
        )
        validation = cls(
            normalized,
            _connect_existing_for_validation_v1(normalized),
        )
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

    def __enter__(self) -> GlobalEconomicEpochJournalV1:
        self._require_open_v1()
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()

    def _require_open_v1(self) -> None:
        if self._closed:
            raise RuntimeError("durable epoch journal is closed")

    def close(self) -> None:
        with self._lock:
            if self._closed:
                return
            self._connection.close()
            self._cas_tokens.clear()
            self._closed = True

    @property
    def head(self) -> DurableEconomicPublicationHeadV1:
        with self._lock:
            self._require_open_v1()
            return self._read_snapshot_v1()

    @property
    def activation_bundle(self) -> DurableEconomicInitialStateBundleV1:
        """Return an owned snapshot of the immutable activation bundle."""

        with self._lock:
            self._require_open_v1()
            self._connection.execute("BEGIN")
            try:
                self._validate_store_v1()
                activation = self._read_activation_v1()
                self._connection.execute("COMMIT")
                return activation
            except BaseException:
                _rollback_v1(self._connection)
                raise

    def publication_head(
        self,
        publication_id: str,
    ) -> DurableEconomicPublicationHeadV1 | None:
        """Resolve one exact activation or epoch head from validated history."""

        if type(publication_id) is not str:
            raise TypeError("durable epoch publication id must be exact str")
        _require_root(publication_id, name="durable epoch publication id")
        with self._lock:
            self._require_open_v1()
            self._connection.execute("BEGIN")
            try:
                self._validate_store_v1()
                activation = self._read_activation_v1()
                if publication_id == activation.record.activation_id:
                    result = DurableEconomicPublicationHeadV1.from_activation(
                        activation.head
                    )
                else:
                    row = self._connection.execute(
                        "SELECT publication_id, commit_id, sequence_decimal, "
                        "bundle_bytes FROM economic_epochs WHERE publication_id = ?",
                        (publication_id,),
                    ).fetchone()
                    result = (
                        None
                        if row is None
                        else self._decode_epoch_row_v1(row).head
                    )
                self._connection.execute("COMMIT")
                return result
            except BaseException:
                _rollback_v1(self._connection)
                raise

    def acquire_cas_head_token(self) -> DurableEconomicEpochCasTokenV1:
        with self._lock:
            self._require_open_v1()
            head = self._read_snapshot_v1()
            authority_coordinates = self._authority_coordinates_v1()
            token = DurableEconomicEpochCasTokenV1(
                _CAS_TOKEN_MINT_V1,
                head.publication_id,
                head.sequence,
                *authority_coordinates,
            )
            self._cas_tokens[token] = (
                self._instance_token,
                head.publication_id,
                head.sequence,
                *authority_coordinates,
            )
            return token

    def _authority_coordinates_v1(self) -> tuple[str | None, int | None]:
        expected = self._expected_authority
        if expected is None:
            return None, None
        if self._connection.in_transaction:
            current = _validate_authority_store_on_connection_v1(
                self._connection,
                database="economic_authority",
            )
            return current.authority_root, current.generation
        self._connection.execute("BEGIN")
        try:
            current = _validate_authority_store_on_connection_v1(
                self._connection,
                database="economic_authority",
            )
            self._connection.execute("COMMIT")
            return current.authority_root, current.generation
        except BaseException:
            _rollback_v1(self._connection)
            raise

    def _require_current_authority_v1(self) -> None:
        expected = self._expected_authority
        if expected is None:
            raise ValueError("durable epoch journal lacks an authority fence")
        coordinates = self._authority_coordinates_v1()
        if coordinates != (expected.authority_root, expected.generation):
            raise ValueError("durable epoch journal current authority mismatch")

    def _create_store_v1(
        self,
        activation: DurableEconomicInitialStateBundleV1,
    ) -> None:
        connection = self._connection
        try:
            connection.execute("BEGIN IMMEDIATE")
            existing = connection.execute(
                "SELECT 1 FROM sqlite_master WHERE name NOT LIKE 'sqlite_%' LIMIT 1"
            ).fetchone()
            if existing is not None:
                raise RuntimeError("epoch bootstrap candidate is not empty")
            connection.execute(_CREATE_METADATA_SQL_V1)
            connection.execute(_CREATE_EPOCHS_SQL_V1)
            connection.execute(_CREATE_CURRENT_HEAD_SQL_V1)
            connection.execute(
                "INSERT INTO metadata(singleton, schema_name, activation_id, activation_bundle) "
                "VALUES (1, ?, ?, ?)",
                (
                    DURABLE_ECONOMIC_EPOCH_SCHEMA_V1,
                    activation.record.activation_id,
                    activation.canonical_bytes,
                ),
            )
            connection.execute(
                "INSERT INTO current_head(singleton, publication_id, sequence_decimal) "
                "VALUES (1, ?, '0')",
                (activation.record.activation_id,),
            )
            connection.execute("COMMIT")
        except BaseException:
            _rollback_v1(connection)
            raise

    @staticmethod
    def _expected_columns_v1() -> tuple[tuple[str, tuple[tuple[object, ...], ...]], ...]:
        return (
            (
                "metadata",
                (
                    (0, "singleton", "INTEGER", 0, None, 1),
                    (1, "schema_name", "TEXT", 1, None, 0),
                    (2, "activation_id", "TEXT", 1, None, 0),
                    (3, "activation_bundle", "BLOB", 1, None, 0),
                ),
            ),
            (
                "economic_epochs",
                (
                    (0, "publication_id", "TEXT", 1, None, 1),
                    (1, "commit_id", "TEXT", 1, None, 0),
                    (2, "sequence_decimal", "TEXT", 1, None, 0),
                    (3, "bundle_bytes", "BLOB", 1, None, 0),
                ),
            ),
            (
                "current_head",
                (
                    (0, "singleton", "INTEGER", 0, None, 1),
                    (1, "publication_id", "TEXT", 1, None, 0),
                    (2, "sequence_decimal", "TEXT", 1, None, 0),
                ),
            ),
        )

    def _validate_schema_v1(self) -> None:
        objects = self._connection.execute(
            "SELECT name, sql FROM sqlite_master "
            "WHERE name NOT LIKE 'sqlite_%' ORDER BY name"
        ).fetchall()
        if tuple(objects) != _EXPECTED_TABLE_SQL_V1:
            raise RuntimeError("durable epoch journal exact schema mismatch")
        strict = {
            row[1]: row[5]
            for row in self._connection.execute("PRAGMA table_list").fetchall()
            if len(row) == 6 and row[1] in {name for name, _ in _EXPECTED_TABLE_SQL_V1}
        }
        if strict != {"metadata": 1, "economic_epochs": 1, "current_head": 1}:
            raise RuntimeError("durable epoch journal STRICT schema mismatch")
        for table, expected in self._expected_columns_v1():
            actual = self._connection.execute(f"PRAGMA table_info({table})").fetchall()
            if tuple(actual) != expected:
                raise RuntimeError(f"durable epoch journal {table} column mismatch")
        if self._connection.execute("PRAGMA trusted_schema").fetchone() != (0,):
            raise RuntimeError("durable epoch journal trusted schema must be disabled")
        if self._connection.execute("PRAGMA integrity_check").fetchall() != [("ok",)]:
            raise RuntimeError("durable epoch journal integrity check failed")

    def _read_activation_v1(self) -> DurableEconomicInitialStateBundleV1:
        rows = self._connection.execute(
            "SELECT singleton, schema_name, activation_id, activation_bundle "
            "FROM metadata ORDER BY singleton"
        ).fetchall()
        if len(rows) != 1 or rows[0][0] != 1 or rows[0][1] != DURABLE_ECONOMIC_EPOCH_SCHEMA_V1:
            raise RuntimeError("durable epoch metadata mismatch")
        activation_id, raw = rows[0][2], rows[0][3]
        if type(activation_id) is not str or type(raw) is not bytes:
            raise TypeError("durable epoch activation row types are invalid")
        activation = decode_durable_economic_initial_state_bundle_v1(raw)
        if activation.record.activation_id != activation_id:
            raise ValueError("durable epoch activation id mismatch")
        return activation

    @staticmethod
    def _decode_epoch_row_v1(row: tuple[object, ...]) -> DurableEconomicEpochBundleV1:
        if len(row) != 4:
            raise RuntimeError("durable epoch history row shape mismatch")
        publication_id, commit_id, sequence_decimal, raw = row
        if (
            type(publication_id) is not str
            or type(commit_id) is not str
            or type(raw) is not bytes
        ):
            raise TypeError("durable epoch history row types are invalid")
        sequence = _canonical_decimal_v1(sequence_decimal, name="durable epoch row sequence")
        epoch = decode_durable_economic_epoch_bundle_v1(raw)
        if (
            epoch.record.publication_id != publication_id
            or epoch.record.commit_id != commit_id
            or epoch.record.sequence != sequence
        ):
            raise ValueError("durable epoch history row binding mismatch")
        return epoch

    def _read_epochs_v1(self) -> tuple[DurableEconomicEpochBundleV1, ...]:
        row_count, byte_count = self._history_bounds_v1()
        if row_count > _MAX_EPOCH_HISTORY_V1:
            raise ValueError("durable epoch history exceeds row capacity")
        if byte_count > _MAX_EPOCH_STORE_BYTES_V1:
            raise ValueError("durable epoch history exceeds byte capacity")
        rows = self._connection.execute(
            "SELECT publication_id, commit_id, sequence_decimal, bundle_bytes "
            "FROM economic_epochs ORDER BY length(sequence_decimal), sequence_decimal"
        ).fetchall()
        if len(rows) != row_count:
            raise RuntimeError("durable epoch history count changed")
        return tuple(self._decode_epoch_row_v1(row) for row in rows)

    def _validate_store_v1(self) -> DurableEconomicPublicationHeadV1:
        self._validate_schema_v1()
        activation = self._read_activation_v1()
        expected_release_root = _activation_release_observation_root_v1(activation)
        current = DurableEconomicPublicationHeadV1.from_activation(activation.head)
        for expected_sequence, epoch in enumerate(self._read_epochs_v1(), start=1):
            record = epoch.record
            if record.sequence != expected_sequence:
                raise ValueError("durable epoch history sequence is not contiguous")
            bindings = (
                (record.activation_id, current.activation_id),
                (record.source_publication_id, current.publication_id),
                (record.chain_id, current.chain_id),
                (record.deployment_root, current.deployment_root),
                (record.profile_root, current.profile_root),
                (record.writer_epoch, current.writer_epoch),
                (record.height, current.height + 1),
                (record.pre_state_root, current.state_root),
                (record.release_observation_root, expected_release_root),
            )
            if any(actual != expected for actual, expected in bindings):
                raise ValueError("durable epoch history lineage mismatch")
            current = epoch.head
        rows = self._connection.execute(
            "SELECT singleton, publication_id, sequence_decimal "
            "FROM current_head ORDER BY singleton"
        ).fetchall()
        if len(rows) != 1 or rows[0][0] != 1:
            raise RuntimeError("durable epoch current head row mismatch")
        head_sequence = _canonical_decimal_v1(rows[0][2], name="durable epoch head sequence")
        if type(rows[0][1]) is not str:
            raise TypeError("durable epoch current head id must be exact str")
        if (rows[0][1], head_sequence) != (current.publication_id, current.sequence):
            raise ValueError("durable epoch current head is not the history tip")
        return current

    def _read_snapshot_v1(self) -> DurableEconomicPublicationHeadV1:
        if self._connection.in_transaction:
            return self._validate_store_v1()
        self._connection.execute("BEGIN")
        try:
            head = self._validate_store_v1()
            self._connection.execute("COMMIT")
            return head
        except BaseException:
            _rollback_v1(self._connection)
            raise

    def _commit_epoch_from_verified_publisher_v1(
        self,
        epoch: DurableEconomicEpochBundleV1,
        cas_token: DurableEconomicEpochCasTokenV1,
        write_capability: DurableEconomicEpochWriteCapabilityV1,
    ) -> DurableEconomicEpochCommitOutcomeV1:
        _require_write_capability_v1(self, write_capability)
        return self._commit_epoch_v1(epoch, cas_token, fault=None)

    def _commit_epoch_with_fault_for_test_v1(
        self,
        epoch: DurableEconomicEpochBundleV1,
        cas_token: DurableEconomicEpochCasTokenV1,
        fault: _DurableEconomicEpochCommitFaultV1,
        write_capability: DurableEconomicEpochWriteCapabilityV1,
    ) -> DurableEconomicEpochCommitOutcomeV1:
        _require_write_capability_v1(self, write_capability)
        if type(fault) is not _DurableEconomicEpochCommitFaultV1:
            raise TypeError("durable epoch test fault is not closed")
        return self._commit_epoch_v1(epoch, cas_token, fault=fault)

    def _commit_epoch_v1(
        self,
        epoch: DurableEconomicEpochBundleV1,
        cas_token: DurableEconomicEpochCasTokenV1,
        *,
        fault: _DurableEconomicEpochCommitFaultV1 | None,
    ) -> DurableEconomicEpochCommitOutcomeV1:
        owned = _snapshot_epoch_v1(epoch)
        if type(cas_token) is not DurableEconomicEpochCasTokenV1:
            raise TypeError("durable epoch commit requires exact CAS token")
        with self._lock:
            self._require_open_v1()
            binding = self._cas_tokens.get(cas_token)
            if binding is None or binding[0] is not self._instance_token:
                raise ValueError("durable epoch CAS token is foreign or forged")
            return self._commit_under_lock_v1(
                owned,
                expected_publication_id=binding[1],
                expected_sequence=binding[2],
                expected_authority_root=binding[3],
                expected_authority_generation=binding[4],
                fault=fault,
            )

    def _commit_under_lock_v1(
        self,
        epoch: DurableEconomicEpochBundleV1,
        *,
        expected_publication_id: str,
        expected_sequence: int,
        expected_authority_root: str | None,
        expected_authority_generation: int | None,
        fault: _DurableEconomicEpochCommitFaultV1 | None,
    ) -> DurableEconomicEpochCommitOutcomeV1:
        connection = self._connection
        target_bytes = epoch.canonical_bytes
        committed = False
        connection.execute("BEGIN IMMEDIATE")
        try:
            if fault is _DurableEconomicEpochCommitFaultV1.AFTER_BEGIN:
                raise _SimulatedDurableEconomicEpochCrashV1(fault.value)
            current = self._validate_store_v1()
            retry = self._exact_retry_v1(epoch, target_bytes)
            if retry is not None:
                connection.execute("COMMIT")
                committed = True
                return DurableEconomicEpochCommitOutcomeV1(
                    DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED,
                    current,
                    retry.head,
                )
            if not self._authority_is_current_v1(
                expected_authority_root,
                expected_authority_generation,
            ):
                connection.execute("ROLLBACK")
                return DurableEconomicEpochCommitOutcomeV1(
                    DurableEconomicEpochCommitStatusV1.AUTHORITY_STALE,
                    current,
                )
            record = epoch.record
            source_matches = (
                expected_publication_id == current.publication_id
                and expected_sequence == current.sequence
                and record.source_publication_id == current.publication_id
                and record.sequence == current.sequence + 1
                and record.activation_id == current.activation_id
                and record.chain_id == current.chain_id
                and record.deployment_root == current.deployment_root
                and record.profile_root == current.profile_root
                and record.writer_epoch == current.writer_epoch
                and record.height == current.height + 1
                and record.pre_state_root == current.state_root
            )
            if not source_matches:
                connection.execute("ROLLBACK")
                return DurableEconomicEpochCommitOutcomeV1(
                    DurableEconomicEpochCommitStatusV1.STALE_HEAD,
                    current,
                )
            duplicate_commit = connection.execute(
                "SELECT publication_id FROM economic_epochs WHERE commit_id = ?",
                (record.commit_id,),
            ).fetchone()
            if duplicate_commit is not None:
                raise ValueError("durable epoch commit identity is already published")
            count, byte_count = self._history_bounds_v1()
            if count + 1 > _MAX_EPOCH_HISTORY_V1 or byte_count + len(target_bytes) > _MAX_EPOCH_STORE_BYTES_V1:
                connection.execute("ROLLBACK")
                return DurableEconomicEpochCommitOutcomeV1(
                    DurableEconomicEpochCommitStatusV1.CAPACITY_EXCEEDED,
                    current,
                )
            connection.execute(
                "INSERT INTO economic_epochs("
                "publication_id, commit_id, sequence_decimal, bundle_bytes"
                ") VALUES (?, ?, ?, ?)",
                (
                    record.publication_id,
                    record.commit_id,
                    str(record.sequence),
                    target_bytes,
                ),
            )
            if fault is _DurableEconomicEpochCommitFaultV1.AFTER_INSERT:
                raise _SimulatedDurableEconomicEpochCrashV1(fault.value)
            cursor = connection.execute(
                "UPDATE current_head SET publication_id = ?, sequence_decimal = ? "
                "WHERE singleton = 1 AND publication_id = ? AND sequence_decimal = ?",
                (
                    record.publication_id,
                    str(record.sequence),
                    current.publication_id,
                    str(current.sequence),
                ),
            )
            if cursor.rowcount != 1:
                raise RuntimeError("durable epoch head CAS changed inside transaction")
            if fault is _DurableEconomicEpochCommitFaultV1.AFTER_HEAD_UPDATE_BEFORE_COMMIT:
                raise _SimulatedDurableEconomicEpochCrashV1(fault.value)
            connection.execute("COMMIT")
            committed = True
            if fault is _DurableEconomicEpochCommitFaultV1.AFTER_COMMIT_BEFORE_ACK:
                raise _SimulatedDurableEconomicEpochCrashV1(fault.value)
            return DurableEconomicEpochCommitOutcomeV1(
                DurableEconomicEpochCommitStatusV1.COMMITTED,
                epoch.head,
                epoch.head,
            )
        except BaseException:
            if not committed:
                _rollback_v1(connection)
            raise

    def _authority_is_current_v1(
        self,
        expected_authority_root: str | None,
        expected_authority_generation: int | None,
    ) -> bool:
        authority = self._expected_authority
        if authority is None:
            return False
        current = _validate_authority_store_on_connection_v1(
            self._connection,
            database="economic_authority",
        )
        return (
            current.status is GlobalEconomicAuthorityStatusV1.ACTIVE
            and current == authority
            and current.authority_root == expected_authority_root
            and current.generation == expected_authority_generation
        )

    def _exact_retry_v1(
        self,
        epoch: DurableEconomicEpochBundleV1,
        target_bytes: bytes,
    ) -> DurableEconomicEpochBundleV1 | None:
        row = self._connection.execute(
            "SELECT publication_id, commit_id, sequence_decimal, bundle_bytes "
            "FROM economic_epochs WHERE publication_id = ?",
            (epoch.record.publication_id,),
        ).fetchone()
        if row is None:
            return None
        existing = self._decode_epoch_row_v1(row)
        if existing.canonical_bytes != target_bytes:
            raise RuntimeError("durable epoch id collision or store corruption")
        return existing

    def _history_bounds_v1(self) -> tuple[int, int]:
        row = self._connection.execute(
            "SELECT COUNT(*), COALESCE(SUM(length(bundle_bytes)), 0) FROM economic_epochs"
        ).fetchone()
        if row is None or type(row[0]) is not int or type(row[1]) is not int:
            raise RuntimeError("durable epoch history bounds query failed")
        return row[0], row[1]


def _path_entry_exists_v1(path: Path) -> bool:
    try:
        path.lstat()
    except FileNotFoundError:
        return False
    return True


def _initialize_epoch_candidate_v1(
    candidate_path: Path,
    activation: DurableEconomicInitialStateBundleV1,
    *,
    authority_path: Path | None,
    expected_authority: GlobalEconomicAuthorityHeadV1 | None,
) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW
    try:
        candidate_fd = os.open(candidate_path, flags, 0o600)
    except FileExistsError:
        raise RuntimeError(
            "durable epoch crash-left bootstrap candidate exists"
        ) from None
    os.close(candidate_fd)
    candidate = GlobalEconomicEpochJournalV1(
        candidate_path,
        _connect_v1(candidate_path, authority_path),
        expected_authority=expected_authority,
    )
    try:
        candidate._create_store_v1(activation)
        candidate._read_snapshot_v1()
        if expected_authority is not None:
            candidate._require_current_authority_v1()
    finally:
        candidate.close()
    _require_owned_regular_epoch_store_v1(
        candidate_path,
        name="durable epoch bootstrap candidate",
    )
    fsync_fd = os.open(
        candidate_path,
        os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
    )
    try:
        os.fsync(fsync_fd)
    finally:
        os.close(fsync_fd)


def _recover_linked_epoch_install_v1(
    path: Path,
    candidate_path: Path,
    activation: DurableEconomicInitialStateBundleV1,
    directory_fd: int,
    *,
    authority_path: Path | None,
    expected_authority: GlobalEconomicAuthorityHeadV1 | None,
) -> None:
    """Complete only the exact validated two-name post-link crash state."""

    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
    final_fd = os.open(path, flags)
    try:
        candidate_fd = os.open(candidate_path, flags)
        try:
            final_metadata = os.fstat(final_fd)
            candidate_metadata = os.fstat(candidate_fd)
            _require_linked_private_epoch_inode_v1(
                final_metadata,
                name="durable epoch final store",
            )
            _require_linked_private_epoch_inode_v1(
                candidate_metadata,
                name="durable epoch bootstrap candidate",
            )
            if not _same_epoch_inode_v1(final_metadata, candidate_metadata):
                raise RuntimeError(
                    "durable epoch bootstrap names do not share one inode"
                )
            _reject_wal_artifacts_v1(path)
            _reject_wal_artifacts_v1(candidate_path)
            validation = GlobalEconomicEpochJournalV1(
                path,
                _connect_epoch_descriptor_for_validation_v1(
                    final_fd,
                    authority_path,
                ),
                expected_authority=expected_authority,
            )
            try:
                if (
                    validation.activation_bundle.canonical_bytes
                    != activation.canonical_bytes
                ):
                    raise RuntimeError(
                        "durable epoch bootstrap recovery activation mismatch"
                    )
                expected_head = DurableEconomicPublicationHeadV1.from_activation(
                    activation.head
                )
                if validation.head != expected_head:
                    raise RuntimeError(
                        "durable epoch bootstrap recovery requires sequence zero"
                    )
                if expected_authority is not None:
                    validation._require_current_authority_v1()
            finally:
                validation.close()
            _require_epoch_path_matches_fd_v1(
                path,
                final_fd,
                name="durable epoch final store",
            )
            _require_epoch_path_matches_fd_v1(
                candidate_path,
                candidate_fd,
                name="durable epoch bootstrap candidate",
            )
            os.unlink(candidate_path.name, dir_fd=directory_fd)
            os.fsync(directory_fd)
            _require_epoch_path_matches_fd_v1(
                path,
                final_fd,
                name="durable epoch final store",
            )
            if os.fstat(final_fd).st_nlink != 1:
                raise RuntimeError("durable epoch recovery did not restore one link")
        finally:
            os.close(candidate_fd)
    finally:
        os.close(final_fd)


def _install_epoch_store_no_replace_v1(
    path: Path,
    activation: DurableEconomicInitialStateBundleV1,
    *,
    authority_path: Path | None,
    expected_authority: GlobalEconomicAuthorityHeadV1 | None,
) -> None:
    directory_fd = _acquire_epoch_bootstrap_lock_v1(path)
    try:
        candidate_path = _epoch_bootstrap_candidate_path_v1(path)
        if candidate_path == path:
            raise ValueError("durable epoch path uses a reserved name")
        final_exists = _path_entry_exists_v1(path)
        candidate_exists = _path_entry_exists_v1(candidate_path)
        if final_exists and candidate_exists:
            _recover_linked_epoch_install_v1(
                path,
                candidate_path,
                activation,
                directory_fd,
                authority_path=authority_path,
                expected_authority=expected_authority,
            )
            return
        if final_exists:
            raise FileExistsError("durable epoch journal path already exists")
        if candidate_exists:
            raise RuntimeError("durable epoch crash-left bootstrap candidate exists")
        _initialize_epoch_candidate_v1(
            candidate_path,
            activation,
            authority_path=authority_path,
            expected_authority=expected_authority,
        )
        try:
            os.link(candidate_path, path, follow_symlinks=False)
        except FileExistsError:
            raise FileExistsError("durable epoch journal path already exists") from None
        os.fsync(directory_fd)
        os.unlink(candidate_path)
        os.fsync(directory_fd)
    finally:
        _release_epoch_bootstrap_lock_v1(directory_fd)


def _create_epoch_journal_for_verified_publisher_v1(
    path: str | Path,
    activation: DurableEconomicInitialStateBundleV1,
    authority_path: Path,
    expected_authority: GlobalEconomicAuthorityHeadV1,
) -> tuple[GlobalEconomicEpochJournalV1, DurableEconomicEpochWriteCapabilityV1]:
    """Create or recover one exact journal and its publisher capability."""

    owned_activation = _snapshot_activation_v1(activation)
    try:
        normalized = _normalize_path_v1(path)
        if not normalized.parent.is_dir():
            raise FileNotFoundError("durable epoch journal parent directory is absent")
        _install_epoch_store_no_replace_v1(
            normalized,
            owned_activation,
            authority_path=authority_path,
            expected_authority=expected_authority,
        )
        journal = _open_epoch_journal_with_authority_v1(
            normalized,
            authority_path,
            expected_authority,
        )
    except FileExistsError:
        journal = _open_epoch_journal_with_authority_v1(
            path,
            authority_path,
            expected_authority,
        )
        if journal.activation_bundle.canonical_bytes != owned_activation.canonical_bytes:
            journal.close()
            raise ValueError(
                "durable epoch journal existing activation bundle mismatch"
            ) from None
        expected_head = DurableEconomicPublicationHeadV1.from_activation(
            owned_activation.head
        )
        if journal.head != expected_head:
            journal.close()
            raise ValueError(
                "durable epoch journal create recovery requires sequence-zero "
                "activation head"
            ) from None
    try:
        journal._require_current_authority_v1()
        capability = _mint_write_capability_for_verified_publisher_v1(journal)
    except BaseException:
        journal.close()
        raise
    return journal, capability


def _open_epoch_journal_for_verified_publisher_v1(
    path: str | Path,
    authority_path: Path,
    expected_authority: GlobalEconomicAuthorityHeadV1,
) -> tuple[GlobalEconomicEpochJournalV1, DurableEconomicEpochWriteCapabilityV1]:
    """Open one journal and mint a fresh instance-bound publisher capability."""

    journal = _open_epoch_journal_with_authority_v1(
        path,
        authority_path,
        expected_authority,
    )
    try:
        capability = _mint_write_capability_for_verified_publisher_v1(journal)
    except BaseException:
        journal.close()
        raise
    return journal, capability


def _open_epoch_journal_with_authority_v1(
    path: str | Path,
    authority_path: Path,
    expected_authority: GlobalEconomicAuthorityHeadV1,
) -> GlobalEconomicEpochJournalV1:
    normalized = _normalize_path_v1(path)
    _require_owned_regular_epoch_store_v1(
        normalized,
        name="durable epoch journal",
    )
    validation = GlobalEconomicEpochJournalV1(
        normalized,
        _connect_existing_for_validation_v1(normalized, authority_path),
        expected_authority=expected_authority,
    )
    try:
        validation._read_snapshot_v1()
    finally:
        validation.close()
    journal = GlobalEconomicEpochJournalV1(
        normalized,
        _connect_v1(normalized, authority_path),
        expected_authority=expected_authority,
    )
    try:
        journal._read_snapshot_v1()
    except BaseException:
        journal.close()
        raise
    return journal


def _mint_write_capability_for_verified_publisher_v1(
    journal: GlobalEconomicEpochJournalV1,
) -> DurableEconomicEpochWriteCapabilityV1:
    """Central same-process issuer for the unmounted verified publisher."""

    if type(journal) is not GlobalEconomicEpochJournalV1:
        raise TypeError("durable epoch write capability journal type is not closed")
    if journal._expected_authority is None:
        raise ValueError("durable epoch writer requires a current-authority fence")
    return DurableEconomicEpochWriteCapabilityV1(
        _WRITE_CAPABILITY_MINT_V1,
        journal,
    )


__all__ = [
    "DurableEconomicEpochBootstrapBusyV1",
    "DurableEconomicEpochLegacyStoreMigrationRequiredV1",
    "DurableEconomicEpochCasTokenV1",
    "DurableEconomicEpochCommitOutcomeV1",
    "DurableEconomicEpochCommitStatusV1",
    "GlobalEconomicEpochJournalV1",
]

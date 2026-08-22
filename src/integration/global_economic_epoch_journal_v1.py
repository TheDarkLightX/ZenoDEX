"""Atomic SQLite journal for complete ordinary economic epoch bundles.

This adapter is deliberately unmounted.  It offers bounded durability, CAS,
exact retry, and coherent recovery.  It does not verify proof receipts or grant
settlement, finality, consensus, or production writer authority.
"""

from __future__ import annotations

import sqlite3
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from threading import Lock
from typing import Final
from weakref import WeakKeyDictionary

from ..core.global_economic_durable_activation_v1 import (
    DurableEconomicComponentKindV1,
    DurableEconomicInitialStateBundleV1,
    _decode_exact_canonical_json_v1,
    decode_durable_economic_initial_state_bundle_v1,
)
from ..core.global_settlement_types_v1 import hash_global_v1
from .global_economic_durable_epoch_v1 import (
    DURABLE_ECONOMIC_EPOCH_SCHEMA_V1,
    DurableEconomicEpochBundleV1,
    DurableEconomicPublicationHeadV1,
    decode_durable_economic_epoch_bundle_v1,
)

_MAX_EPOCH_HISTORY_V1: Final = 4096
_MAX_EPOCH_STORE_BYTES_V1: Final = 512 * 1024 * 1024
_CAS_TOKEN_MINT_V1: Final = object()
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

    __slots__ = ("__publication_id", "__sequence", "__sealed", "__weakref__")
    __publication_id: str
    __sequence: int
    __sealed: bool

    def __init__(self, mint: object, publication_id: str, sequence: int) -> None:
        if mint is not _CAS_TOKEN_MINT_V1:
            raise TypeError("durable epoch CAS tokens are journal-minted")
        object.__setattr__(self, "_DurableEconomicEpochCasTokenV1__publication_id", publication_id)
        object.__setattr__(self, "_DurableEconomicEpochCasTokenV1__sequence", sequence)
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


class _DurableEconomicEpochCommitFaultV1(str, Enum):
    AFTER_BEGIN = "AFTER_BEGIN"
    AFTER_INSERT = "AFTER_INSERT"
    AFTER_HEAD_UPDATE_BEFORE_COMMIT = "AFTER_HEAD_UPDATE_BEFORE_COMMIT"
    AFTER_COMMIT_BEFORE_ACK = "AFTER_COMMIT_BEFORE_ACK"


class _SimulatedDurableEconomicEpochCrashV1(RuntimeError):
    pass


def _normalize_path_v1(path: str | Path) -> Path:
    if type(path) is str:
        candidate = Path(path)
    elif isinstance(path, Path):
        candidate = path
    else:
        raise TypeError("durable epoch journal path must be str or Path")
    if not candidate.name:
        raise ValueError("durable epoch journal path must name a file")
    return candidate.absolute()


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

    def __init__(self, path: Path, connection: sqlite3.Connection) -> None:
        self._path = path
        self._connection = connection
        self._lock = Lock()
        self._instance_token = object()
        self._cas_tokens: WeakKeyDictionary[
            DurableEconomicEpochCasTokenV1,
            tuple[object, str, int],
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
        if normalized.exists() or normalized.is_symlink():
            raise FileExistsError("durable epoch journal path already exists")
        if not normalized.parent.is_dir():
            raise FileNotFoundError("durable epoch journal parent directory is absent")
        journal = cls(normalized, _connect_v1(normalized))
        try:
            journal._create_store_v1(owned_activation)
            journal._read_snapshot_v1()
        except BaseException:
            journal.close()
            raise
        return journal

    @classmethod
    def open(cls, path: str | Path) -> GlobalEconomicEpochJournalV1:
        normalized = _normalize_path_v1(path)
        if normalized.is_symlink():
            raise ValueError("durable epoch journal path must not be a symlink")
        if not normalized.is_file():
            raise FileNotFoundError("durable epoch journal file is absent")
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

    def acquire_cas_head_token(self) -> DurableEconomicEpochCasTokenV1:
        with self._lock:
            self._require_open_v1()
            head = self._read_snapshot_v1()
            token = DurableEconomicEpochCasTokenV1(
                _CAS_TOKEN_MINT_V1,
                head.publication_id,
                head.sequence,
            )
            self._cas_tokens[token] = (
                self._instance_token,
                head.publication_id,
                head.sequence,
            )
            return token

    def _create_store_v1(
        self,
        activation: DurableEconomicInitialStateBundleV1,
    ) -> None:
        connection = self._connection
        connection.execute("BEGIN IMMEDIATE")
        try:
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
        rows = self._connection.execute(
            "SELECT publication_id, commit_id, sequence_decimal, bundle_bytes "
            "FROM economic_epochs ORDER BY length(sequence_decimal), sequence_decimal"
        ).fetchall()
        if len(rows) > _MAX_EPOCH_HISTORY_V1:
            raise ValueError("durable epoch history exceeds row capacity")
        if sum(len(row[3]) for row in rows if type(row[3]) is bytes) > _MAX_EPOCH_STORE_BYTES_V1:
            raise ValueError("durable epoch history exceeds byte capacity")
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

    def commit_epoch(
        self,
        epoch: DurableEconomicEpochBundleV1,
        cas_token: DurableEconomicEpochCasTokenV1,
    ) -> DurableEconomicEpochCommitOutcomeV1:
        return self._commit_epoch_v1(epoch, cas_token, fault=None)

    def _commit_epoch_with_fault_for_test_v1(
        self,
        epoch: DurableEconomicEpochBundleV1,
        cas_token: DurableEconomicEpochCasTokenV1,
        fault: _DurableEconomicEpochCommitFaultV1,
    ) -> DurableEconomicEpochCommitOutcomeV1:
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
                fault=fault,
            )

    def _commit_under_lock_v1(
        self,
        epoch: DurableEconomicEpochBundleV1,
        *,
        expected_publication_id: str,
        expected_sequence: int,
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


__all__ = [
    "DurableEconomicEpochCasTokenV1",
    "DurableEconomicEpochCommitOutcomeV1",
    "DurableEconomicEpochCommitStatusV1",
    "GlobalEconomicEpochJournalV1",
]

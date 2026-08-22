"""SQLite durability shell for complete global economic activation bundles.

The journal provides a bounded compare-and-swap checkpoint for genesis and
migration activation bundles.  It is deliberately unmounted and does not
publish ordinary epochs, verify receipts, or establish consensus finality.
"""

from __future__ import annotations

import sqlite3
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from threading import Lock
from typing import Final
from weakref import WeakKeyDictionary

from ..core.economic_initial_state_atom_coverage_v1 import EconomicInitialStateKindV1
from ..core.global_economic_durable_activation_v1 import (
    DURABLE_ECONOMIC_ACTIVATION_SCHEMA_V1,
    MAX_DURABLE_ECONOMIC_BUNDLE_BYTES_V1,
    DurableEconomicHeadV1,
    DurableEconomicInitialStateBundleV1,
    decode_durable_economic_initial_state_bundle_v1,
)

_MAX_ACTIVATION_HISTORY_V1: Final = 256
_MAX_ACTIVATION_STORE_BYTES_V1: Final = 256 * 1024 * 1024
_CAS_TOKEN_MINT_V1: Final = object()
_CREATE_METADATA_SQL_V1: Final = (
    "CREATE TABLE metadata ("
    "singleton INTEGER PRIMARY KEY CHECK (singleton = 1), "
    "schema_name TEXT NOT NULL"
    ") STRICT"
)
_CREATE_ACTIVATIONS_SQL_V1: Final = (
    "CREATE TABLE activations ("
    "activation_id TEXT PRIMARY KEY NOT NULL, "
    "generation_decimal TEXT NOT NULL UNIQUE, "
    "bundle_bytes BLOB NOT NULL"
    ") STRICT"
)
_CREATE_CURRENT_HEAD_SQL_V1: Final = (
    "CREATE TABLE current_head ("
    "singleton INTEGER PRIMARY KEY CHECK (singleton = 1), "
    "activation_id TEXT NOT NULL, "
    "FOREIGN KEY (activation_id) REFERENCES activations (activation_id)"
    ") STRICT"
)
_EXPECTED_TABLE_SQL_V1: Final = (
    ("activations", _CREATE_ACTIVATIONS_SQL_V1),
    ("current_head", _CREATE_CURRENT_HEAD_SQL_V1),
    ("metadata", _CREATE_METADATA_SQL_V1),
)


class DurableEconomicCommitStatusV1(str, Enum):
    COMMITTED = "COMMITTED"
    ALREADY_COMMITTED = "ALREADY_COMMITTED"
    STALE_HEAD = "STALE_HEAD"
    CAPACITY_EXCEEDED = "CAPACITY_EXCEEDED"


@dataclass(frozen=True, slots=True)
class DurableEconomicCommitOutcomeV1:
    status: DurableEconomicCommitStatusV1
    head: DurableEconomicHeadV1
    committed_activation: DurableEconomicHeadV1 | None = None

    def __post_init__(self) -> None:
        if type(self.status) is not DurableEconomicCommitStatusV1:
            raise TypeError("durable economic commit status is not closed")
        if type(self.head) is not DurableEconomicHeadV1:
            raise TypeError("durable economic commit outcome head is not closed")
        committed_statuses = {
            DurableEconomicCommitStatusV1.COMMITTED,
            DurableEconomicCommitStatusV1.ALREADY_COMMITTED,
        }
        if self.status in committed_statuses:
            if type(self.committed_activation) is not DurableEconomicHeadV1:
                raise TypeError("durable economic successful outcome lacks activation")
        elif self.committed_activation is not None:
            raise ValueError("durable economic no-effect outcome declares an activation")


class DurableEconomicCasHeadTokenV1:
    """Process-local CAS snapshot token; it grants no writer authorization."""

    __slots__ = ("__activation_id", "__generation", "__sealed", "__weakref__")
    __activation_id: str
    __generation: int
    __sealed: bool

    def __init__(
        self,
        mint: object,
        activation_id: str,
        generation: int,
    ) -> None:
        if mint is not _CAS_TOKEN_MINT_V1:
            raise TypeError("durable economic CAS tokens are journal-minted")
        object.__setattr__(self, "_DurableEconomicCasHeadTokenV1__activation_id", activation_id)
        object.__setattr__(self, "_DurableEconomicCasHeadTokenV1__generation", generation)
        object.__setattr__(self, "_DurableEconomicCasHeadTokenV1__sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_DurableEconomicCasHeadTokenV1__sealed", False):
            raise TypeError("durable economic CAS head tokens are immutable")
        object.__setattr__(self, name, value)

    @property
    def activation_id(self) -> str:
        return self.__activation_id

    @property
    def generation(self) -> int:
        return self.__generation


class _DurableEconomicCommitFaultV1(str, Enum):
    AFTER_BEGIN = "AFTER_BEGIN"
    AFTER_INSERT = "AFTER_INSERT"
    AFTER_HEAD_UPDATE_BEFORE_COMMIT = "AFTER_HEAD_UPDATE_BEFORE_COMMIT"
    AFTER_COMMIT_BEFORE_ACK = "AFTER_COMMIT_BEFORE_ACK"


class _SimulatedDurableEconomicCrashV1(RuntimeError):
    pass


def _normalize_journal_path_v1(path: str | Path) -> Path:
    if type(path) is str:
        candidate = Path(path)
    elif isinstance(path, Path):
        candidate = path
    else:
        raise TypeError("durable economic journal path must be str or Path")
    if not candidate.name:
        raise ValueError("durable economic journal path must name a file")
    return candidate.absolute()


def _configure_connection_v1(connection: sqlite3.Connection) -> None:
    connection.execute("PRAGMA foreign_keys = ON")
    foreign_keys = connection.execute("PRAGMA foreign_keys").fetchone()
    if foreign_keys != (1,):
        raise RuntimeError("durable economic journal could not enable foreign keys")
    journal_mode = connection.execute("PRAGMA journal_mode = DELETE").fetchone()
    if journal_mode is None or str(journal_mode[0]).lower() != "delete":
        raise RuntimeError("durable economic journal requires DELETE journal mode")
    connection.execute("PRAGMA synchronous = FULL")
    synchronous = connection.execute("PRAGMA synchronous").fetchone()
    if synchronous != (2,):
        raise RuntimeError("durable economic journal requires FULL synchronization")
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


def _rollback_if_active_v1(connection: sqlite3.Connection) -> None:
    if connection.in_transaction:
        connection.execute("ROLLBACK")


def _snapshot_bundle_v1(
    bundle: DurableEconomicInitialStateBundleV1,
) -> DurableEconomicInitialStateBundleV1:
    if type(bundle) is not DurableEconomicInitialStateBundleV1:
        raise TypeError("durable economic bundle type is not closed")
    return decode_durable_economic_initial_state_bundle_v1(bundle.canonical_bytes)


class GlobalEconomicMigrationJournalV1:
    """Durable PRE-or-POST migration activation checkpoint."""

    def __init__(self, path: Path, connection: sqlite3.Connection) -> None:
        self._path = path
        self._connection = connection
        self._lock = Lock()
        self._instance_token = object()
        self._cas_tokens: WeakKeyDictionary[
            DurableEconomicCasHeadTokenV1,
            tuple[object, str, int],
        ] = WeakKeyDictionary()
        self._closed = False

    @classmethod
    def create(
        cls,
        path: str | Path,
        genesis_bundle: DurableEconomicInitialStateBundleV1,
    ) -> GlobalEconomicMigrationJournalV1:
        normalized = _normalize_journal_path_v1(path)
        owned_genesis = _snapshot_bundle_v1(genesis_bundle)
        if owned_genesis.record.kind is not EconomicInitialStateKindV1.GENESIS:
            raise ValueError("durable journal must be created from genesis")
        if normalized.exists() or normalized.is_symlink():
            raise FileExistsError("durable economic journal path already exists")
        if not normalized.parent.is_dir():
            raise FileNotFoundError("durable economic journal parent directory is absent")
        connection = _connect_v1(normalized)
        journal = cls(normalized, connection)
        try:
            journal._create_schema_and_genesis_v1(owned_genesis)
            journal._read_snapshot_v1()
        except BaseException:
            journal.close()
            raise
        return journal

    @classmethod
    def open(cls, path: str | Path) -> GlobalEconomicMigrationJournalV1:
        normalized = _normalize_journal_path_v1(path)
        if normalized.is_symlink():
            raise ValueError("durable economic journal path must not be a symlink")
        if not normalized.is_file():
            raise FileNotFoundError("durable economic journal file is absent")
        connection = _connect_v1(normalized)
        journal = cls(normalized, connection)
        try:
            journal._read_snapshot_v1()
        except BaseException:
            journal.close()
            raise
        return journal

    def __enter__(self) -> GlobalEconomicMigrationJournalV1:
        self._require_open_v1()
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()

    def _require_open_v1(self) -> None:
        if self._closed:
            raise RuntimeError("durable economic journal is closed")

    def close(self) -> None:
        with self._lock:
            if self._closed:
                return
            self._connection.close()
            self._cas_tokens.clear()
            self._closed = True

    @property
    def path(self) -> Path:
        return self._path

    @property
    def head(self) -> DurableEconomicHeadV1:
        with self._lock:
            self._require_open_v1()
            return self._read_snapshot_v1()

    def acquire_cas_head_token(self) -> DurableEconomicCasHeadTokenV1:
        with self._lock:
            self._require_open_v1()
            head = self._read_snapshot_v1()
            token = DurableEconomicCasHeadTokenV1(
                _CAS_TOKEN_MINT_V1,
                head.activation_id,
                head.generation,
            )
            self._cas_tokens[token] = (
                self._instance_token,
                head.activation_id,
                head.generation,
            )
            return token

    def _create_schema_and_genesis_v1(
        self,
        genesis_bundle: DurableEconomicInitialStateBundleV1,
    ) -> None:
        bundle_bytes = genesis_bundle.canonical_bytes
        connection = self._connection
        connection.execute("BEGIN IMMEDIATE")
        try:
            connection.execute(_CREATE_METADATA_SQL_V1)
            connection.execute(_CREATE_ACTIVATIONS_SQL_V1)
            connection.execute(_CREATE_CURRENT_HEAD_SQL_V1)
            connection.execute(
                "INSERT INTO metadata(singleton, schema_name) VALUES (1, ?)",
                (DURABLE_ECONOMIC_ACTIVATION_SCHEMA_V1,),
            )
            connection.execute(
                """
                INSERT INTO activations(
                    activation_id,
                    generation_decimal,
                    bundle_bytes
                ) VALUES (?, ?, ?)
                """,
                (
                    genesis_bundle.record.activation_id,
                    str(genesis_bundle.record.generation),
                    bundle_bytes,
                ),
            )
            connection.execute(
                "INSERT INTO current_head(singleton, activation_id) VALUES (1, ?)",
                (genesis_bundle.record.activation_id,),
            )
            connection.execute("COMMIT")
        except BaseException:
            _rollback_if_active_v1(connection)
            raise

    @staticmethod
    def _expected_columns_v1(
        ) -> tuple[tuple[str, tuple[tuple[object, ...], ...]], ...]:
        return (
            ("metadata", (
                (0, "singleton", "INTEGER", 0, None, 1),
                (1, "schema_name", "TEXT", 1, None, 0),
            )),
            ("activations", (
                (0, "activation_id", "TEXT", 1, None, 1),
                (1, "generation_decimal", "TEXT", 1, None, 0),
                (2, "bundle_bytes", "BLOB", 1, None, 0),
            )),
            ("current_head", (
                (0, "singleton", "INTEGER", 0, None, 1),
                (1, "activation_id", "TEXT", 1, None, 0),
            )),
        )

    def _validate_schema_v1(self) -> None:
        connection = self._connection
        objects = connection.execute(
            """
            SELECT name, sql
            FROM sqlite_master
            WHERE name NOT LIKE 'sqlite_%'
            ORDER BY name
            """
        ).fetchall()
        if tuple(objects) != _EXPECTED_TABLE_SQL_V1:
            raise RuntimeError("durable economic journal exact schema mismatch")
        table_rows = connection.execute("PRAGMA table_list").fetchall()
        strict_by_name = {
            row[1]: row[5]
            for row in table_rows
            if len(row) == 6 and row[1] in {name for name, _ in _EXPECTED_TABLE_SQL_V1}
        }
        if strict_by_name != {
            "activations": 1,
            "current_head": 1,
            "metadata": 1,
        }:
            raise RuntimeError("durable economic journal STRICT schema mismatch")
        for table_name, expected_columns in self._expected_columns_v1():
            columns = connection.execute(f"PRAGMA table_info({table_name})").fetchall()
            if tuple(columns) != expected_columns:
                raise RuntimeError(
                    f"durable economic journal {table_name} column schema mismatch"
                )
        metadata_rows = connection.execute(
            "SELECT singleton, schema_name FROM metadata ORDER BY singleton"
        ).fetchall()
        if metadata_rows != [(1, DURABLE_ECONOMIC_ACTIVATION_SCHEMA_V1)]:
            raise RuntimeError("durable economic journal metadata mismatch")
        foreign_keys = connection.execute("PRAGMA foreign_key_list(current_head)").fetchall()
        if len(foreign_keys) != 1:
            raise RuntimeError("durable economic journal foreign-key schema mismatch")
        foreign_key = foreign_keys[0]
        if (
            foreign_key[2],
            foreign_key[3],
            foreign_key[4],
            foreign_key[5],
            foreign_key[6],
        ) != (
            "activations",
            "activation_id",
            "activation_id",
            "NO ACTION",
            "NO ACTION",
        ):
            raise RuntimeError("durable economic journal foreign-key binding mismatch")
        if connection.execute("PRAGMA foreign_key_check").fetchall():
            raise RuntimeError("durable economic journal foreign-key check failed")
        index_rows = connection.execute("PRAGMA index_list(activations)").fetchall()
        index_contracts = {(row[2], row[3], row[4]) for row in index_rows}
        if index_contracts != {(1, "pk", 0), (1, "u", 0)}:
            raise RuntimeError("durable economic journal unique-index schema mismatch")
        if connection.execute("PRAGMA trusted_schema").fetchone() != (0,):
            raise RuntimeError("durable economic journal trusted schema must be disabled")
        integrity = connection.execute("PRAGMA integrity_check").fetchall()
        if integrity != [("ok",)]:
            raise RuntimeError("durable economic journal integrity check failed")

    @staticmethod
    def _decode_activation_row_v1(
        row: tuple[object, ...],
    ) -> DurableEconomicInitialStateBundleV1:
        if len(row) != 3:
            raise RuntimeError("durable economic activation row shape mismatch")
        activation_id, generation_decimal, raw_bundle = row
        if type(activation_id) is not str:
            raise TypeError("durable activation row id must be exact str")
        if type(generation_decimal) is not str:
            raise TypeError("durable activation row generation must be exact str")
        if (
            not generation_decimal
            or not generation_decimal.isascii()
            or not generation_decimal.isdecimal()
            or (len(generation_decimal) > 1 and generation_decimal.startswith("0"))
        ):
            raise ValueError("durable activation row generation is not canonical decimal")
        if type(raw_bundle) is not bytes:
            raise TypeError("durable activation row bundle must be exact bytes")
        bundle = decode_durable_economic_initial_state_bundle_v1(raw_bundle)
        if activation_id != bundle.record.activation_id:
            raise ValueError("durable activation row id mismatch")
        if generation_decimal != str(bundle.record.generation):
            raise ValueError("durable activation row generation mismatch")
        return bundle

    def _history_bounds_v1(self) -> tuple[int, int]:
        bounds = self._connection.execute(
            "SELECT COUNT(*), COALESCE(SUM(LENGTH(bundle_bytes)), 0) FROM activations"
        ).fetchone()
        if (
            bounds is None
            or len(bounds) != 2
            or type(bounds[0]) is not int
            or type(bounds[1]) is not int
        ):
            raise RuntimeError("durable economic activation history bounds are malformed")
        if not 1 <= bounds[0] <= _MAX_ACTIVATION_HISTORY_V1:
            raise RuntimeError("durable economic activation history is outside its bound")
        if not 1 <= bounds[1] <= _MAX_ACTIVATION_STORE_BYTES_V1:
            raise RuntimeError("durable economic activation store is outside its byte bound")
        return bounds

    def _read_history_v1(self) -> tuple[DurableEconomicInitialStateBundleV1, ...]:
        self._history_bounds_v1()
        rows = self._connection.execute(
            """
            SELECT activation_id, generation_decimal, bundle_bytes
            FROM activations
            """
        ).fetchall()
        if any(
            type(row[2]) is not bytes
            or not 1 <= len(row[2]) <= MAX_DURABLE_ECONOMIC_BUNDLE_BYTES_V1
            for row in rows
        ):
            raise RuntimeError("durable economic activation row is outside its byte bound")
        bundles = tuple(self._decode_activation_row_v1(row) for row in rows)
        return tuple(sorted(bundles, key=lambda item: item.record.generation))

    def _validate_store_v1(self) -> DurableEconomicHeadV1:
        if not self._connection.in_transaction:
            raise RuntimeError("durable economic store validation requires one snapshot")
        self._validate_schema_v1()
        bundles = self._read_history_v1()
        genesis = bundles[0].record
        if genesis.kind is not EconomicInitialStateKindV1.GENESIS:
            raise ValueError("durable economic history does not begin with genesis")
        for expected_generation, bundle in enumerate(bundles):
            record = bundle.record
            if record.generation != expected_generation:
                raise ValueError("durable economic history generation is not contiguous")
            if expected_generation == 0:
                continue
            predecessor = bundles[expected_generation - 1].record
            if record.kind is not EconomicInitialStateKindV1.MIGRATION:
                raise ValueError("durable economic successor is not a migration")
            bindings = (
                (record.source_activation_id, predecessor.activation_id),
                (record.chain_id, predecessor.chain_id),
                (record.deployment_root, predecessor.deployment_root),
                (record.source_profile_root, predecessor.profile_root),
                (record.source_state_root, predecessor.state_root),
                (record.source_writer_epoch, predecessor.writer_epoch),
                (record.source_height, predecessor.height),
            )
            if any(actual != expected for actual, expected in bindings):
                raise ValueError("durable economic history lineage mismatch")
        head_rows = self._connection.execute(
            "SELECT singleton, activation_id FROM current_head ORDER BY singleton"
        ).fetchall()
        if len(head_rows) != 1 or head_rows[0][0] != 1:
            raise RuntimeError("durable economic current head row mismatch")
        current_activation_id = head_rows[0][1]
        if type(current_activation_id) is not str:
            raise TypeError("durable economic current head id must be exact str")
        if current_activation_id != bundles[-1].record.activation_id:
            raise ValueError("durable economic current head is not the history tip")
        return bundles[-1].head

    def _read_snapshot_v1(self) -> DurableEconomicHeadV1:
        connection = self._connection
        if connection.in_transaction:
            return self._validate_store_v1()
        connection.execute("BEGIN")
        try:
            head = self._validate_store_v1()
            connection.execute("COMMIT")
            return head
        except BaseException:
            _rollback_if_active_v1(connection)
            raise

    def commit_migration(
        self,
        migration_bundle: DurableEconomicInitialStateBundleV1,
        cas_head_token: DurableEconomicCasHeadTokenV1,
    ) -> DurableEconomicCommitOutcomeV1:
        return self._commit_migration_v1(
            migration_bundle,
            cas_head_token,
            fault=None,
        )

    def _commit_migration_with_fault_for_test_v1(
        self,
        migration_bundle: DurableEconomicInitialStateBundleV1,
        cas_head_token: DurableEconomicCasHeadTokenV1,
        fault: _DurableEconomicCommitFaultV1,
    ) -> DurableEconomicCommitOutcomeV1:
        if type(fault) is not _DurableEconomicCommitFaultV1:
            raise TypeError("durable economic test fault is not closed")
        return self._commit_migration_v1(migration_bundle, cas_head_token, fault=fault)

    def _commit_migration_v1(
        self,
        migration_bundle: DurableEconomicInitialStateBundleV1,
        cas_head_token: DurableEconomicCasHeadTokenV1,
        *,
        fault: _DurableEconomicCommitFaultV1 | None,
    ) -> DurableEconomicCommitOutcomeV1:
        owned_migration = _snapshot_bundle_v1(migration_bundle)
        if owned_migration.record.kind is not EconomicInitialStateKindV1.MIGRATION:
            raise ValueError("durable migration commit requires a migration bundle")
        if type(cas_head_token) is not DurableEconomicCasHeadTokenV1:
            raise TypeError("durable migration commit requires an exact CAS head token")
        with self._lock:
            self._require_open_v1()
            token_binding = self._cas_tokens.get(cas_head_token)
            if token_binding is None or token_binding[0] is not self._instance_token:
                raise ValueError("durable migration CAS head token is foreign or forged")
            return self._commit_under_lock_v1(
                owned_migration,
                expected_activation_id=token_binding[1],
                expected_generation=token_binding[2],
                fault=fault,
            )

    def _commit_under_lock_v1(
        self,
        migration_bundle: DurableEconomicInitialStateBundleV1,
        *,
        expected_activation_id: str,
        expected_generation: int,
        fault: _DurableEconomicCommitFaultV1 | None,
    ) -> DurableEconomicCommitOutcomeV1:
        connection = self._connection
        target_bytes = migration_bundle.canonical_bytes
        committed = False
        connection.execute("BEGIN IMMEDIATE")
        try:
            if fault is _DurableEconomicCommitFaultV1.AFTER_BEGIN:
                raise _SimulatedDurableEconomicCrashV1(fault.value)
            current_head = self._validate_store_v1()
            committed_retry = self._exact_committed_retry_v1(
                migration_bundle,
                target_bytes,
            )
            if committed_retry is not None:
                connection.execute("COMMIT")
                committed = True
                return DurableEconomicCommitOutcomeV1(
                    DurableEconomicCommitStatusV1.ALREADY_COMMITTED,
                    current_head,
                    committed_retry.head,
                )
            if not self._source_matches_v1(
                migration_bundle,
                current_head,
                expected_activation_id=expected_activation_id,
                expected_generation=expected_generation,
            ):
                connection.execute("ROLLBACK")
                return DurableEconomicCommitOutcomeV1(
                    DurableEconomicCommitStatusV1.STALE_HEAD,
                    current_head,
                )
            if not self._projected_capacity_allows_v1(len(target_bytes)):
                connection.execute("ROLLBACK")
                return DurableEconomicCommitOutcomeV1(
                    DurableEconomicCommitStatusV1.CAPACITY_EXCEEDED,
                    current_head,
                )
            self._insert_activation_v1(migration_bundle, target_bytes)
            if fault is _DurableEconomicCommitFaultV1.AFTER_INSERT:
                raise _SimulatedDurableEconomicCrashV1(fault.value)
            cursor = connection.execute(
                """
                UPDATE current_head
                SET activation_id = ?
                WHERE singleton = 1 AND activation_id = ?
                """,
                (
                    migration_bundle.record.activation_id,
                    current_head.activation_id,
                ),
            )
            if cursor.rowcount != 1:
                raise RuntimeError("durable economic head CAS changed inside transaction")
            if fault is _DurableEconomicCommitFaultV1.AFTER_HEAD_UPDATE_BEFORE_COMMIT:
                raise _SimulatedDurableEconomicCrashV1(fault.value)
            connection.execute("COMMIT")
            committed = True
            if fault is _DurableEconomicCommitFaultV1.AFTER_COMMIT_BEFORE_ACK:
                raise _SimulatedDurableEconomicCrashV1(fault.value)
            return DurableEconomicCommitOutcomeV1(
                DurableEconomicCommitStatusV1.COMMITTED,
                migration_bundle.head,
                migration_bundle.head,
            )
        except BaseException:
            if not committed and connection.in_transaction:
                connection.execute("ROLLBACK")
            raise

    def _exact_committed_retry_v1(
        self,
        migration_bundle: DurableEconomicInitialStateBundleV1,
        target_bytes: bytes,
    ) -> DurableEconomicInitialStateBundleV1 | None:
        existing_row = self._connection.execute(
            """
            SELECT activation_id, generation_decimal, bundle_bytes
            FROM activations
            WHERE activation_id = ?
            """,
            (migration_bundle.record.activation_id,),
        ).fetchone()
        if existing_row is None:
            return None
        existing_bundle = self._decode_activation_row_v1(existing_row)
        if existing_bundle.canonical_bytes != target_bytes:
            raise RuntimeError("durable activation id collision or store corruption")
        return existing_bundle

    def _projected_capacity_allows_v1(self, target_byte_count: int) -> bool:
        current_count, current_bytes = self._history_bounds_v1()
        return (
            current_count + 1 <= _MAX_ACTIVATION_HISTORY_V1
            and current_bytes + target_byte_count <= _MAX_ACTIVATION_STORE_BYTES_V1
        )

    @staticmethod
    def _source_matches_v1(
        migration_bundle: DurableEconomicInitialStateBundleV1,
        current_head: DurableEconomicHeadV1,
        *,
        expected_activation_id: str,
        expected_generation: int,
    ) -> bool:
        record = migration_bundle.record
        return (
            expected_activation_id == current_head.activation_id
            and expected_generation == current_head.generation
            and record.source_activation_id == current_head.activation_id
            and record.generation == current_head.generation + 1
            and record.chain_id == current_head.chain_id
            and record.deployment_root == current_head.deployment_root
            and record.source_profile_root == current_head.profile_root
            and record.source_state_root == current_head.state_root
            and record.source_writer_epoch == current_head.writer_epoch
            and record.source_height == current_head.height
        )

    def _insert_activation_v1(
        self,
        migration_bundle: DurableEconomicInitialStateBundleV1,
        target_bytes: bytes,
    ) -> None:
        self._connection.execute(
            """
            INSERT INTO activations(
                activation_id,
                generation_decimal,
                bundle_bytes
            ) VALUES (?, ?, ?)
            """,
            (
                migration_bundle.record.activation_id,
                str(migration_bundle.record.generation),
                target_bytes,
            ),
        )


__all__ = [
    "DurableEconomicCommitOutcomeV1",
    "DurableEconomicCommitStatusV1",
    "DurableEconomicCasHeadTokenV1",
    "GlobalEconomicMigrationJournalV1",
]

"""Durable transactional replay-index admission for authenticated ZRPF roots.

This module owns one local SQLite replay database. It commits replay indexes
and a canonical acceptance outcome in one ``BEGIN IMMEDIATE`` transaction.
It applies no balances, mint or burn, rewards, carry, message delivery,
application state, or settlement effects.

The only mutating entry point is private and consumes the private authenticated
value minted by ``PinnedRecursiveStarkVerifier``. Public cursors, receipts, and
results are data-only recovery views.
"""

from __future__ import annotations

import sqlite3
from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn, final

from src.core.recursive_stark_admission import (
    RecursiveStarkAdmissionRejectReason,
    _AuthenticatedRecursiveStarkRootFacts,
    _plan_authenticated_recursive_stark_root,
)
from src.integration._recursive_stark_admission_store_engine import (
    _AdmissionCommitContext,
    _cas_meta,
    _database_snapshot,
    _next_cursor,
    _persist_admission_rows,
    _read_admission_row,
    _read_cursor,
    _receipt_from_row,
    _StoredRootStatus,
    _validate_stored_outcome_key,
)
from src.integration._recursive_stark_admission_store_hashes import (
    _facts_digest,
    _outcome_key,
)
from src.integration._recursive_stark_admission_store_history import (
    _validate_complete_history,
)
from src.integration._recursive_stark_admission_store_schema import (
    DEFAULT_BUSY_TIMEOUT_MS,
    MAX_BUSY_TIMEOUT_MS,
    STORE_APPLICATION_ID,
    STORE_SCHEMA_VERSION,
    _connect_database,
    _create_private_database_file,
    _fsync_directory,
    _initialize_or_validate,
    _require_private_parent,
    _validate_schema,
)
from src.integration.recursive_stark_admission_store_types import (
    DurableRecursiveStarkAdmissionCursor,
    DurableRecursiveStarkAdmissionDisposition,
    DurableRecursiveStarkAdmissionReceipt,
    DurableRecursiveStarkAdmissionResult,
    RecursiveStarkAdmissionStoreError,
    _hash_bytes,
)


@dataclass(frozen=True, slots=True)
class _LockedAdmissionEvaluation:
    actual_cursor: DurableRecursiveStarkAdmissionCursor
    existing: sqlite3.Row | None
    facts_digest: bytes
    outcome_key: bytes
    plan_reject_reason: RecursiveStarkAdmissionRejectReason | None
    idempotent_replay: bool


@final
class SQLiteRecursiveStarkAdmissionStore:
    """Local fsync-backed store for replay indexes and canonical outcomes."""

    __slots__ = ("_busy_timeout_ms", "_path")
    _busy_timeout_ms: int
    _path: Path

    def __init__(self, path: Path, *, busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS) -> None:
        self._validate_constructor_inputs(path, busy_timeout_ms)
        object.__setattr__(self, "_path", path)
        object.__setattr__(self, "_busy_timeout_ms", busy_timeout_ms)
        _create_private_database_file(path)
        try:
            with self._connect() as connection:
                self._initialize_and_validate(connection)
        except (OSError, sqlite3.Error, ValueError) as exc:
            raise RecursiveStarkAdmissionStoreError(
                "STORE_OPEN_FAILED",
                str(exc),
            ) from exc
        try:
            _fsync_directory(path.parent)
        except OSError as exc:
            raise RecursiveStarkAdmissionStoreError(
                "STORE_DIRECTORY_SYNC_FAILED",
                str(exc),
            ) from exc

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SQLiteRecursiveStarkAdmissionStore cannot be subclassed")

    @property
    def path(self) -> Path:
        return self._path

    def read_cursor(self) -> DurableRecursiveStarkAdmissionCursor:
        """Read the current canonical replay-index head."""

        try:
            with self._connect() as connection:
                _validate_schema(connection)
                return _read_cursor(connection)
        except (OSError, sqlite3.Error, ValueError) as exc:
            raise RecursiveStarkAdmissionStoreError(
                "STORE_READ_FAILED",
                str(exc),
            ) from exc

    def get_committed_receipt(
        self,
        root_journal_hash: str,
    ) -> DurableRecursiveStarkAdmissionReceipt | None:
        """Return one data-only stored outcome by authenticated journal hash."""

        root_bytes = _hash_bytes(root_journal_hash, name="root_journal_hash")
        try:
            with self._connect() as connection:
                _validate_schema(connection)
                row = _read_admission_row(connection, root_bytes)
                if row is None:
                    return None
                _validate_stored_outcome_key(row)
                return _receipt_from_row(row)
        except (OSError, sqlite3.Error, ValueError) as exc:
            raise RecursiveStarkAdmissionStoreError(
                "STORE_RECEIPT_READ_FAILED",
                str(exc),
            ) from exc

    def _commit_authenticated_recursive_stark_root(
        self,
        *,
        expected_cursor: DurableRecursiveStarkAdmissionCursor,
        authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
    ) -> DurableRecursiveStarkAdmissionResult:
        self._validate_commit_inputs(expected_cursor, authenticated_root)
        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            result = self._execute_transaction(
                connection,
                expected_cursor=expected_cursor,
                authenticated_root=authenticated_root,
            )
            return result
        except RecursiveStarkAdmissionStoreError:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise
        except (OSError, sqlite3.Error, ValueError) as exc:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise RecursiveStarkAdmissionStoreError(
                "STORE_COMMIT_FAILED",
                str(exc),
            ) from exc
        finally:
            if connection is not None:
                connection.close()

    def _execute_transaction(
        self,
        connection: sqlite3.Connection,
        *,
        expected_cursor: DurableRecursiveStarkAdmissionCursor,
        authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
    ) -> DurableRecursiveStarkAdmissionResult:
        connection.execute("BEGIN IMMEDIATE")
        _validate_schema(connection)
        evaluation = _read_locked_evaluation(connection, authenticated_root)
        no_commit = _resolve_no_commit_result(evaluation, expected_cursor)
        if no_commit is not None:
            connection.rollback()
            return no_commit

        facts = authenticated_root.facts
        next_cursor = _next_cursor(
            evaluation.actual_cursor,
            facts,
            evaluation.outcome_key,
            evaluation.facts_digest,
        )
        context = _AdmissionCommitContext(
            authenticated_root=authenticated_root,
            facts_digest=evaluation.facts_digest,
            outcome_key=evaluation.outcome_key,
            previous_cursor=evaluation.actual_cursor,
            next_cursor=next_cursor,
        )
        _persist_admission_rows(connection, context)
        _cas_meta(connection, evaluation.actual_cursor, next_cursor)
        connection.commit()
        return self._committed_result(facts.root_journal_hash, next_cursor)

    def _committed_result(
        self,
        root_journal_hash: str,
        next_cursor: DurableRecursiveStarkAdmissionCursor,
    ) -> DurableRecursiveStarkAdmissionResult:
        receipt = self.get_committed_receipt(root_journal_hash)
        if receipt is None:
            raise RecursiveStarkAdmissionStoreError(
                "COMMITTED_RECEIPT_MISSING",
                "committed admission receipt was not recoverable",
            )
        return DurableRecursiveStarkAdmissionResult(
            disposition=DurableRecursiveStarkAdmissionDisposition.COMMITTED,
            head_cursor=next_cursor,
            receipt=receipt,
            reject_reason=None,
        )

    def _connect(self) -> sqlite3.Connection:
        return _connect_database(self._path, busy_timeout_ms=self._busy_timeout_ms)

    @staticmethod
    def _initialize_and_validate(connection: sqlite3.Connection) -> None:
        connection.execute("BEGIN EXCLUSIVE")
        try:
            _initialize_or_validate(connection)
            _validate_complete_history(connection)
            connection.commit()
        except (sqlite3.Error, ValueError):
            if connection.in_transaction:
                connection.rollback()
            raise

    @staticmethod
    def _validate_constructor_inputs(path: Path, busy_timeout_ms: int) -> None:
        if not isinstance(path, Path):
            raise TypeError("durable admission path must be pathlib.Path")
        if not path.is_absolute():
            raise ValueError("durable admission path must be absolute")
        if type(busy_timeout_ms) is not int:
            raise TypeError("busy_timeout_ms must be an int")
        if busy_timeout_ms < 1 or busy_timeout_ms > MAX_BUSY_TIMEOUT_MS:
            raise ValueError(f"busy_timeout_ms must be in 1..{MAX_BUSY_TIMEOUT_MS}")
        if path.resolve(strict=False) != path:
            raise ValueError("durable admission path must be canonical and symlink-free")
        _require_private_parent(path.parent)

    @staticmethod
    def _validate_commit_inputs(
        expected_cursor: DurableRecursiveStarkAdmissionCursor,
        authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
    ) -> None:
        if type(expected_cursor) is not DurableRecursiveStarkAdmissionCursor:
            raise TypeError("expected_cursor must be DurableRecursiveStarkAdmissionCursor")
        if type(authenticated_root) is not _AuthenticatedRecursiveStarkRootFacts:
            raise TypeError("authenticated_root must be _AuthenticatedRecursiveStarkRootFacts")
        if not authenticated_root._has_private_seal():
            raise TypeError("authenticated_root lacks the private seal")
        provenance = authenticated_root.provenance
        if (
            provenance.release_binding_config_digest is None
            or provenance.replay_manifest_sha256 is None
        ):
            raise TypeError("durable admission requires release-bound verification provenance")


def _read_locked_evaluation(
    connection: sqlite3.Connection,
    authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
) -> _LockedAdmissionEvaluation:
    actual_cursor = _read_cursor(connection)
    facts = authenticated_root.facts
    facts_digest = _facts_digest(facts)
    outcome_key = _outcome_key(authenticated_root, facts_digest)
    existing = _read_admission_row(
        connection,
        _hash_bytes(facts.root_journal_hash, name="facts.root_journal_hash"),
    )
    idempotent = False
    if existing is not None:
        _validate_stored_outcome_key(existing)
        idempotent = bytes(existing["outcome_key"]) == outcome_key
    snapshot = _database_snapshot(
        connection,
        actual_cursor,
        facts,
        _StoredRootStatus(seen=existing is not None, idempotent_outcome=idempotent),
    )
    plan = _plan_authenticated_recursive_stark_root(authenticated_root, snapshot)
    return _LockedAdmissionEvaluation(
        actual_cursor=actual_cursor,
        existing=existing,
        facts_digest=facts_digest,
        outcome_key=outcome_key,
        plan_reject_reason=plan.reject_reason,
        idempotent_replay=plan.idempotent_replay,
    )


def _resolve_no_commit_result(
    evaluation: _LockedAdmissionEvaluation,
    expected_cursor: DurableRecursiveStarkAdmissionCursor,
) -> DurableRecursiveStarkAdmissionResult | None:
    if evaluation.idempotent_replay:
        if evaluation.existing is None:
            raise ValueError("idempotent replay has no stored admission")
        return DurableRecursiveStarkAdmissionResult(
            disposition=DurableRecursiveStarkAdmissionDisposition.IDEMPOTENT_REPLAY,
            head_cursor=evaluation.actual_cursor,
            receipt=_receipt_from_row(evaluation.existing),
            reject_reason=None,
        )
    if evaluation.plan_reject_reason is not None:
        return _rejected_result(evaluation.actual_cursor, evaluation.plan_reject_reason)
    if evaluation.actual_cursor != expected_cursor:
        return _rejected_result(
            evaluation.actual_cursor,
            RecursiveStarkAdmissionRejectReason.DURABLE_CURSOR_MISMATCH,
        )
    return None


def _rejected_result(
    cursor: DurableRecursiveStarkAdmissionCursor,
    reason: RecursiveStarkAdmissionRejectReason,
) -> DurableRecursiveStarkAdmissionResult:
    return DurableRecursiveStarkAdmissionResult(
        disposition=DurableRecursiveStarkAdmissionDisposition.REJECTED,
        head_cursor=cursor,
        receipt=None,
        reject_reason=reason,
    )


__all__ = [
    "DEFAULT_BUSY_TIMEOUT_MS",
    "STORE_APPLICATION_ID",
    "STORE_SCHEMA_VERSION",
    "DurableRecursiveStarkAdmissionCursor",
    "DurableRecursiveStarkAdmissionDisposition",
    "DurableRecursiveStarkAdmissionReceipt",
    "DurableRecursiveStarkAdmissionResult",
    "RecursiveStarkAdmissionStoreError",
    "SQLiteRecursiveStarkAdmissionStore",
]

"""Atomic SQLite kernel for non-authoritative ZRPF settlement evidence.

One ``BEGIN IMMEDIATE`` transaction couples the existing authenticated-root
replay admission with the canonical settlement plan, economic action IDs,
authorization nullifiers, and all effect rows.  The current Semantic Epoch V2
receipt lacks the exact plan-binding ABI, so the sole commit entry is private,
consumes a sealed test-only input, and persists ``settlement_authority=false``.
"""

from __future__ import annotations

import sqlite3
from pathlib import Path
from typing import NoReturn, final

from src.core._zrpf_settlement_commit_authority import (
    SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    _AuthenticatedSettlementCommitV1,
)
from src.integration._recursive_stark_admission_store_engine import (
    _AdmissionCommitContext,
    _cas_meta,
    _next_cursor,
    _persist_admission_rows,
    _read_admission_row,
    _read_cursor,
)
from src.integration._recursive_stark_admission_store_history import (
    _validate_complete_history,
)
from src.integration._recursive_stark_admission_store_schema import (
    DEFAULT_BUSY_TIMEOUT_MS,
    MAX_BUSY_TIMEOUT_MS,
    _connect_database,
    _create_private_database_file,
    _fsync_directory,
    _require_private_parent,
)
from src.integration._zrpf_atomic_settlement_store_decision import (
    _accepted_atomic_settlement_result,
    _AtomicSettlementAcceptedRowsV1,
    _AtomicSettlementExpectedCursorsV1,
    _evaluate_atomic_settlement_locked,
    _resolve_atomic_settlement_no_commit,
)
from src.integration._zrpf_atomic_settlement_store_engine import (
    _cas_settlement_meta,
    _next_settlement_cursor,
    _persist_settlement_actions,
    _persist_settlement_header,
    _persist_settlement_rows,
    _read_settlement_cursor,
    _read_settlement_plan_row,
    _settlement_receipt_from_row,
)
from src.integration._zrpf_atomic_settlement_store_history import (
    _validate_complete_settlement_history,
    _validate_coupled_admission_settlement_history,
)
from src.integration._zrpf_atomic_settlement_store_schema import (
    ATOMIC_SETTLEMENT_STORE_APPLICATION_ID_V1,
    ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V1,
    _initialize_or_validate_atomic_settlement_store,
    _validate_atomic_settlement_schema,
)
from src.integration.recursive_stark_admission_store_types import (
    DurableRecursiveStarkAdmissionCursor,
    _hash_bytes,
)
from src.integration.zrpf_atomic_settlement_store_types import (
    DurableZrpfAtomicSettlementResultV1,
    DurableZrpfSettlementCursorV1,
    DurableZrpfSettlementReceiptV1,
    ZrpfAtomicSettlementDispositionV1,
    ZrpfAtomicSettlementRejectReasonV1,
    ZrpfAtomicSettlementStoreErrorV1,
)


@final
class SQLiteZrpfAtomicSettlementStoreV1:
    """Combined replay and settlement transaction-mechanics evidence store."""

    __slots__ = ("_busy_timeout_ms", "_genesis_settlement_state_root", "_path")
    _busy_timeout_ms: int
    _genesis_settlement_state_root: bytes
    _path: Path

    def __init__(
        self,
        path: Path,
        *,
        genesis_settlement_state_root: str,
        busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS,
    ) -> None:
        self._validate_constructor_inputs(path, genesis_settlement_state_root, busy_timeout_ms)
        object.__setattr__(self, "_path", path)
        object.__setattr__(self, "_busy_timeout_ms", busy_timeout_ms)
        object.__setattr__(
            self,
            "_genesis_settlement_state_root",
            _hash_bytes(genesis_settlement_state_root, name="genesis settlement state root"),
        )
        _create_private_database_file(path)
        try:
            with self._connect() as connection:
                self._initialize_and_validate(connection)
        except (OSError, sqlite3.Error, ValueError) as exc:
            raise ZrpfAtomicSettlementStoreErrorV1(
                "ATOMIC_SETTLEMENT_STORE_OPEN_FAILED",
                str(exc),
            ) from exc
        try:
            _fsync_directory(path.parent)
        except OSError as exc:
            raise ZrpfAtomicSettlementStoreErrorV1(
                "ATOMIC_SETTLEMENT_DIRECTORY_SYNC_FAILED",
                str(exc),
            ) from exc

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SQLiteZrpfAtomicSettlementStoreV1 cannot be subclassed")

    @property
    def path(self) -> Path:
        return self._path

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def authority_blocked_reason(self) -> str:
        return SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1

    def read_admission_cursor(self) -> DurableRecursiveStarkAdmissionCursor:
        try:
            with self._connect() as connection:
                _validate_atomic_settlement_schema(connection)
                return _read_cursor(connection)
        except (OSError, sqlite3.Error, ValueError) as exc:
            raise ZrpfAtomicSettlementStoreErrorV1(
                "ATOMIC_SETTLEMENT_ADMISSION_READ_FAILED",
                str(exc),
            ) from exc

    def read_settlement_cursor(self) -> DurableZrpfSettlementCursorV1:
        try:
            with self._connect() as connection:
                _validate_atomic_settlement_schema(connection)
                return _read_settlement_cursor(connection)
        except (OSError, sqlite3.Error, ValueError) as exc:
            raise ZrpfAtomicSettlementStoreErrorV1(
                "ATOMIC_SETTLEMENT_CURSOR_READ_FAILED",
                str(exc),
            ) from exc

    def get_settlement_receipt(
        self,
        plan_commitment: str,
    ) -> DurableZrpfSettlementReceiptV1 | None:
        try:
            commitment = _hash_bytes(plan_commitment, name="plan commitment")
            with self._connect() as connection:
                _validate_atomic_settlement_schema(connection)
                row = connection.execute(
                    "SELECT * FROM zrpf_settlement_plans WHERE plan_commitment = ?",
                    (commitment,),
                ).fetchone()
                return None if row is None else _settlement_receipt_from_row(row)
        except (OSError, sqlite3.Error, ValueError) as exc:
            raise ZrpfAtomicSettlementStoreErrorV1(
                "ATOMIC_SETTLEMENT_RECEIPT_READ_FAILED",
                str(exc),
            ) from exc

    def _commit_authenticated_settlement(
        self,
        *,
        expected_admission_cursor: DurableRecursiveStarkAdmissionCursor,
        expected_settlement_cursor: DurableZrpfSettlementCursorV1,
        authenticated_settlement: _AuthenticatedSettlementCommitV1,
    ) -> DurableZrpfAtomicSettlementResultV1:
        self._validate_commit_inputs(
            expected_admission_cursor,
            expected_settlement_cursor,
            authenticated_settlement,
        )
        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            return self._execute_transaction(
                connection,
                expected_admission_cursor=expected_admission_cursor,
                expected_settlement_cursor=expected_settlement_cursor,
                authenticated_settlement=authenticated_settlement,
            )
        except ZrpfAtomicSettlementStoreErrorV1:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise
        except (OSError, sqlite3.Error, ValueError) as exc:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise ZrpfAtomicSettlementStoreErrorV1(
                "ATOMIC_SETTLEMENT_COMMIT_FAILED",
                str(exc),
            ) from exc
        finally:
            if connection is not None:
                connection.close()

    def _execute_transaction(
        self,
        connection: sqlite3.Connection,
        *,
        expected_admission_cursor: DurableRecursiveStarkAdmissionCursor,
        expected_settlement_cursor: DurableZrpfSettlementCursorV1,
        authenticated_settlement: _AuthenticatedSettlementCommitV1,
    ) -> DurableZrpfAtomicSettlementResultV1:
        connection.execute("BEGIN IMMEDIATE")
        _validate_atomic_settlement_schema(connection)
        evaluation = _evaluate_atomic_settlement_locked(connection, authenticated_settlement)
        no_commit = _resolve_atomic_settlement_no_commit(
            connection,
            evaluation,
            _AtomicSettlementExpectedCursorsV1(
                admission=expected_admission_cursor,
                settlement=expected_settlement_cursor,
            ),
            authenticated_settlement,
        )
        if no_commit is not None:
            connection.rollback()
            return no_commit

        root = authenticated_settlement.authenticated_root
        plan = authenticated_settlement.plan
        next_admission = _next_cursor(
            evaluation.admission_head,
            root.facts,
            evaluation.admission_outcome_key,
            evaluation.admission_facts_digest,
        )
        next_settlement = _next_settlement_cursor(evaluation.settlement_head, plan)
        _persist_admission_rows(
            connection,
            _AdmissionCommitContext(
                authenticated_root=root,
                facts_digest=evaluation.admission_facts_digest,
                outcome_key=evaluation.admission_outcome_key,
                previous_cursor=evaluation.admission_head,
                next_cursor=next_admission,
            ),
        )
        _persist_settlement_header(connection, authenticated_settlement, next_settlement)
        _persist_settlement_actions(connection, plan)
        _persist_settlement_rows(connection, plan)
        _cas_meta(connection, evaluation.admission_head, next_admission)
        _cas_settlement_meta(connection, evaluation.settlement_head, next_settlement)
        connection.commit()
        return self._committed_result(
            root.facts.root_journal_hash,
            plan.commitment,
            next_admission,
            next_settlement,
        )

    def _committed_result(
        self,
        root_journal_hash: str,
        plan_commitment: str,
        admission_head: DurableRecursiveStarkAdmissionCursor,
        settlement_head: DurableZrpfSettlementCursorV1,
    ) -> DurableZrpfAtomicSettlementResultV1:
        try:
            with self._connect() as connection:
                admission_row = _read_admission_row(
                    connection,
                    _hash_bytes(root_journal_hash, name="root journal hash"),
                )
                settlement_row = _read_settlement_plan_row(
                    connection,
                    root_journal_hash=root_journal_hash,
                )
                if admission_row is None or settlement_row is None:
                    raise ValueError("committed atomic settlement rows are missing")
                settlement_receipt = _settlement_receipt_from_row(settlement_row)
                if settlement_receipt.plan_commitment != plan_commitment:
                    raise ValueError("committed settlement plan commitment mismatch")
                return _accepted_atomic_settlement_result(
                    ZrpfAtomicSettlementDispositionV1.TRANSACTION_COMMITTED,
                    _AtomicSettlementAcceptedRowsV1(
                        admission_head=admission_head,
                        settlement_head=settlement_head,
                        admission_row=admission_row,
                        settlement_row=settlement_row,
                    ),
                )
        except (OSError, sqlite3.Error, ValueError) as exc:
            raise ZrpfAtomicSettlementStoreErrorV1(
                "ATOMIC_SETTLEMENT_COMMITTED_RECEIPT_MISSING",
                str(exc),
            ) from exc

    def _connect(self) -> sqlite3.Connection:
        return _connect_database(self._path, busy_timeout_ms=self._busy_timeout_ms)

    def _initialize_and_validate(self, connection: sqlite3.Connection) -> None:
        connection.execute("BEGIN EXCLUSIVE")
        try:
            _initialize_or_validate_atomic_settlement_store(
                connection,
                genesis_settlement_state_root=self._genesis_settlement_state_root,
            )
            _validate_complete_history(connection)
            _validate_complete_settlement_history(
                connection,
                genesis_state_root=self._genesis_settlement_state_root,
            )
            _validate_coupled_admission_settlement_history(connection)
            connection.commit()
        except (sqlite3.Error, ValueError):
            if connection.in_transaction:
                connection.rollback()
            raise

    @staticmethod
    def _validate_constructor_inputs(
        path: Path,
        genesis_settlement_state_root: str,
        busy_timeout_ms: int,
    ) -> None:
        if not isinstance(path, Path):
            raise TypeError("atomic settlement path must be pathlib.Path")
        if not path.is_absolute():
            raise ValueError("atomic settlement path must be absolute")
        if path.resolve(strict=False) != path:
            raise ValueError("atomic settlement path must be canonical and symlink-free")
        _require_private_parent(path.parent)
        _hash_bytes(genesis_settlement_state_root, name="genesis settlement state root")
        if type(busy_timeout_ms) is not int:
            raise TypeError("busy_timeout_ms must be an int")
        if not 1 <= busy_timeout_ms <= MAX_BUSY_TIMEOUT_MS:
            raise ValueError(f"busy_timeout_ms must be in 1..{MAX_BUSY_TIMEOUT_MS}")

    @staticmethod
    def _validate_commit_inputs(
        expected_admission_cursor: DurableRecursiveStarkAdmissionCursor,
        expected_settlement_cursor: DurableZrpfSettlementCursorV1,
        authenticated_settlement: _AuthenticatedSettlementCommitV1,
    ) -> None:
        if type(expected_admission_cursor) is not DurableRecursiveStarkAdmissionCursor:
            raise TypeError("expected_admission_cursor must be a durable admission cursor")
        if type(expected_settlement_cursor) is not DurableZrpfSettlementCursorV1:
            raise TypeError("expected_settlement_cursor must be a durable settlement cursor")
        if type(authenticated_settlement) is not _AuthenticatedSettlementCommitV1:
            raise TypeError("authenticated_settlement must be _AuthenticatedSettlementCommitV1")
        if not authenticated_settlement._has_private_seal():
            raise TypeError("authenticated_settlement lacks the private seal")
        if authenticated_settlement.settlement_authority is not False:
            raise TypeError("V1 atomic settlement authority must remain false")
        if (
            authenticated_settlement.authority_blocked_reason
            != SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1
        ):
            raise TypeError("V1 atomic settlement blocked reason mismatch")
        provenance = authenticated_settlement.authenticated_root.provenance
        if (
            provenance.release_binding_config_digest is None
            or provenance.replay_manifest_sha256 is None
        ):
            raise TypeError("atomic settlement requires release-bound root provenance")


__all__ = [
    "ATOMIC_SETTLEMENT_STORE_APPLICATION_ID_V1",
    "ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V1",
    "DurableZrpfAtomicSettlementResultV1",
    "DurableZrpfSettlementCursorV1",
    "DurableZrpfSettlementReceiptV1",
    "SQLiteZrpfAtomicSettlementStoreV1",
    "ZrpfAtomicSettlementDispositionV1",
    "ZrpfAtomicSettlementRejectReasonV1",
    "ZrpfAtomicSettlementStoreErrorV1",
]

"""Serializable SQLite implementation of test-only sealed Spot V7 mechanics.

Executable tests establish that replay identities, authorization nullifiers,
exact artifacts, economic cell updates, and the root cursor commit together or
roll back together on the supported SQLite profile.  The only sink accepts a
module-sealed, permanently non-authoritative test candidate.  Raw verifier
output, a JSON report, or caller booleans have no admission entrypoint.
"""

from __future__ import annotations

import sqlite3
from pathlib import Path
from typing import NoReturn, final

from src.integration._recursive_stark_admission_store_schema import (
    DEFAULT_BUSY_TIMEOUT_MS,
    MAX_BUSY_TIMEOUT_MS,
    _connect_database,
    _create_private_database_file,
    _fsync_directory,
    _require_private_parent,
)
from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _TestOnlySealedSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_atomic_settlement_engine import (
    _candidate_cells_match_locked,
    _candidate_reject_reason_locked,
    _cas_spot_v7_meta,
    _persist_candidate,
)
from src.integration._zrpf_spot_v7_atomic_settlement_history import (
    _stored_candidate_matches,
    _validate_complete_spot_v7_history,
)
from src.integration._zrpf_spot_v7_atomic_settlement_records import (
    _receipt_for_commitment,
)
from src.integration._zrpf_spot_v7_atomic_settlement_schema import (
    _initialize_or_validate_spot_v7_store,
    _read_current_cells,
    _read_spot_v7_cursor,
    _validate_spot_v7_schema,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    DurableSpotV7AtomicSettlementReceiptV1,
    SpotV7AtomicSettlementCursorV1,
    SpotV7AtomicSettlementDispositionV1,
    SpotV7AtomicSettlementRejectReasonV1,
    SpotV7AtomicSettlementResultV1,
    SpotV7AtomicSettlementStoreErrorV1,
    SpotV7AtomicSettlementStoreIdentityV1,
    SpotV7CellOpeningV1,
)


@final
class SQLiteSpotV7AtomicSettlementStoreV1:
    """One scoped, fail-closed database for authority-false Spot V7 mechanics."""

    __slots__ = ("_busy_timeout_ms", "_genesis_cells", "_identity", "_path")

    _busy_timeout_ms: int
    _genesis_cells: tuple[SpotV7CellOpeningV1, ...]
    _identity: SpotV7AtomicSettlementStoreIdentityV1
    _path: Path

    def __init__(
        self,
        path: Path,
        *,
        identity: SpotV7AtomicSettlementStoreIdentityV1,
        genesis_cells: tuple[SpotV7CellOpeningV1, ...],
        busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS,
    ) -> None:
        _validate_constructor_inputs(path, identity, genesis_cells, busy_timeout_ms)
        object.__setattr__(self, "_path", path)
        object.__setattr__(self, "_identity", identity)
        object.__setattr__(self, "_genesis_cells", genesis_cells)
        object.__setattr__(self, "_busy_timeout_ms", busy_timeout_ms)
        try:
            _require_private_parent(path.parent)
            _create_private_database_file(path)
            with self._connect() as connection:
                connection.execute("BEGIN IMMEDIATE")
                _initialize_or_validate_spot_v7_store(
                    connection,
                    identity=identity,
                    genesis_cells=genesis_cells,
                )
                _validate_complete_spot_v7_history(connection)
                connection.commit()
            _fsync_directory(path.parent)
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED",
                str(exc),
            ) from exc

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SQLiteSpotV7AtomicSettlementStoreV1 cannot be subclassed")

    @property
    def path(self) -> Path:
        return self._path

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    @property
    def governed_firecracker_binder_available(self) -> bool:
        return False

    @property
    def authority_blocked_reason(self) -> str:
        return SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1

    def read_cursor(self) -> SpotV7AtomicSettlementCursorV1:
        try:
            with self._connect() as connection:
                connection.execute("BEGIN")
                _validate_spot_v7_schema(connection)
                _validate_complete_spot_v7_history(connection)
                return _read_spot_v7_cursor(connection)
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_SETTLEMENT_READ_FAILED",
                str(exc),
            ) from exc

    def read_cells(self) -> tuple[SpotV7CellOpeningV1, ...]:
        try:
            with self._connect() as connection:
                connection.execute("BEGIN")
                _validate_spot_v7_schema(connection)
                _validate_complete_spot_v7_history(connection)
                return _read_current_cells(connection)
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_SETTLEMENT_READ_FAILED",
                str(exc),
            ) from exc

    def get_receipt(
        self,
        settlement_commitment: str,
    ) -> DurableSpotV7AtomicSettlementReceiptV1 | None:
        try:
            with self._connect() as connection:
                connection.execute("BEGIN")
                _validate_spot_v7_schema(connection)
                _validate_complete_spot_v7_history(connection)
                return _receipt_for_commitment(connection, settlement_commitment)
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_SETTLEMENT_READ_FAILED",
                str(exc),
            ) from exc

    def _commit_test_only_sealed_candidate(
        self,
        *,
        expected_cursor: SpotV7AtomicSettlementCursorV1,
        candidate: _TestOnlySealedSpotV7SettlementV1,
    ) -> SpotV7AtomicSettlementResultV1:
        """Apply one sealed authority-false candidate in a single write lock."""

        if type(expected_cursor) is not SpotV7AtomicSettlementCursorV1:
            raise TypeError("expected_cursor must be exact SpotV7AtomicSettlementCursorV1")
        if type(candidate) is not _TestOnlySealedSpotV7SettlementV1:
            raise TypeError("candidate must be a test-only sealed Spot V7 candidate")
        if not candidate._has_private_test_seal():
            raise TypeError("candidate lacks the module-private test-only seal")
        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            connection.execute("BEGIN IMMEDIATE")
            _validate_spot_v7_schema(connection)
            _validate_complete_spot_v7_history(connection)
            return self._evaluate_and_commit_locked(
                connection,
                expected_cursor=expected_cursor,
                candidate=candidate,
            )
        except SpotV7AtomicSettlementStoreErrorV1:
            _rollback_if_needed(connection)
            raise
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            _rollback_if_needed(connection)
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_SETTLEMENT_COMMIT_FAILED",
                str(exc),
            ) from exc
        finally:
            if connection is not None:
                connection.close()

    def _evaluate_and_commit_locked(
        self,
        connection: sqlite3.Connection,
        *,
        expected_cursor: SpotV7AtomicSettlementCursorV1,
        candidate: _TestOnlySealedSpotV7SettlementV1,
    ) -> SpotV7AtomicSettlementResultV1:
        head = _read_spot_v7_cursor(connection)
        existing = _receipt_for_commitment(connection, candidate.settlement_commitment)
        if existing is not None:
            if _stored_candidate_matches(connection, candidate):
                connection.rollback()
                return SpotV7AtomicSettlementResultV1(
                    SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY,
                    head,
                    existing,
                    None,
                )
            return _reject_locked(
                connection,
                head,
                SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SETTLEMENT_PLAN,
            )
        reject_reason = self._precommit_reject_reason(
            connection,
            head=head,
            expected_cursor=expected_cursor,
            candidate=candidate,
        )
        if reject_reason is not None:
            return _reject_locked(connection, head, reject_reason)
        next_cursor = SpotV7AtomicSettlementCursorV1(
            revision=head.revision + 1,
            state_root=candidate.post_state_root,
            settlement_count=head.settlement_count + 1,
            cell_count=head.cell_count,
            last_epoch_id=candidate.epoch_id,
        )
        _persist_candidate(connection, candidate, next_cursor)
        _cas_spot_v7_meta(connection, head, next_cursor)
        _validate_complete_spot_v7_history(connection)
        receipt = _receipt_for_commitment(connection, candidate.settlement_commitment)
        if receipt is None:
            raise ValueError("committed Spot V7 receipt is missing before commit")
        connection.commit()
        return SpotV7AtomicSettlementResultV1(
            SpotV7AtomicSettlementDispositionV1.COMMITTED,
            next_cursor,
            receipt,
            None,
        )

    def _precommit_reject_reason(
        self,
        connection: sqlite3.Connection,
        *,
        head: SpotV7AtomicSettlementCursorV1,
        expected_cursor: SpotV7AtomicSettlementCursorV1,
        candidate: _TestOnlySealedSpotV7SettlementV1,
    ) -> SpotV7AtomicSettlementRejectReasonV1 | None:
        if expected_cursor != head:
            return SpotV7AtomicSettlementRejectReasonV1.CURSOR_MISMATCH
        if not self._candidate_matches_store_identity(candidate):
            return SpotV7AtomicSettlementRejectReasonV1.STORE_IDENTITY_MISMATCH
        if candidate.pre_state_root != head.state_root:
            return SpotV7AtomicSettlementRejectReasonV1.PRE_STATE_ROOT_MISMATCH
        if head.last_epoch_id is not None and candidate.epoch_id <= head.last_epoch_id:
            return SpotV7AtomicSettlementRejectReasonV1.EPOCH_NOT_MONOTONIC
        if not _candidate_cells_match_locked(connection, candidate):
            return SpotV7AtomicSettlementRejectReasonV1.CELL_PRE_STATE_MISMATCH
        return _candidate_reject_reason_locked(connection, candidate)

    def _candidate_matches_store_identity(
        self,
        candidate: _TestOnlySealedSpotV7SettlementV1,
    ) -> bool:
        return all(
            (
                candidate.application_id == self._identity.application_id,
                candidate.chain_or_domain_id == self._identity.chain_or_domain_id,
                candidate.verified_program_id == self._identity.verified_program_id,
                candidate.verified_profile_id == self._identity.verified_profile_id,
                candidate.verified_program_manifest_root
                == self._identity.verified_program_manifest_root,
            )
        )

    def _connect(self) -> sqlite3.Connection:
        _require_private_parent(self._path.parent)
        _create_private_database_file(self._path)
        return _connect_database(self._path, busy_timeout_ms=self._busy_timeout_ms)


def _validate_constructor_inputs(
    path: Path,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
    busy_timeout_ms: int,
) -> None:
    if not isinstance(path, Path) or not path.is_absolute():
        raise ValueError("Spot V7 store path must be an absolute pathlib.Path")
    if type(identity) is not SpotV7AtomicSettlementStoreIdentityV1:
        raise TypeError("identity must be exact SpotV7AtomicSettlementStoreIdentityV1")
    if type(genesis_cells) is not tuple or not genesis_cells:
        raise ValueError("genesis_cells must be a nonempty tuple")
    if any(type(cell) is not SpotV7CellOpeningV1 for cell in genesis_cells):
        raise TypeError("genesis_cells must contain exact SpotV7CellOpeningV1 values")
    if type(busy_timeout_ms) is not int or not 1 <= busy_timeout_ms <= MAX_BUSY_TIMEOUT_MS:
        raise ValueError(f"busy_timeout_ms must be in 1..{MAX_BUSY_TIMEOUT_MS}")


def _reject_locked(
    connection: sqlite3.Connection,
    head: SpotV7AtomicSettlementCursorV1,
    reason: SpotV7AtomicSettlementRejectReasonV1,
) -> SpotV7AtomicSettlementResultV1:
    connection.rollback()
    return SpotV7AtomicSettlementResultV1(
        SpotV7AtomicSettlementDispositionV1.REJECTED,
        head,
        None,
        reason,
    )


def _rollback_if_needed(connection: sqlite3.Connection | None) -> None:
    if connection is not None and connection.in_transaction:
        connection.rollback()

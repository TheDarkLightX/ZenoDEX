"""Serializable authority-neutral Spot V7 operational store V4.

Every open, read, and write replays the complete economic and operational
history. Persisted bytes never reconstruct the governed Firecracker settlement
capability; the caller supplies a resolver for that process-local authority.
Release, settlement, and production authority remain false.
"""

from __future__ import annotations

import os
import sqlite3
import stat
from collections.abc import Callable
from pathlib import Path
from typing import NoReturn, TypeVar, final

from src.integration._recursive_stark_admission_store_schema import (
    DEFAULT_BUSY_TIMEOUT_MS,
    MAX_BUSY_TIMEOUT_MS,
    _connect_database,
    _create_private_database_file,
    _fsync_directory,
    _require_private_parent,
)
from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _seal_test_only_spot_v7_settlement_v1,
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
)
from src.integration._zrpf_spot_v7_atomic_settlement_history_v4 import (
    MAX_SPOT_V7_V4_HISTORY_ENTRIES,
    SettlementResolverV4,
    _validate_complete_spot_v7_operational_history_v4,
)
from src.integration._zrpf_spot_v7_atomic_settlement_records import (
    _receipt_for_commitment,
)
from src.integration._zrpf_spot_v7_atomic_settlement_records_v4 import (
    _cas_operational_cursor_v4,
    _operational_v4_reject_reason_locked,
    _persist_operational_packet_v4,
    _stored_operational_packet_matches_v4,
)
from src.integration._zrpf_spot_v7_atomic_settlement_schema import (
    _read_current_cells,
    _read_spot_v7_cursor,
)
from src.integration._zrpf_spot_v7_atomic_settlement_schema_v4 import (
    _initialize_or_validate_spot_v7_store_v4,
    _validate_spot_v7_schema_v4,
)
from src.integration._zrpf_spot_v7_operational_capability_v3 import (
    _SpotV7AtomicEconomicCommitCapabilityV3,
    _SpotV7OperationalCommitPacketV3,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
    _require_governed_operational_policy_v3,
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

_T = TypeVar("_T")


@final
class SQLiteSpotV7AtomicOperationalStoreV4:
    """V4 durable mechanics with exact replay on every authority boundary."""

    __slots__ = (
        "_busy_timeout_ms",
        "_database_identity",
        "_genesis_cells",
        "_identity",
        "_path",
        "_policy",
        "_settlement_resolver",
    )

    _busy_timeout_ms: int
    _database_identity: tuple[int, int]
    _genesis_cells: tuple[SpotV7CellOpeningV1, ...]
    _identity: SpotV7AtomicSettlementStoreIdentityV1
    _path: Path
    _policy: _GovernedSpotV7OperationalPolicyV3
    _settlement_resolver: SettlementResolverV4

    def __init__(
        self,
        path: Path,
        *,
        identity: SpotV7AtomicSettlementStoreIdentityV1,
        genesis_cells: tuple[SpotV7CellOpeningV1, ...],
        governed_operational_policy: _GovernedSpotV7OperationalPolicyV3,
        settlement_resolver: SettlementResolverV4,
        busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS,
    ) -> None:
        _validate_constructor_inputs(
            path,
            identity=identity,
            genesis_cells=genesis_cells,
            governed_operational_policy=governed_operational_policy,
            settlement_resolver=settlement_resolver,
            busy_timeout_ms=busy_timeout_ms,
        )
        policy = _require_governed_operational_policy_v3(governed_operational_policy)
        object.__setattr__(self, "_path", path)
        object.__setattr__(self, "_identity", identity)
        object.__setattr__(self, "_genesis_cells", genesis_cells)
        object.__setattr__(self, "_policy", policy)
        object.__setattr__(self, "_settlement_resolver", settlement_resolver)
        object.__setattr__(self, "_busy_timeout_ms", busy_timeout_ms)
        try:
            _require_private_parent(path.parent)
            if path.exists():
                _recover_published_initialization_link_v4(
                    path,
                    identity=identity,
                    genesis_cells=genesis_cells,
                    policy=policy,
                    settlement_resolver=settlement_resolver,
                    busy_timeout_ms=busy_timeout_ms,
                )
            else:
                _initialize_new_database_atomically_v4(
                    path,
                    identity=identity,
                    genesis_cells=genesis_cells,
                    policy=policy,
                    settlement_resolver=settlement_resolver,
                    busy_timeout_ms=busy_timeout_ms,
                )
            object.__setattr__(self, "_database_identity", _database_identity(path))
            with self._connect() as connection:
                connection.execute("BEGIN IMMEDIATE")
                self._validate_locked(connection)
                connection.commit()
            _fsync_directory(path.parent)
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_OPERATIONAL_V4_OPEN_FAILED",
                str(exc),
            ) from exc

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SQLiteSpotV7AtomicOperationalStoreV4 cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("SQLiteSpotV7AtomicOperationalStoreV4 cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("SQLiteSpotV7AtomicOperationalStoreV4 cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("SQLiteSpotV7AtomicOperationalStoreV4 cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("SQLiteSpotV7AtomicOperationalStoreV4 cannot be serialized")

    @property
    def path(self) -> Path:
        return self._path

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    @property
    def authority_blocked_reason(self) -> str:
        return SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1

    @property
    def durable_replay_on_open(self) -> bool:
        return True

    def read_cursor(self) -> SpotV7AtomicSettlementCursorV1:
        return self._read_locked(_read_spot_v7_cursor)

    def read_cells(self) -> tuple[SpotV7CellOpeningV1, ...]:
        return self._read_locked(_read_current_cells)

    def get_receipt(
        self,
        settlement_commitment: str,
    ) -> DurableSpotV7AtomicSettlementReceiptV1 | None:
        try:
            with self._connect() as connection:
                connection.execute("BEGIN")
                self._validate_locked(connection)
                return _receipt_for_commitment(connection, settlement_commitment)
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_OPERATIONAL_V4_READ_FAILED",
                str(exc),
            ) from exc

    def _commit_operational_capability_v3(
        self,
        *,
        expected_cursor: SpotV7AtomicSettlementCursorV1,
        capability: object,
    ) -> SpotV7AtomicSettlementResultV1:
        if type(expected_cursor) is not SpotV7AtomicSettlementCursorV1:
            raise TypeError("expected_cursor must be exact SpotV7AtomicSettlementCursorV1")
        if type(capability) is not _SpotV7AtomicEconomicCommitCapabilityV3:
            raise TypeError("capability must be exact Spot V7 operational V3")
        operational = capability
        if not operational._has_private_seal():
            raise TypeError("operational V3 capability lacks its private seal")
        preflight = operational._packet_for_atomic_store_v4()
        self._require_packet_policy(preflight)
        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            connection.execute("BEGIN IMMEDIATE")
            self._validate_locked(connection)
            packet = operational._packet_for_atomic_store_v4()
            self._require_packet_policy(packet)
            return self._evaluate_and_commit_locked(
                connection,
                expected_cursor=expected_cursor,
                packet=packet,
            )
        except SpotV7AtomicSettlementStoreErrorV1:
            _rollback_if_needed(connection)
            raise
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            _rollback_if_needed(connection)
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_OPERATIONAL_V4_COMMIT_FAILED",
                str(exc),
            ) from exc
        finally:
            if connection is not None:
                _close_connection_without_masking_v4(connection)

    def _evaluate_and_commit_locked(
        self,
        connection: sqlite3.Connection,
        *,
        expected_cursor: SpotV7AtomicSettlementCursorV1,
        packet: _SpotV7OperationalCommitPacketV3,
    ) -> SpotV7AtomicSettlementResultV1:
        candidate = _seal_test_only_spot_v7_settlement_v1(packet.candidate)
        head = _read_spot_v7_cursor(connection)
        existing = _receipt_for_commitment(connection, candidate.settlement_commitment)
        if existing is not None:
            if _stored_candidate_matches(
                connection,
                candidate,
            ) and _stored_operational_packet_matches_v4(connection, packet):
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
        reason = self._precommit_reject_reason(
            connection,
            head=head,
            expected_cursor=expected_cursor,
            candidate=candidate,
        )
        if reason is None:
            reason = _operational_v4_reject_reason_locked(connection, packet)
        if reason is not None:
            return _reject_locked(connection, head, reason)
        next_cursor = SpotV7AtomicSettlementCursorV1(
            revision=head.revision + 1,
            state_root=candidate.post_state_root,
            settlement_count=head.settlement_count + 1,
            cell_count=head.cell_count,
            last_epoch_id=candidate.epoch_id,
        )
        _persist_candidate(connection, candidate, next_cursor)
        _persist_operational_packet_v4(connection, packet)
        _cas_operational_cursor_v4(connection, packet)
        _cas_spot_v7_meta(connection, head, next_cursor)
        _validate_spot_v7_schema_v4(connection)
        _validate_complete_spot_v7_operational_history_v4(
            connection,
            policy=self._policy,
            settlement_resolver=self._settlement_resolver,
            pending_settlements={candidate.settlement_commitment: packet.settlement},
        )
        receipt = _receipt_for_commitment(connection, candidate.settlement_commitment)
        if receipt is None:
            raise ValueError("committed Spot V7 V4 receipt is missing before commit")
        result = SpotV7AtomicSettlementResultV1(
            SpotV7AtomicSettlementDispositionV1.COMMITTED,
            next_cursor,
            receipt,
            None,
        )
        try:
            connection.commit()
        except (OSError, sqlite3.Error) as exc:
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_OPERATIONAL_V4_COMMIT_OUTCOME_UNKNOWN",
                "commit acknowledgement failed; reconcile with an exact retry",
            ) from exc
        return result

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
        if head.revision >= MAX_SPOT_V7_V4_HISTORY_ENTRIES:
            return SpotV7AtomicSettlementRejectReasonV1.HISTORY_CAPACITY_EXHAUSTED
        if not _candidate_matches_identity(candidate, self._identity):
            return SpotV7AtomicSettlementRejectReasonV1.STORE_IDENTITY_MISMATCH
        if candidate.pre_state_root != head.state_root:
            return SpotV7AtomicSettlementRejectReasonV1.PRE_STATE_ROOT_MISMATCH
        if head.last_epoch_id is not None and candidate.epoch_id <= head.last_epoch_id:
            return SpotV7AtomicSettlementRejectReasonV1.EPOCH_NOT_MONOTONIC
        if not _candidate_cells_match_locked(connection, candidate):
            return SpotV7AtomicSettlementRejectReasonV1.CELL_PRE_STATE_MISMATCH
        return _candidate_reject_reason_locked(connection, candidate)

    def _validate_locked(
        self,
        connection: sqlite3.Connection,
        *,
        allow_initialize: bool = False,
    ) -> None:
        _initialize_or_validate_spot_v7_store_v4(
            connection,
            identity=self._identity,
            genesis_cells=self._genesis_cells,
            policy=self._policy,
            allow_initialize=allow_initialize,
        )
        _validate_complete_spot_v7_operational_history_v4(
            connection,
            policy=self._policy,
            settlement_resolver=self._settlement_resolver,
        )

    def _require_packet_policy(self, packet: _SpotV7OperationalCommitPacketV3) -> None:
        if packet.policy is not self._policy:
            raise ValueError("Spot V7 operational packet policy differs from store policy")
        self._policy._require_active_at_epoch_for_finality_v3(packet.candidate.epoch_id)

    def _read_locked(self, reader: Callable[[sqlite3.Connection], _T]) -> _T:
        try:
            with self._connect() as connection:
                connection.execute("BEGIN")
                self._validate_locked(connection)
                return reader(connection)
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_OPERATIONAL_V4_READ_FAILED",
                str(exc),
            ) from exc

    def _connect(self) -> sqlite3.Connection:
        _require_private_parent(self._path.parent)
        _require_database_identity(self._path, self._database_identity)
        connection = _connect_database(self._path, busy_timeout_ms=self._busy_timeout_ms)
        try:
            _require_database_identity(self._path, self._database_identity)
        except (OSError, ValueError):
            connection.close()
            raise
        return connection


def _validate_constructor_inputs(
    path: Path,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
    governed_operational_policy: _GovernedSpotV7OperationalPolicyV3,
    settlement_resolver: SettlementResolverV4,
    busy_timeout_ms: int,
) -> None:
    if not isinstance(path, Path) or not path.is_absolute():
        raise ValueError("Spot V7 V4 store path must be an absolute pathlib.Path")
    if type(identity) is not SpotV7AtomicSettlementStoreIdentityV1:
        raise TypeError("identity must be exact SpotV7AtomicSettlementStoreIdentityV1")
    if type(genesis_cells) is not tuple or not genesis_cells:
        raise ValueError("genesis_cells must be a nonempty tuple")
    if any(type(cell) is not SpotV7CellOpeningV1 for cell in genesis_cells):
        raise TypeError("genesis_cells must contain exact SpotV7CellOpeningV1 values")
    policy = _require_governed_operational_policy_v3(governed_operational_policy)
    projection = policy._projection_for_governed_da_v2()
    if (
        projection.application_id != identity.application_id
        or projection.chain_or_domain_id != identity.chain_or_domain_id
    ):
        raise ValueError("Spot V7 V4 policy does not match the store scope")
    if not callable(settlement_resolver):
        raise TypeError("settlement_resolver must be callable")
    if type(busy_timeout_ms) is not int or not 1 <= busy_timeout_ms <= MAX_BUSY_TIMEOUT_MS:
        raise ValueError(f"busy_timeout_ms must be in 1..{MAX_BUSY_TIMEOUT_MS}")


def _candidate_matches_identity(
    candidate: _TestOnlySealedSpotV7SettlementV1,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
) -> bool:
    return all(
        (
            candidate.application_id == identity.application_id,
            candidate.chain_or_domain_id == identity.chain_or_domain_id,
            candidate.verified_program_id == identity.verified_program_id,
            candidate.verified_profile_id == identity.verified_profile_id,
            candidate.verified_program_manifest_root == identity.verified_program_manifest_root,
        )
    )


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
    if connection is None:
        return
    try:
        if connection.in_transaction:
            connection.rollback()
    except (OSError, sqlite3.Error):
        return


def _close_connection_without_masking_v4(connection: sqlite3.Connection) -> None:
    try:
        connection.close()
    except (OSError, sqlite3.Error):
        return


def _initialize_new_database_atomically_v4(
    path: Path,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
    policy: _GovernedSpotV7OperationalPolicyV3,
    settlement_resolver: SettlementResolverV4,
    busy_timeout_ms: int,
) -> None:
    staging = _initialization_staging_path_v4(path)
    created = _create_private_database_file(staging)
    staging_identity = _database_identity(staging)
    published = False
    try:
        with _connect_database(staging, busy_timeout_ms=busy_timeout_ms) as connection:
            connection.execute("BEGIN IMMEDIATE")
            _initialize_or_validate_spot_v7_store_v4(
                connection,
                identity=identity,
                genesis_cells=genesis_cells,
                policy=policy,
                allow_initialize=created,
            )
            _validate_complete_spot_v7_operational_history_v4(
                connection,
                policy=policy,
                settlement_resolver=settlement_resolver,
            )
            revision = int(
                connection.execute(
                    "SELECT revision FROM spot_v7_store_meta WHERE singleton = 1"
                ).fetchone()[0]
            )
            if revision != 0:
                raise ValueError("Spot V7 V4 staging database is not a genesis store")
            connection.commit()
        with _connect_database(staging, busy_timeout_ms=busy_timeout_ms) as connection:
            connection.execute("BEGIN")
            _initialize_or_validate_spot_v7_store_v4(
                connection,
                identity=identity,
                genesis_cells=genesis_cells,
                policy=policy,
            )
            _validate_complete_spot_v7_operational_history_v4(
                connection,
                policy=policy,
                settlement_resolver=settlement_resolver,
            )
            connection.rollback()
        _require_no_staging_sidecars_v4(staging)
        _fsync_database_file_v4(staging, staging_identity)
        os.link(staging, path, follow_symlinks=False)
        published = True
        _fsync_directory(path.parent)
        os.unlink(staging)
        _fsync_directory(path.parent)
        _database_identity(path)
    except Exception:
        if not published:
            _remove_unpublished_staging_v4(staging, staging_identity)
        raise


def _recover_published_initialization_link_v4(
    path: Path,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
    policy: _GovernedSpotV7OperationalPolicyV3,
    settlement_resolver: SettlementResolverV4,
    busy_timeout_ms: int,
) -> None:
    staging = _initialization_staging_path_v4(path)
    try:
        final_info = path.stat(follow_symlinks=False)
        staging_info = staging.stat(follow_symlinks=False)
    except FileNotFoundError:
        return
    identities_match = (final_info.st_dev, final_info.st_ino) == (
        staging_info.st_dev,
        staging_info.st_ino,
    )
    if not identities_match:
        return
    for info in (final_info, staging_info):
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or info.st_nlink != 2
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise ValueError("Spot V7 V4 linked initialization files are invalid")
    with _connect_database(path, busy_timeout_ms=busy_timeout_ms) as connection:
        connection.execute("BEGIN")
        _initialize_or_validate_spot_v7_store_v4(
            connection,
            identity=identity,
            genesis_cells=genesis_cells,
            policy=policy,
        )
        _validate_complete_spot_v7_operational_history_v4(
            connection,
            policy=policy,
            settlement_resolver=settlement_resolver,
        )
        connection.rollback()
    final_after = path.stat(follow_symlinks=False)
    staging_after = staging.stat(follow_symlinks=False)
    if (
        (final_after.st_dev, final_after.st_ino) != (final_info.st_dev, final_info.st_ino)
        or (staging_after.st_dev, staging_after.st_ino)
        != (staging_info.st_dev, staging_info.st_ino)
        or final_after.st_nlink != 2
        or staging_after.st_nlink != 2
    ):
        raise ValueError("Spot V7 V4 linked initialization identity changed")
    os.unlink(staging)
    _fsync_directory(path.parent)


def _initialization_staging_path_v4(path: Path) -> Path:
    return path.with_name(f".{path.name}.spot-v7-v4-initializing")


def _require_no_staging_sidecars_v4(staging: Path) -> None:
    for suffix in ("-journal", "-wal", "-shm"):
        if Path(f"{staging}{suffix}").exists():
            raise ValueError("Spot V7 V4 initialization left a SQLite sidecar")


def _fsync_database_file_v4(path: Path, expected: tuple[int, int]) -> None:
    flags = os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(path, flags)
    try:
        info = os.fstat(descriptor)
        if (info.st_dev, info.st_ino) != expected:
            raise ValueError("Spot V7 V4 staging database identity changed")
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _remove_unpublished_staging_v4(
    staging: Path,
    expected: tuple[int, int],
) -> None:
    try:
        info = staging.stat(follow_symlinks=False)
    except FileNotFoundError:
        return
    if (
        not stat.S_ISREG(info.st_mode)
        or info.st_uid != os.geteuid()
        or info.st_nlink != 1
        or stat.S_IMODE(info.st_mode) != 0o600
        or (info.st_dev, info.st_ino) != expected
    ):
        return
    sidecars = tuple(Path(f"{staging}{suffix}") for suffix in ("-journal", "-wal", "-shm"))
    for sidecar in sidecars:
        try:
            sidecar_info = sidecar.stat(follow_symlinks=False)
        except FileNotFoundError:
            continue
        if (
            not stat.S_ISREG(sidecar_info.st_mode)
            or sidecar_info.st_uid != os.geteuid()
            or sidecar_info.st_nlink != 1
            or stat.S_IMODE(sidecar_info.st_mode) != 0o600
        ):
            return
    for sidecar in sidecars:
        try:
            os.unlink(sidecar)
        except FileNotFoundError:
            pass
    os.unlink(staging)
    _fsync_directory(staging.parent)


def _database_identity(path: Path) -> tuple[int, int]:
    info = path.stat(follow_symlinks=False)
    if not stat.S_ISREG(info.st_mode):
        raise ValueError("Spot V7 V4 database must be a regular file")
    if info.st_uid != os.geteuid() or info.st_nlink != 1:
        raise ValueError("Spot V7 V4 database ownership or link count invalid")
    if stat.S_IMODE(info.st_mode) != 0o600:
        raise ValueError("Spot V7 V4 database mode must be 0600")
    return info.st_dev, info.st_ino


def _require_database_identity(path: Path, expected: tuple[int, int]) -> None:
    if _database_identity(path) != expected:
        raise ValueError("Spot V7 V4 database file identity changed")


__all__ = ["SQLiteSpotV7AtomicOperationalStoreV4"]

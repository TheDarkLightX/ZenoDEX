"""Authority-neutral Spot V7 V6 store with exact finality-invocation replay."""

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
from src.integration._zrpf_spot_v7_atomic_settlement_engine_v5 import (
    SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5,
    SpotV7OperationalStoreActivationBlockerV5,
    SpotV7OperationalStoreActivationUnavailableV5,
    _authority_v5_reject_reason_locked,
    _DormantSpotV7AuthorityPrerequisitesV5,
    _persist_authority_provenance_v5,
    _SpotV7DormantAuthorityPacketV5,
    _stored_authority_provenance_matches_v5,
)
from src.integration._zrpf_spot_v7_atomic_settlement_engine_v6 import (
    _finality_invocation_v6_reject_reason_locked,
    _persist_finality_invocation_v6,
    _stored_finality_invocation_matches_v6,
)
from src.integration._zrpf_spot_v7_atomic_settlement_history import (
    _stored_candidate_matches,
    _validate_complete_spot_v7_economic_history,
)
from src.integration._zrpf_spot_v7_atomic_settlement_history_v4 import (
    _SpotV7OperationalHistoryAnchorV4,
)
from src.integration._zrpf_spot_v7_atomic_settlement_history_v5 import (
    _SpotV7OperationalHistoryAnchorV5,
)
from src.integration._zrpf_spot_v7_atomic_settlement_history_v6 import (
    MAX_SPOT_V7_V6_HISTORY_ENTRIES,
    PrerequisiteResolverV6,
    _append_resolved_operational_history_v6,
    _capture_operational_history_anchor_locked_v6,
    _empty_resolved_operational_history_locked_v6,
    _resolve_operational_history_outside_transaction_v6,
    _ResolvedSpotV7OperationalHistoryV6,
    _SpotV7OperationalHistoryAnchorV6,
    _SpotV7OperationalHistoryChangedV6,
    _validate_complete_spot_v7_operational_history_v6,
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
from src.integration._zrpf_spot_v7_atomic_settlement_schema_v6 import (
    _initialize_or_validate_spot_v7_store_v6,
    _validate_spot_v7_schema_v6,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
    _require_governed_operational_policy_v3,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
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
class SQLiteSpotV7AtomicOperationalStoreV6:
    """Persist exact checker invocation artifacts with every V5 commit."""

    _busy_timeout_ms: int
    _database_identity: tuple[int, int]
    _genesis_cells: tuple[SpotV7CellOpeningV1, ...]
    _identity: SpotV7AtomicSettlementStoreIdentityV1
    _path: Path
    _policy: _GovernedSpotV7OperationalPolicyV3
    _prerequisite_resolver: PrerequisiteResolverV6

    __slots__ = (
        "_busy_timeout_ms",
        "_database_identity",
        "_genesis_cells",
        "_identity",
        "_path",
        "_policy",
        "_prerequisite_resolver",
    )

    def __init__(
        self,
        path: Path,
        *,
        identity: SpotV7AtomicSettlementStoreIdentityV1,
        genesis_cells: tuple[SpotV7CellOpeningV1, ...],
        governed_operational_policy: _GovernedSpotV7OperationalPolicyV3,
        prerequisite_resolver: PrerequisiteResolverV6,
        busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS,
    ) -> None:
        _validate_constructor_inputs_v6(
            path,
            identity=identity,
            genesis_cells=genesis_cells,
            governed_operational_policy=governed_operational_policy,
            prerequisite_resolver=prerequisite_resolver,
            busy_timeout_ms=busy_timeout_ms,
        )
        policy = _require_governed_operational_policy_v3(governed_operational_policy)
        object.__setattr__(self, "_path", path)
        object.__setattr__(self, "_identity", identity)
        object.__setattr__(self, "_genesis_cells", genesis_cells)
        object.__setattr__(self, "_policy", policy)
        object.__setattr__(self, "_prerequisite_resolver", prerequisite_resolver)
        object.__setattr__(self, "_busy_timeout_ms", busy_timeout_ms)
        try:
            _require_private_parent(path.parent)
            if path.exists():
                _recover_published_initialization_link_v6(
                    path,
                    identity=identity,
                    genesis_cells=genesis_cells,
                    policy=policy,
                    busy_timeout_ms=busy_timeout_ms,
                )
            else:
                _initialize_new_database_atomically_v6(
                    path,
                    identity=identity,
                    genesis_cells=genesis_cells,
                    policy=policy,
                    busy_timeout_ms=busy_timeout_ms,
                )
            object.__setattr__(self, "_database_identity", _database_identity_v6(path))
            resolved = self._resolve_history_outside_transaction_v6()
            connection = self._connect()
            try:
                connection.execute("BEGIN IMMEDIATE")
                self._validate_locked(connection, resolved_history=resolved)
                connection.commit()
            finally:
                _close_connection_without_masking_v6(connection)
            _fsync_directory(path.parent)
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_OPERATIONAL_V6_OPEN_FAILED",
                str(exc),
            ) from exc

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SQLiteSpotV7AtomicOperationalStoreV6 cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("SQLiteSpotV7AtomicOperationalStoreV6 cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("SQLiteSpotV7AtomicOperationalStoreV6 cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("SQLiteSpotV7AtomicOperationalStoreV6 cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("SQLiteSpotV7AtomicOperationalStoreV6 cannot be serialized")

    @property
    def path(self) -> Path:
        return self._path

    @property
    def activation_blocker(self) -> SpotV7OperationalStoreActivationBlockerV5:
        return SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5

    @property
    def manifest_pinned_checkpoint_finality_cross_check_executed(self) -> bool:
        return self._read_locked(
            lambda connection: (
                int(
                    connection.execute(
                        "SELECT count(*) FROM spot_v7_checkpoint_finality_invocation_v6"
                    ).fetchone()[0]
                )
                > 0
            )
        )

    @property
    def release_governed_checkpoint_finality_checker_identity_verified(self) -> bool:
        return False

    @property
    def hostile_same_interpreter_resistance_established(self) -> bool:
        return False

    @property
    def proof_receipt_authority(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    def _activate_with_fresh_governed_release_evidence_v6(
        self,
        _untrusted_evidence: object,
    ) -> NoReturn:
        raise SpotV7OperationalStoreActivationUnavailableV5()

    def read_cursor(self) -> SpotV7AtomicSettlementCursorV1:
        return self._read_locked(_read_spot_v7_cursor)

    def read_cells(self) -> tuple[SpotV7CellOpeningV1, ...]:
        return self._read_locked(_read_current_cells)

    def get_receipt(
        self,
        settlement_commitment: str,
    ) -> DurableSpotV7AtomicSettlementReceiptV1 | None:
        return self._read_locked(
            lambda connection: _receipt_for_commitment(
                connection,
                settlement_commitment,
            )
        )

    def _commit_authority_prerequisites_v6(
        self,
        *,
        expected_cursor: SpotV7AtomicSettlementCursorV1,
        prerequisites: object,
    ) -> SpotV7AtomicSettlementResultV1:
        if type(expected_cursor) is not SpotV7AtomicSettlementCursorV1:
            raise TypeError("expected_cursor must be exact SpotV7AtomicSettlementCursorV1")
        if (
            not isinstance(prerequisites, _DormantSpotV7AuthorityPrerequisitesV5)
            or type(prerequisites) is not _DormantSpotV7AuthorityPrerequisitesV5
        ):
            raise TypeError("prerequisites must be exact sealed Spot V7 V5 prerequisites")
        exact = prerequisites
        if not exact._has_private_seal():
            raise TypeError("prerequisites lack their private V5 prerequisite seal")
        preflight = exact._packet_for_atomic_store_v5()
        self._require_packet_policy(preflight)
        connection: sqlite3.Connection | None = None
        try:
            resolved = self._resolve_history_outside_transaction_v6()
            connection = self._connect()
            connection.execute("BEGIN IMMEDIATE")
            self._validate_locked(connection, resolved_history=resolved)
            packet = exact._packet_for_atomic_store_v5()
            self._require_packet_policy(packet)
            return self._evaluate_and_commit_locked(
                connection,
                expected_cursor=expected_cursor,
                prerequisites=exact,
                packet=packet,
                resolved_history=resolved,
            )
        except _SpotV7OperationalHistoryChangedV6 as exc:
            _rollback_if_needed_v6(connection)
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_OPERATIONAL_V6_RETRY_REQUIRED",
                "operational history changed during external prerequisite resolution",
            ) from exc
        except SpotV7AtomicSettlementStoreErrorV1:
            _rollback_if_needed_v6(connection)
            raise
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            _rollback_if_needed_v6(connection)
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_OPERATIONAL_V6_COMMIT_FAILED",
                str(exc),
            ) from exc
        finally:
            if connection is not None:
                _close_connection_without_masking_v6(connection)

    def _evaluate_and_commit_locked(
        self,
        connection: sqlite3.Connection,
        *,
        expected_cursor: SpotV7AtomicSettlementCursorV1,
        prerequisites: _DormantSpotV7AuthorityPrerequisitesV5,
        packet: _SpotV7DormantAuthorityPacketV5,
        resolved_history: _ResolvedSpotV7OperationalHistoryV6,
    ) -> SpotV7AtomicSettlementResultV1:
        operational = packet.operational
        candidate = _seal_test_only_spot_v7_settlement_v1(operational.candidate)
        head = _read_spot_v7_cursor(connection)
        existing = _receipt_for_commitment(connection, candidate.settlement_commitment)
        if existing is not None:
            if (
                _stored_candidate_matches(connection, candidate)
                and _stored_operational_packet_matches_v4(connection, operational)
                and _stored_authority_provenance_matches_v5(connection, packet)
                and _stored_finality_invocation_matches_v6(connection, packet)
            ):
                connection.rollback()
                return SpotV7AtomicSettlementResultV1(
                    SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY,
                    head,
                    existing,
                    None,
                )
            return _reject_locked_v6(
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
            reason = _operational_v4_reject_reason_locked(connection, operational)
        if reason is None:
            reason = _authority_v5_reject_reason_locked(connection, packet)
        if reason is None:
            reason = _finality_invocation_v6_reject_reason_locked(connection, packet)
        if reason is not None:
            return _reject_locked_v6(connection, head, reason)
        return self._commit_new_packet_locked(
            connection,
            head=head,
            candidate=candidate,
            prerequisites=prerequisites,
            packet=packet,
            resolved_history=resolved_history,
        )

    def _commit_new_packet_locked(
        self,
        connection: sqlite3.Connection,
        *,
        head: SpotV7AtomicSettlementCursorV1,
        candidate: _TestOnlySealedSpotV7SettlementV1,
        prerequisites: _DormantSpotV7AuthorityPrerequisitesV5,
        packet: _SpotV7DormantAuthorityPacketV5,
        resolved_history: _ResolvedSpotV7OperationalHistoryV6,
    ) -> SpotV7AtomicSettlementResultV1:
        operational = packet.operational
        next_cursor = SpotV7AtomicSettlementCursorV1(
            revision=head.revision + 1,
            state_root=candidate.post_state_root,
            settlement_count=head.settlement_count + 1,
            cell_count=head.cell_count,
            last_epoch_id=candidate.epoch_id,
        )
        _persist_candidate(connection, candidate, next_cursor)
        _persist_operational_packet_v4(connection, operational)
        _persist_authority_provenance_v5(connection, packet)
        _persist_finality_invocation_v6(connection, packet)
        _cas_operational_cursor_v4(connection, operational)
        _cas_spot_v7_meta(connection, head, next_cursor)
        _validate_spot_v7_schema_v6(connection)
        self._validate_post_write_history_locked(
            connection,
            candidate=candidate,
            prerequisites=prerequisites,
            packet=packet,
            next_cursor=next_cursor,
            resolved_history=resolved_history,
        )
        receipt = _receipt_for_commitment(connection, candidate.settlement_commitment)
        if receipt is None:
            raise ValueError("committed Spot V7 V6 receipt is missing before commit")
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
                "SPOT_V7_ATOMIC_OPERATIONAL_V6_COMMIT_OUTCOME_UNKNOWN",
                "commit acknowledgement failed; reconcile with an exact retry",
            ) from exc
        return result

    def _validate_post_write_history_locked(
        self,
        connection: sqlite3.Connection,
        *,
        candidate: _TestOnlySealedSpotV7SettlementV1,
        prerequisites: _DormantSpotV7AuthorityPrerequisitesV5,
        packet: _SpotV7DormantAuthorityPacketV5,
        next_cursor: SpotV7AtomicSettlementCursorV1,
        resolved_history: _ResolvedSpotV7OperationalHistoryV6,
    ) -> None:
        finality = packet.operational.finality
        v4_post_anchor = _SpotV7OperationalHistoryAnchorV4(
            next_cursor,
            finality.next_application_checkpoint_sequence,
            finality.next_application_checkpoint_hash,
            resolved_history.anchor.v5.v4.ordered_settlement_commitments
            + (candidate.settlement_commitment,),
        )
        v5_post_anchor = _SpotV7OperationalHistoryAnchorV5(
            v4_post_anchor,
            resolved_history.anchor.v5.authority_provenance_count + 1,
        )
        post_anchor = _SpotV7OperationalHistoryAnchorV6(
            v5_post_anchor,
            resolved_history.anchor.finality_invocation_count + 1,
        )
        post_history = _append_resolved_operational_history_v6(
            resolved_history,
            expected_anchor=post_anchor,
            commitment=candidate.settlement_commitment,
            prerequisites=prerequisites,
        )
        try:
            _validate_complete_spot_v7_operational_history_v6(
                connection,
                policy=self._policy,
                resolved_history=post_history,
            )
        except _SpotV7OperationalHistoryChangedV6 as exc:
            raise ValueError("Spot V7 V6 post-write history invariant mismatch") from exc

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
        if head.revision >= MAX_SPOT_V7_V6_HISTORY_ENTRIES:
            return SpotV7AtomicSettlementRejectReasonV1.HISTORY_CAPACITY_EXHAUSTED
        if not _candidate_matches_identity_v6(candidate, self._identity):
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
        resolved_history: _ResolvedSpotV7OperationalHistoryV6,
        allow_initialize: bool = False,
    ) -> None:
        _initialize_or_validate_spot_v7_store_v6(
            connection,
            identity=self._identity,
            genesis_cells=self._genesis_cells,
            policy=self._policy,
            allow_initialize=allow_initialize,
        )
        _validate_complete_spot_v7_operational_history_v6(
            connection,
            policy=self._policy,
            resolved_history=resolved_history,
        )

    def _require_packet_policy(self, packet: _SpotV7DormantAuthorityPacketV5) -> None:
        operational = packet.operational
        if operational.policy is not self._policy:
            raise ValueError("Spot V7 V6 packet policy differs from store policy")
        self._policy._require_active_at_epoch_for_finality_v3(operational.candidate.epoch_id)

    def _read_locked(self, reader: Callable[[sqlite3.Connection], _T]) -> _T:
        connection: sqlite3.Connection | None = None
        try:
            resolved = self._resolve_history_outside_transaction_v6()
            connection = self._connect()
            connection.execute("BEGIN")
            self._validate_locked(connection, resolved_history=resolved)
            return reader(connection)
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            raise SpotV7AtomicSettlementStoreErrorV1(
                "SPOT_V7_ATOMIC_OPERATIONAL_V6_READ_FAILED",
                str(exc),
            ) from exc
        finally:
            if connection is not None:
                _close_connection_without_masking_v6(connection)

    def _resolve_history_outside_transaction_v6(
        self,
    ) -> _ResolvedSpotV7OperationalHistoryV6:
        connection = self._connect()
        try:
            connection.execute("BEGIN")
            _initialize_or_validate_spot_v7_store_v6(
                connection,
                identity=self._identity,
                genesis_cells=self._genesis_cells,
                policy=self._policy,
            )
            _validate_complete_spot_v7_economic_history(connection)
            anchor = _capture_operational_history_anchor_locked_v6(connection)
            connection.rollback()
        finally:
            connection.close()
        return _resolve_operational_history_outside_transaction_v6(
            anchor,
            self._prerequisite_resolver,
        )

    def _connect(self) -> sqlite3.Connection:
        _require_private_parent(self._path.parent)
        _require_database_identity_v6(self._path, self._database_identity)
        connection = _connect_database(self._path, busy_timeout_ms=self._busy_timeout_ms)
        try:
            _require_database_identity_v6(self._path, self._database_identity)
        except (OSError, ValueError):
            connection.close()
            raise
        return connection


def _validate_constructor_inputs_v6(
    path: Path,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
    governed_operational_policy: _GovernedSpotV7OperationalPolicyV3,
    prerequisite_resolver: PrerequisiteResolverV6,
    busy_timeout_ms: int,
) -> None:
    if not isinstance(path, Path) or not path.is_absolute():
        raise ValueError("Spot V7 V6 store path must be an absolute pathlib.Path")
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
        raise ValueError("Spot V7 V6 policy does not match the store scope")
    if not callable(prerequisite_resolver):
        raise TypeError("prerequisite_resolver must be callable")
    if type(busy_timeout_ms) is not int or not 1 <= busy_timeout_ms <= MAX_BUSY_TIMEOUT_MS:
        raise ValueError(f"busy_timeout_ms must be in 1..{MAX_BUSY_TIMEOUT_MS}")


def _candidate_matches_identity_v6(
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


def _reject_locked_v6(
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


def _rollback_if_needed_v6(connection: sqlite3.Connection | None) -> None:
    if connection is None:
        return
    try:
        if connection.in_transaction:
            connection.rollback()
    except (OSError, sqlite3.Error):
        return


def _close_connection_without_masking_v6(connection: sqlite3.Connection) -> None:
    try:
        connection.close()
    except (OSError, sqlite3.Error):
        return


def _initialize_new_database_atomically_v6(
    path: Path,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
    policy: _GovernedSpotV7OperationalPolicyV3,
    busy_timeout_ms: int,
) -> None:
    staging = _initialization_staging_path_v6(path)
    created = _create_private_database_file(staging)
    staging_identity = _database_identity_v6(staging)
    published = False
    try:
        with _connect_database(staging, busy_timeout_ms=busy_timeout_ms) as connection:
            connection.execute("BEGIN IMMEDIATE")
            _initialize_or_validate_spot_v7_store_v6(
                connection,
                identity=identity,
                genesis_cells=genesis_cells,
                policy=policy,
                allow_initialize=created,
            )
            empty_history = _empty_resolved_operational_history_locked_v6(connection)
            _validate_complete_spot_v7_operational_history_v6(
                connection,
                policy=policy,
                resolved_history=empty_history,
            )
            revision = int(
                connection.execute(
                    "SELECT revision FROM spot_v7_store_meta WHERE singleton = 1"
                ).fetchone()[0]
            )
            if revision != 0:
                raise ValueError("Spot V7 V6 staging database is not a genesis store")
            connection.commit()
        with _connect_database(staging, busy_timeout_ms=busy_timeout_ms) as connection:
            connection.execute("BEGIN")
            _initialize_or_validate_spot_v7_store_v6(
                connection,
                identity=identity,
                genesis_cells=genesis_cells,
                policy=policy,
            )
            empty_history = _empty_resolved_operational_history_locked_v6(connection)
            _validate_complete_spot_v7_operational_history_v6(
                connection,
                policy=policy,
                resolved_history=empty_history,
            )
            connection.rollback()
        _require_no_staging_sidecars_v6(staging)
        _fsync_database_file_v6(staging, staging_identity)
        os.link(staging, path, follow_symlinks=False)
        published = True
        _fsync_directory(path.parent)
        os.unlink(staging)
        _fsync_directory(path.parent)
        _database_identity_v6(path)
    except (OSError, sqlite3.Error, TypeError, ValueError):
        if not published:
            _remove_unpublished_staging_v6(staging, staging_identity)
        raise


def _recover_published_initialization_link_v6(
    path: Path,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
    policy: _GovernedSpotV7OperationalPolicyV3,
    busy_timeout_ms: int,
) -> None:
    staging = _initialization_staging_path_v6(path)
    try:
        final_info = path.stat(follow_symlinks=False)
        staging_info = staging.stat(follow_symlinks=False)
    except FileNotFoundError:
        return
    if (final_info.st_dev, final_info.st_ino) != (
        staging_info.st_dev,
        staging_info.st_ino,
    ):
        return
    for info in (final_info, staging_info):
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or info.st_nlink != 2
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise ValueError("Spot V7 V6 linked initialization files are invalid")
    with _connect_database(path, busy_timeout_ms=busy_timeout_ms) as connection:
        connection.execute("BEGIN")
        _initialize_or_validate_spot_v7_store_v6(
            connection,
            identity=identity,
            genesis_cells=genesis_cells,
            policy=policy,
        )
        empty_history = _empty_resolved_operational_history_locked_v6(connection)
        _validate_complete_spot_v7_operational_history_v6(
            connection,
            policy=policy,
            resolved_history=empty_history,
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
        raise ValueError("Spot V7 V6 linked initialization identity changed")
    os.unlink(staging)
    _fsync_directory(path.parent)


def _initialization_staging_path_v6(path: Path) -> Path:
    return path.with_name(f".{path.name}.spot-v7-v6-initializing")


def _require_no_staging_sidecars_v6(staging: Path) -> None:
    for suffix in ("-journal", "-wal", "-shm"):
        if Path(f"{staging}{suffix}").exists():
            raise ValueError("Spot V7 V6 initialization left a SQLite sidecar")


def _fsync_database_file_v6(path: Path, expected: tuple[int, int]) -> None:
    flags = os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(path, flags)
    try:
        info = os.fstat(descriptor)
        if (info.st_dev, info.st_ino) != expected:
            raise ValueError("Spot V7 V6 staging database identity changed")
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _remove_unpublished_staging_v6(
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


def _database_identity_v6(path: Path) -> tuple[int, int]:
    info = path.stat(follow_symlinks=False)
    if not stat.S_ISREG(info.st_mode):
        raise ValueError("Spot V7 V6 database must be a regular file")
    if info.st_uid != os.geteuid() or info.st_nlink != 1:
        raise ValueError("Spot V7 V6 database ownership or link count invalid")
    if stat.S_IMODE(info.st_mode) != 0o600:
        raise ValueError("Spot V7 V6 database mode must be 0600")
    return info.st_dev, info.st_ino


def _require_database_identity_v6(path: Path, expected: tuple[int, int]) -> None:
    if _database_identity_v6(path) != expected:
        raise ValueError("Spot V7 V6 database file identity changed")


__all__ = ["SQLiteSpotV7AtomicOperationalStoreV6"]

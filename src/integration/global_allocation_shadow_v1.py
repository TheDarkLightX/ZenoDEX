"""Bounded read-only allocation observations of an isolated ordinary epoch journal.

The source validates one SQLite read transaction, exact bundle bytes and complete
predecessor lineage. This is local consistency evidence; it authenticates neither
the store nor its receipts. No publisher, writer capability or economic effect is
passed to the observer. Diagnostics live in a separate bounded memory ring.

DELETE-mode SQLite readers can delay concurrent writers. This unmounted adapter
does not establish deployment, timing/resource isolation or production SHADOW
qualification. Missing lane witnesses remain visible evidence gaps.
"""

from __future__ import annotations

import sqlite3
from collections import deque
from dataclasses import dataclass, fields
from enum import Enum
from pathlib import Path
from typing import Any, Final

from ..core import global_settlement_types_v1 as types
from ..core.global_accounting_allocation_certificate_v1 import (
    EMPTY_LANE_WITNESS_SLOTS_V1,
    LANE_ALLOCATION_PRODUCER_REGISTRY_V1,
    AllocationCertificateAcceptedV1,
    LaneProducerKindV1,
    VerifiedLaneAllocationFragmentV1,
    check_global_accounting_allocation_certificate_v1,
)
from ..core.global_accounting_allocation_projection_v1 import (
    AllocationProjectionRejectedV1,
    project_allocation_certificate_v1,
)
from ..core.global_economic_durable_activation_v1 import (
    DurableEconomicComponentKindV1,
    _decode_exact_canonical_json_v1,
)
from ..core.global_economic_refinement_snapshot_v1 import _snapshot_state_v1
from .global_economic_durable_epoch_v1 import (
    DurableEconomicPublicationHeadV1,
    _decode_payload_sections_v1,
)
from .global_economic_epoch_journal_v1 import (
    GlobalEconomicEpochJournalV1,
    _normalize_path_v1,
    _reject_wal_artifacts_v1,
    _require_owned_regular_epoch_store_v1,
)

MAX_SHADOW_HISTORY_EPOCHS_V1: Final = 64
MAX_SHADOW_STORE_BYTES_V1: Final = 32 * 1024 * 1024
MAX_SHADOW_STATE_ROWS_V1: Final = 8192
MAX_SHADOW_DIAGNOSTICS_V1: Final = 128
SHADOW_SOURCE_PROVENANCE_V1: Final = "LOCAL_JOURNAL_CONSISTENCY_RECEIPTS_UNVERIFIED"

# Exact decode registry. Each table is decoded in full or observation fails.
_TABLES_V1: Final = (
    ("lane_roots", types.LaneStateRootV1, len(types.ALL_LANE_IDS_V1)),
    ("balances", types.EconomicAmountV1, types.MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1),
    ("supplies", types.AssetSupplyV1, types.MAX_GLOBAL_SUPPLY_ROWS_V1),
    ("custody", types.EconomicAmountV1, types.MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1),
    ("liabilities", types.EconomicAmountV1, types.MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1),
    ("reserves", types.EconomicAmountV1, types.MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1),
    ("oracle_occurrences", types.OracleOccurrenceStateV1, types.MAX_GLOBAL_ORACLE_ROWS_V1),
    ("replay_state", types.ReplayStateV1, types.MAX_GLOBAL_REPLAY_ROWS_V1),
    ("terminal_obligations", types.TerminalObligationV1, types.MAX_GLOBAL_TERMINAL_ROWS_V1),
    ("outbox", types.OutboxStateV1, types.MAX_GLOBAL_OUTBOX_ROWS_V1),
)


class ShadowObservationStatusV1(str, Enum):
    AGREES = "AGREES"
    DIFFERS = "DIFFERS"
    PROJECTED = "PROJECTED"
    PROJECTION_REJECTED = "PROJECTION_REJECTED"
    MISSING_WITNESS = "MISSING_WITNESS"
    SOURCE_UNAVAILABLE = "SOURCE_UNAVAILABLE"
    SOURCE_INVALID = "SOURCE_INVALID"
    RESOURCE_LIMIT = "RESOURCE_LIMIT"
    OBSERVATION_FAILED = "OBSERVATION_FAILED"


class _ObservationLimitV1(ValueError):
    pass


@dataclass(frozen=True, slots=True)
class CommittedAllocationSnapshotV1:
    """Owned observation data with local consistency provenance, no authority."""

    head: DurableEconomicPublicationHeadV1
    state: types.GlobalEconomicStateV1
    predecessor_head: DurableEconomicPublicationHeadV1 | None
    predecessor_state: types.GlobalEconomicStateV1 | None
    provenance: str = SHADOW_SOURCE_PROVENANCE_V1


@dataclass(frozen=True, slots=True)
class ShadowAllocationDiagnosticV1:
    status: ShadowObservationStatusV1
    code: str
    publication_id: str | None
    state_root: str | None
    predecessor_publication_id: str | None
    allocation_root: str | None
    expected_allocation_root: str | None
    provenance: str = SHADOW_SOURCE_PROVENANCE_V1
    authority: str = "NONE"


def _exact_row_v1(row_type: type[Any], raw: object) -> Any:
    if type(raw) is not dict or set(raw) != {field.name for field in fields(row_type)}:
        raise ValueError("shadow state row has an open field set")
    owned = dict(raw)
    if "lane_id" in owned:
        if type(owned["lane_id"]) is not str:
            raise TypeError("shadow lane id must be text")
        owned["lane_id"] = types.LaneIdV1(owned["lane_id"])
    if row_type is types.TerminalObligationV1:
        owned["status"] = types.TerminalObligationStatusV1(owned["status"])
    if row_type is types.OutboxStateV1:
        owned["status"] = types.OutboxStatusV1(owned["status"])
    return row_type(**owned)


def decode_shadow_state_v1(raw: object) -> types.GlobalEconomicStateV1:
    """Decode exact V1 fields and bounded complete tables without coercion."""

    expected = {field.name for field in fields(types.GlobalEconomicStateV1)} | {"schema"}
    if type(raw) is not dict or set(raw) != expected:
        raise ValueError("shadow state has an open field set")
    if raw["schema"] != types.GLOBAL_SETTLEMENT_ABI_V1:
        raise ValueError("shadow state schema mismatch")
    total = 0
    for name, _row_type, limit in _TABLES_V1:
        values = raw[name]
        if type(values) is not list:
            raise TypeError("shadow state table must be an exact array")
        total += len(values)
        if len(values) > limit or total > MAX_SHADOW_STATE_ROWS_V1:
            raise _ObservationLimitV1("shadow state row budget exceeded")
    owned = {key: value for key, value in raw.items() if key != "schema"}
    for name, row_type, _limit in _TABLES_V1:
        owned[name] = tuple(_exact_row_v1(row_type, row) for row in raw[name])
    return _snapshot_state_v1(types.GlobalEconomicStateV1(**owned))


def _bind_snapshot_state_v1(
    state: types.GlobalEconomicStateV1, head: DurableEconomicPublicationHeadV1
) -> None:
    if state.state_root != head.state_root or any(
        getattr(state, field) != getattr(head, field)
        for field in ("chain_id", "deployment_root", "profile_root", "writer_epoch", "height")
    ):
        raise ValueError("shadow committed state/head binding mismatch")


def _read_only_authorizer_v1(
    action: int, first: str | None, second: str | None, _db: str | None, _trigger: str | None
) -> int:
    if action in {
        sqlite3.SQLITE_READ,
        sqlite3.SQLITE_SELECT,
        sqlite3.SQLITE_FUNCTION,
        sqlite3.SQLITE_TRANSACTION,
    }:
        return sqlite3.SQLITE_OK
    if action == sqlite3.SQLITE_PRAGMA and first in {
        "table_list",
        "table_info",
        "integrity_check",
        "trusted_schema",
        "query_only",
        "journal_mode",
    }:
        if second is None or first == "table_info":
            return sqlite3.SQLITE_OK
    return sqlite3.SQLITE_DENY


def _check_capture_budget_v1(connection: sqlite3.Connection) -> None:
    row = connection.execute(
        "SELECT COUNT(*), COALESCE(SUM(length(bundle_bytes)), 0) FROM economic_epochs"
    ).fetchone()
    activation = connection.execute(
        "SELECT COALESCE(SUM(length(activation_bundle)), 0) FROM metadata"
    ).fetchone()
    if (
        row is None
        or activation is None
        or any(type(value) is not int for value in (*row, *activation))
    ):
        raise ValueError("shadow store bound query is malformed")
    if row[0] > MAX_SHADOW_HISTORY_EPOCHS_V1 or row[1] + activation[0] > MAX_SHADOW_STORE_BYTES_V1:
        raise _ObservationLimitV1("shadow history budget exceeded")


def _read_committed_snapshot_v1(
    journal: GlobalEconomicEpochJournalV1,
) -> CommittedAllocationSnapshotV1:
    # All methods called here validate/read. No publisher/write capability exists.
    journal._validate_schema_v1()
    _check_capture_budget_v1(journal._connection)
    head = journal._validate_store_v1()
    activation = journal._read_activation_v1()
    activation_raw = next(
        component.payload
        for component in activation.components
        if component.kind is DurableEconomicComponentKindV1.STATE
    )
    initial_state = decode_shadow_state_v1(
        _decode_exact_canonical_json_v1(activation_raw, name="shadow activation state")
    )
    initial_head = DurableEconomicPublicationHeadV1.from_activation(activation.head)
    _bind_snapshot_state_v1(initial_state, initial_head)
    epochs = journal._read_epochs_v1()
    if not epochs:
        return CommittedAllocationSnapshotV1(head, initial_state, None, None)
    current = epochs[-1]
    state = decode_shadow_state_v1(_decode_payload_sections_v1(current.payload).state)
    prior_head = initial_head if len(epochs) == 1 else epochs[-2].head
    prior_state = (
        initial_state
        if len(epochs) == 1
        else decode_shadow_state_v1(_decode_payload_sections_v1(epochs[-2].payload).state)
    )
    _bind_snapshot_state_v1(state, head)
    _bind_snapshot_state_v1(prior_state, prior_head)
    if (
        current.record.source_publication_id != prior_head.publication_id
        or current.record.pre_state_root != prior_state.state_root
    ):
        raise ValueError("shadow predecessor state binding mismatch")
    return CommittedAllocationSnapshotV1(head, state, prior_head, prior_state)


@dataclass(frozen=True, slots=True)
class ReadOnlyAllocationSourceV1:
    """Path-only read capability. No journal, connection, token or writer is exposed.

    Each call opens a fresh read-only connection and closes its read transaction
    before returning. Python process/OS compromise is outside this boundary.
    """

    path: Path

    def __post_init__(self) -> None:
        object.__setattr__(self, "path", _normalize_path_v1(self.path))

    def read_snapshot(self) -> CommittedAllocationSnapshotV1:
        _require_owned_regular_epoch_store_v1(self.path, name="shadow epoch source")
        before = self.path.stat()
        if before.st_size > MAX_SHADOW_STORE_BYTES_V1:
            raise _ObservationLimitV1("shadow file byte budget exceeded")
        _reject_wal_artifacts_v1(self.path)
        connection = sqlite3.connect(
            f"{self.path.as_uri()}?mode=ro", uri=True, isolation_level=None, timeout=0.05
        )
        try:
            connection.execute("PRAGMA query_only = ON")
            connection.execute("PRAGMA trusted_schema = OFF")
            connection.set_authorizer(_read_only_authorizer_v1)
            if connection.execute("PRAGMA query_only").fetchone() != (1,):
                raise RuntimeError("shadow source is not query-only")
            if connection.execute("PRAGMA journal_mode").fetchone() != ("delete",):
                raise ValueError("shadow source requires DELETE journal mode")
            connection.execute("BEGIN")
            snapshot = _read_committed_snapshot_v1(
                GlobalEconomicEpochJournalV1(self.path, connection)
            )
            connection.execute("COMMIT")
            _require_owned_regular_epoch_store_v1(self.path, name="shadow epoch source")
            after = self.path.stat()
            if (before.st_dev, before.st_ino) != (after.st_dev, after.st_ino):
                raise ValueError("shadow source path identity changed")
            return snapshot
        finally:
            try:
                if connection.in_transaction:
                    connection.rollback()
            finally:
                connection.close()


class GlobalAllocationShadowObserverV1:
    """Explicitly invoked diagnostics consumer, absent from every commit decision."""

    __slots__ = ("_diagnostics",)

    def __init__(self, *, capacity: int = MAX_SHADOW_DIAGNOSTICS_V1) -> None:
        if type(capacity) is not int or not 1 <= capacity <= MAX_SHADOW_DIAGNOSTICS_V1:
            raise ValueError("shadow diagnostic capacity is outside its bound")
        self._diagnostics: deque[ShadowAllocationDiagnosticV1] = deque(maxlen=capacity)

    @property
    def diagnostics(self) -> tuple[ShadowAllocationDiagnosticV1, ...]:
        return tuple(self._diagnostics)

    def observe(
        self,
        source: ReadOnlyAllocationSourceV1,
        *,
        expected_allocation_root: str | None = None,
        lane_witnesses: tuple[VerifiedLaneAllocationFragmentV1 | None, ...] = (),
    ) -> ShadowAllocationDiagnosticV1:
        if type(source) is not ReadOnlyAllocationSourceV1:
            raise TypeError("shadow requires the exact read-only source capability")
        if expected_allocation_root is not None:
            types._require_root(expected_allocation_root, name="shadow comparison root")
        snapshot = None
        try:
            snapshot = source.read_snapshot()
            status, code, root = _observe_allocation_v1(
                snapshot, lane_witnesses, expected_allocation_root
            )
        except _ObservationLimitV1:
            status, code, root = (
                ShadowObservationStatusV1.RESOURCE_LIMIT,
                "OBSERVATION_BUDGET_EXCEEDED",
                None,
            )
        except (OSError, sqlite3.OperationalError):
            status, code, root = (
                ShadowObservationStatusV1.SOURCE_UNAVAILABLE,
                "SOURCE_UNAVAILABLE",
                None,
            )
        except (ValueError, TypeError, RuntimeError, sqlite3.DatabaseError):
            status = (
                ShadowObservationStatusV1.SOURCE_INVALID
                if snapshot is None
                else ShadowObservationStatusV1.OBSERVATION_FAILED
            )
            code, root = status.value, None
        diagnostic = ShadowAllocationDiagnosticV1(
            status,
            code,
            None if snapshot is None else snapshot.head.publication_id,
            None if snapshot is None else snapshot.head.state_root,
            None
            if snapshot is None or snapshot.predecessor_head is None
            else snapshot.predecessor_head.publication_id,
            root,
            expected_allocation_root,
            provenance="SOURCE_NOT_OBSERVED" if snapshot is None else SHADOW_SOURCE_PROVENANCE_V1,
        )
        self._diagnostics.append(diagnostic)
        return diagnostic


def _observe_allocation_v1(
    snapshot: CommittedAllocationSnapshotV1,
    lane_witnesses: tuple[VerifiedLaneAllocationFragmentV1 | None, ...],
    expected_root: str | None,
) -> tuple[ShadowObservationStatusV1, str, str | None]:
    if type(lane_witnesses) is not tuple or (
        lane_witnesses and len(lane_witnesses) != len(types.ALL_LANE_IDS_V1)
    ):
        raise TypeError("shadow witness slots are malformed")
    if any(
        slot is not None and type(slot) is not VerifiedLaneAllocationFragmentV1
        for slot in lane_witnesses
    ):
        raise TypeError("shadow witness slot is not an admitted witness")
    slots = lane_witnesses or EMPTY_LANE_WITNESS_SLOTS_V1
    required = [
        index
        for index, lane in enumerate(snapshot.state.lane_roots)
        if lane.enabled
        and LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane.lane_id][0]
        is LaneProducerKindV1.RECEIPT_BACKED
    ]
    if any(slots[index] is None for index in required):
        return (
            ShadowObservationStatusV1.MISSING_WITNESS,
            "RECEIPT_ALLOCATION_WITNESS_UNAVAILABLE",
            None,
        )
    roots = tuple(
        (slot.fragment.lane_id, slot.fragment.binding_root) for slot in slots if slot is not None
    )
    projected = project_allocation_certificate_v1(snapshot.state, roots, slots)
    if isinstance(projected, AllocationProjectionRejectedV1):
        return ShadowObservationStatusV1.PROJECTION_REJECTED, projected.code.value, None
    checked = check_global_accounting_allocation_certificate_v1(projected, snapshot.state, slots)
    if not isinstance(checked, AllocationCertificateAcceptedV1):
        return ShadowObservationStatusV1.PROJECTION_REJECTED, checked.code.value, None
    if expected_root is None:
        return ShadowObservationStatusV1.PROJECTED, "NO_COMPARISON_ROOT", projected.allocation_root
    status = (
        ShadowObservationStatusV1.AGREES
        if expected_root == projected.allocation_root
        else ShadowObservationStatusV1.DIFFERS
    )
    return status, "CALLER_COMPARISON_ROOT", projected.allocation_root

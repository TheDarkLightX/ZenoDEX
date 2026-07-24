"""Restart replay for exact Spot V7 V6 finality-invocation persistence."""

from __future__ import annotations

import sqlite3
from collections.abc import Callable
from dataclasses import dataclass
from typing import TypeAlias

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _derive_capability_commitment,
)
from src.integration._zrpf_spot_v7_atomic_settlement_engine_v5 import (
    _DormantSpotV7AuthorityPrerequisitesV5,
)
from src.integration._zrpf_spot_v7_atomic_settlement_engine_v6 import (
    _validate_finality_invocation_row_v6,
)
from src.integration._zrpf_spot_v7_atomic_settlement_history_v4 import (
    _SpotV7OperationalHistoryChangedV4,
)
from src.integration._zrpf_spot_v7_atomic_settlement_history_v5 import (
    MAX_SPOT_V7_V5_DATABASE_BYTES,
    MAX_SPOT_V7_V5_HISTORY_ENTRIES,
    _append_resolved_operational_history_v5,
    _capture_operational_history_anchor_locked_v5,
    _resolve_operational_history_outside_transaction_v5,
    _ResolvedSpotV7AuthorityEntryV5,
    _ResolvedSpotV7OperationalHistoryV5,
    _SpotV7OperationalHistoryAnchorV5,
    _SpotV7OperationalHistoryChangedV5,
    _validate_complete_spot_v7_operational_history_v5,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import _hash_bytes

PrerequisiteResolverV6: TypeAlias = Callable[[str], object]
MAX_SPOT_V7_V6_HISTORY_ENTRIES = MAX_SPOT_V7_V5_HISTORY_ENTRIES
MAX_SPOT_V7_V6_DATABASE_BYTES = MAX_SPOT_V7_V5_DATABASE_BYTES


class _SpotV7OperationalHistoryChangedV6(ValueError):
    """The database changed after the resolver-safe V6 snapshot closed."""


@dataclass(frozen=True, slots=True)
class _SpotV7OperationalHistoryAnchorV6:
    v5: _SpotV7OperationalHistoryAnchorV5
    finality_invocation_count: int


@dataclass(frozen=True, slots=True)
class _ResolvedSpotV7OperationalHistoryV6:
    anchor: _SpotV7OperationalHistoryAnchorV6
    entries: tuple[_ResolvedSpotV7AuthorityEntryV5, ...]


def _capture_operational_history_anchor_locked_v6(
    connection: sqlite3.Connection,
) -> _SpotV7OperationalHistoryAnchorV6:
    v5 = _capture_operational_history_anchor_locked_v5(connection)
    count = int(
        connection.execute(
            "SELECT count(*) FROM spot_v7_checkpoint_finality_invocation_v6"
        ).fetchone()[0]
    )
    if count != v5.v4.economic_cursor.revision:
        raise ValueError("Spot V7 V6 finality-invocation count mismatch")
    return _SpotV7OperationalHistoryAnchorV6(v5, count)


def _resolve_operational_history_outside_transaction_v6(
    anchor: _SpotV7OperationalHistoryAnchorV6,
    prerequisite_resolver: PrerequisiteResolverV6,
) -> _ResolvedSpotV7OperationalHistoryV6:
    v5 = _resolve_operational_history_outside_transaction_v5(
        anchor.v5,
        prerequisite_resolver,
    )
    return _ResolvedSpotV7OperationalHistoryV6(anchor, v5.entries)


def _empty_resolved_operational_history_locked_v6(
    connection: sqlite3.Connection,
) -> _ResolvedSpotV7OperationalHistoryV6:
    anchor = _capture_operational_history_anchor_locked_v6(connection)
    if (
        anchor.v5.v4.economic_cursor.revision != 0
        or anchor.v5.v4.ordered_settlement_commitments
        or anchor.v5.authority_provenance_count != 0
        or anchor.finality_invocation_count != 0
    ):
        raise ValueError("Spot V7 V6 initialization history is not empty")
    return _ResolvedSpotV7OperationalHistoryV6(anchor, ())


def _append_resolved_operational_history_v6(
    resolved: _ResolvedSpotV7OperationalHistoryV6,
    *,
    expected_anchor: _SpotV7OperationalHistoryAnchorV6,
    commitment: str,
    prerequisites: _DormantSpotV7AuthorityPrerequisitesV5,
) -> _ResolvedSpotV7OperationalHistoryV6:
    if expected_anchor.finality_invocation_count != (resolved.anchor.finality_invocation_count + 1):
        raise ValueError("Spot V7 V6 successor invocation count mismatch")
    v5 = _append_resolved_operational_history_v5(
        _ResolvedSpotV7OperationalHistoryV5(resolved.anchor.v5, resolved.entries),
        expected_anchor=expected_anchor.v5,
        commitment=commitment,
        prerequisites=prerequisites,
    )
    return _ResolvedSpotV7OperationalHistoryV6(expected_anchor, v5.entries)


def _validate_complete_spot_v7_operational_history_v6(
    connection: sqlite3.Connection,
    *,
    policy: _GovernedSpotV7OperationalPolicyV3,
    resolved_history: _ResolvedSpotV7OperationalHistoryV6,
) -> None:
    v5_history = _ResolvedSpotV7OperationalHistoryV5(
        resolved_history.anchor.v5,
        resolved_history.entries,
    )
    try:
        _validate_complete_spot_v7_operational_history_v5(
            connection,
            policy=policy,
            resolved_history=v5_history,
        )
    except (
        _SpotV7OperationalHistoryChangedV4,
        _SpotV7OperationalHistoryChangedV5,
    ) as exc:
        raise _SpotV7OperationalHistoryChangedV6(
            "Spot V7 V6 history changed during V5 prerequisite resolution"
        ) from exc
    actual_anchor = _capture_operational_history_anchor_locked_v6(connection)
    if actual_anchor != resolved_history.anchor:
        raise _SpotV7OperationalHistoryChangedV6(
            "Spot V7 V6 operational history changed during external resolution"
        )
    if len(resolved_history.entries) != actual_anchor.finality_invocation_count:
        raise ValueError("Spot V7 V6 resolved invocation history count mismatch")
    for entry in resolved_history.entries:
        packet = entry.prerequisites._packet_for_atomic_store_v5()
        commitment = _derive_capability_commitment(packet.operational.candidate)
        if commitment != entry.commitment:
            raise ValueError("Spot V7 V6 resolver returned the wrong prerequisites")
        row = connection.execute(
            "SELECT * FROM spot_v7_checkpoint_finality_invocation_v6 "
            "WHERE settlement_commitment = ?",
            (_hash_bytes(commitment, name="V6 history commitment"),),
        ).fetchone()
        if row is None:
            raise ValueError("Spot V7 V6 finality-invocation row is missing")
        _validate_finality_invocation_row_v6(row, packet)


__all__ = ()

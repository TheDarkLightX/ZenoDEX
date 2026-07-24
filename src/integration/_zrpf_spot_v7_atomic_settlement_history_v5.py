"""Restart replay for dormant authority-capable Spot V7 schema V5."""

from __future__ import annotations

import sqlite3
from collections.abc import Callable
from dataclasses import dataclass

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _derive_capability_commitment,
)
from src.integration._zrpf_spot_v7_atomic_settlement_engine_v5 import (
    _DormantSpotV7AuthorityPrerequisitesV5,
    _validate_authority_provenance_row_v5,
)
from src.integration._zrpf_spot_v7_atomic_settlement_history_v4 import (
    MAX_SPOT_V7_V4_DATABASE_BYTES,
    MAX_SPOT_V7_V4_HISTORY_ENTRIES,
    _capture_operational_history_anchor_locked_v4,
    _ResolvedSpotV7OperationalHistoryV4,
    _ResolvedSpotV7SettlementEntryV4,
    _SpotV7OperationalHistoryAnchorV4,
    _validate_complete_spot_v7_operational_history_v4,
)
from src.integration._zrpf_spot_v7_atomic_settlement_schema_v5 import (
    _validate_activation_blocker_v5,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import _hash_bytes

PrerequisiteResolverV5 = Callable[[str], object]
MAX_SPOT_V7_V5_HISTORY_ENTRIES = MAX_SPOT_V7_V4_HISTORY_ENTRIES
MAX_SPOT_V7_V5_DATABASE_BYTES = MAX_SPOT_V7_V4_DATABASE_BYTES


class _SpotV7PrerequisiteResolverErrorV5(ValueError):
    """Typed fail-closed wrapper for the external prerequisite resolver."""


class _SpotV7OperationalHistoryChangedV5(ValueError):
    """The database changed after the resolver-safe V5 snapshot closed."""


@dataclass(frozen=True, slots=True)
class _SpotV7OperationalHistoryAnchorV5:
    v4: _SpotV7OperationalHistoryAnchorV4
    authority_provenance_count: int


@dataclass(frozen=True, slots=True)
class _ResolvedSpotV7AuthorityEntryV5:
    commitment: str
    prerequisites: _DormantSpotV7AuthorityPrerequisitesV5


@dataclass(frozen=True, slots=True)
class _ResolvedSpotV7OperationalHistoryV5:
    anchor: _SpotV7OperationalHistoryAnchorV5
    entries: tuple[_ResolvedSpotV7AuthorityEntryV5, ...]


def _capture_operational_history_anchor_locked_v5(
    connection: sqlite3.Connection,
) -> _SpotV7OperationalHistoryAnchorV5:
    v4 = _capture_operational_history_anchor_locked_v4(connection)
    _validate_activation_blocker_v5(connection)
    count = int(
        connection.execute("SELECT count(*) FROM spot_v7_authority_provenance_v5").fetchone()[0]
    )
    if count != v4.economic_cursor.revision:
        raise ValueError("Spot V7 V5 authority provenance count mismatch")
    return _SpotV7OperationalHistoryAnchorV5(v4, count)


def _resolve_operational_history_outside_transaction_v5(
    anchor: _SpotV7OperationalHistoryAnchorV5,
    prerequisite_resolver: PrerequisiteResolverV5,
) -> _ResolvedSpotV7OperationalHistoryV5:
    entries = tuple(
        _resolve_prerequisite_entry(commitment, prerequisite_resolver)
        for commitment in anchor.v4.ordered_settlement_commitments
    )
    return _ResolvedSpotV7OperationalHistoryV5(anchor, entries)


def _empty_resolved_operational_history_locked_v5(
    connection: sqlite3.Connection,
) -> _ResolvedSpotV7OperationalHistoryV5:
    anchor = _capture_operational_history_anchor_locked_v5(connection)
    if (
        anchor.v4.economic_cursor.revision != 0
        or anchor.v4.ordered_settlement_commitments
        or anchor.authority_provenance_count != 0
    ):
        raise ValueError("Spot V7 V5 initialization history is not empty")
    return _ResolvedSpotV7OperationalHistoryV5(anchor, ())


def _append_resolved_operational_history_v5(
    resolved: _ResolvedSpotV7OperationalHistoryV5,
    *,
    expected_anchor: _SpotV7OperationalHistoryAnchorV5,
    commitment: str,
    prerequisites: _DormantSpotV7AuthorityPrerequisitesV5,
) -> _ResolvedSpotV7OperationalHistoryV5:
    if expected_anchor.v4.ordered_settlement_commitments != (
        resolved.anchor.v4.ordered_settlement_commitments + (commitment,)
    ):
        raise ValueError("Spot V7 V5 successor history commitment order mismatch")
    if expected_anchor.authority_provenance_count != (
        resolved.anchor.authority_provenance_count + 1
    ):
        raise ValueError("Spot V7 V5 successor provenance count mismatch")
    entry = _resolved_prerequisite_entry(commitment, prerequisites)
    return _ResolvedSpotV7OperationalHistoryV5(
        expected_anchor,
        resolved.entries + (entry,),
    )


def _validate_complete_spot_v7_operational_history_v5(
    connection: sqlite3.Connection,
    *,
    policy: _GovernedSpotV7OperationalPolicyV3,
    resolved_history: _ResolvedSpotV7OperationalHistoryV5,
) -> None:
    v4_history = _ResolvedSpotV7OperationalHistoryV4(
        resolved_history.anchor.v4,
        tuple(
            _ResolvedSpotV7SettlementEntryV4(
                entry.commitment,
                entry.prerequisites._packet_for_atomic_store_v5().operational.settlement,
            )
            for entry in resolved_history.entries
        ),
    )
    _validate_complete_spot_v7_operational_history_v4(
        connection,
        policy=policy,
        resolved_history=v4_history,
    )
    actual_anchor = _capture_operational_history_anchor_locked_v5(connection)
    if actual_anchor != resolved_history.anchor:
        raise _SpotV7OperationalHistoryChangedV5(
            "Spot V7 V5 operational history changed during external resolution"
        )
    if len(resolved_history.entries) != actual_anchor.authority_provenance_count:
        raise ValueError("Spot V7 V5 resolved authority history count mismatch")
    for entry in resolved_history.entries:
        packet = entry.prerequisites._packet_for_atomic_store_v5()
        commitment = _derive_capability_commitment(packet.operational.candidate)
        if commitment != entry.commitment:
            raise ValueError("Spot V7 V5 resolver returned the wrong prerequisites")
        row = connection.execute(
            "SELECT * FROM spot_v7_authority_provenance_v5 WHERE settlement_commitment = ?",
            (_hash_bytes(commitment, name="V5 history commitment"),),
        ).fetchone()
        if row is None:
            raise ValueError("Spot V7 V5 authority provenance row is missing")
        _validate_authority_provenance_row_v5(row, packet)


def _resolve_prerequisite_entry(
    commitment: str,
    prerequisite_resolver: PrerequisiteResolverV5,
) -> _ResolvedSpotV7AuthorityEntryV5:
    try:
        value = prerequisite_resolver(commitment)
    except Exception as exc:
        raise _SpotV7PrerequisiteResolverErrorV5("Spot V7 V5 prerequisite resolver failed") from exc
    return _resolved_prerequisite_entry(commitment, value)


def _resolved_prerequisite_entry(
    commitment: str,
    value: object,
) -> _ResolvedSpotV7AuthorityEntryV5:
    if type(value) is not _DormantSpotV7AuthorityPrerequisitesV5:
        raise TypeError("V5 resolver must return exact sealed Spot V7 V5 prerequisites")
    prerequisites = value
    if not prerequisites._has_private_seal():
        raise TypeError("V5 resolver prerequisites lack their private seal")
    packet = prerequisites._packet_for_atomic_store_v5()
    if _derive_capability_commitment(packet.operational.candidate) != commitment:
        raise ValueError("Spot V7 V5 resolver returned the wrong prerequisites")
    return _ResolvedSpotV7AuthorityEntryV5(commitment, prerequisites)


__all__ = ()

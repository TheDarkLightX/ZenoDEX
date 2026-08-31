"""Owned row values and snapshot views for GlobalEconomicStateV2."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeVar, cast

from .global_settlement_types_v2 import (
    AssetSupplyV2,
    EconomicAmountV2,
    LaneIdV2,
    OracleOccurrenceStateV2,
    TerminalObligationV2,
    _require_bool_v2,
    _require_root_v2,
    _require_token_v2,
    _snapshot_dataclass_tuple_v2,
)

MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V2: Final = 65_536
MAX_GLOBAL_SUPPLY_ROWS_V2: Final = 4_096
MAX_GLOBAL_ORACLE_ROWS_V2: Final = 4_096
MAX_GLOBAL_REPLAY_ROWS_V2: Final = 65_536
MAX_GLOBAL_TERMINAL_ROWS_V2: Final = 65_536
MAX_GLOBAL_OUTBOX_ROWS_V2: Final = 65_536

_T = TypeVar("_T")


@dataclass(frozen=True, slots=True, order=True)
class LaneStateRootV2:
    lane_id: LaneIdV2
    module_release_id: str
    enabled: bool
    state_root: str

    def __post_init__(self) -> None:
        if type(self.lane_id) is not LaneIdV2:
            raise TypeError("lane state root lane is not closed")
        _require_root_v2(
            self.module_release_id,
            name="lane state module release",
        )
        _require_bool_v2(self.enabled, name="lane state enabled")
        _require_root_v2(
            self.state_root,
            name="lane state root",
            allow_zero=True,
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "lane_id": self.lane_id,
            "module_release_id": self.module_release_id,
            "enabled": self.enabled,
            "state_root": self.state_root,
        }


@dataclass(frozen=True, slots=True, order=True)
class ReplayStateV2:
    replay_id: str
    occurrence_id: str

    def __post_init__(self) -> None:
        _require_token_v2(self.replay_id, name="replay id")
        _require_root_v2(self.occurrence_id, name="replay occurrence id")

    def to_canonical(self) -> dict[str, object]:
        return {
            "replay_id": self.replay_id,
            "occurrence_id": self.occurrence_id,
        }


class OutboxStatusV2(str, Enum):
    PENDING = "PENDING"
    ACKNOWLEDGED = "ACKNOWLEDGED"


@dataclass(frozen=True, slots=True, order=True)
class OutboxStateV2:
    effect_id: str
    destination_id: str
    payload_hash: str
    adapter_profile_root: str
    commit_id: str
    status: OutboxStatusV2

    def __post_init__(self) -> None:
        _require_root_v2(self.effect_id, name="outbox effect id")
        _require_token_v2(self.destination_id, name="outbox destination")
        if self.destination_id.startswith("zenoledger:"):
            raise ValueError("same-ledger movement must not enter the external outbox")
        _require_root_v2(self.payload_hash, name="outbox payload hash")
        _require_root_v2(
            self.adapter_profile_root,
            name="outbox adapter profile root",
        )
        _require_root_v2(self.commit_id, name="outbox commit id")
        if type(self.status) is not OutboxStatusV2:
            raise TypeError("outbox status is not closed")

    def to_canonical(self) -> dict[str, object]:
        return {
            "effect_id": self.effect_id,
            "destination_id": self.destination_id,
            "payload_hash": self.payload_hash,
            "adapter_profile_root": self.adapter_profile_root,
            "commit_id": self.commit_id,
            "status": self.status,
        }


def _bounded_tuple(
    values: object,
    expected_type: type[_T],
    name: str,
    maximum: int,
) -> tuple[_T, ...]:
    owned = _snapshot_dataclass_tuple_v2(values, expected_type, name)
    if len(owned) > maximum:
        raise ValueError(f"{name} exceeds the ABI V2 bounded shape")
    return cast(tuple[_T, ...], owned)


def _snapshot_owned_tuple(
    values: tuple[_T, ...],
    expected_type: type[_T],
    name: str,
) -> tuple[_T, ...]:
    return cast(
        tuple[_T, ...],
        _snapshot_dataclass_tuple_v2(values, expected_type, name),
    )


class _GlobalEconomicStateGraphViewV2:
    """Snapshot-returning public view over privately owned state tables."""

    __slots__ = ()

    @property
    def lane_roots(self) -> tuple[LaneStateRootV2, ...]:
        return _snapshot_owned_tuple(
            object.__getattribute__(self, "_lane_roots"),
            LaneStateRootV2,
            "global state lane roots",
        )

    @property
    def balances(self) -> tuple[EconomicAmountV2, ...]:
        return _snapshot_owned_tuple(
            object.__getattribute__(self, "_balances"),
            EconomicAmountV2,
            "global state balances",
        )

    @property
    def supplies(self) -> tuple[AssetSupplyV2, ...]:
        return _snapshot_owned_tuple(
            object.__getattribute__(self, "_supplies"),
            AssetSupplyV2,
            "global state supplies",
        )

    @property
    def custody(self) -> tuple[EconomicAmountV2, ...]:
        return _snapshot_owned_tuple(
            object.__getattribute__(self, "_custody"),
            EconomicAmountV2,
            "global state custody",
        )

    @property
    def liabilities(self) -> tuple[EconomicAmountV2, ...]:
        return _snapshot_owned_tuple(
            object.__getattribute__(self, "_liabilities"),
            EconomicAmountV2,
            "global state liabilities",
        )

    @property
    def reserves(self) -> tuple[EconomicAmountV2, ...]:
        return _snapshot_owned_tuple(
            object.__getattribute__(self, "_reserves"),
            EconomicAmountV2,
            "global state reserves",
        )

    @property
    def oracle_occurrences(self) -> tuple[OracleOccurrenceStateV2, ...]:
        return _snapshot_owned_tuple(
            object.__getattribute__(self, "_oracle_occurrences"),
            OracleOccurrenceStateV2,
            "global state Oracle occurrences",
        )

    @property
    def replay_state(self) -> tuple[ReplayStateV2, ...]:
        return _snapshot_owned_tuple(
            object.__getattribute__(self, "_replay_state"),
            ReplayStateV2,
            "global state replay state",
        )

    @property
    def terminal_obligations(self) -> tuple[TerminalObligationV2, ...]:
        return _snapshot_owned_tuple(
            object.__getattribute__(self, "_terminal_obligations"),
            TerminalObligationV2,
            "global state terminal obligations",
        )

    @property
    def outbox(self) -> tuple[OutboxStateV2, ...]:
        return _snapshot_owned_tuple(
            object.__getattribute__(self, "_outbox"),
            OutboxStateV2,
            "global state outbox",
        )


def snapshot_global_lifecycle_rows_v2(
    rows: tuple[_T, ...],
    expected_type: type[_T],
    name: str,
    maximum: int,
) -> tuple[_T, ...]:
    """Own lifecycle derivation inputs before indexing or comparison."""

    return _bounded_tuple(rows, expected_type, name, maximum)


__all__ = [
    "MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V2",
    "MAX_GLOBAL_SUPPLY_ROWS_V2",
    "MAX_GLOBAL_ORACLE_ROWS_V2",
    "MAX_GLOBAL_REPLAY_ROWS_V2",
    "MAX_GLOBAL_TERMINAL_ROWS_V2",
    "MAX_GLOBAL_OUTBOX_ROWS_V2",
    "LaneStateRootV2",
    "ReplayStateV2",
    "OutboxStatusV2",
    "OutboxStateV2",
    "snapshot_global_lifecycle_rows_v2",
]

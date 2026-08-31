"""Owned authoritative state values for GlobalSettlementABI V2.

The objects in this module are immutable canonical inputs to global
state/effect refinement.  They carry no verifier, publisher, settlement, or
value-moving authority.  ``custody`` and ``custody_domain`` are ABI field
names for protocol accounting locations; they make no legal custody claim.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeVar, cast

from .global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    GLOBAL_SETTLEMENT_ABI_V2,
    MAX_ATOMS_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    LaneIdV2,
    OracleOccurrenceStateV2,
    TerminalObligationV2,
    _require_bool_v2,
    _require_nonnegative_int_v2,
    _require_ordered_objects_v2,
    _require_root_v2,
    _require_token_v2,
    _snapshot_dataclass_tuple_v2,
    hash_global_v2,
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


def _require_sparse_amount_rows(
    rows: tuple[EconomicAmountV2, ...],
    *,
    name: str,
) -> None:
    if any(row.amount_atoms == 0 for row in rows):
        raise ValueError(f"{name} must contain only nonzero sparse rows")


def _sum_amounts_by_asset(
    tables: tuple[tuple[EconomicAmountV2, ...], ...],
    *,
    name: str,
) -> dict[str, int]:
    totals: dict[str, int] = {}
    for table in tables:
        for row in table:
            total = totals.get(row.asset, 0) + row.amount_atoms
            if total > MAX_ATOMS_V2:
                raise ValueError(f"{name} total exceeds unsigned 128-bit bounds")
            totals[row.asset] = total
    return totals


@dataclass(frozen=True, slots=True)
class GlobalEconomicStateV2:
    chain_id: str
    deployment_root: str
    writer_epoch: int
    height: int
    profile_root: str
    lane_roots: tuple[LaneStateRootV2, ...]
    balances: tuple[EconomicAmountV2, ...] = ()
    supplies: tuple[AssetSupplyV2, ...] = ()
    custody: tuple[EconomicAmountV2, ...] = ()
    liabilities: tuple[EconomicAmountV2, ...] = ()
    reserves: tuple[EconomicAmountV2, ...] = ()
    oracle_occurrences: tuple[OracleOccurrenceStateV2, ...] = ()
    replay_state: tuple[ReplayStateV2, ...] = ()
    terminal_obligations: tuple[TerminalObligationV2, ...] = ()
    history_root: str = ZERO_ROOT_V2
    outbox: tuple[OutboxStateV2, ...] = ()

    def __post_init__(self) -> None:
        _require_token_v2(self.chain_id, name="global state chain id")
        _require_root_v2(self.deployment_root, name="global state deployment root")
        _require_nonnegative_int_v2(self.writer_epoch, name="global state writer epoch")
        _require_nonnegative_int_v2(self.height, name="global state height")
        _require_root_v2(self.profile_root, name="global state profile root")
        self._own_lane_roots()
        self._own_economic_tables()
        self._own_control_tables()
        _require_root_v2(
            self.history_root,
            name="global state history root",
            allow_zero=True,
        )

    def _own_lane_roots(self) -> None:
        owned = _bounded_tuple(
            self.lane_roots,
            LaneStateRootV2,
            "global state lane roots",
            len(ALL_LANE_IDS_V2),
        )
        if tuple(row.lane_id for row in owned) != ALL_LANE_IDS_V2:
            raise ValueError("global state must commit every ABI V2 lane in canonical order")
        object.__setattr__(self, "lane_roots", owned)

    def _own_economic_tables(self) -> None:
        for field_name in ("balances", "custody", "liabilities", "reserves"):
            owned = _bounded_tuple(
                getattr(self, field_name),
                EconomicAmountV2,
                f"global state {field_name}",
                MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V2,
            )
            _require_ordered_objects_v2(
                owned,
                name=f"global state {field_name}",
                expected_type=EconomicAmountV2,
                key="key",
            )
            _require_sparse_amount_rows(owned, name=f"global state {field_name}")
            object.__setattr__(self, field_name, owned)
        supplies = _bounded_tuple(
            self.supplies,
            AssetSupplyV2,
            "global state supplies",
            MAX_GLOBAL_SUPPLY_ROWS_V2,
        )
        _require_ordered_objects_v2(
            supplies,
            name="global state supplies",
            expected_type=AssetSupplyV2,
            key="asset",
        )
        if any(row.amount_atoms == 0 for row in supplies):
            raise ValueError("global state supplies must contain only nonzero sparse rows")
        object.__setattr__(self, "supplies", supplies)

    def _own_control_tables(self) -> None:
        specifications = (
            (
                "oracle_occurrences",
                OracleOccurrenceStateV2,
                "oracle_id",
                MAX_GLOBAL_ORACLE_ROWS_V2,
            ),
            ("replay_state", ReplayStateV2, "replay_id", MAX_GLOBAL_REPLAY_ROWS_V2),
            (
                "terminal_obligations",
                TerminalObligationV2,
                "obligation_id",
                MAX_GLOBAL_TERMINAL_ROWS_V2,
            ),
            ("outbox", OutboxStateV2, "effect_id", MAX_GLOBAL_OUTBOX_ROWS_V2),
        )
        for field_name, expected_type, key, maximum in specifications:
            owned = _bounded_tuple(
                getattr(self, field_name),
                expected_type,
                f"global state {field_name}",
                maximum,
            )
            _require_ordered_objects_v2(
                owned,
                name=f"global state {field_name}",
                expected_type=expected_type,
                key=key,
            )
            object.__setattr__(self, field_name, owned)
        occurrence_ids = tuple(row.occurrence_id for row in self.replay_state)
        if len(occurrence_ids) != len(set(occurrence_ids)):
            raise ValueError("global state replay occurrence ids must be unique")

    @property
    def state_root(self) -> str:
        return hash_global_v2("global-economic-state-root-v2", self.to_canonical())

    def owned_atoms_by_asset(self) -> dict[str, int]:
        return _sum_amounts_by_asset(
            (self.balances, self.custody, self.reserves),
            name="global owned accounting",
        )

    def liability_atoms_by_asset(self) -> dict[str, int]:
        return _sum_amounts_by_asset(
            (self.liabilities,),
            name="global liability",
        )

    def supply_atoms_by_asset(self) -> dict[str, int]:
        return {row.asset: row.amount_atoms for row in self.supplies}

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V2,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "writer_epoch": self.writer_epoch,
            "height": self.height,
            "profile_root": self.profile_root,
            "lane_roots": self.lane_roots,
            "balances": self.balances,
            "supplies": self.supplies,
            "custody": self.custody,
            "liabilities": self.liabilities,
            "reserves": self.reserves,
            "oracle_occurrences": self.oracle_occurrences,
            "replay_state": self.replay_state,
            "terminal_obligations": self.terminal_obligations,
            "history_root": self.history_root,
            "outbox": self.outbox,
        }


@dataclass(frozen=True, slots=True)
class GlobalEconomicStateRootV2:
    root: str
    profile_root: str
    writer_epoch: int
    height: int

    def __post_init__(self) -> None:
        _require_root_v2(self.root, name="global economic state root")
        _require_root_v2(self.profile_root, name="global economic profile root")
        _require_nonnegative_int_v2(
            self.writer_epoch,
            name="global economic writer epoch",
        )
        _require_nonnegative_int_v2(self.height, name="global economic height")

    @classmethod
    def from_state(cls, state: GlobalEconomicStateV2) -> GlobalEconomicStateRootV2:
        if cls is not GlobalEconomicStateRootV2:
            raise TypeError("state root factory requires the exact V2 type")
        owned = snapshot_global_economic_state_v2(state)
        return cls(
            root=owned.state_root,
            profile_root=owned.profile_root,
            writer_epoch=owned.writer_epoch,
            height=owned.height,
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "root": self.root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "height": self.height,
        }


def snapshot_global_economic_state_v2(
    state: GlobalEconomicStateV2,
) -> GlobalEconomicStateV2:
    if type(state) is not GlobalEconomicStateV2:
        raise TypeError("global economic state snapshot requires the exact V2 type")
    return GlobalEconomicStateV2(
        chain_id=state.chain_id,
        deployment_root=state.deployment_root,
        writer_epoch=state.writer_epoch,
        height=state.height,
        profile_root=state.profile_root,
        lane_roots=state.lane_roots,
        balances=state.balances,
        supplies=state.supplies,
        custody=state.custody,
        liabilities=state.liabilities,
        reserves=state.reserves,
        oracle_occurrences=state.oracle_occurrences,
        replay_state=state.replay_state,
        terminal_obligations=state.terminal_obligations,
        history_root=state.history_root,
        outbox=state.outbox,
    )


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
    "GlobalEconomicStateV2",
    "GlobalEconomicStateRootV2",
    "snapshot_global_economic_state_v2",
]

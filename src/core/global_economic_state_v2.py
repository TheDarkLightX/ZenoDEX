"""Owned authoritative state values for GlobalSettlementABI V2.

The objects in this module are immutable canonical inputs to global
state/effect refinement.  They carry no verifier, publisher, settlement, or
value-moving authority.  ``custody`` and ``custody_domain`` are ABI field
names for protocol accounting locations; they make no legal custody claim.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass, field

from .global_economic_state_ownership_v2 import (
    MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V2,
    MAX_GLOBAL_ORACLE_ROWS_V2,
    MAX_GLOBAL_OUTBOX_ROWS_V2,
    MAX_GLOBAL_REPLAY_ROWS_V2,
    MAX_GLOBAL_SUPPLY_ROWS_V2,
    MAX_GLOBAL_TERMINAL_ROWS_V2,
    LaneStateRootV2,
    OutboxStateV2,
    OutboxStatusV2,
    ReplayStateV2,
    _bounded_tuple,
    _GlobalEconomicStateGraphViewV2,
)
from .global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    GLOBAL_SETTLEMENT_ABI_V2,
    MAX_ATOMS_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    OracleOccurrenceStateV2,
    TerminalObligationV2,
    _require_nonnegative_int_v2,
    _require_ordered_objects_v2,
    _require_root_v2,
    _require_token_v2,
    hash_global_v2,
)


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


@dataclass(frozen=True, slots=True, init=False)
class GlobalEconomicStateV2(_GlobalEconomicStateGraphViewV2):
    chain_id: str
    deployment_root: str
    writer_epoch: int
    height: int
    profile_root: str
    lane_roots: InitVar[tuple[LaneStateRootV2, ...]] = (
        _GlobalEconomicStateGraphViewV2.lane_roots
    )
    balances: InitVar[tuple[EconomicAmountV2, ...]] = (
        _GlobalEconomicStateGraphViewV2.balances
    )
    supplies: InitVar[tuple[AssetSupplyV2, ...]] = (
        _GlobalEconomicStateGraphViewV2.supplies
    )
    custody: InitVar[tuple[EconomicAmountV2, ...]] = (
        _GlobalEconomicStateGraphViewV2.custody
    )
    liabilities: InitVar[tuple[EconomicAmountV2, ...]] = (
        _GlobalEconomicStateGraphViewV2.liabilities
    )
    reserves: InitVar[tuple[EconomicAmountV2, ...]] = (
        _GlobalEconomicStateGraphViewV2.reserves
    )
    oracle_occurrences: InitVar[tuple[OracleOccurrenceStateV2, ...]] = (
        _GlobalEconomicStateGraphViewV2.oracle_occurrences
    )
    replay_state: InitVar[tuple[ReplayStateV2, ...]] = (
        _GlobalEconomicStateGraphViewV2.replay_state
    )
    terminal_obligations: InitVar[tuple[TerminalObligationV2, ...]] = (
        _GlobalEconomicStateGraphViewV2.terminal_obligations
    )
    outbox: InitVar[tuple[OutboxStateV2, ...]] = (
        _GlobalEconomicStateGraphViewV2.outbox
    )
    history_root: str = ZERO_ROOT_V2
    _lane_roots: tuple[LaneStateRootV2, ...] = field(init=False, repr=False)
    _balances: tuple[EconomicAmountV2, ...] = field(init=False, repr=False)
    _supplies: tuple[AssetSupplyV2, ...] = field(init=False, repr=False)
    _custody: tuple[EconomicAmountV2, ...] = field(init=False, repr=False)
    _liabilities: tuple[EconomicAmountV2, ...] = field(init=False, repr=False)
    _reserves: tuple[EconomicAmountV2, ...] = field(init=False, repr=False)
    _oracle_occurrences: tuple[OracleOccurrenceStateV2, ...] = field(
        init=False,
        repr=False,
    )
    _replay_state: tuple[ReplayStateV2, ...] = field(init=False, repr=False)
    _terminal_obligations: tuple[TerminalObligationV2, ...] = field(
        init=False,
        repr=False,
    )
    _outbox: tuple[OutboxStateV2, ...] = field(init=False, repr=False)

    def __init__(
        self,
        chain_id: str,
        deployment_root: str,
        writer_epoch: int,
        height: int,
        profile_root: str,
        lane_roots: tuple[LaneStateRootV2, ...],
        balances: tuple[EconomicAmountV2, ...] = (),
        supplies: tuple[AssetSupplyV2, ...] = (),
        custody: tuple[EconomicAmountV2, ...] = (),
        liabilities: tuple[EconomicAmountV2, ...] = (),
        reserves: tuple[EconomicAmountV2, ...] = (),
        oracle_occurrences: tuple[OracleOccurrenceStateV2, ...] = (),
        replay_state: tuple[ReplayStateV2, ...] = (),
        terminal_obligations: tuple[TerminalObligationV2, ...] = (),
        history_root: str = ZERO_ROOT_V2,
        outbox: tuple[OutboxStateV2, ...] = (),
    ) -> None:
        object.__setattr__(self, "chain_id", chain_id)
        object.__setattr__(self, "deployment_root", deployment_root)
        object.__setattr__(self, "writer_epoch", writer_epoch)
        object.__setattr__(self, "height", height)
        object.__setattr__(self, "profile_root", profile_root)
        object.__setattr__(self, "history_root", history_root)
        object.__setattr__(self, "_lane_roots", lane_roots)
        object.__setattr__(self, "_balances", balances)
        object.__setattr__(self, "_supplies", supplies)
        object.__setattr__(self, "_custody", custody)
        object.__setattr__(self, "_liabilities", liabilities)
        object.__setattr__(self, "_reserves", reserves)
        object.__setattr__(self, "_oracle_occurrences", oracle_occurrences)
        object.__setattr__(self, "_replay_state", replay_state)
        object.__setattr__(self, "_terminal_obligations", terminal_obligations)
        object.__setattr__(self, "_outbox", outbox)
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
            object.__getattribute__(self, "_lane_roots"),
            LaneStateRootV2,
            "global state lane roots",
            len(ALL_LANE_IDS_V2),
        )
        if tuple(row.lane_id for row in owned) != ALL_LANE_IDS_V2:
            raise ValueError("global state must commit every ABI V2 lane in canonical order")
        object.__setattr__(self, "_lane_roots", owned)

    def _own_economic_tables(self) -> None:
        for field_name in ("balances", "custody", "liabilities", "reserves"):
            owned = _bounded_tuple(
                object.__getattribute__(self, f"_{field_name}"),
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
            object.__setattr__(self, f"_{field_name}", owned)
        supplies = _bounded_tuple(
            object.__getattribute__(self, "_supplies"),
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
        object.__setattr__(self, "_supplies", supplies)

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
                object.__getattribute__(self, f"_{field_name}"),
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
            object.__setattr__(self, f"_{field_name}", owned)
        replay_state = object.__getattribute__(self, "_replay_state")
        occurrence_ids = tuple(row.occurrence_id for row in replay_state)
        if len(occurrence_ids) != len(set(occurrence_ids)):
            raise ValueError("global state replay occurrence ids must be unique")
        oracle_occurrences = object.__getattribute__(self, "_oracle_occurrences")
        if any(row.observed_height > self.height for row in oracle_occurrences):
            raise ValueError("Oracle observed height exceeds global state height")

    @property
    def state_root(self) -> str:
        return hash_global_v2("global-economic-state-root-v2", self.to_canonical())

    def owned_atoms_by_asset(self) -> dict[str, int]:
        return _sum_amounts_by_asset(
            (
                object.__getattribute__(self, "_balances"),
                object.__getattribute__(self, "_custody"),
                object.__getattribute__(self, "_reserves"),
            ),
            name="global owned accounting",
        )

    def liability_atoms_by_asset(self) -> dict[str, int]:
        return _sum_amounts_by_asset(
            (object.__getattribute__(self, "_liabilities"),),
            name="global liability",
        )

    def supply_atoms_by_asset(self) -> dict[str, int]:
        supplies = object.__getattribute__(self, "_supplies")
        return {row.asset: row.amount_atoms for row in supplies}

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

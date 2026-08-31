"""Bounded, transitively owned economic effect plans for GlobalSettlementABI V2."""

from __future__ import annotations

from dataclasses import dataclass
from typing import ClassVar, Final

from .global_settlement_effect_values_v2 import (
    AssetConservationRowV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    ExternalOutboxEnqueueV2,
    FeeConservationRowV2,
    LaneWriteV2,
)
from .global_settlement_ownership_v2 import (
    _DataclassTupleSnapshotPropertyV2,
    _SortedTokenTupleSnapshotPropertyV2,
)
from .global_settlement_primitives_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    _require_ordered_objects_v2,
    _require_root_v2,
    _require_sorted_unique_tokens_v2,
    canonical_global_bytes_v2,
    hash_global_v2,
)

# Each collection ceiling is independent. Aggregate-item and canonical-byte
# ceilings can impose a smaller feasible maximum on a concrete combination.
MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2: Final = 4_096
MAX_ASSET_CONSERVATION_ROWS_PER_PLAN_V2: Final = 256
MAX_FEE_CONSERVATION_ROWS_PER_PLAN_V2: Final = 256
MAX_LANE_WRITES_PER_PLAN_V2: Final = 12
MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2: Final = 64
MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2: Final = 4_096
MAX_ECONOMIC_EFFECT_PLAN_ITEMS_V2: Final = 8_192
MAX_ECONOMIC_EFFECT_PLAN_CANONICAL_BYTES_V2: Final = 1_048_576


def _require_economic_effect_plan_item_bounds_v2(
    *,
    rows: int,
    asset_conservation: int,
    fee_conservation: int,
    lane_writes: int,
    occurrence_consumptions: int,
    external_outbox_enqueue: int,
) -> None:
    counts_and_limits = (
        ("rows", rows, MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2),
        (
            "asset conservation",
            asset_conservation,
            MAX_ASSET_CONSERVATION_ROWS_PER_PLAN_V2,
        ),
        ("fee conservation", fee_conservation, MAX_FEE_CONSERVATION_ROWS_PER_PLAN_V2),
        ("lane writes", lane_writes, MAX_LANE_WRITES_PER_PLAN_V2),
        (
            "occurrence consumptions",
            occurrence_consumptions,
            MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2,
        ),
        (
            "external outbox enqueue",
            external_outbox_enqueue,
            MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2,
        ),
    )
    for name, count, limit in counts_and_limits:
        if type(count) is not int or count < 0:
            raise ValueError(f"effect plan {name} count must be a non-negative integer")
        if count > limit:
            raise ValueError(f"effect plan {name} exceeds its {limit}-item ceiling")
    if sum(count for _, count, _ in counts_and_limits) > MAX_ECONOMIC_EFFECT_PLAN_ITEMS_V2:
        raise ValueError(
            "effect plan total items exceeds its "
            f"{MAX_ECONOMIC_EFFECT_PLAN_ITEMS_V2}-item ceiling"
        )


@dataclass(frozen=True)
class GlobalEconomicEffectPlanV2:
    __slots__ = (
        "_rows",
        "_asset_conservation",
        "_fee_conservation",
        "_lane_writes",
        "_occurrence_consumptions",
        "_external_outbox_enqueue",
    )

    _rows: ClassVar[tuple[EconomicEffectRowV2, ...]]
    _asset_conservation: ClassVar[tuple[AssetConservationRowV2, ...]]
    _fee_conservation: ClassVar[tuple[FeeConservationRowV2, ...]]
    _lane_writes: ClassVar[tuple[LaneWriteV2, ...]]
    _occurrence_consumptions: ClassVar[tuple[str, ...]]
    _external_outbox_enqueue: ClassVar[tuple[ExternalOutboxEnqueueV2, ...]]

    rows: tuple[EconomicEffectRowV2, ...] = (
        _DataclassTupleSnapshotPropertyV2(  # type: ignore[assignment]
            "_rows",
            EconomicEffectRowV2,
            "effect plan rows",
            item_ceiling=MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2,
        )
    )
    asset_conservation: tuple[AssetConservationRowV2, ...] = (
        _DataclassTupleSnapshotPropertyV2(  # type: ignore[assignment]
            "_asset_conservation",
            AssetConservationRowV2,
            "effect plan asset_conservation",
            item_ceiling=MAX_ASSET_CONSERVATION_ROWS_PER_PLAN_V2,
        )
    )
    fee_conservation: tuple[FeeConservationRowV2, ...] = (
        _DataclassTupleSnapshotPropertyV2(  # type: ignore[assignment]
            "_fee_conservation",
            FeeConservationRowV2,
            "effect plan fee_conservation",
            item_ceiling=MAX_FEE_CONSERVATION_ROWS_PER_PLAN_V2,
        )
    )
    lane_writes: tuple[LaneWriteV2, ...] = (
        _DataclassTupleSnapshotPropertyV2(  # type: ignore[assignment]
            "_lane_writes",
            LaneWriteV2,
            "effect plan lane_writes",
            item_ceiling=MAX_LANE_WRITES_PER_PLAN_V2,
        )
    )
    occurrence_consumptions: tuple[str, ...] = (
        _SortedTokenTupleSnapshotPropertyV2(  # type: ignore[assignment]
            "_occurrence_consumptions",
            "effect plan occurrence consumptions",
            MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2,
        )
    )
    external_outbox_enqueue: tuple[ExternalOutboxEnqueueV2, ...] = (
        _DataclassTupleSnapshotPropertyV2(  # type: ignore[assignment]
            "_external_outbox_enqueue",
            ExternalOutboxEnqueueV2,
            "effect plan external_outbox_enqueue",
            item_ceiling=MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2,
        )
    )

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_economic_effect_plan_item_bounds_v2(
            rows=len(self._rows),
            asset_conservation=len(self._asset_conservation),
            fee_conservation=len(self._fee_conservation),
            lane_writes=len(self._lane_writes),
            occurrence_consumptions=len(self._occurrence_consumptions),
            external_outbox_enqueue=len(self._external_outbox_enqueue),
        )
        _require_ordered_objects_v2(
            self._rows,
            name="effect plan rows",
            expected_type=EconomicEffectRowV2,
            key="key",
        )
        _require_ordered_objects_v2(
            self._asset_conservation,
            name="effect plan asset conservation",
            expected_type=AssetConservationRowV2,
            key="asset",
        )
        _require_ordered_objects_v2(
            self._fee_conservation,
            name="effect plan fee conservation",
            expected_type=FeeConservationRowV2,
            key="asset",
        )
        _require_ordered_objects_v2(
            self._lane_writes,
            name="effect plan lane writes",
            expected_type=LaneWriteV2,
            key="lane_id",
        )
        consumptions = _require_sorted_unique_tokens_v2(
            self._occurrence_consumptions,
            name="effect plan occurrence consumptions",
        )
        for index, occurrence_id in enumerate(consumptions):
            _require_root_v2(
                occurrence_id,
                name=f"effect plan occurrence consumption[{index}]",
            )
        _require_ordered_objects_v2(
            self._external_outbox_enqueue,
            name="effect plan external outbox",
            expected_type=ExternalOutboxEnqueueV2,
            key="effect_id",
        )
        self._validate_issue_burn_projection()
        self._validate_fee_projection()
        if (
            len(canonical_global_bytes_v2(self.to_canonical()))
            > MAX_ECONOMIC_EFFECT_PLAN_CANONICAL_BYTES_V2
        ):
            raise ValueError(
                "effect plan canonical encoding exceeds its "
                f"{MAX_ECONOMIC_EFFECT_PLAN_CANONICAL_BYTES_V2}-byte ceiling"
            )

    def _validate_issue_burn_projection(self) -> None:
        issue_by_asset: dict[str, int] = {}
        burn_by_asset: dict[str, int] = {}
        for row in self._rows:
            if row.kind is EconomicEffectKindV2.ISSUE:
                issue_by_asset[row.asset] = issue_by_asset.get(row.asset, 0) + row.delta_atoms
            elif row.kind is EconomicEffectKindV2.BURN:
                burn_by_asset[row.asset] = burn_by_asset.get(row.asset, 0) - row.delta_atoms
        conservation_assets = {row.asset for row in self._asset_conservation}
        effect_assets = set(issue_by_asset) | set(burn_by_asset)
        if not effect_assets.issubset(conservation_assets):
            raise ValueError("issue or burn effect lacks an asset conservation row")
        for conservation_row in self._asset_conservation:
            if conservation_row.authorized_issue_atoms != issue_by_asset.get(
                conservation_row.asset,
                0,
            ):
                raise ValueError("authorized issue does not match canonical effect rows")
            if conservation_row.authorized_burn_atoms != burn_by_asset.get(
                conservation_row.asset,
                0,
            ):
                raise ValueError("authorized burn does not match canonical effect rows")

    def _validate_fee_projection(self) -> None:
        allocations: dict[str, int] = {}
        for row in self._rows:
            if row.kind is EconomicEffectKindV2.FEE_ALLOCATION:
                if row.delta_atoms < 0:
                    raise ValueError("fee allocation effect must be positive")
                allocations[row.asset] = allocations.get(row.asset, 0) + row.delta_atoms
        for fee_row in self._fee_conservation:
            if fee_row.current_allocations_atoms != allocations.get(fee_row.asset, 0):
                raise ValueError("fee conservation does not match canonical allocation effects")
        if not set(allocations).issubset(
            {row.asset for row in self._fee_conservation}
        ):
            raise ValueError("fee allocation effect lacks a fee conservation row")

    @property
    def effect_plan_root(self) -> str:
        self.validate()
        return hash_global_v2("global-economic-effect-plan-v2", self.to_canonical())

    @property
    def is_empty(self) -> bool:
        return not (
            self._rows
            or self._asset_conservation
            or self._fee_conservation
            or self._lane_writes
            or self._occurrence_consumptions
            or self._external_outbox_enqueue
        )

    @classmethod
    def empty(cls) -> GlobalEconomicEffectPlanV2:
        if cls is not GlobalEconomicEffectPlanV2:
            raise TypeError("effect plan factory requires the exact declared type")
        return cls((), (), (), (), (), ())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V2,
            "rows": self.rows,
            "asset_conservation": self.asset_conservation,
            "fee_conservation": self.fee_conservation,
            "lane_writes": self.lane_writes,
            "occurrence_consumptions": self.occurrence_consumptions,
            "external_outbox_enqueue": self.external_outbox_enqueue,
        }


__all__ = [
    "MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2",
    "MAX_ASSET_CONSERVATION_ROWS_PER_PLAN_V2",
    "MAX_FEE_CONSERVATION_ROWS_PER_PLAN_V2",
    "MAX_LANE_WRITES_PER_PLAN_V2",
    "MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2",
    "MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2",
    "MAX_ECONOMIC_EFFECT_PLAN_ITEMS_V2",
    "MAX_ECONOMIC_EFFECT_PLAN_CANONICAL_BYTES_V2",
    "GlobalEconomicEffectPlanV2",
]

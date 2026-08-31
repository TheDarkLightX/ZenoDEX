from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_types_v2 import (
    MAX_ASSET_CONSERVATION_ROWS_PER_PLAN_V2,
    MAX_ECONOMIC_EFFECT_PLAN_CANONICAL_BYTES_V2,
    MAX_ECONOMIC_EFFECT_PLAN_ITEMS_V2,
    MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2,
    MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2,
    MAX_FEE_CONSERVATION_ROWS_PER_PLAN_V2,
    MAX_LANE_WRITES_PER_PLAN_V2,
    MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    ExternalOutboxEnqueueV2,
    GlobalEconomicEffectPlanV2,
    _require_economic_effect_plan_item_bounds_v2,
    canonical_global_bytes_v2,
)

_EFFECT_PLAN_COUNT_LIMITS = (
    ("rows", MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2, "rows"),
    (
        "asset_conservation",
        MAX_ASSET_CONSERVATION_ROWS_PER_PLAN_V2,
        "asset conservation",
    ),
    (
        "fee_conservation",
        MAX_FEE_CONSERVATION_ROWS_PER_PLAN_V2,
        "fee conservation",
    ),
    ("lane_writes", MAX_LANE_WRITES_PER_PLAN_V2, "lane writes"),
    (
        "occurrence_consumptions",
        MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2,
        "occurrence consumptions",
    ),
    (
        "external_outbox_enqueue",
        MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2,
        "external outbox enqueue",
    ),
)


def _require_effect_plan_counts(counts: dict[str, int]) -> None:
    _require_economic_effect_plan_item_bounds_v2(
        rows=counts["rows"],
        asset_conservation=counts["asset_conservation"],
        fee_conservation=counts["fee_conservation"],
        lane_writes=counts["lane_writes"],
        occurrence_consumptions=counts["occurrence_consumptions"],
        external_outbox_enqueue=counts["external_outbox_enqueue"],
    )


@pytest.mark.parametrize(("field_name", "limit", "error_name"), _EFFECT_PLAN_COUNT_LIMITS)
def test_effect_plan_collection_bounds_accept_limit_and_reject_next(
    field_name: str,
    limit: int,
    error_name: str,
) -> None:
    counts = {name: 0 for name, _, _ in _EFFECT_PLAN_COUNT_LIMITS}
    counts[field_name] = limit

    _require_effect_plan_counts(counts)

    counts[field_name] = limit + 1
    with pytest.raises(ValueError, match=rf"{error_name} exceeds.*{limit}-item"):
        _require_effect_plan_counts(counts)


def test_effect_plan_aggregate_bound_accepts_8192_and_rejects_8193_items() -> None:
    # Isolate the count guard here. A constructed plan must independently fit
    # canonical ordering, uniqueness, and the one-MiB byte ceiling.
    counts = {name: 0 for name, _, _ in _EFFECT_PLAN_COUNT_LIMITS}
    counts["rows"] = MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2
    counts["external_outbox_enqueue"] = MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2

    assert sum(counts.values()) == MAX_ECONOMIC_EFFECT_PLAN_ITEMS_V2
    _require_effect_plan_counts(counts)

    counts["asset_conservation"] = 1
    with pytest.raises(ValueError, match=r"total items exceeds.*8192-item"):
        _require_effect_plan_counts(counts)


def test_effect_plan_runtime_enforces_the_row_count_ceiling() -> None:
    rows = tuple(
        EconomicEffectRowV2(
            kind=EconomicEffectKindV2.ACCOUNT_MOVEMENT,
            principal=f"p{index:04d}",
            asset="A",
            custody_domain="c",
            delta_atoms=1,
        )
        for index in range(MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2)
    )

    accepted = GlobalEconomicEffectPlanV2(rows, (), (), (), (), ())
    assert len(accepted.rows) == MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2

    with pytest.raises(ValueError, match=r"rows exceeds.*4096-item"):
        GlobalEconomicEffectPlanV2((*rows, rows[-1]), (), (), (), (), ())


def test_effect_plan_canonical_byte_ceiling_accepts_limit_and_rejects_next() -> None:
    def root(index: int) -> str:
        return f"0x{index:064x}"

    base_rows = tuple(
        ExternalOutboxEnqueueV2(
            effect_id=root(index + 1),
            destination_id="d",
            payload_hash=root(5_000),
            adapter_profile_root=root(5_001),
        )
        for index in range(3_000)
    )
    base = GlobalEconomicEffectPlanV2((), (), (), (), (), base_rows)
    extra_bytes = MAX_ECONOMIC_EFFECT_PLAN_CANONICAL_BYTES_V2 - len(
        canonical_global_bytes_v2(base.to_canonical())
    )
    assert 0 <= extra_bytes <= 159 * len(base_rows)

    padded_rows: list[ExternalOutboxEnqueueV2] = []
    remaining = extra_bytes
    for row in base_rows:
        padding = min(remaining, 159)
        padded_rows.append(replace(row, destination_id="d" + ("x" * padding)))
        remaining -= padding
    assert remaining == 0

    exact = GlobalEconomicEffectPlanV2((), (), (), (), (), tuple(padded_rows))
    assert (
        len(canonical_global_bytes_v2(exact.to_canonical()))
        == MAX_ECONOMIC_EFFECT_PLAN_CANONICAL_BYTES_V2
    )

    overflow_rows = list(exact.external_outbox_enqueue)
    expandable_index = next(
        index
        for index in range(len(overflow_rows) - 1, -1, -1)
        if len(overflow_rows[index].destination_id) < 160
    )
    overflow_rows[expandable_index] = replace(
        overflow_rows[expandable_index],
        destination_id=overflow_rows[expandable_index].destination_id + "x",
    )
    with pytest.raises(ValueError, match=r"canonical encoding exceeds.*1048576-byte"):
        GlobalEconomicEffectPlanV2((), (), (), (), (), tuple(overflow_rows))

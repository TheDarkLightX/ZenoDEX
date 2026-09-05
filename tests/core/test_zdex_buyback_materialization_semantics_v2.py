"""Bounded semantic evidence for SHADOW buyback effect materialization."""

from __future__ import annotations

from dataclasses import asdict

import pytest

from src.core.global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    ZERO_ROOT_V1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    ExternalOutboxEnqueueV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
    ProfileStatusV1,
)
from src.core.zdex_atomic_buyback_lane_coordinator_v2 import (
    _materialize_fee_allocations_v2,
    _materialize_spot_custody_v2,
)
from src.core.zdex_atomic_buyback_route_composition_v2 import (
    ZDEXAtomicBuybackRouteAcceptedV2,
    _compose_effects_v2,
    compose_zdex_atomic_buyback_route_shadow_v2,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    PROTOCOL_BURN_CUSTODY_DOMAIN_V1,
    PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1,
    ZDEX_SUPPLY_PRINCIPAL_V1,
    zdex_pool_reserve_principal_v1,
)
from tests.core.test_zdex_atomic_buyback_route_composition_v2 import (
    _verified_route_candidate,
)

_OCCURRENCE = "0x" + "01" * 32


def _row(
    kind: EconomicEffectKindV1,
    principal: str,
    asset: str,
    domain: str,
    delta_atoms: int,
) -> EconomicEffectRowV1:
    return EconomicEffectRowV1(kind, principal, asset, domain, delta_atoms)


def _plan(
    rows: tuple[EconomicEffectRowV1, ...],
    *,
    fees: tuple[FeeConservationRowV1, ...] = (),
    lane: LaneIdV1 | None = None,
    occurrence: tuple[str, ...] = (),
    outbox: tuple[ExternalOutboxEnqueueV1, ...] = (),
) -> GlobalEconomicEffectPlanV1:
    writes = () if lane is None else (LaneWriteV1(lane, ZERO_ROOT_V1, ZERO_ROOT_V1),)
    return GlobalEconomicEffectPlanV1(
        tuple(sorted(rows, key=lambda row: row.key)), (), fees, writes, occurrence, outbox
    )


def _plans_snapshot(*plans: GlobalEconomicEffectPlanV1) -> tuple[dict[str, object], ...]:
    return tuple(asdict(plan) for plan in plans)


def _reference_rows(
    rows: tuple[EconomicEffectRowV1, ...], *, fee_mirrors: bool = False, custody_only: bool = False
) -> tuple[EconomicEffectRowV1, ...]:
    totals: dict[tuple[str, str, str, str], int] = {}
    fields: dict[tuple[str, str, str, str], tuple[EconomicEffectKindV1, str, str, str]] = {}
    for row in rows:
        additions = ((row.kind, row.principal, row.asset, row.custody_domain, row.delta_atoms),)
        if custody_only:
            additions = ((EconomicEffectKindV1.CUSTODY, *additions[0][1:]),)
        elif fee_mirrors and row.kind is EconomicEffectKindV1.FEE_ALLOCATION:
            additions += ((EconomicEffectKindV1.CUSTODY, *additions[0][1:]),)
        for kind, principal, asset, domain, delta_atoms in additions:
            key = (kind.value, asset, principal, domain)
            totals[key] = totals.get(key, 0) + delta_atoms
            fields[key] = (kind, principal, asset, domain)
    return tuple(
        EconomicEffectRowV1(*fields[key], delta_atoms)
        for key, delta_atoms in sorted(totals.items())
        if delta_atoms
    )


def _compose_pair(
    spot_rows: tuple[EconomicEffectRowV1, ...],
    tokenomics_rows: tuple[EconomicEffectRowV1, ...],
) -> GlobalEconomicEffectPlanV1:
    return _compose_effects_v2(
        _plan(spot_rows, lane=LaneIdV1.SPOT_LIQUIDITY),
        _plan(tokenomics_rows, lane=LaneIdV1.ZDEX_TOKENOMICS, occurrence=(_OCCURRENCE,)),
    )


def test_fee_materialization_keeps_full_effect_key_and_elides_zero__guards_partial_key_merge() -> None:
    effects = _plan(
        (
            _row(EconomicEffectKindV1.FEE_ALLOCATION, "same-owner", "asset-fee", "domain-a", 5),
            _row(EconomicEffectKindV1.FEE_ALLOCATION, "other-owner", "asset-fee", "domain-a", 2),
            _row(EconomicEffectKindV1.CUSTODY, "same-owner", "asset-fee", "domain-a", -5),
            _row(EconomicEffectKindV1.LIABILITY, "same-owner", "asset-fee", "domain-a", 7),
            _row(EconomicEffectKindV1.FEE_ALLOCATION, "same-owner", "asset-mirror", "domain-a", 2),
            _row(EconomicEffectKindV1.CUSTODY, "same-owner", "asset-fee", "domain-b", 3),
            _row(EconomicEffectKindV1.CUSTODY, "same-owner", "asset-other", "domain-a", 4),
        ),
        fees=(FeeConservationRowV1("asset-fee", 7, 7, 0), FeeConservationRowV1("asset-mirror", 2, 2, 0)),
    )

    before = _plans_snapshot(effects)
    actual = _materialize_fee_allocations_v2(effects)

    assert _plans_snapshot(effects) == before
    assert actual.rows == _reference_rows(effects.rows, fee_mirrors=True)
    values = {(row.kind, row.principal, row.asset, row.custody_domain): row.delta_atoms for row in actual.rows}
    assert values[(EconomicEffectKindV1.FEE_ALLOCATION, "same-owner", "asset-fee", "domain-a")] == 5
    assert values[(EconomicEffectKindV1.FEE_ALLOCATION, "other-owner", "asset-fee", "domain-a")] == 2
    assert values[(EconomicEffectKindV1.CUSTODY, "same-owner", "asset-mirror", "domain-a")] == 2
    assert values[(EconomicEffectKindV1.CUSTODY, "other-owner", "asset-fee", "domain-a")] == 2
    assert values[(EconomicEffectKindV1.LIABILITY, "same-owner", "asset-fee", "domain-a")] == 7
    assert (EconomicEffectKindV1.CUSTODY, "same-owner", "asset-fee", "domain-a") not in values


def test_spot_materialization_changes_only_kind__guards_account_movement_leak() -> None:
    effects = _plan(
        (
            _row(EconomicEffectKindV1.ACCOUNT_MOVEMENT, "pool-owner", "asset-a", AMM_POOL_CUSTODY_DOMAIN_V1, -9),
            _row(EconomicEffectKindV1.ACCOUNT_MOVEMENT, "pool-owner", "asset-b", AMM_POOL_CUSTODY_DOMAIN_V1, 9),
        )
    )

    before = _plans_snapshot(effects)
    actual = _materialize_spot_custody_v2(effects)

    assert _plans_snapshot(effects) == before
    assert actual.rows == _reference_rows(effects.rows, custody_only=True)
    assert all(row.kind is EconomicEffectKindV1.CUSTODY for row in actual.rows)


def test_spot_materialization_rejects_wrong_count_kind_or_domain__guards_shape_check() -> None:
    malformed = (
        _plan((_row(EconomicEffectKindV1.ACCOUNT_MOVEMENT, "owner", "asset-a", AMM_POOL_CUSTODY_DOMAIN_V1, 1),)),
        _plan((_row(EconomicEffectKindV1.CUSTODY, "owner", "asset-a", AMM_POOL_CUSTODY_DOMAIN_V1, 1), _row(EconomicEffectKindV1.ACCOUNT_MOVEMENT, "owner", "asset-b", AMM_POOL_CUSTODY_DOMAIN_V1, -1))),
        _plan((_row(EconomicEffectKindV1.ACCOUNT_MOVEMENT, "owner", "asset-a", "other-domain", 1), _row(EconomicEffectKindV1.ACCOUNT_MOVEMENT, "owner", "asset-b", "other-domain", -1))),
    )

    for effects in malformed:
        before = _plans_snapshot(effects)
        with pytest.raises(ValueError, match="unexpected shape"):
            _materialize_spot_custody_v2(effects)
        assert _plans_snapshot(effects) == before


def test_composition_nets_permutations_with_complete_rows_and_route_controls__guards_partial_key_fold() -> None:
    plus = _row(EconomicEffectKindV1.CUSTODY, "same-owner", "asset-a", "domain-a", 5)
    minus = _row(EconomicEffectKindV1.CUSTODY, "same-owner", "asset-a", "domain-a", -5)
    domain = _row(EconomicEffectKindV1.CUSTODY, "same-owner", "asset-a", "domain-b", 3)
    asset = _row(EconomicEffectKindV1.CUSTODY, "same-owner", "asset-b", "domain-a", 4)
    liability = _row(EconomicEffectKindV1.LIABILITY, "same-owner", "asset-a", "domain-a", 7)
    other_principal = _row(EconomicEffectKindV1.CUSTODY, "other-owner", "asset-a", "domain-a", -5)

    first = _compose_pair((plus, domain), (minus, asset, liability, other_principal))
    second = _compose_pair((minus, domain), (plus, asset, liability, other_principal))

    expected = _reference_rows((plus, domain, minus, asset, liability, other_principal))
    assert first.rows == second.rows == expected
    assert other_principal in first.rows
    assert tuple(row.key for row in first.rows) == tuple(sorted(row.key for row in first.rows))
    assert first.occurrence_consumptions == (_OCCURRENCE,)
    assert tuple(write.lane_id for write in first.lane_writes) == (LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS)
    assert first.external_outbox_enqueue == ()


def test_composition_rejects_invalid_occurrence_lane_and_outbox_controls__guards_control_placement() -> None:
    tokenomics = _plan((), lane=LaneIdV1.ZDEX_TOKENOMICS, occurrence=(_OCCURRENCE,))
    outbox = ExternalOutboxEnqueueV1(_OCCURRENCE, "adapter:remote", "0x" + "02" * 32, "0x" + "03" * 32)
    cases = (
        (_plan((), lane=LaneIdV1.SPOT_LIQUIDITY, occurrence=(_OCCURRENCE,)), "must consume one occurrence once"),
        (_plan((), lane=LaneIdV1.ZDEX_TOKENOMICS), "lane writes are incomplete"),
        (_plan((), lane=LaneIdV1.SPOT_LIQUIDITY, outbox=(outbox,)), "forbids external effects"),
    )
    for spot, message in cases:
        before = _plans_snapshot(spot, tokenomics)
        with pytest.raises(ValueError, match=message):
            _compose_effects_v2(spot, tokenomics)
        assert _plans_snapshot(spot, tokenomics) == before


@pytest.mark.parametrize(
    ("first", "second", "expected"),
    ((MAX_DELTA_ATOMS_V1 - 1, 1, MAX_DELTA_ATOMS_V1), (MIN_DELTA_ATOMS_V1 + 1, -1, MIN_DELTA_ATOMS_V1)),
)
def test_composition_accepts_signed_i128_bound_neighbors__guards_strict_bound_reject(
    first: int, second: int, expected: int
) -> None:
    result = _compose_pair(
        (_row(EconomicEffectKindV1.CUSTODY, "owner", "asset", "domain", first),),
        (_row(EconomicEffectKindV1.CUSTODY, "owner", "asset", "domain", second),),
    )

    assert result.rows == (_row(EconomicEffectKindV1.CUSTODY, "owner", "asset", "domain", expected),)


def test_checked_i128_prefix_overflow_rejects_before_final_effect_plan__guards_checked_accumulation() -> None:
    tokenomics = _plan(
        (
            _row(EconomicEffectKindV1.CUSTODY, "owner", "asset", "domain", 1),
            _row(EconomicEffectKindV1.FEE_ALLOCATION, "owner", "asset", "domain", MAX_DELTA_ATOMS_V1),
        ),
        fees=(FeeConservationRowV1("asset", MAX_DELTA_ATOMS_V1, MAX_DELTA_ATOMS_V1, 0),),
        lane=LaneIdV1.ZDEX_TOKENOMICS,
        occurrence=(_OCCURRENCE,),
    )
    later_spot = _plan((_row(EconomicEffectKindV1.CUSTODY, "owner", "asset", "domain", -1),), lane=LaneIdV1.SPOT_LIQUIDITY)
    before = _plans_snapshot(tokenomics, later_spot)
    reference = _reference_rows((*tokenomics.rows, *later_spot.rows), fee_mirrors=True)

    assert tuple(row for row in reference if row.kind is EconomicEffectKindV1.CUSTODY) == (
        _row(EconomicEffectKindV1.CUSTODY, "owner", "asset", "domain", MAX_DELTA_ATOMS_V1),
    )
    with pytest.raises(ValueError, match="exceeds signed i128"):
        _materialize_fee_allocations_v2(tokenomics)
    assert _plans_snapshot(tokenomics, later_spot) == before
    for first, second in ((MAX_DELTA_ATOMS_V1, 1), (MIN_DELTA_ATOMS_V1, -1)):
        with pytest.raises(ValueError, match="aggregate exceeds signed i128"):
            _compose_pair(
                (_row(EconomicEffectKindV1.CUSTODY, "owner", "asset", "domain", first),),
                (_row(EconomicEffectKindV1.CUSTODY, "owner", "asset", "domain", second),),
            )


def test_shadow_route_materializes_exact_pool_debit_supply_burn_and_no_burn_port_holding__guards_burn_port_custody() -> None:
    fixture, candidate = _verified_route_candidate()
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)

    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2
    assert fixture.profile.status is ProfileStatusV1.SHADOW
    zdex_asset = fixture.tokenomics.journal.zdex_asset_id
    pool = zdex_pool_reserve_principal_v1(pool_id=fixture.tokenomics.journal.selected_pool_id, asset_id=zdex_asset)
    values = {(row.kind, row.principal, row.asset, row.custody_domain): row.delta_atoms for row in result.effects.rows}
    assert values[(EconomicEffectKindV1.CUSTODY, pool, zdex_asset, AMM_POOL_CUSTODY_DOMAIN_V1)] == -fixture.spot.journal.purchased_zdex_atoms
    assert values[(EconomicEffectKindV1.BURN, ZDEX_SUPPLY_PRINCIPAL_V1, zdex_asset, PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1)] == -fixture.tokenomics.journal.burned_zdex_atoms
    assert result.effects.occurrence_consumptions == (fixture.occurrence.occurrence_id,)
    assert not any(row.custody_domain == PROTOCOL_BURN_CUSTODY_DOMAIN_V1 for row in result.post_state.custody)

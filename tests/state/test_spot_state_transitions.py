from __future__ import annotations

from itertools import permutations
from typing import cast

from src.core.batch_clearing import apply_settlement_pure
from src.core.cpmm import MIN_LP_LOCK, compute_lp_mint
from src.core.settlement import BalanceDelta, LPDelta, ReserveDelta, Settlement
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.owned_collections import OwnedMapV1
from src.state.pool_creation_transition import PoolCreationV1
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.snapshot_combinators import MAX_CANONICAL_BYTES_V1
from src.state.spot_state_transitions import (
    SpotDeltaBatchV1,
    SpotTransitionOkV1,
    apply_spot_deltas_v1,
)
from src.state.state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedLPTableV1,
    CommittedPoolStateV1,
)
from src.state.state_snapshots import snapshot_balance_table, snapshot_lp_table, snapshot_pool_map
from src.state.state_transitions import (
    BalanceDeltaV1,
    LPPositionDeltaV1,
    PoolPatchCodeV1,
    PoolPatchRejectV1,
    PoolReserveDeltaV1,
)

LP_LOCK_PUBKEY = "0x" + "00" * 48


def _empty_spot() -> tuple[
    CommittedBalanceTableV1,
    OwnedMapV1[str, CommittedPoolStateV1],
    CommittedLPTableV1,
]:
    return (
        snapshot_balance_table(BalanceTable()),
        snapshot_pool_map({}),
        snapshot_lp_table(LPTable()),
    )


def test_spot_creation_matches_legacy_apply_and_derives_pool_supply_from_lp() -> None:
    creator = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    amount0 = 4_000
    amount1 = 9_000
    fee_bps = 30
    created_at = 7
    pool_id = compute_pool_id(asset0, asset1, fee_bps)
    lp_minted = compute_lp_mint(amount0, amount1, amount0, amount1, 0)

    legacy_balances = BalanceTable()
    legacy_balances.set(creator, asset0, amount0 + 5)
    legacy_balances.set(creator, asset1, amount1 + 7)
    pre_balances = snapshot_balance_table(legacy_balances)
    pre_pools = snapshot_pool_map({})
    pre_lp = snapshot_lp_table(LPTable())

    result = apply_spot_deltas_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        SpotDeltaBatchV1(
            balance_deltas=(
                BalanceDeltaV1((creator, asset0), -amount0),
                BalanceDeltaV1((creator, asset1), -amount1),
            ),
            reserve_deltas=(
                PoolReserveDeltaV1(pool_id, asset0, amount0),
                PoolReserveDeltaV1(pool_id, asset1, amount1),
            ),
            lp_deltas=(
                LPPositionDeltaV1((creator, pool_id), lp_minted),
                LPPositionDeltaV1((LP_LOCK_PUBKEY, pool_id), MIN_LP_LOCK),
            ),
            pool_creations=(
                PoolCreationV1(
                    pool_id=pool_id,
                    asset0=asset0,
                    asset1=asset1,
                    fee_bps=fee_bps,
                    created_at=created_at,
                    curve_tag="CPMM",
                    curve_params="",
                ),
            ),
        ),
    )

    assert type(result) is SpotTransitionOkV1
    assert result.balance_patch is not None
    assert result.pool_patch is not None
    assert result.lp_patch is not None
    assert result.pools[pool_id].lp_supply == lp_minted + MIN_LP_LOCK

    settlement = Settlement(
        module="TauSwap",
        version="1",
        batch_ref="batch",
        included_intents=[],
        fills=[],
        balance_deltas=[
            BalanceDelta(creator, asset0, delta_add=0, delta_sub=amount0),
            BalanceDelta(creator, asset1, delta_add=0, delta_sub=amount1),
        ],
        reserve_deltas=[
            ReserveDelta(pool_id, asset0, delta_add=amount0, delta_sub=0),
            ReserveDelta(pool_id, asset1, delta_add=amount1, delta_sub=0),
        ],
        lp_deltas=[
            LPDelta(creator, pool_id, delta_add=lp_minted, delta_sub=0),
            LPDelta(LP_LOCK_PUBKEY, pool_id, delta_add=MIN_LP_LOCK, delta_sub=0),
        ],
        events=[
            {
                "type": "CREATE_POOL",
                "pool_id": pool_id,
                "asset0": asset0,
                "asset1": asset1,
                "fee_bps": fee_bps,
                "curve_tag": "CPMM",
                "curve_params": "",
                "status": PoolStatus.ACTIVE.value,
                "created_at": created_at,
            }
        ],
    )
    legacy_next = apply_settlement_pure(settlement, legacy_balances, {}, LPTable())

    assert result.balances.entries == snapshot_balance_table(legacy_next[0]).entries
    assert result.pools.entries == snapshot_pool_map(legacy_next[1]).entries
    assert result.lp_balances.balance_entries == snapshot_lp_table(legacy_next[2]).balance_entries


def test_spot_transition_is_permutation_invariant_across_each_unordered_delta_family() -> None:
    pool = PoolState(
        pool_id=compute_pool_id("asset-a", "asset-b", 30),
        asset0="asset-a",
        asset1="asset-b",
        reserve0=100,
        reserve1=200,
        fee_bps=30,
        lp_supply=10,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set("alice", "asset-a", 10)
    lp = LPTable()
    lp.set("alice", pool.pool_id, 10)
    pre = (
        snapshot_balance_table(balances),
        snapshot_pool_map({pool.pool_id: pool}),
        snapshot_lp_table(lp),
    )
    balance_deltas = (
        BalanceDeltaV1(("alice", "asset-a"), -3),
        BalanceDeltaV1(("alice", "asset-a"), 1),
    )
    reserve_deltas = (
        PoolReserveDeltaV1(pool.pool_id, "asset-a", 3),
        PoolReserveDeltaV1(pool.pool_id, "asset-a", -1),
    )
    lp_deltas = (
        LPPositionDeltaV1(("alice", pool.pool_id), 2),
        LPPositionDeltaV1(("alice", pool.pool_id), -1),
    )

    results = tuple(
        apply_spot_deltas_v1(
            *pre,
            SpotDeltaBatchV1(
                balance_deltas=balance_order,
                reserve_deltas=reserve_order,
                lp_deltas=lp_order,
                pool_creations=(),
            ),
        )
        for balance_order in permutations(balance_deltas)
        for reserve_order in permutations(reserve_deltas)
        for lp_order in permutations(lp_deltas)
    )

    assert all(type(result) is SpotTransitionOkV1 for result in results)
    candidates = tuple(cast(SpotTransitionOkV1, result) for result in results)
    assert len({candidate.balances.entries for candidate in candidates}) == 1
    assert len({candidate.pools.entries for candidate in candidates}) == 1
    assert len({candidate.lp_balances.balance_entries for candidate in candidates}) == 1
    assert candidates[0].pools[pool.pool_id].lp_supply == 11


def test_spot_transition_rejects_unknown_lp_pool_without_partial_candidate() -> None:
    pre_balances, pre_pools, pre_lp = _empty_spot()

    result = apply_spot_deltas_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        SpotDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(),
            lp_deltas=(LPPositionDeltaV1(("alice", "unknown-pool"), 1),),
            pool_creations=(),
        ),
    )

    assert result == PoolPatchRejectV1(
        PoolPatchCodeV1.UNKNOWN_POOL,
        ("pools", "unknown-pool"),
    )
    assert not hasattr(result, "balances")


def test_spot_transition_preflights_all_delta_representations_before_state_math() -> None:
    balances = BalanceTable()
    balances.set("alice", "asset-a", 1)
    reserve_delta = PoolReserveDeltaV1("unknown-pool", "asset-a", 1)
    deltas = SpotDeltaBatchV1(
        balance_deltas=(BalanceDeltaV1(("alice", "asset-a"), -2),),
        reserve_deltas=(reserve_delta,),
        lp_deltas=(),
        pool_creations=(),
    )
    object.__setattr__(reserve_delta, "net_delta", True)

    result = apply_spot_deltas_v1(
        snapshot_balance_table(balances),
        snapshot_pool_map({}),
        snapshot_lp_table(LPTable()),
        deltas,
    )

    assert result == PoolPatchRejectV1(
        PoolPatchCodeV1.WRONG_EXACT_TYPE,
        ("reserve_deltas", "net_delta"),
    )
    assert not hasattr(result, "balances")


def test_spot_transition_enforces_one_aggregate_work_byte_budget() -> None:
    balance_delta = BalanceDeltaV1(("alice", "asset-a"), 1)
    lp_delta = LPPositionDeltaV1(("alice", "pool-a"), 1)
    deltas = SpotDeltaBatchV1(
        balance_deltas=(balance_delta,),
        reserve_deltas=(),
        lp_deltas=(lp_delta,),
        pool_creations=(),
    )
    half_budget_integer = 1 << ((MAX_CANONICAL_BYTES_V1 // 2) * 8)
    object.__setattr__(balance_delta, "net_delta", half_budget_integer)
    object.__setattr__(lp_delta, "net_delta", half_budget_integer)

    result = apply_spot_deltas_v1(*_empty_spot(), deltas)

    assert result == PoolPatchRejectV1(
        PoolPatchCodeV1.BYTE_LIMIT,
        ("deltas",),
    )
    assert not hasattr(result, "balances")

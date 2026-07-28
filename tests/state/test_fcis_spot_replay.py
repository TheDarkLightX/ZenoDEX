"""Parity and adversarial tests for the direct-import-clean exact spot leaf."""

from __future__ import annotations

from typing import cast

from src.core.cpmm import MIN_LP_LOCK
from src.state import spot_state_transitions as compatibility_spot
from src.state.balances import BalanceTable
from src.state.fcis_spot_replay import (
    FCISSpotDeltaBatchV1,
    FCISSpotReplayDeltaBatchV1,
    FCISSpotReplayOkV1,
    FCISSpotTransitionOkV1,
    apply_fcis_spot_deltas_observed_v1,
    apply_fcis_spot_replay_observed_v1,
)
from src.state.lp import LPTable
from src.state.lp_duration_transitions import LPDurationEventV1
from src.state.owned_collections import OwnedMapV1
from src.state.pool_creation_transition import PoolCreationV1
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedLPTableV1,
    CommittedPoolStateV1,
)
from src.state.state_snapshots import snapshot_balance_table, snapshot_lp_table, snapshot_pool_map
from src.state.state_transitions import (
    BalanceDeltaV1,
    BalancePatchCodeV1,
    BalancePatchRejectV1,
    LPPositionDeltaV1,
    LPPositionPatchCodeV1,
    LPPositionPatchRejectV1,
    PoolPatchCodeV1,
    PoolPatchRejectV1,
    PoolReserveDeltaV1,
)


def _existing_spot() -> tuple[
    CommittedBalanceTableV1,
    OwnedMapV1[str, CommittedPoolStateV1],
    CommittedLPTableV1,
    str,
]:
    pool_id = compute_pool_id("asset-a", "asset-b", 30)
    pool = PoolState(
        pool_id=pool_id,
        asset0="asset-a",
        asset1="asset-b",
        reserve0=100,
        reserve1=200,
        fee_bps=30,
        lp_supply=5,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set("alice", "asset-a", 10)
    lp = LPTable()
    lp.set("alice", pool_id, 5)
    return (
        snapshot_balance_table(balances),
        snapshot_pool_map({pool_id: pool}),
        snapshot_lp_table(lp),
        pool_id,
    )


def test_exact_replay_matches_private_compatibility_result_and_reads() -> None:
    pre_balances, pre_pools, pre_lp, pool_id = _existing_spot()
    deltas = FCISSpotReplayDeltaBatchV1(
        balance_deltas=(BalanceDeltaV1(("alice", "asset-a"), -2),),
        reserve_deltas=(PoolReserveDeltaV1(pool_id, "asset-a", 2),),
        lp_deltas=(LPPositionDeltaV1(("alice", pool_id), 1),),
        pool_creations=(),
    )

    exact, exact_reads = apply_fcis_spot_replay_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        deltas,
    )
    compatibility, compatibility_reads = compatibility_spot._apply_spot_replay_deltas_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        deltas,
    )

    assert type(exact) is FCISSpotReplayOkV1
    assert type(compatibility).__name__ == "_SpotReplayOkV1"
    assert compatibility.balances == exact.balances
    assert compatibility.pools == exact.pools
    assert compatibility.lp_balances == exact.lp_balances
    assert compatibility_reads == exact_reads
    assert exact.balances.get("alice", "asset-a") == 8
    assert exact.pools[pool_id].reserve0 == 102
    assert exact.pools[pool_id].lp_supply == 6
    assert exact.lp_balances.get("alice", pool_id) == 6
    assert not hasattr(exact, "balance_patch")


def test_exact_replay_retains_balance_lp_and_pool_rejection_prefixes() -> None:
    pre_balances, pre_pools, pre_lp, pool_id = _existing_spot()
    balance_reject, balance_reads = apply_fcis_spot_replay_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        FCISSpotReplayDeltaBatchV1(
            balance_deltas=(BalanceDeltaV1(("alice", "asset-a"), -11),),
            reserve_deltas=(),
            lp_deltas=(),
            pool_creations=(),
        ),
    )
    assert balance_reject == BalancePatchRejectV1(
        BalancePatchCodeV1.OUT_OF_RANGE,
        ("deltas", "net_delta"),
    )
    assert balance_reads.balance_keys == (("alice", "asset-a"),)

    lp_reject, lp_reads = apply_fcis_spot_replay_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        FCISSpotReplayDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(),
            lp_deltas=(LPPositionDeltaV1(("alice", pool_id), -6),),
            pool_creations=(),
        ),
    )
    assert lp_reject == LPPositionPatchRejectV1(
        LPPositionPatchCodeV1.OUT_OF_RANGE,
        ("deltas", "net_delta"),
    )
    assert lp_reads.lp_keys == (("alice", pool_id),)

    pool_reject, pool_reads = apply_fcis_spot_replay_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        FCISSpotReplayDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(PoolReserveDeltaV1("missing", "asset-a", 1),),
            lp_deltas=(),
            pool_creations=(),
        ),
    )
    assert pool_reject == PoolPatchRejectV1(
        PoolPatchCodeV1.UNKNOWN_POOL,
        ("pools", "missing"),
    )
    assert pool_reads.pool_ids == ("missing",)


def test_exact_replay_pool_creation_derives_supply_from_lp_patch() -> None:
    pool_id = compute_pool_id("asset-a", "asset-b", 30)
    empty_balances = snapshot_balance_table(BalanceTable())
    empty_pools = snapshot_pool_map({})
    empty_lp = snapshot_lp_table(LPTable())
    result, reads = apply_fcis_spot_replay_observed_v1(
        empty_balances,
        empty_pools,
        empty_lp,
        FCISSpotReplayDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(
                PoolReserveDeltaV1(pool_id, "asset-a", 10),
                PoolReserveDeltaV1(pool_id, "asset-b", 20),
            ),
            lp_deltas=(LPPositionDeltaV1(("alice", pool_id), MIN_LP_LOCK),),
            pool_creations=(
                PoolCreationV1(
                    pool_id=pool_id,
                    asset0="asset-a",
                    asset1="asset-b",
                    fee_bps=30,
                    created_at=0,
                    curve_tag="CPMM",
                    curve_params="",
                ),
            ),
        ),
    )

    assert type(result) is FCISSpotReplayOkV1
    assert result.pools[pool_id].reserve0 == 10
    assert result.pools[pool_id].reserve1 == 20
    assert result.pools[pool_id].lp_supply == MIN_LP_LOCK
    assert result.lp_balances.get("alice", pool_id) == MIN_LP_LOCK
    assert reads.pool_ids == (pool_id,)
    assert reads.lp_keys == (("alice", pool_id),)


def test_exact_aggregate_matches_compatibility_candidate_and_patches() -> None:
    pre_balances, pre_pools, pre_lp, pool_id = _existing_spot()
    deltas = FCISSpotDeltaBatchV1(
        balance_deltas=(BalanceDeltaV1(("alice", "asset-a"), -2),),
        reserve_deltas=(PoolReserveDeltaV1(pool_id, "asset-a", 2),),
        lp_events=(LPDurationEventV1(("alice", pool_id), 1, 0),),
        pool_creations=(),
    )

    exact = apply_fcis_spot_deltas_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        deltas,
        now=10,
        min_age_seconds=0,
        policy=None,
    )
    compatibility = compatibility_spot.apply_spot_deltas_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        deltas,
        now=10,
        min_age_seconds=0,
        policy=None,
    )

    assert exact == compatibility
    candidate, reads = exact
    assert type(candidate) is FCISSpotTransitionOkV1
    assert candidate.balance_patch is not None
    assert candidate.pool_patch is not None
    assert candidate.lp_patch is not None
    assert candidate.pools[pool_id].lp_supply == 6
    assert reads.balance_keys == (("alice", "asset-a"),)
    assert reads.pool_ids == (pool_id,)
    assert reads.lp_keys == (("alice", pool_id),)


def test_exact_replay_rejects_hostile_nested_delta_mutation_before_reads() -> None:
    pre_balances, pre_pools, pre_lp, pool_id = _existing_spot()
    reserve_delta = PoolReserveDeltaV1(pool_id, "asset-a", 1)
    deltas = FCISSpotReplayDeltaBatchV1(
        balance_deltas=(),
        reserve_deltas=(reserve_delta,),
        lp_deltas=(),
        pool_creations=(),
    )
    object.__setattr__(reserve_delta, "net_delta", True)

    result, reads = apply_fcis_spot_replay_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        deltas,
    )

    assert result == PoolPatchRejectV1(
        PoolPatchCodeV1.WRONG_EXACT_TYPE,
        ("reserve_deltas", "net_delta"),
    )
    assert reads.balance_keys == ()
    assert reads.pool_ids == ()
    assert reads.lp_keys == ()


def test_exact_replay_rejects_hostile_nested_prestate_mutation() -> None:
    pre_balances, pre_pools, pre_lp, pool_id = _existing_spot()
    pool = pre_pools[pool_id]
    assert type(pool) is CommittedPoolStateV1
    object.__setattr__(pool, "reserve0", -1)

    result, reads = apply_fcis_spot_replay_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        FCISSpotReplayDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(),
            lp_deltas=(),
            pool_creations=(),
        ),
    )

    assert type(result) is PoolPatchRejectV1
    exact_reject = cast(PoolPatchRejectV1, result)
    assert exact_reject.code is PoolPatchCodeV1.INVALID_PRESTATE
    assert reads.balance_keys == ()
    assert reads.pool_ids == ()
    assert reads.lp_keys == ()


def test_exact_replay_batch_requires_exact_tuple_families() -> None:
    deltas = FCISSpotReplayDeltaBatchV1(
        balance_deltas=(),
        reserve_deltas=(),
        lp_deltas=(),
        pool_creations=(),
    )
    object.__setattr__(deltas, "balance_deltas", [])

    result, reads = apply_fcis_spot_replay_observed_v1(
        snapshot_balance_table(BalanceTable()),
        snapshot_pool_map({}),
        snapshot_lp_table(LPTable()),
        deltas,
    )

    assert result == BalancePatchRejectV1(
        BalancePatchCodeV1.WRONG_EXACT_TYPE,
        ("deltas",),
    )
    assert reads.balance_keys == ()
    assert reads.pool_ids == ()
    assert reads.lp_keys == ()

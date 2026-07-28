from __future__ import annotations

import sys
from itertools import permutations
from typing import cast

import pytest

from src.core.batch_clearing import apply_settlement_pure
from src.core.cpmm import MIN_LP_LOCK, compute_lp_mint
from src.core.fcis_state_read_trace_v5 import FCISStateReadTraceV5
from src.core.fcis_traced_reads_v5 import apply_spot_deltas_traced_v5
from src.core.settlement import BalanceDelta, LPDelta, ReserveDelta, Settlement
from src.state.balances import BalanceTable
from src.state.fcis_spot_replay import apply_fcis_spot_deltas_v1
from src.state.lp import LPTable
from src.state.lp_duration_transitions import (
    LPDurationEventV1,
    LPDurationRiskPolicyV1,
    LPDurationTransitionCodeV1,
    LPDurationTransitionOkV1,
    LPDurationTransitionRejectV1,
)
from src.state.owned_collections import OwnedMapV1
from src.state.pool_creation_transition import PoolCreationV1
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.snapshot_combinators import MAX_CANONICAL_BYTES_V1
from src.state.spot_state_transitions import (
    SpotDeltaBatchV1,
    SpotStateReadSetV1,
    SpotTransitionOkV1,
    apply_spot_deltas_observed_v1,
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


def _existing_lp_spot(
    *,
    last_mint_timestamp: int,
) -> tuple[
    CommittedBalanceTableV1,
    OwnedMapV1[str, CommittedPoolStateV1],
    CommittedLPTableV1,
    str,
]:
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
    lp = LPTable()
    lp.set("alice", pool.pool_id, 10)
    lp.set_last_mint_timestamp("alice", pool.pool_id, last_mint_timestamp)
    return (
        snapshot_balance_table(BalanceTable()),
        snapshot_pool_map({pool.pool_id: pool}),
        snapshot_lp_table(lp),
        pool.pool_id,
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
            lp_events=(
                LPDurationEventV1((LP_LOCK_PUBKEY, pool_id), MIN_LP_LOCK, 0),
                LPDurationEventV1((creator, pool_id), lp_minted, 0),
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
        now=created_at,
        min_age_seconds=0,
        policy=None,
    )

    assert type(result) is SpotTransitionOkV1
    assert result.balance_patch is not None
    assert result.pool_patch is not None
    assert result.lp_patch is not None
    assert result.pools[pool_id].lp_supply == lp_minted + MIN_LP_LOCK
    assert result.lp_balances.get_last_mint_timestamp(creator, pool_id) == created_at
    assert result.lp_balances.get_last_mint_timestamp(LP_LOCK_PUBKEY, pool_id) == created_at

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


def test_spot_observed_reads_are_exact_on_accept_and_rejection() -> None:
    pre_balances, pre_pools, pre_lp, pool_id = _existing_lp_spot(
        last_mint_timestamp=10,
    )
    deltas = SpotDeltaBatchV1(
        balance_deltas=(),
        reserve_deltas=(),
        lp_events=(LPDurationEventV1(("alice", pool_id), 0, 1),),
        pool_creations=(),
    )

    accepted, accepted_reads = apply_spot_deltas_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        deltas,
        now=20,
        min_age_seconds=10,
        policy=None,
    )
    rejected, rejected_reads = apply_spot_deltas_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        deltas,
        now=20,
        min_age_seconds=11,
        policy=None,
    )

    assert type(accepted) is SpotTransitionOkV1
    assert accepted_reads == SpotStateReadSetV1(
        pool_ids=(pool_id,),
        lp_keys=(("alice", pool_id),),
    )
    assert rejected == LPDurationTransitionRejectV1(
        LPDurationTransitionCodeV1.POSITION_LOCKED,
        ("events", 0, "last_mint_timestamp"),
    )
    assert rejected_reads == SpotStateReadSetV1(
        lp_keys=(("alice", pool_id),),
    )


def test_v5_traced_spot_rejections_preserve_balance_pool_and_lp_reads() -> None:
    empty_balances, empty_pools, empty_lp = _empty_spot()
    balance_reject, balance_trace = apply_spot_deltas_traced_v5(
        pre_balances=empty_balances,
        pre_pools=empty_pools,
        pre_lp_balances=empty_lp,
        deltas=SpotDeltaBatchV1(
            balance_deltas=(BalanceDeltaV1(("alice", "asset-a"), -1),),
            reserve_deltas=(),
            lp_events=(),
            pool_creations=(),
        ),
        now=0,
        min_age_seconds=0,
        policy=None,
        trace=FCISStateReadTraceV5(),
    )
    assert type(balance_reject) is not SpotTransitionOkV1
    assert balance_trace.balance_keys == (("alice", "asset-a"),)

    pool_reject, pool_trace = apply_spot_deltas_traced_v5(
        pre_balances=empty_balances,
        pre_pools=empty_pools,
        pre_lp_balances=empty_lp,
        deltas=SpotDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(PoolReserveDeltaV1("missing-pool", "asset-a", 1),),
            lp_events=(),
            pool_creations=(),
        ),
        now=0,
        min_age_seconds=0,
        policy=None,
        trace=FCISStateReadTraceV5(),
    )
    assert type(pool_reject) is not SpotTransitionOkV1
    assert pool_trace.pool_ids == ("missing-pool",)

    pre_balances, pre_pools, pre_lp, pool_id = _existing_lp_spot(last_mint_timestamp=10)
    lp_reject, lp_trace = apply_spot_deltas_traced_v5(
        pre_balances=pre_balances,
        pre_pools=pre_pools,
        pre_lp_balances=pre_lp,
        deltas=SpotDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(),
            lp_events=(LPDurationEventV1(("alice", pool_id), 0, 1),),
            pool_creations=(),
        ),
        now=20,
        min_age_seconds=11,
        policy=None,
        trace=FCISStateReadTraceV5(),
    )
    assert type(lp_reject) is not SpotTransitionOkV1
    assert lp_trace.lp_keys == (("alice", pool_id),)


def test_private_replay_observed_result_retains_each_rejecting_leaf_read() -> None:
    spot_module = sys.modules[apply_spot_deltas_v1.__module__]
    empty_balances, empty_pools, empty_lp = _empty_spot()

    balance_reject, balance_reads = spot_module._apply_spot_replay_deltas_observed_v1(
        empty_balances,
        empty_pools,
        empty_lp,
        spot_module._SpotReplayDeltaBatchV1(
            balance_deltas=(BalanceDeltaV1(("alice", "asset-a"), -1),),
            reserve_deltas=(),
            lp_deltas=(),
            pool_creations=(),
        ),
    )
    assert type(balance_reject).__name__ != "_SpotReplayOkV1"
    assert balance_reads == SpotStateReadSetV1(
        balance_keys=(("alice", "asset-a"),),
    )

    lp_reject, lp_reads = spot_module._apply_spot_replay_deltas_observed_v1(
        empty_balances,
        empty_pools,
        empty_lp,
        spot_module._SpotReplayDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(),
            lp_deltas=(LPPositionDeltaV1(("alice", "missing-pool"), -1),),
            pool_creations=(),
        ),
    )
    assert type(lp_reject).__name__ != "_SpotReplayOkV1"
    assert lp_reads == SpotStateReadSetV1(
        lp_keys=(("alice", "missing-pool"),),
    )

    pool_reject, pool_reads = spot_module._apply_spot_replay_deltas_observed_v1(
        empty_balances,
        empty_pools,
        empty_lp,
        spot_module._SpotReplayDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(PoolReserveDeltaV1("missing-pool", "asset-a", 1),),
            lp_deltas=(),
            pool_creations=(),
        ),
    )
    assert type(pool_reject).__name__ != "_SpotReplayOkV1"
    assert pool_reads == SpotStateReadSetV1(pool_ids=("missing-pool",))


def test_spot_transition_is_permutation_invariant_across_unordered_net_delta_families() -> None:
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
    lp_events = (LPDurationEventV1(("alice", pool.pool_id), 2, 1),)

    results = tuple(
        apply_spot_deltas_v1(
            *pre,
            SpotDeltaBatchV1(
                balance_deltas=balance_order,
                reserve_deltas=reserve_order,
                lp_events=lp_events,
                pool_creations=(),
            ),
            now=50,
            min_age_seconds=0,
            policy=None,
        )
        for balance_order in permutations(balance_deltas)
        for reserve_order in permutations(reserve_deltas)
    )

    assert all(type(result) is SpotTransitionOkV1 for result in results)
    candidates = tuple(cast(SpotTransitionOkV1, result) for result in results)
    assert len({candidate.balances.entries for candidate in candidates}) == 1
    assert len({candidate.pools.entries for candidate in candidates}) == 1
    assert len({candidate.lp_balances.balance_entries for candidate in candidates}) == 1
    assert candidates[0].pools[pool.pool_id].lp_supply == 11


def test_balance_only_replay_helper_cannot_emit_the_public_authority_candidate() -> None:
    spot_module = sys.modules[apply_spot_deltas_v1.__module__]

    assert "_apply_spot_replay_deltas_v1" not in spot_module.__all__
    assert "_SpotReplayDeltaBatchV1" not in spot_module.__all__
    replay_result = spot_module._apply_spot_replay_deltas_v1(
        *_empty_spot(),
        spot_module._SpotReplayDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(),
            lp_deltas=(),
            pool_creations=(),
        ),
    )

    assert type(replay_result).__name__ == "_SpotReplayOkV1"
    assert type(replay_result) is not SpotTransitionOkV1
    assert not hasattr(replay_result, "balance_patch")


def test_spot_transition_carries_the_single_guarded_lp_candidate_without_recomputation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pre_balances, pre_pools, pre_lp, pool_id = _existing_lp_spot(
        last_mint_timestamp=10,
    )
    event = LPDurationEventV1(("alice", pool_id), 0, 1)
    guarded_results: list[LPDurationTransitionOkV1] = []
    exact_spot_module = sys.modules[apply_fcis_spot_deltas_v1.__module__]
    real_guard = exact_spot_module.apply_guarded_lp_position_events_observed_v1

    def counted_guard(*args: object, **kwargs: object) -> object:
        guarded, observed_keys = real_guard(*args, **kwargs)
        assert type(guarded) is LPDurationTransitionOkV1
        guarded_results.append(guarded)
        return guarded, observed_keys

    monkeypatch.setattr(
        exact_spot_module,
        "apply_guarded_lp_position_events_observed_v1",
        counted_guard,
    )

    result = apply_spot_deltas_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        SpotDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(),
            lp_events=(event,),
            pool_creations=(),
        ),
        now=20,
        min_age_seconds=10,
        policy=None,
    )

    assert type(result) is SpotTransitionOkV1
    assert len(guarded_results) == 1
    assert result.lp_balances is guarded_results[0].state
    assert result.lp_patch is guarded_results[0].patch
    assert result.pools[pool_id].lp_supply == 9


def test_spot_transition_age_rejection_exposes_no_partial_candidate() -> None:
    pre_balances, pre_pools, pre_lp, pool_id = _existing_lp_spot(
        last_mint_timestamp=90,
    )

    result = apply_spot_deltas_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        SpotDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(),
            lp_events=(LPDurationEventV1(("alice", pool_id), 0, 1),),
            pool_creations=(),
        ),
        now=100,
        min_age_seconds=11,
        policy=None,
    )

    assert result == LPDurationTransitionRejectV1(
        LPDurationTransitionCodeV1.POSITION_LOCKED,
        ("events", 0, "last_mint_timestamp"),
    )
    assert not hasattr(result, "balances")
    assert pre_lp.get("alice", pool_id) == 10
    assert pre_pools[pool_id].lp_supply == 10


def test_spot_transition_preserves_add_sub_to_reject_same_batch_churn() -> None:
    pre_balances, pre_pools, pre_lp, pool_id = _existing_lp_spot(
        last_mint_timestamp=10,
    )

    result = apply_spot_deltas_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        SpotDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(),
            lp_events=(LPDurationEventV1(("alice", pool_id), 1, 1),),
            pool_creations=(),
        ),
        now=20,
        min_age_seconds=0,
        policy=LPDurationRiskPolicyV1(
            base_age_seconds=1,
            churn_window_seconds=100,
        ),
    )

    assert result == LPDurationTransitionRejectV1(
        LPDurationTransitionCodeV1.SAME_BATCH_ADD_REMOVE,
        ("events", 0),
    )
    assert not hasattr(result, "lp_balances")


def test_spot_transition_rejects_unknown_lp_pool_without_partial_candidate() -> None:
    pre_balances, pre_pools, pre_lp = _empty_spot()

    result = apply_spot_deltas_v1(
        pre_balances,
        pre_pools,
        pre_lp,
        SpotDeltaBatchV1(
            balance_deltas=(),
            reserve_deltas=(),
            lp_events=(LPDurationEventV1(("alice", "unknown-pool"), 1, 0),),
            pool_creations=(),
        ),
        now=0,
        min_age_seconds=0,
        policy=None,
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
        lp_events=(),
        pool_creations=(),
    )
    object.__setattr__(reserve_delta, "net_delta", True)

    result = apply_spot_deltas_v1(
        snapshot_balance_table(balances),
        snapshot_pool_map({}),
        snapshot_lp_table(LPTable()),
        deltas,
        now=0,
        min_age_seconds=0,
        policy=None,
    )

    assert result == PoolPatchRejectV1(
        PoolPatchCodeV1.WRONG_EXACT_TYPE,
        ("reserve_deltas", "net_delta"),
    )
    assert not hasattr(result, "balances")


def test_spot_transition_enforces_one_aggregate_work_byte_budget() -> None:
    balance_delta = BalanceDeltaV1(("alice", "asset-a"), 1)
    reserve_delta = PoolReserveDeltaV1("pool-a", "asset-a", 1)
    lp_event = LPDurationEventV1(("alice", "pool-a"), 1, 0)
    deltas = SpotDeltaBatchV1(
        balance_deltas=(balance_delta,),
        reserve_deltas=(reserve_delta,),
        lp_events=(lp_event,),
        pool_creations=(),
    )
    half_budget_integer = 1 << ((MAX_CANONICAL_BYTES_V1 // 2) * 8)
    object.__setattr__(balance_delta, "net_delta", half_budget_integer)
    object.__setattr__(reserve_delta, "net_delta", half_budget_integer)

    result = apply_spot_deltas_v1(
        *_empty_spot(),
        deltas,
        now=0,
        min_age_seconds=0,
        policy=None,
    )

    assert result == PoolPatchRejectV1(
        PoolPatchCodeV1.BYTE_LIMIT,
        ("deltas",),
    )
    assert not hasattr(result, "balances")

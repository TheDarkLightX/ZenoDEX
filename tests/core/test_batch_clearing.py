# [TESTER] v1

from __future__ import annotations

import ast
import inspect
from dataclasses import replace
from pathlib import Path

import pytest

import src.core.batch_clearing_ab_order as batch_clearing_ab_order
import src.core.batch_clearing as batch_clearing_module
import src.core.batch_clearing_ordering as batch_clearing_ordering
from src.core.batch_clearing import (
    _ab_ordering_key as _ab_ordering_key_with_request,
)
from src.core.batch_clearing import (
    _aggregate_balance_deltas_chunked,
    _aggregate_lp_deltas_chunked,
    _aggregate_reserve_deltas_chunked,
    _apply_create_pool_to_locals,
    _cow_pair_netting_exact_in_v1,
    _eval_ordering_ab,
    _get_limit_price,
    _order_swaps_limit_price,
    _order_swaps_mci_ab,
    _parse_create_pool_event_payload,
    _process_liquidity_intent,
    _refine_ab_ordering_global,
    _refine_b_ordering,
    _simulate_swap_reserves,
    _try_create_pool,
    apply_settlement,
    apply_settlement_pure,
    clear_batch_single_pool,
    clear_batch_single_pool_for_request,
    compute_settlement,
    compute_settlement_for_request,
    validate_settlement,
)
from src.core.batch_clearing import (
    _apply_filled_intent_to_locals as _apply_filled_intent_to_locals_with_request,
)
from src.core.batch_clearing import (
    _order_swaps_optimal_ab_bounded as _order_swaps_optimal_ab_bounded_with_request,
)
from src.core.batch_clearing import (
    _process_swap_intent as _process_swap_intent_with_request,
)
from src.core.batch_clearing_apply import _FilledIntentLocalApplyRequest, _FilledIntentLocalContext
from src.core.batch_clearing_requests import ClearBatchSinglePoolRequest, ComputeSettlementRequest
from src.core.batch_clearing_swaps import (
    _apply_swap_fill_to_scratch_balances,
    _SwapIntentRuntimeRequest,
)
from src.core.liquidity import create_pool
from src.core.settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta, Settlement
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus


def _apply_filled_intent_to_locals(
    *,
    intent: Intent,
    fill: Fill,
    pool_id: str,
    pool_state: PoolState,
    balances: BalanceTable,
    lp_balances: LPTable,
    balance_deltas: list[BalanceDelta],
    reserve_deltas: list[ReserveDelta],
    lp_deltas: list[LPDelta],
    protocol_fee_recipient_pubkey: str | None = None,
) -> None:
    _apply_filled_intent_to_locals_with_request(
        _FilledIntentLocalApplyRequest(
            intent=intent,
            fill=fill,
            context=_FilledIntentLocalContext(
                pool_id=pool_id,
                pool_state=pool_state,
                balances=balances,
                lp_balances=lp_balances,
                balance_deltas=balance_deltas,
                reserve_deltas=reserve_deltas,
                lp_deltas=lp_deltas,
                protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
            ),
        )
    )


def _order_swaps_optimal_ab_bounded(
    intents: list[Intent],
    *,
    pool_state: PoolState,
    balances: BalanceTable,
    reserves: tuple[int, int],
    seed: bytes | None = None,
) -> list[Intent]:
    return _order_swaps_optimal_ab_bounded_with_request(
        batch_clearing_ordering._OptimalAbBoundedRequest(
            intents=intents,
            pool_state=pool_state,
            balances=balances,
            reserves=reserves,
            seed=seed,
        )
    )


def _ab_ordering_key(
    ordering: list[Intent] | None = None,
    pool_state: PoolState | None = None,
    reserves: tuple[int, int] | None = None,
    *,
    A_B_order: tuple[int, int, tuple[str, ...]] | None = None,
    seed: bytes | None = None,
) -> tuple[int, int, tuple[str, ...]]:
    if A_B_order is not None:
        return _ab_ordering_key_with_request(
            batch_clearing_ordering._AbOrderingTotalsRequest(
                amount_a=A_B_order[0],
                surplus_b=A_B_order[1],
                intent_ids=A_B_order[2],
                seed=seed,
            )
        )
    if ordering is None or pool_state is None or reserves is None:
        raise ValueError("ordering, pool_state, and reserves are required unless A_B_order is provided")
    return _ab_ordering_key_with_request(
        batch_clearing_ordering._AbOrderingEvaluationRequest(
            ordering=ordering,
            pool_state=pool_state,
            reserves=reserves,
            seed=seed,
        )
    )


def _process_swap_intent(
    intent: Intent,
    reserves: tuple[int, int],
    pool_state: PoolState,
    balances: BalanceTable,
    *,
    protocol_fee_share_bps: int = 0,
) -> Fill:
    return _process_swap_intent_with_request(
        _SwapIntentRuntimeRequest(
            intent=intent,
            reserves=reserves,
            pool_state=pool_state,
            balances=balances,
            protocol_fee_share_bps=protocol_fee_share_bps,
        )
    )


def test_batch_clearing_has_no_bare_broad_candidate_suppression() -> None:
    tree = ast.parse(Path(batch_clearing_module.__file__).read_text(encoding="utf-8"))
    broad_bare_handlers = [
        node.lineno
        for node in ast.walk(tree)
        if isinstance(node, ast.ExceptHandler)
        and isinstance(node.type, ast.Name)
        and node.type.id in {"Exception", "BaseException"}
        and node.name is None
    ]
    assert broad_bare_handlers == []


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_compute_settlement_does_not_mutate_input_pools() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )

    pools = {pool_id: pool}
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    lp_balances = LPTable()

    pre_r0 = pool.reserve0
    pre_r1 = pool.reserve1

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 1000,
                "min_amount_out": 1,
            },
        )
    ]

    settlement = compute_settlement(intents, pools, balances, lp_balances)
    ok, err = validate_settlement(settlement, balances, pools, lp_balances)
    assert ok, err

    # Purity check: original pool object is not mutated by compute_settlement.
    assert pool.reserve0 == pre_r0
    assert pool.reserve1 == pre_r1


def test_batch_clearing_public_defaults_are_explicitly_greedy_ab_refined() -> None:
    compute_default = inspect.signature(compute_settlement).parameters["swap_ordering"].default
    clear_default = inspect.signature(clear_batch_single_pool).parameters["swap_ordering"].default

    assert compute_default == "greedy_ab_refined"
    assert clear_default == "greedy_ab_refined"


def test_compute_settlement_request_api_matches_wrapper() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    lp_balances = LPTable()
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 1000,
                "min_amount_out": 1,
            },
        )
    ]

    request = ComputeSettlementRequest(
        intents=intents,
        pools={pool_id: pool},
        balances=balances,
        lp_balances=lp_balances,
    )

    assert compute_settlement_for_request(request) == compute_settlement(
        intents,
        {pool_id: pool},
        balances,
        lp_balances,
    )


def test_compute_settlement_request_rejects_non_bytes_tiebreak_seed() -> None:
    with pytest.raises(TypeError, match="swap_tiebreak_seed must be bytes or None"):
        compute_settlement_for_request(
            ComputeSettlementRequest(
                intents=[],
                pools={},
                balances=BalanceTable(),
                swap_tiebreak_seed="seed",  # type: ignore[arg-type]
            )
        )


def test_clear_batch_single_pool_request_api_matches_wrapper() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool = PoolState(
        pool_id="0x" + "aa" * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=100_000,
        reserve1=100_000,
        fee_bps=30,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 1_000_000)
    lp_balances = LPTable()
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 1000,
                "min_amount_out": 1,
            },
        )
    ]

    request = ClearBatchSinglePoolRequest(
        intents=intents,
        pool_state=pool,
        balances=balances,
        lp_balances=lp_balances,
    )

    assert clear_batch_single_pool_for_request(request) == clear_batch_single_pool(
        intents,
        pool,
        balances,
        lp_balances,
    )


def test_clear_batch_single_pool_request_rejects_non_bytes_tiebreak_seed() -> None:
    pool = PoolState(
        pool_id="0x" + "aa" * 32,
        asset0="0x" + "01" * 32,
        asset1="0x" + "02" * 32,
        reserve0=100_000,
        reserve1=100_000,
        fee_bps=30,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    with pytest.raises(TypeError, match="swap_tiebreak_seed must be bytes or None"):
        clear_batch_single_pool_for_request(
            ClearBatchSinglePoolRequest(
                intents=[],
                pool_state=pool,
                balances=BalanceTable(),
                lp_balances=LPTable(),
                swap_tiebreak_seed="seed",  # type: ignore[arg-type]
            )
        )


def test_batch_clearing_rejects_second_swap_when_overdrawn() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )

    pools = {pool_id: pool}
    balances = BalanceTable()
    balances.set(pk, asset0, 1000)  # only enough for one of the swaps
    balances.set(pk, asset1, 0)
    lp_balances = LPTable()

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 1000,
                "min_amount_out": 1,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(2),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 1000,
                "min_amount_out": 1,
            },
        ),
    ]

    settlement = compute_settlement(intents, pools, balances, lp_balances)
    ok, err = validate_settlement(settlement, balances, pools, lp_balances)
    assert ok, err

    filled = [f for f in settlement.fills if f.action.value == "FILL"]
    rejected = [f for f in settlement.fills if f.action.value == "REJECT"]
    assert len(filled) == 1
    assert len(rejected) == 1
    assert rejected[0].reason == "INSUFFICIENT_BALANCE"


def test_clear_batch_single_pool_optimal_ab_bounded_canonicalizes_lex_order() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool = PoolState(
        pool_id="0x" + "aa" * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=100,
        reserve1=100,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 200)
    balances.set(pk, asset1, 0)
    lp_balances = LPTable()

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(0),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 50,
                "min_amount_out": 0,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 50,
                "min_amount_out": 1,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(2),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 50,
                "min_amount_out": 1,
            },
        ),
    ]

    fills_limit_price = clear_batch_single_pool(
        intents,
        pool,
        balances,
        lp_balances,
        swap_ordering="limit_price",
    )
    assert [f.intent_id for f in fills_limit_price] == [_iid(1), _iid(2), _iid(0)]

    fills_ab = clear_batch_single_pool(intents, pool, balances, lp_balances, swap_ordering="optimal_ab_bounded")
    assert [f.intent_id for f in fills_ab] == [_iid(0), _iid(1), _iid(2)]


def test_chunked_delta_aggregation_preserves_semantics_and_order() -> None:
    pk_a = "0x" + "11" * 48
    pk_b = "0x" + "22" * 48
    asset_a = "0x" + "01" * 32
    asset_b = "0x" + "02" * 32
    pool_a = "0x" + "aa" * 32
    pool_b = "0x" + "bb" * 32

    balance_deltas = [
        BalanceDelta(pubkey=pk_b, asset=asset_a, delta_add=7, delta_sub=0),
        BalanceDelta(pubkey=pk_a, asset=asset_a, delta_add=3, delta_sub=2),
        BalanceDelta(pubkey=pk_a, asset=asset_a, delta_add=5, delta_sub=1),
        BalanceDelta(pubkey=pk_b, asset=asset_b, delta_add=0, delta_sub=4),
        BalanceDelta(pubkey=pk_b, asset=asset_b, delta_add=2, delta_sub=0),
    ]
    expected_balance = [
        BalanceDelta(pubkey=pk_a, asset=asset_a, delta_add=8, delta_sub=3),
        BalanceDelta(pubkey=pk_b, asset=asset_a, delta_add=7, delta_sub=0),
        BalanceDelta(pubkey=pk_b, asset=asset_b, delta_add=2, delta_sub=4),
    ]
    for chunk_size in (1, 2, 3, 128):
        assert _aggregate_balance_deltas_chunked(balance_deltas, chunk_size=chunk_size) == expected_balance

    reserve_deltas = [
        ReserveDelta(pool_id=pool_b, asset=asset_b, delta_add=0, delta_sub=5),
        ReserveDelta(pool_id=pool_a, asset=asset_a, delta_add=10, delta_sub=0),
        ReserveDelta(pool_id=pool_a, asset=asset_a, delta_add=1, delta_sub=2),
        ReserveDelta(pool_id=pool_b, asset=asset_b, delta_add=3, delta_sub=0),
    ]
    expected_reserve = [
        ReserveDelta(pool_id=pool_a, asset=asset_a, delta_add=11, delta_sub=2),
        ReserveDelta(pool_id=pool_b, asset=asset_b, delta_add=3, delta_sub=5),
    ]
    for chunk_size in (1, 2, 5, 128):
        assert _aggregate_reserve_deltas_chunked(reserve_deltas, chunk_size=chunk_size) == expected_reserve

    lp_deltas = [
        LPDelta(pubkey=pk_b, pool_id=pool_b, delta_add=0, delta_sub=2),
        LPDelta(pubkey=pk_a, pool_id=pool_a, delta_add=4, delta_sub=0),
        LPDelta(pubkey=pk_a, pool_id=pool_a, delta_add=1, delta_sub=1),
        LPDelta(pubkey=pk_b, pool_id=pool_b, delta_add=3, delta_sub=0),
    ]
    expected_lp = [
        LPDelta(pubkey=pk_a, pool_id=pool_a, delta_add=5, delta_sub=1),
        LPDelta(pubkey=pk_b, pool_id=pool_b, delta_add=3, delta_sub=2),
    ]
    for chunk_size in (1, 2, 4, 128):
        assert _aggregate_lp_deltas_chunked(lp_deltas, chunk_size=chunk_size) == expected_lp


def test_cow_pair_netting_fills_opposite_exact_in_intents_without_pool_deltas() -> None:
    pk_a = "0x" + "11" * 48
    pk_b = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool = PoolState(
        pool_id="0x" + "aa" * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    pools = {pool.pool_id: pool}

    balances = BalanceTable()
    balances.set(pk_a, asset0, 1_000)
    balances.set(pk_a, asset1, 0)
    balances.set(pk_b, asset0, 0)
    balances.set(pk_b, asset1, 2_000)
    lp_balances = LPTable()

    intents = [
        # pk_a: asset0 -> asset1, requires at least 150 asset1.
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1),
            sender_pubkey=pk_a,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 150,
            },
        ),
        # pk_b: asset1 -> asset0, requires at least 90 asset0.
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(2),
            sender_pubkey=pk_b,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset1,
                "asset_out": asset0,
                "amount_in": 200,
                "min_amount_out": 90,
            },
        ),
    ]

    settlement = compute_settlement(
        intents,
        pools,
        balances,
        lp_balances,
        swap_ordering="cow_pair_netting_v1",
    )
    ok, err = validate_settlement(settlement, balances, pools, lp_balances)
    assert ok, err

    filled = [f for f in settlement.fills if f.action.value == "FILL"]
    assert [f.intent_id for f in filled] == [_iid(1), _iid(2)]
    assert all(f.reason == "COW_NETTED" for f in filled)
    assert all((f.fee_paid or 0) == 0 for f in filled)

    # No pool interaction => no reserve deltas.
    assert settlement.reserve_deltas == []


def test_cow_pair_netting_bva_min_out_boundary() -> None:
    # BVA: just below / at / above the matchability boundary.
    pk_a = "0x" + "11" * 48
    pk_b = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool = PoolState(
        pool_id="0x" + "aa" * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    pools = {pool.pool_id: pool}

    balances = BalanceTable()
    balances.set(pk_a, asset0, 1_000)
    balances.set(pk_a, asset1, 0)
    balances.set(pk_b, asset0, 0)
    balances.set(pk_b, asset1, 2_000)
    lp_balances = LPTable()

    # Fix pk_b amount_in=200, so pk_a is matchable iff min_out <= 200.
    for min_out_a, expect_netted in [(199, True), (200, True), (201, False)]:
        intents = [
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=_iid(1),
                sender_pubkey=pk_a,
                deadline=9999999999,
                fields={
                    "pool_id": pool.pool_id,
                    "asset_in": asset0,
                    "asset_out": asset1,
                    "amount_in": 100,
                    "min_amount_out": min_out_a,
                },
            ),
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=_iid(2),
                sender_pubkey=pk_b,
                deadline=9999999999,
                fields={
                    "pool_id": pool.pool_id,
                    "asset_in": asset1,
                    "asset_out": asset0,
                    "amount_in": 200,
                    "min_amount_out": 90,
                },
            ),
        ]

        settlement = compute_settlement(
            intents,
            pools,
            balances,
            lp_balances,
            swap_ordering="cow_pair_netting_v1",
        )
        ok, err = validate_settlement(settlement, balances, pools, lp_balances)
        assert ok, err

        filled = [f for f in settlement.fills if f.action.value == "FILL"]
        if expect_netted:
            assert all(f.reason == "COW_NETTED" for f in filled)
            assert settlement.reserve_deltas == []
        else:
            # No netting: at least one swap should hit the pool (reserve deltas non-empty).
            assert any(f.reason != "COW_NETTED" for f in filled)
            assert settlement.reserve_deltas != []


def test_validate_settlement_rejects_invalid_create_pool_event_payload() -> None:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=[
            {
                "type": "CREATE_POOL",
                "pool_id": "0x" + "aa" * 32,
                "asset0": "0x" + "01" * 32,
                "asset1": "0x" + "02" * 32,
                "fee_bps": "30",
                "curve_tag": "CPMM",
                "curve_params": "",
                "status": "ACTIVE",
                "created_at": 0,
            }
        ],
    )

    ok, err = validate_settlement(settlement, BalanceTable(), {}, LPTable())
    assert ok is False
    assert err == "Invalid CREATE_POOL fee_bps for pool: " + ("0x" + "aa" * 32)


def test_apply_settlement_rejects_invalid_create_pool_event_payload() -> None:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=[
            {
                "type": "CREATE_POOL",
                "pool_id": "0x" + "bb" * 32,
                "asset0": "0x" + "01" * 32,
                "asset1": "0x" + "02" * 32,
                "fee_bps": 30,
                "curve_tag": "CPMM",
                "curve_params": "",
                "status": "ACTIVE",
                "created_at": -1,
            }
        ],
    )

    try:
        apply_settlement(settlement, BalanceTable(), {}, LPTable())
    except ValueError as exc:
        assert str(exc) == "Invalid CREATE_POOL created_at for pool: " + ("0x" + "bb" * 32)
    else:
        assert False, "expected invalid CREATE_POOL event payload to raise"


def test_parse_create_pool_event_payload_applies_defaults() -> None:
    pool_id = "0x" + "ab" * 32
    parsed = _parse_create_pool_event_payload(
        {
            "pool_id": pool_id,
            "asset0": "0x" + "01" * 32,
            "asset1": "0x" + "02" * 32,
            "fee_bps": 30,
        }
    )
    assert parsed == (
        pool_id,
        "0x" + "01" * 32,
        "0x" + "02" * 32,
        30,
        "CPMM",
        "",
        PoolStatus.ACTIVE,
        0,
    )


def test_validate_settlement_rejects_create_pool_conflicts_and_duplicates() -> None:
    pool_id, pool, _ = create_pool(
        asset0="0x" + "01" * 32,
        asset1="0x" + "02" * 32,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey="0x" + "11" * 48,
    )
    event = {
        "type": "CREATE_POOL",
        "pool_id": pool_id,
        "asset0": pool.asset0,
        "asset1": pool.asset1,
        "fee_bps": pool.fee_bps,
        "curve_tag": pool.curve_tag,
        "curve_params": pool.curve_params,
        "status": pool.status.value,
        "created_at": pool.created_at,
    }
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=[event],
    )
    ok, err = validate_settlement(settlement, BalanceTable(), {pool_id: pool}, LPTable())
    assert ok is False
    assert err == f"CREATE_POOL conflicts with existing pool: {pool_id}"

    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=[event, event],
    )
    ok, err = validate_settlement(settlement, BalanceTable(), {}, LPTable())
    assert ok is False
    assert err == f"Duplicate CREATE_POOL event for pool: {pool_id}"


def test_validate_settlement_rejects_invalid_created_pool_curve_config() -> None:
    pool_id = "0x" + "cd" * 32
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=[
            {
                "type": "CREATE_POOL",
                "pool_id": pool_id,
                "asset0": "0x" + "01" * 32,
                "asset1": "0x" + "02" * 32,
                "fee_bps": 30,
                "curve_tag": "NOT_A_CURVE",
                "curve_params": "",
                "status": "ACTIVE",
                "created_at": 0,
            }
        ],
    )
    ok, err = validate_settlement(settlement, BalanceTable(), {}, LPTable())
    assert ok is False
    assert err is not None
    assert err.startswith(f"Invalid CREATE_POOL event for pool {pool_id}:")


def test_validate_settlement_propagates_unexpected_created_pool_errors(monkeypatch) -> None:
    pool_id = "0x" + "aa" * 32
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=[
            {
                "type": "CREATE_POOL",
                "pool_id": pool_id,
                "asset0": "0x" + "01" * 32,
                "asset1": "0x" + "02" * 32,
                "fee_bps": 30,
                "curve_tag": "CPMM",
                "curve_params": "",
                "status": "ACTIVE",
                "created_at": 0,
            }
        ],
    )

    def _buggy_pool_state(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("PoolState bug")

    monkeypatch.setattr(batch_clearing_module, "PoolState", _buggy_pool_state)

    with pytest.raises(RuntimeError, match="PoolState bug"):
        validate_settlement(settlement, BalanceTable(), {}, LPTable())


def test_validate_settlement_rejects_negative_balances_reserves_and_lp() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 5)
    lp_balances = LPTable()
    lp_balances.set(pk, pool_id, 1)

    negative_balance = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[BalanceDelta(pubkey=pk, asset=asset0, delta_add=0, delta_sub=6)],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement(negative_balance, balances, {pool_id: pool}, lp_balances)
    assert ok is False
    assert err == f"Negative balance: {pk}, {asset0}, 5 + -6"

    negative_reserve = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=0, delta_sub=pool.reserve0 + 1)],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement(negative_reserve, balances, {pool_id: pool}, lp_balances)
    assert ok is False
    assert err == f"Negative reserve: {pool_id}, {asset0}, {pool.reserve0} + {-pool.reserve0 - 1}"

    negative_lp = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=pk, pool_id=pool_id, delta_add=0, delta_sub=2)],
        events=None,
    )
    ok, err = validate_settlement(negative_lp, balances, {pool_id: pool}, lp_balances)
    assert ok is False
    assert err == f"Negative LP balance: {pk}, {pool_id}, 1 + -2"


def test_validate_settlement_rejects_unknown_pool_and_conservation_violations() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    unknown_reserve_pool = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[ReserveDelta(pool_id="0x" + "ff" * 32, asset=asset0, delta_add=1, delta_sub=0)],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement(unknown_reserve_pool, BalanceTable(), {pool_id: pool}, LPTable())
    assert ok is False
    assert err == f"Pool not found: {'0x' + 'ff' * 32}"

    bad_asset = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[ReserveDelta(pool_id=pool_id, asset="0x" + "03" * 32, delta_add=1, delta_sub=0)],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement(bad_asset, BalanceTable(), {pool_id: pool}, LPTable())
    assert ok is False
    assert err == f"Asset {'0x' + '03' * 32} not in pool {pool_id}"

    bad_conservation = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[BalanceDelta(pubkey=pk, asset=asset0, delta_add=1, delta_sub=0)],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement(bad_conservation, BalanceTable(), {pool_id: pool}, LPTable())
    assert ok is False
    assert err == f"Asset conservation violation: {asset0}, net_delta = 1"

    unknown_lp_pool = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=pk, pool_id="0x" + "ee" * 32, delta_add=1, delta_sub=0)],
        events=None,
    )
    ok, err = validate_settlement(unknown_lp_pool, BalanceTable(), {pool_id: pool}, LPTable())
    assert ok is False
    assert err == f"LP delta references unknown pool: {'0x' + 'ee' * 32}"

    negative_supply = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=pk, pool_id=pool_id, delta_add=0, delta_sub=pool.lp_supply + 1)],
        events=None,
    )
    inconsistent_lp = LPTable()
    inconsistent_lp.set(pk, pool_id, pool.lp_supply + 10)
    ok, err = validate_settlement(negative_supply, BalanceTable(), {pool_id: pool}, inconsistent_lp)
    assert ok is False
    assert err == f"Negative LP supply: {pool_id}, {pool.lp_supply} + {-pool.lp_supply - 1}"


def test_validate_settlement_accepts_multi_pool_lp_supply_iteration() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    asset2 = "0x" + "03" * 32
    pool0_id, pool0, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    pool1_id, pool1, _ = create_pool(
        asset0=asset0,
        asset1=asset2,
        amount0=3_000_000,
        amount1=3_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[
            LPDelta(pubkey=pk, pool_id=pool0_id, delta_add=1, delta_sub=0),
            LPDelta(pubkey=pk, pool_id=pool1_id, delta_add=2, delta_sub=0),
        ],
        events=None,
    )

    ok, err = validate_settlement(settlement, BalanceTable(), {pool0_id: pool0, pool1_id: pool1}, LPTable())
    assert ok is True
    assert err is None


def test_apply_settlement_rejects_reserve_and_lp_failures() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    reserve_unknown = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[ReserveDelta(pool_id="0x" + "aa" * 32, asset=asset0, delta_add=1, delta_sub=0)],
        lp_deltas=[],
        events=None,
    )
    try:
        apply_settlement(reserve_unknown, BalanceTable(), {pool_id: pool}, LPTable())
    except ValueError as exc:
        assert str(exc) == f"Pool not found: {'0x' + 'aa' * 32}"
    else:
        assert False, "expected missing reserve pool to raise"

    reserve_negative = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=0, delta_sub=pool.reserve0 + 1)],
        lp_deltas=[],
        events=None,
    )
    try:
        apply_settlement(reserve_negative, BalanceTable(), {pool_id: pool}, LPTable())
    except ValueError as exc:
        assert str(exc) == f"Negative reserve: {pool_id}, {asset0}, {pool.reserve0} + {-pool.reserve0 - 1}"
    else:
        assert False, "expected negative reserve to raise"

    reserve_wrong_asset = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[ReserveDelta(pool_id=pool_id, asset="0x" + "03" * 32, delta_add=1, delta_sub=0)],
        lp_deltas=[],
        events=None,
    )
    try:
        apply_settlement(reserve_wrong_asset, BalanceTable(), {pool_id: pool}, LPTable())
    except ValueError as exc:
        assert str(exc) == f"Asset {'0x' + '03' * 32} not in pool {pool_id}"
    else:
        assert False, "expected wrong reserve asset to raise"

    lp_unknown = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=pk, pool_id="0x" + "bb" * 32, delta_add=1, delta_sub=0)],
        events=None,
    )
    try:
        apply_settlement(lp_unknown, BalanceTable(), {pool_id: pool}, LPTable())
    except ValueError as exc:
        assert str(exc) == f"Pool not found for LP delta: {'0x' + 'bb' * 32}"
    else:
        assert False, "expected missing LP pool to raise"

    lp_negative = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=pk, pool_id=pool_id, delta_add=0, delta_sub=pool.lp_supply + 1)],
        events=None,
    )
    try:
        apply_settlement(lp_negative, BalanceTable(), {pool_id: pool}, LPTable())
    except ValueError as exc:
        assert str(exc) == f"Negative LP supply: {pool_id}"
    else:
        assert False, "expected negative LP supply to raise"


def test_legacy_validate_settlement_rejects_malformed_delta_limbs() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    invalid_balance = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[BalanceDelta(pubkey=pk, asset=asset0, delta_add=True, delta_sub=0)],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement(invalid_balance, BalanceTable(), {pool_id: pool}, LPTable())
    assert ok is False
    assert err == "balance_delta.delta_add must be a non-negative int"

    invalid_reserve = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=-1, delta_sub=0)],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement(invalid_reserve, BalanceTable(), {pool_id: pool}, LPTable())
    assert ok is False
    assert err == "reserve_delta.delta_add must be a non-negative int"

    invalid_lp = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=pk, pool_id=pool_id, delta_add=0, delta_sub="1")],
        events=None,
    )
    ok, err = validate_settlement(invalid_lp, BalanceTable(), {pool_id: pool}, LPTable())
    assert ok is False
    assert err == "lp_delta.delta_sub must be a non-negative int"


def test_apply_settlement_rejects_malformed_delta_limbs() -> None:
    pk = "0x" + "11" * 48
    asset = "0x" + "01" * 32
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[BalanceDelta(pubkey=pk, asset=asset, delta_add=True, delta_sub=0)],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    with pytest.raises(TypeError, match="balance_delta.delta_add must be a non-negative int"):
        apply_settlement(settlement, BalanceTable(), {}, LPTable())


def test_apply_settlement_pure_returns_copies_and_applies_create_pool_event() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = "0x" + "cc" * 32
    balances = BalanceTable()
    balances.set(pk, asset0, 10)
    pools: dict[str, PoolState] = {}
    lp_balances = LPTable()

    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[BalanceDelta(pubkey=pk, asset=asset0, delta_add=3, delta_sub=0)],
        reserve_deltas=[ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=5, delta_sub=0)],
        lp_deltas=[LPDelta(pubkey=pk, pool_id=pool_id, delta_add=7, delta_sub=0)],
        events=[
            {
                "type": "CREATE_POOL",
                "pool_id": pool_id,
                "asset0": asset0,
                "asset1": asset1,
                "fee_bps": 30,
                "curve_tag": "CPMM",
                "curve_params": "",
                "status": "ACTIVE",
                "created_at": 0,
            }
        ],
    )

    new_balances, new_pools, new_lp = apply_settlement_pure(settlement, balances, pools, lp_balances)
    assert balances.get(pk, asset0) == 10
    assert pools == {}
    assert lp_balances.get(pk, pool_id) == 0
    assert new_balances.get(pk, asset0) == 13
    assert pool_id in new_pools
    assert new_pools[pool_id].reserve0 == 5
    assert new_pools[pool_id].lp_supply == 7
    assert new_lp.get(pk, pool_id) == 7


def test_compute_settlement_rejects_unknown_pool_and_invalid_non_pool_intents() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1001),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": "0x" + "aa" * 32,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 1,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1002),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 1,
            },
        ),
    ]

    settlement = compute_settlement(intents, {}, balances, LPTable())
    assert settlement.included_intents == [
        (_iid(1001), settlement.included_intents[0][1]),
        (_iid(1002), settlement.included_intents[1][1]),
    ]
    assert settlement.fills[0].action == FillAction.REJECT
    assert settlement.fills[0].reason == "POOL_NOT_FOUND"
    assert settlement.fills[1].action == FillAction.REJECT
    assert settlement.fills[1].reason == "INVALID_INTENT"


def test_compute_settlement_handles_create_pool_success_and_reject_before_pool_batches() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    asset2 = "0x" + "03" * 32
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    balances.set(pk, asset2, 10_000_000)

    valid_create = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(10017),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset0": asset0, "asset1": asset1, "fee_bps": 30, "amount0": 2_000_000, "amount1": 2_000_000},
    )
    invalid_create = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(10018),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset0": asset1, "asset1": asset2, "fee_bps": 30, "amount0": 2_000_000},
    )
    settlement = compute_settlement([invalid_create, valid_create], {}, balances, LPTable())
    assert [it for it, _ in settlement.included_intents] == [valid_create.intent_id, invalid_create.intent_id]
    by_id = {fill.intent_id: fill for fill in settlement.fills}
    assert by_id[invalid_create.intent_id].reason == "MISSING_PARAMS"
    assert by_id[valid_create.intent_id].reason == "POOL_CREATED"
    assert settlement.events is not None
    assert len(settlement.events) == 1
    assert settlement.events[0]["type"] == "CREATE_POOL"


def test_chunked_delta_aggregation_drops_zero_nets() -> None:
    pk = "0x" + "11" * 48
    asset = "0x" + "01" * 32
    pool_id = "0x" + "aa" * 32

    assert _aggregate_balance_deltas_chunked(
        [
            BalanceDelta(pubkey=pk, asset=asset, delta_add=0, delta_sub=0),
        ],
        chunk_size=1,
    ) == []
    assert _aggregate_reserve_deltas_chunked(
        [
            ReserveDelta(pool_id=pool_id, asset=asset, delta_add=0, delta_sub=0),
        ],
        chunk_size=1,
    ) == []
    assert _aggregate_lp_deltas_chunked(
        [
            LPDelta(pubkey=pk, pool_id=pool_id, delta_add=0, delta_sub=0),
        ],
        chunk_size=1,
    ) == []


def test_chunked_delta_aggregation_rejects_malformed_delta_limbs() -> None:
    pk = "0x" + "11" * 48
    asset = "0x" + "01" * 32
    pool_id = "0x" + "aa" * 32

    with pytest.raises(TypeError, match="balance_deltas.delta_add must be a non-negative int"):
        _aggregate_balance_deltas_chunked(
            [BalanceDelta(pubkey=pk, asset=asset, delta_add=True, delta_sub=0)],
            chunk_size=1,
        )
    with pytest.raises(TypeError, match="balance_deltas.delta_sub must be a non-negative int"):
        _aggregate_balance_deltas_chunked(
            [BalanceDelta(pubkey=pk, asset=asset, delta_add=0, delta_sub="1")],
            chunk_size=1,
        )
    with pytest.raises(TypeError, match="reserve_deltas.delta_add must be a non-negative int"):
        _aggregate_reserve_deltas_chunked(
            [ReserveDelta(pool_id=pool_id, asset=asset, delta_add=-1, delta_sub=0)],
            chunk_size=1,
        )
    with pytest.raises(TypeError, match="lp_deltas.delta_sub must be a non-negative int"):
        _aggregate_lp_deltas_chunked(
            [LPDelta(pubkey=pk, pool_id=pool_id, delta_add=0, delta_sub=False)],
            chunk_size=1,
        )


def test_parse_create_pool_event_payload_rejects_missing_pool_assets_curve_fields_and_status() -> None:
    try:
        _parse_create_pool_event_payload({"asset0": "0x" + "01" * 32, "asset1": "0x" + "02" * 32, "fee_bps": 30})
    except ValueError as exc:
        assert str(exc) == "Invalid CREATE_POOL event: missing pool_id"
    else:
        assert False, "expected missing pool_id to raise"

    try:
        _parse_create_pool_event_payload(
            {
                "pool_id": "0x" + "aa" * 32,
                "asset0": 1,
                "asset1": "0x" + "02" * 32,
                "fee_bps": 30,
            }
        )
    except ValueError as exc:
        assert str(exc) == "Invalid CREATE_POOL assets for pool: " + ("0x" + "aa" * 32)
    else:
        assert False, "expected invalid assets to raise"

    try:
        _parse_create_pool_event_payload(
            {
                "pool_id": "0x" + "ab" * 32,
                "asset0": "0x" + "01" * 32,
                "asset1": "0x" + "02" * 32,
                "fee_bps": 30,
                "curve_tag": "",
            }
        )
    except ValueError as exc:
        assert str(exc) == "Invalid CREATE_POOL curve_tag for pool: " + ("0x" + "ab" * 32)
    else:
        assert False, "expected invalid curve_tag to raise"

    try:
        _parse_create_pool_event_payload(
            {
                "pool_id": "0x" + "ac" * 32,
                "asset0": "0x" + "01" * 32,
                "asset1": "0x" + "02" * 32,
                "fee_bps": 30,
                "curve_params": {},
            }
        )
    except ValueError as exc:
        assert str(exc) == "Invalid CREATE_POOL curve_params for pool: " + ("0x" + "ac" * 32)
    else:
        assert False, "expected invalid curve_params to raise"

    try:
        _parse_create_pool_event_payload(
            {
                "pool_id": "0x" + "ad" * 32,
                "asset0": "0x" + "01" * 32,
                "asset1": "0x" + "02" * 32,
                "fee_bps": 30,
                "status": "BROKEN",
            }
        )
    except ValueError as exc:
        assert str(exc) == "Invalid CREATE_POOL status for pool: " + ("0x" + "ad" * 32)
    else:
        assert False, "expected invalid status to raise"


def test_try_create_pool_rejects_invalid_params_balance_computation_and_duplicates() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    base_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(1003),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 30,
            "amount0": 2_000_000,
            "amount1": 2_000_000,
        },
    )

    fill, pool_id, created_pool, err = _try_create_pool(
        Intent(
            module=base_intent.module,
            version=base_intent.version,
            kind=base_intent.kind,
            intent_id=_iid(1004),
            sender_pubkey=pk,
            deadline=base_intent.deadline,
            fields={"asset0": asset0, "asset1": asset1, "fee_bps": 30, "amount0": 2_000_000},
        ),
        {},
        balances,
    )
    assert fill.action == FillAction.REJECT
    assert fill.reason == "MISSING_PARAMS"
    assert pool_id is None and created_pool is None and err == "missing params"

    fill, _pool_id, _created_pool, err = _try_create_pool(
        Intent(
            module=base_intent.module,
            version=base_intent.version,
            kind=base_intent.kind,
            intent_id=_iid(1005),
            sender_pubkey=pk,
            deadline=base_intent.deadline,
            fields={**base_intent.fields, "asset1": 7},
        ),
        {},
        balances,
    )
    assert fill.reason == "INVALID_PARAMS"
    assert err == "asset ids must be strings"

    fill, _pool_id, _created_pool, err = _try_create_pool(
        Intent(
            module=base_intent.module,
            version=base_intent.version,
            kind=base_intent.kind,
            intent_id=_iid(1006),
            sender_pubkey=pk,
            deadline=base_intent.deadline,
            fields={**base_intent.fields, "fee_bps": 10_001},
        ),
        {},
        balances,
    )
    assert fill.reason == "INVALID_PARAMS"
    assert err == "fee_bps out of domain"

    fill, _pool_id, _created_pool, err = _try_create_pool(
        Intent(
            module=base_intent.module,
            version=base_intent.version,
            kind=base_intent.kind,
            intent_id=_iid(1007),
            sender_pubkey=pk,
            deadline=base_intent.deadline,
            fields={**base_intent.fields, "amount0": 0},
        ),
        {},
        balances,
    )
    assert fill.reason == "INVALID_PARAMS"
    assert err == "amount0 out of domain"

    fill, _pool_id, _created_pool, err = _try_create_pool(
        Intent(
            module=base_intent.module,
            version=base_intent.version,
            kind=base_intent.kind,
            intent_id=_iid(1008),
            sender_pubkey=pk,
            deadline=base_intent.deadline,
            fields={**base_intent.fields, "amount1": 0},
        ),
        {},
        balances,
    )
    assert fill.reason == "INVALID_PARAMS"
    assert err == "amount1 out of domain"

    fill, _pool_id, _created_pool, err = _try_create_pool(
        Intent(
            module=base_intent.module,
            version=base_intent.version,
            kind=base_intent.kind,
            intent_id=_iid(1009),
            sender_pubkey=pk,
            deadline=base_intent.deadline,
            fields={**base_intent.fields, "created_at": -1},
        ),
        {},
        balances,
    )
    assert fill.reason == "INVALID_PARAMS"
    assert err == "created_at out of domain"

    low_balances = BalanceTable()
    low_balances.set(pk, asset0, 1)
    low_balances.set(pk, asset1, 1)
    fill, _pool_id, _created_pool, err = _try_create_pool(base_intent, {}, low_balances)
    assert fill.reason == "INSUFFICIENT_BALANCE"
    assert err == "insufficient balance"

    fill, _pool_id, _created_pool, err = _try_create_pool(
        Intent(
            module=base_intent.module,
            version=base_intent.version,
            kind=base_intent.kind,
            intent_id=_iid(1010),
            sender_pubkey=pk,
            deadline=base_intent.deadline,
            fields={**base_intent.fields, "asset1": asset0},
        ),
        {},
        balances,
    )
    assert fill.reason is not None
    assert fill.reason.startswith("COMPUTATION_ERROR:")
    assert err is not None

    existing_pool_id, existing_pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    fill, _pool_id, _created_pool, err = _try_create_pool(base_intent, {existing_pool_id: existing_pool}, balances)
    assert fill.reason == "POOL_ALREADY_EXISTS"
    assert err == "pool already exists"


def test_try_create_pool_propagates_unexpected_create_pool_errors(monkeypatch) -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(1012),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset0": asset0, "asset1": asset1, "fee_bps": 30, "amount0": 2_000_000, "amount1": 2_000_000},
    )

    def _buggy_create_pool(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("create_pool bug")

    monkeypatch.setattr(batch_clearing_module, "create_pool", _buggy_create_pool)

    with pytest.raises(RuntimeError, match="create_pool bug"):
        _try_create_pool(intent, {}, balances)


def test_try_create_pool_success_and_apply_create_pool_to_locals() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    lp_balances = LPTable()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(1011),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 30,
            "amount0": 2_000_000,
            "amount1": 2_000_000,
            "created_at": None,
        },
    )

    pool_states: dict[str, PoolState] = {}
    fill, pool_id, created_pool, err = _try_create_pool(intent, pool_states, balances)
    assert err is None
    assert fill.action == FillAction.FILL
    assert fill.reason == "POOL_CREATED"
    assert pool_id is not None and created_pool is not None
    assert pool_states[pool_id] == created_pool

    balance_deltas: list[BalanceDelta] = []
    reserve_deltas: list[ReserveDelta] = []
    lp_deltas: list[LPDelta] = []
    events: list[dict[str, object]] = []
    _apply_create_pool_to_locals(
        intent,
        pool_id,
        created_pool,
        balances,
        lp_balances,
        balance_deltas,
        reserve_deltas,
        lp_deltas,
        events,
    )
    assert balances.get(pk, asset0) == 8_000_000
    assert balances.get(pk, asset1) == 8_000_000
    assert lp_balances.get(pk, pool_id) == fill.lp_minted
    assert lp_balances.get("0x" + "00" * 48, pool_id) == created_pool.lp_supply - fill.lp_minted
    assert events == [
        {
            "type": "CREATE_POOL",
            "pool_id": pool_id,
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 30,
            "curve_tag": created_pool.curve_tag,
            "curve_params": created_pool.curve_params,
            "status": PoolStatus.ACTIVE.value,
            "created_at": None,
        }
    ]
    assert len(balance_deltas) == 2
    assert len(reserve_deltas) == 2
    assert len(lp_deltas) == 2


def test_apply_filled_intent_to_locals_handles_swap_liquidity_and_cow_paths() -> None:
    pk = "0x" + "11" * 48
    recipient = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, lp_minted = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    def _fresh_balances() -> BalanceTable:
        table = BalanceTable()
        table.set(pk, asset0, 10_000_000)
        table.set(pk, asset1, 10_000_000)
        table.set(recipient, asset0, 0)
        table.set(recipient, asset1, 0)
        return table

    balances = _fresh_balances()
    lp_balances = LPTable()
    swap_deltas: list[BalanceDelta] = []
    swap_reserves: list[ReserveDelta] = []
    swap_lp: list[LPDelta] = []
    swap_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1012),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": asset0, "asset_out": asset1, "recipient": recipient},
    )
    _apply_filled_intent_to_locals(
        intent=swap_intent,
        fill=Fill(
            intent_id=swap_intent.intent_id,
            action=FillAction.FILL,
            amount_in_filled=100,
            amount_out_filled=90,
        ),
        pool_id=pool_id,
        pool_state=pool,
        balances=balances,
        lp_balances=lp_balances,
        balance_deltas=swap_deltas,
        reserve_deltas=swap_reserves,
        lp_deltas=swap_lp,
    )
    assert balances.get(pk, asset0) == 9_999_900
    assert balances.get(recipient, asset1) == 90
    assert pool.reserve0 == 2_000_100
    assert pool.reserve1 == 1_999_910
    assert len(swap_deltas) == 2
    assert len(swap_reserves) == 2
    assert swap_lp == []

    with pytest.raises(TypeError, match="protocol_fee_paid must be int"):
        _apply_filled_intent_to_locals(
            intent=swap_intent,
            fill=Fill(
                intent_id=swap_intent.intent_id,
                action=FillAction.FILL,
                amount_in_filled=100,
                amount_out_filled=90,
                protocol_fee_paid=False,
            ),
            pool_id=pool_id,
            pool_state=pool,
            balances=_fresh_balances(),
            lp_balances=LPTable(),
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            protocol_fee_recipient_pubkey=recipient,
        )

    with pytest.raises(TypeError, match="protocol_fee_paid must be int"):
        _apply_swap_fill_to_scratch_balances(
            swap_intent,
            Fill(
                intent_id=swap_intent.intent_id,
                action=FillAction.FILL,
                amount_in_filled=100,
                amount_out_filled=90,
                protocol_fee_paid=False,
            ),
            _fresh_balances(),
            recipient,
        )

    reverse_balances = _fresh_balances()
    reverse_pool = PoolState(**{**pool.__dict__, "reserve0": 2_000_000, "reserve1": 2_000_000, "lp_supply": lp_minted + 1000})
    reverse_deltas: list[BalanceDelta] = []
    reverse_reserves: list[ReserveDelta] = []
    reverse_lp: list[LPDelta] = []
    reverse_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(1013),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": asset1, "asset_out": asset0, "recipient": recipient},
    )
    _apply_filled_intent_to_locals(
        intent=reverse_intent,
        fill=Fill(
            intent_id=reverse_intent.intent_id,
            action=FillAction.FILL,
            amount_in_filled=80,
            amount_out_filled=70,
        ),
        pool_id=pool_id,
        pool_state=reverse_pool,
        balances=reverse_balances,
        lp_balances=LPTable(),
        balance_deltas=reverse_deltas,
        reserve_deltas=reverse_reserves,
        lp_deltas=reverse_lp,
    )
    assert reverse_pool.reserve1 == 2_000_080
    assert reverse_pool.reserve0 == 1_999_930

    cow_balances = _fresh_balances()
    cow_pool = PoolState(**{**pool.__dict__, "reserve0": 2_000_000, "reserve1": 2_000_000, "lp_supply": lp_minted + 1000})
    cow_reserves: list[ReserveDelta] = []
    _apply_filled_intent_to_locals(
        intent=swap_intent,
        fill=Fill(
            intent_id=swap_intent.intent_id,
            action=FillAction.FILL,
            reason="COW_NETTED",
            amount_in_filled=100,
            amount_out_filled=90,
        ),
        pool_id=pool_id,
        pool_state=cow_pool,
        balances=cow_balances,
        lp_balances=LPTable(),
        balance_deltas=[],
        reserve_deltas=cow_reserves,
        lp_deltas=[],
    )
    assert cow_reserves == []
    assert cow_pool.reserve0 == 2_000_000
    assert cow_pool.reserve1 == 2_000_000

    add_balances = _fresh_balances()
    add_pool = PoolState(**{**pool.__dict__, "reserve0": 2_000_000, "reserve1": 2_000_000, "lp_supply": lp_minted + 1000})
    add_lp = LPTable()
    add_balance_deltas: list[BalanceDelta] = []
    add_reserve_deltas: list[ReserveDelta] = []
    add_lp_deltas: list[LPDelta] = []
    add_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(1014),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "recipient": recipient},
    )
    _apply_filled_intent_to_locals(
        intent=add_intent,
        fill=Fill(
            intent_id=add_intent.intent_id,
            action=FillAction.FILL,
            amount0_used=50,
            amount1_used=60,
            lp_minted=70,
        ),
        pool_id=pool_id,
        pool_state=add_pool,
        balances=add_balances,
        lp_balances=add_lp,
        balance_deltas=add_balance_deltas,
        reserve_deltas=add_reserve_deltas,
        lp_deltas=add_lp_deltas,
    )
    assert add_pool.reserve0 == 2_000_050
    assert add_pool.reserve1 == 2_000_060
    assert add_pool.lp_supply == lp_minted + 1070
    assert add_lp.get(recipient, pool_id) == 70
    assert len(add_balance_deltas) == 2
    assert len(add_reserve_deltas) == 2
    assert len(add_lp_deltas) == 1

    remove_balances = _fresh_balances()
    remove_pool = PoolState(**{**pool.__dict__, "reserve0": 2_000_000, "reserve1": 2_000_000, "lp_supply": lp_minted + 1000})
    remove_lp = LPTable()
    remove_lp.set(pk, pool_id, 500)
    remove_balance_deltas: list[BalanceDelta] = []
    remove_reserve_deltas: list[ReserveDelta] = []
    remove_lp_deltas: list[LPDelta] = []
    remove_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(1015),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "recipient": recipient},
    )
    _apply_filled_intent_to_locals(
        intent=remove_intent,
        fill=Fill(
            intent_id=remove_intent.intent_id,
            action=FillAction.FILL,
            lp_burned=40,
            amount0_out=30,
            amount1_out=20,
        ),
        pool_id=pool_id,
        pool_state=remove_pool,
        balances=remove_balances,
        lp_balances=remove_lp,
        balance_deltas=remove_balance_deltas,
        reserve_deltas=remove_reserve_deltas,
        lp_deltas=remove_lp_deltas,
    )
    assert remove_pool.reserve0 == 1_999_970
    assert remove_pool.reserve1 == 1_999_980
    assert remove_pool.lp_supply == lp_minted + 960
    assert remove_lp.get(pk, pool_id) == 460
    assert remove_balances.get(recipient, asset0) == 30
    assert remove_balances.get(recipient, asset1) == 20
    assert len(remove_balance_deltas) == 2
    assert len(remove_reserve_deltas) == 2
    assert len(remove_lp_deltas) == 1

    unsupported_pool = PoolState(**{**pool.__dict__, "reserve0": 2_000_000, "reserve1": 2_000_000, "lp_supply": lp_minted + 1000})
    weird_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind="MYSTERY_KIND",
        intent_id=_iid(1016),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id},
    )
    try:
        _apply_filled_intent_to_locals(
            intent=weird_intent,
            fill=Fill(intent_id=weird_intent.intent_id, action=FillAction.FILL),
            pool_id=pool_id,
            pool_state=unsupported_pool,
            balances=_fresh_balances(),
            lp_balances=LPTable(),
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
        )
    except ValueError as exc:
        assert str(exc) == "Unsupported intent kind for fill application: MYSTERY_KIND"
    else:
        assert False, "expected unsupported intent kind to raise"


def test_compute_and_clear_single_pool_reject_unsupported_swap_ordering() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)

    try:
        compute_settlement([], {pool_id: pool}, balances, LPTable(), swap_ordering="bad_ordering")
    except ValueError as exc:
        assert str(exc) == "unsupported swap_ordering: 'bad_ordering'"
    else:
        assert False, "expected compute_settlement to reject unsupported ordering"

    try:
        clear_batch_single_pool([], pool, balances, LPTable(), swap_ordering="bad_ordering")
    except ValueError as exc:
        assert str(exc) == "unsupported swap_ordering: 'bad_ordering'"
    else:
        assert False, "expected clear_batch_single_pool to reject unsupported ordering"


def test_process_swap_intent_reject_matrix_and_helper_paths(monkeypatch) -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 10_000)
    reserves = (pool.reserve0, pool.reserve1)

    def _swap_intent(intent_id: str, kind: object, fields: dict[str, object]) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=kind,
            intent_id=intent_id,
            sender_pubkey=pk,
            deadline=9999999999,
            fields=fields,
        )

    assert _process_swap_intent(
        _swap_intent(_iid(1101), IntentKind.SWAP_EXACT_IN, {"asset_in": 7, "asset_out": asset1}),
        reserves,
        pool,
        balances,
    ).reason == "MISSING_PARAMS"
    assert _process_swap_intent(
        _swap_intent(_iid(1102), IntentKind.SWAP_EXACT_IN, {"asset_in": asset0, "asset_out": asset0}),
        reserves,
        pool,
        balances,
    ).reason == "INVALID_ASSET_PAIR"
    assert _process_swap_intent(
        _swap_intent(_iid(1103), IntentKind.SWAP_EXACT_IN, {"asset_in": "0x" + "03" * 32, "asset_out": asset1}),
        reserves,
        pool,
        balances,
    ).reason == "ASSET_NOT_IN_POOL"
    assert _process_swap_intent(
        _swap_intent(
            _iid(1104),
            IntentKind.SWAP_EXACT_IN,
            {"asset_in": asset0, "asset_out": asset1, "amount_in": False, "min_amount_out": 1},
        ),
        reserves,
        pool,
        balances,
    ).reason == "MISSING_PARAMS"
    assert _process_swap_intent(
        _swap_intent(
            _iid(1105),
            IntentKind.SWAP_EXACT_IN,
            {"asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": False},
        ),
        reserves,
        pool,
        balances,
    ).reason == "MISSING_PARAMS"
    assert _process_swap_intent(
        _swap_intent(
            _iid(1106),
            IntentKind.SWAP_EXACT_OUT,
            {"asset_in": asset0, "asset_out": asset1, "amount_out": False, "max_amount_in": 1000},
        ),
        reserves,
        pool,
        balances,
    ).reason == "MISSING_PARAMS"
    assert _process_swap_intent(
        _swap_intent(
            _iid(1107),
            IntentKind.SWAP_EXACT_OUT,
            {"asset_in": asset0, "asset_out": asset1, "amount_out": 100, "max_amount_in": False},
        ),
        reserves,
        pool,
        balances,
    ).reason == "MISSING_PARAMS"

    low_balances = BalanceTable()
    low_balances.set(pk, asset0, 0)
    low_balances.set(pk, asset1, 10_000)
    assert _process_swap_intent(
        _swap_intent(
            _iid(1108),
            IntentKind.SWAP_EXACT_OUT,
            {"asset_in": asset0, "asset_out": asset1, "amount_out": 100, "max_amount_in": 1000},
        ),
        reserves,
        pool,
        low_balances,
    ).reason == "INSUFFICIENT_BALANCE"
    assert _process_swap_intent(
        _swap_intent(
            _iid(1109),
            IntentKind.SWAP_EXACT_OUT,
            {"asset_in": asset0, "asset_out": asset1, "amount_out": 100, "max_amount_in": 1},
        ),
        reserves,
        pool,
        balances,
    ).reason == "SLIPPAGE"

    def _boom_swap_exact_in(*_args: object, **_kwargs: object) -> object:
        raise ValueError("boom")

    monkeypatch.setattr(batch_clearing_module, "quote_cpmm_swap_exact_in", _boom_swap_exact_in)
    assert _process_swap_intent(
        _swap_intent(
            _iid(1110),
            IntentKind.SWAP_EXACT_IN,
            {"asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1},
        ),
        reserves,
        pool,
        balances,
    ).reason == "COMPUTATION_ERROR: boom"
    monkeypatch.undo()

    assert _process_swap_intent(
        _swap_intent(_iid(1111), "MYSTERY_KIND", {"asset_in": asset0, "asset_out": asset1}),
        reserves,
        pool,
        balances,
    ).reason == "UNKNOWN_INTENT_TYPE"


def test_process_liquidity_intent_reject_matrix_and_helper_paths(monkeypatch) -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, lp_minted = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 10_000)
    lp_balances = LPTable()
    lp_balances.set(pk, pool_id, lp_minted)

    def _liq_intent(intent_id: str, kind: object, fields: dict[str, object]) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=kind,
            intent_id=intent_id,
            sender_pubkey=pk,
            deadline=9999999999,
            fields={"pool_id": pool_id, **fields},
        )

    assert _process_liquidity_intent(
        _liq_intent(_iid(1112), IntentKind.ADD_LIQUIDITY, {"amount0_desired": 100}),
        pool,
        lp_balances,
        balances,
    ).reason == "MISSING_PARAMS"
    assert _process_liquidity_intent(
        _liq_intent(_iid(1113), IntentKind.ADD_LIQUIDITY, {"amount0_desired": 0, "amount1_desired": 100}),
        pool,
        lp_balances,
        balances,
    ).reason == "INVALID_PARAMS"
    assert _process_liquidity_intent(
        _liq_intent(_iid(1114), IntentKind.ADD_LIQUIDITY, {"amount0_desired": 100, "amount1_desired": 0}),
        pool,
        lp_balances,
        balances,
    ).reason == "INVALID_PARAMS"
    assert _process_liquidity_intent(
        _liq_intent(
            _iid(1115),
            IntentKind.ADD_LIQUIDITY,
            {"amount0_desired": 100, "amount1_desired": 100, "amount0_min": False},
        ),
        pool,
        lp_balances,
        balances,
    ).reason == "INVALID_PARAMS"
    assert _process_liquidity_intent(
        _liq_intent(
            _iid(1116),
            IntentKind.ADD_LIQUIDITY,
            {"amount0_desired": 100, "amount1_desired": 100, "amount1_min": False},
        ),
        pool,
        lp_balances,
        balances,
    ).reason == "INVALID_PARAMS"

    low_a_balances = BalanceTable()
    low_a_balances.set(pk, asset0, 0)
    low_a_balances.set(pk, asset1, 10_000)
    assert _process_liquidity_intent(
        _liq_intent(_iid(1117), IntentKind.ADD_LIQUIDITY, {"amount0_desired": 100, "amount1_desired": 100}),
        pool,
        lp_balances,
        low_a_balances,
    ).reason == "INSUFFICIENT_BALANCE"

    low_b_balances = BalanceTable()
    low_b_balances.set(pk, asset0, 10_000)
    low_b_balances.set(pk, asset1, 0)
    assert _process_liquidity_intent(
        _liq_intent(_iid(1118), IntentKind.ADD_LIQUIDITY, {"amount0_desired": 100, "amount1_desired": 100}),
        pool,
        lp_balances,
        low_b_balances,
    ).reason == "INSUFFICIENT_BALANCE"

    assert _process_liquidity_intent(
        _liq_intent(_iid(1119), IntentKind.REMOVE_LIQUIDITY, {}),
        pool,
        lp_balances,
        balances,
    ).reason == "MISSING_PARAMS"
    assert _process_liquidity_intent(
        _liq_intent(_iid(1120), IntentKind.REMOVE_LIQUIDITY, {"lp_amount": 0}),
        pool,
        lp_balances,
        balances,
    ).reason == "INVALID_PARAMS"
    assert _process_liquidity_intent(
        _liq_intent(_iid(1121), IntentKind.REMOVE_LIQUIDITY, {"lp_amount": 1, "amount0_min": False}),
        pool,
        lp_balances,
        balances,
    ).reason == "INVALID_PARAMS"
    assert _process_liquidity_intent(
        _liq_intent(_iid(1122), IntentKind.REMOVE_LIQUIDITY, {"lp_amount": 1, "amount1_min": False}),
        pool,
        lp_balances,
        balances,
    ).reason == "INVALID_PARAMS"

    no_lp = LPTable()
    assert _process_liquidity_intent(
        _liq_intent(_iid(1123), IntentKind.REMOVE_LIQUIDITY, {"lp_amount": 1}),
        pool,
        no_lp,
        balances,
    ).reason == "INSUFFICIENT_LP"

    def _boom_add(*_args: object, **_kwargs: object) -> tuple[int, int, int]:
        raise ValueError("boom_add")

    monkeypatch.setattr(batch_clearing_module, "add_liquidity", _boom_add)
    assert _process_liquidity_intent(
        _liq_intent(_iid(1124), IntentKind.ADD_LIQUIDITY, {"amount0_desired": 100, "amount1_desired": 100}),
        pool,
        lp_balances,
        balances,
    ).reason == "COMPUTATION_ERROR: boom_add"
    monkeypatch.undo()

    def _boom_remove(*_args: object, **_kwargs: object) -> tuple[int, int]:
        raise ValueError("boom_remove")

    monkeypatch.setattr(batch_clearing_module, "remove_liquidity", _boom_remove)
    assert _process_liquidity_intent(
        _liq_intent(_iid(1125), IntentKind.REMOVE_LIQUIDITY, {"lp_amount": 1}),
        pool,
        lp_balances,
        balances,
    ).reason == "COMPUTATION_ERROR: boom_remove"
    monkeypatch.undo()

    assert _process_liquidity_intent(
        _liq_intent(_iid(1126), "MYSTERY_KIND", {}),
        pool,
        lp_balances,
        balances,
    ).reason == "UNKNOWN_INTENT_TYPE"


def test_simulate_swap_reserves_and_ab_helpers_cover_fallbacks() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    reserves = (pool.reserve0, pool.reserve1)

    def _swap(intent_id: str, fields: dict[str, object], kind: object = IntentKind.SWAP_EXACT_IN) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=kind,
            intent_id=intent_id,
            sender_pubkey=pk,
            deadline=9999999999,
            fields={"pool_id": pool_id, **fields},
        )

    assert _simulate_swap_reserves(
        _swap(_iid(1127), {"asset_in": asset0, "asset_out": asset1}, IntentKind.ADD_LIQUIDITY),
        pool,
        reserves,
    ) == (0, 0, reserves)
    assert _simulate_swap_reserves(
        _swap(_iid(1128), {"asset_in": "0x" + "03" * 32, "asset_out": asset1}),
        pool,
        reserves,
    ) == (0, 0, reserves)
    assert _simulate_swap_reserves(
        _swap(_iid(1129), {"asset_in": asset0, "asset_out": asset1, "amount_in": False, "min_amount_out": 1}),
        pool,
        reserves,
    ) == (0, 0, reserves)
    assert _simulate_swap_reserves(
        _swap(_iid(1130), {"asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": False}),
        pool,
        reserves,
    ) == (0, 0, reserves)
    assert _simulate_swap_reserves(
        _swap(_iid(1131), {"asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": -1}),
        pool,
        reserves,
    ) == (0, 0, reserves)

    reverse = _swap(
        _iid(1132),
        {"asset_in": asset1, "asset_out": asset0, "amount_in": 100, "min_amount_out": 1},
    )
    a, b, new_reserves = _simulate_swap_reserves(reverse, pool, reserves)
    assert a == 100
    assert b >= 0
    assert new_reserves != reserves

    key = _ab_ordering_key([reverse], pool, reserves)
    assert key[0] == a
    assert key[2] == (reverse.intent_id,)


def test_non_cpmm_swap_paths_cover_runtime_and_objective_fallbacks(monkeypatch) -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    pool = replace(pool, curve_tag="CUBIC_SUM_V1", curve_params='{"p":1,"q":1}')
    reserves = (pool.reserve0, pool.reserve1)
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 10_000)

    def _swap(intent_id: str, kind: IntentKind, fields: dict[str, object]) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=kind,
            intent_id=intent_id,
            sender_pubkey=pk,
            deadline=9999999999,
            fields={"pool_id": pool_id, **fields},
        )

    exact_in_01 = _swap(
        _iid(1133),
        IntentKind.SWAP_EXACT_IN,
        {"asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 10},
    )
    exact_out_01 = _swap(
        _iid(1134),
        IntentKind.SWAP_EXACT_OUT,
        {"asset_in": asset0, "asset_out": asset1, "amount_out": 50, "max_amount_in": 500},
    )
    exact_in_10 = _swap(
        _iid(1135),
        IntentKind.SWAP_EXACT_IN,
        {"asset_in": asset1, "asset_out": asset0, "amount_in": 120, "min_amount_out": 10},
    )
    exact_out_10 = _swap(
        _iid(1136),
        IntentKind.SWAP_EXACT_OUT,
        {"asset_in": asset1, "asset_out": asset0, "amount_out": 60, "max_amount_in": 600},
    )

    calls: list[tuple[str, int, int, int]] = []

    def _fake_swap_exact_in_for_pool(pool_state: PoolState, *, reserve_in: int, reserve_out: int, amount_in: int) -> tuple[int, tuple[int, int]]:
        assert pool_state.curve_tag == "CUBIC_SUM_V1"
        calls.append(("in", reserve_in, reserve_out, amount_in))
        amount_out = max(1, amount_in - 7)
        return amount_out, (reserve_in + amount_in, max(0, reserve_out - amount_out))

    def _fake_swap_exact_out_for_pool(pool_state: PoolState, *, reserve_in: int, reserve_out: int, amount_out: int) -> tuple[int, tuple[int, int]]:
        assert pool_state.curve_tag == "CUBIC_SUM_V1"
        calls.append(("out", reserve_in, reserve_out, amount_out))
        amount_in = amount_out + 5
        return amount_in, (reserve_in + amount_in, max(0, reserve_out - amount_out))

    monkeypatch.setattr(batch_clearing_module, "swap_exact_in_for_pool", _fake_swap_exact_in_for_pool)
    monkeypatch.setattr(batch_clearing_module, "swap_exact_out_for_pool", _fake_swap_exact_out_for_pool)
    monkeypatch.setattr(batch_clearing_ordering, "swap_exact_in_for_pool", _fake_swap_exact_in_for_pool)
    monkeypatch.setattr(batch_clearing_ordering, "swap_exact_out_for_pool", _fake_swap_exact_out_for_pool)

    fill = _process_swap_intent(exact_in_01, reserves, pool, balances)
    assert fill.action == FillAction.FILL
    assert fill.amount_out_filled == 93

    fill = _process_swap_intent(exact_out_01, reserves, pool, balances)
    assert fill.action == FillAction.FILL
    assert fill.amount_in_filled == 55

    amount_a, surplus_b, new_reserves = _simulate_swap_reserves(exact_in_10, pool, reserves)
    assert amount_a == 120
    assert surplus_b == 103
    assert new_reserves == (1_999_887, 2_000_120)

    fills = clear_batch_single_pool(
        [exact_in_01, exact_out_01, exact_in_10, exact_out_10],
        pool,
        balances,
        LPTable(),
        swap_ordering="greedy_ab_refined",
    )
    assert [fill.action for fill in fills] == [FillAction.FILL] * 4

    ab_exact_in = _eval_ordering_ab([exact_in_01], pool, reserves)
    assert ab_exact_in == (100, 83)

    optimal_exact_out = _order_swaps_optimal_ab_bounded(
        [exact_out_01],
        pool_state=pool,
        balances=balances,
        reserves=reserves,
    )
    assert [intent.intent_id for intent in optimal_exact_out] == [_iid(1134)]
    assert any(tag == "in" for tag, *_rest in calls)
    assert any(tag == "out" for tag, *_rest in calls)


def test_order_swaps_mci_and_refinement_helpers(monkeypatch) -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    _pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    reserves = (pool.reserve0, pool.reserve1)

    def _swap(intent_id: int, fields: dict[str, object]) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(intent_id),
            sender_pubkey=pk,
            deadline=9999999999,
            fields=fields,
        )

    solo = [_swap(1133, {"asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1})]
    assert _order_swaps_mci_ab(solo, pool_state=pool, reserves=reserves) == solo

    many = [
        _swap(1200 + i, {"asset_in": asset0, "asset_out": asset1, "amount_in": 100 + i, "min_amount_out": 1})
        for i in range(19)
    ]
    many_result = _order_swaps_mci_ab(many, pool_state=pool, reserves=reserves)
    assert sorted(it.intent_id for it in many_result) == sorted(it.intent_id for it in many)

    bad_first = [
        _swap(1134, {"asset_in": 7, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1}),
        _swap(1135, {"asset_in": asset0, "asset_out": asset1, "amount_in": 110, "min_amount_out": 1}),
    ]
    assert _order_swaps_mci_ab(bad_first, pool_state=pool, reserves=reserves) == _order_swaps_limit_price(bad_first)

    same_asset = [
        _swap(1136, {"asset_in": asset0, "asset_out": asset0, "amount_in": 100, "min_amount_out": 1}),
        _swap(1137, {"asset_in": asset0, "asset_out": asset0, "amount_in": 110, "min_amount_out": 1}),
    ]
    assert _order_swaps_mci_ab(same_asset, pool_state=pool, reserves=reserves) == _order_swaps_limit_price(same_asset)

    not_in_pool = [
        _swap(1138, {"asset_in": "0x" + "03" * 32, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1}),
        _swap(1139, {"asset_in": "0x" + "03" * 32, "asset_out": asset1, "amount_in": 110, "min_amount_out": 1}),
    ]
    assert _order_swaps_mci_ab(not_in_pool, pool_state=pool, reserves=reserves) == _order_swaps_limit_price(not_in_pool)

    mixed = [
        _swap(1140, {"asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1}),
        _swap(1141, {"asset_in": asset1, "asset_out": asset0, "amount_in": 110, "min_amount_out": 1}),
    ]
    assert _order_swaps_mci_ab(mixed, pool_state=pool, reserves=reserves) == _order_swaps_limit_price(mixed)

    valid = [
        _swap(1142, {"asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1}),
        _swap(1143, {"asset_in": asset0, "asset_out": asset1, "amount_in": 120, "min_amount_out": 1}),
    ]
    valid_result = _order_swaps_mci_ab(valid, pool_state=pool, reserves=reserves)
    assert sorted(it.intent_id for it in valid_result) == sorted(it.intent_id for it in valid)

    order = [valid[0], valid[1]]
    eval_map = {
        (valid[0].intent_id, valid[1].intent_id): (1, 1),
        (valid[1].intent_id, valid[0].intent_id): (2, 2),
    }

    def _eval_stub(ordering: list[Intent], *_args: object) -> tuple[int, int]:
        return eval_map[tuple(it.intent_id for it in ordering)]

    monkeypatch.setattr(batch_clearing_ordering, "_eval_ordering_ab", _eval_stub)
    refined = _refine_b_ordering(order, pool_state=pool, reserves=reserves)
    assert [it.intent_id for it in refined] == [valid[1].intent_id, valid[0].intent_id]
    monkeypatch.undo()

    assert _refine_ab_ordering_global([valid[0]], pool_state=pool, reserves=reserves) == [valid[0]]

    over_cap = valid * 13
    expected_fallback = _refine_b_ordering(over_cap, pool_state=pool, reserves=reserves)
    assert _refine_ab_ordering_global(over_cap, pool_state=pool, reserves=reserves) == expected_fallback

    global_eval_map = {
        (valid[0].intent_id, valid[1].intent_id): (1, 1),
        (valid[1].intent_id, valid[0].intent_id): (2, 3),
    }

    def _global_eval(ordering: list[Intent], *_args: object) -> tuple[int, int]:
        return global_eval_map[tuple(it.intent_id for it in ordering)]

    monkeypatch.setattr(batch_clearing_ordering, "_eval_ordering_ab", _global_eval)
    globally_refined = _refine_ab_ordering_global(order, pool_state=pool, reserves=reserves)
    assert [it.intent_id for it in globally_refined] == [valid[1].intent_id, valid[0].intent_id]


def test_order_swaps_optimal_ab_bounded_fallbacks_and_exact_out_path() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    _pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 10_000)
    reserves = (pool.reserve0, pool.reserve1)

    def _exact_in(intent_id: int, fields: dict[str, object]) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(intent_id),
            sender_pubkey=pk,
            deadline=9999999999,
            fields=fields,
        )

    def _exact_out(intent_id: int, fields: dict[str, object]) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_OUT,
            intent_id=_iid(intent_id),
            sender_pubkey=pk,
            deadline=9999999999,
            fields=fields,
        )

    too_many = [
        _exact_in(1300 + i, {"asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1})
        for i in range(13)
    ]
    assert _order_swaps_optimal_ab_bounded(too_many, pool_state=pool, balances=balances, reserves=reserves) == _order_swaps_limit_price(too_many)

    bad_first_asset = [
        _exact_in(1314, {"asset_in": 7, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1}),
        _exact_in(1315, {"asset_in": asset0, "asset_out": asset1, "amount_in": 110, "min_amount_out": 1}),
    ]
    assert _order_swaps_optimal_ab_bounded(
        bad_first_asset, pool_state=pool, balances=balances, reserves=reserves
    ) == _order_swaps_limit_price(bad_first_asset)

    same_asset = [
        _exact_in(1316, {"asset_in": asset0, "asset_out": asset0, "amount_in": 100, "min_amount_out": 1}),
        _exact_in(1317, {"asset_in": asset0, "asset_out": asset0, "amount_in": 110, "min_amount_out": 1}),
    ]
    assert _order_swaps_optimal_ab_bounded(
        same_asset, pool_state=pool, balances=balances, reserves=reserves
    ) == _order_swaps_limit_price(same_asset)

    out_of_pool = [
        _exact_in(1318, {"asset_in": "0x" + "03" * 32, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1}),
        _exact_in(1319, {"asset_in": "0x" + "03" * 32, "asset_out": asset1, "amount_in": 110, "min_amount_out": 1}),
    ]
    assert _order_swaps_optimal_ab_bounded(
        out_of_pool, pool_state=pool, balances=balances, reserves=reserves
    ) == _order_swaps_limit_price(out_of_pool)

    reverse_same_direction = [
        _exact_in(1320, {"asset_in": asset1, "asset_out": asset0, "amount_in": 100, "min_amount_out": 1}),
        _exact_in(1321, {"asset_in": asset1, "asset_out": asset0, "amount_in": 110, "min_amount_out": 1}),
    ]
    reverse_result = _order_swaps_optimal_ab_bounded(
        reverse_same_direction, pool_state=pool, balances=balances, reserves=reserves
    )
    assert sorted(it.intent_id for it in reverse_result) == sorted(it.intent_id for it in reverse_same_direction)

    invalid_exact_in = [
        _exact_in(1322, {"asset_in": asset0, "asset_out": asset1, "amount_in": False, "min_amount_out": 1}),
        _exact_in(1323, {"asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": False}),
    ]
    invalid_result = _order_swaps_optimal_ab_bounded(
        invalid_exact_in, pool_state=pool, balances=balances, reserves=reserves
    )
    assert sorted(it.intent_id for it in invalid_result) == sorted(it.intent_id for it in invalid_exact_in)

    exact_outs = [
        _exact_out(1324, {"asset_in": asset0, "asset_out": asset1, "amount_out": 100, "max_amount_in": 500}),
        _exact_out(1325, {"asset_in": asset0, "asset_out": asset1, "amount_out": 110, "max_amount_in": 600}),
    ]
    exact_out_result = _order_swaps_optimal_ab_bounded(
        exact_outs, pool_state=pool, balances=balances, reserves=reserves
    )
    assert sorted(it.intent_id for it in exact_out_result) == sorted(it.intent_id for it in exact_outs)

    invalid_exact_out_amount = [
        _exact_out(1326, {"asset_in": asset0, "asset_out": asset1, "amount_out": False, "max_amount_in": 500}),
        _exact_out(1327, {"asset_in": asset0, "asset_out": asset1, "amount_out": 110, "max_amount_in": 600}),
    ]
    invalid_exact_out_amount_result = _order_swaps_optimal_ab_bounded(
        invalid_exact_out_amount, pool_state=pool, balances=balances, reserves=reserves
    )
    assert sorted(it.intent_id for it in invalid_exact_out_amount_result) == sorted(
        it.intent_id for it in invalid_exact_out_amount
    )

    invalid_exact_out_max = [
        _exact_out(1328, {"asset_in": asset0, "asset_out": asset1, "amount_out": 100, "max_amount_in": False}),
        _exact_out(1329, {"asset_in": asset0, "asset_out": asset1, "amount_out": 110, "max_amount_in": 600}),
    ]
    invalid_exact_out_max_result = _order_swaps_optimal_ab_bounded(
        invalid_exact_out_max, pool_state=pool, balances=balances, reserves=reserves
    )
    assert sorted(it.intent_id for it in invalid_exact_out_max_result) == sorted(
        it.intent_id for it in invalid_exact_out_max
    )

    low_balance_table = BalanceTable()
    low_balance_table.set(pk, asset0, 1)
    low_balance_table.set(pk, asset1, 10_000)
    low_balance_result = _order_swaps_optimal_ab_bounded(
        exact_outs, pool_state=pool, balances=low_balance_table, reserves=reserves
    )
    assert sorted(it.intent_id for it in low_balance_result) == sorted(it.intent_id for it in exact_outs)

    slippage_exact_outs = [
        _exact_out(1330, {"asset_in": asset0, "asset_out": asset1, "amount_out": 100, "max_amount_in": 1}),
        _exact_out(1331, {"asset_in": asset0, "asset_out": asset1, "amount_out": 110, "max_amount_in": 1}),
    ]
    slippage_exact_out_result = _order_swaps_optimal_ab_bounded(
        slippage_exact_outs, pool_state=pool, balances=balances, reserves=reserves
    )
    assert sorted(it.intent_id for it in slippage_exact_out_result) == sorted(
        it.intent_id for it in slippage_exact_outs
    )


def test_order_swaps_optimal_ab_subset_dp_matches_bruteforce_when_forced(monkeypatch) -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    _pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=5_000,
        amount1=7_000,
        fee_bps=37,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 1_000)
    reserves = (pool.reserve0, pool.reserve1)

    def _exact_in(intent_id: int, amount_in: int, min_amount_out: int) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(intent_id),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": amount_in,
                "min_amount_out": min_amount_out,
            },
        )

    intents = [
        _exact_in(1410, 80, 105),
        _exact_in(1411, 35, 45),
        _exact_in(1412, 120, 155),
        _exact_in(1413, 60, 80),
        _exact_in(1414, 25, 34),
        _exact_in(1415, 100, 128),
    ]
    brute_order = _order_swaps_optimal_ab_bounded(intents, pool_state=pool, balances=balances, reserves=reserves)

    monkeypatch.setattr(batch_clearing_ab_order, "_MAX_AB_BRUTE_FORCE_EXACT_N", 0)
    dp_order = _order_swaps_optimal_ab_bounded(intents, pool_state=pool, balances=balances, reserves=reserves)

    assert [intent.intent_id for intent in dp_order] == [intent.intent_id for intent in brute_order]


def test_order_swaps_optimal_ab_uses_subset_dp_above_small_bruteforce_threshold(monkeypatch) -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    _pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    reserves = (pool.reserve0, pool.reserve1)

    def _exact_in(intent_id: int) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(intent_id),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={"asset_in": asset0, "asset_out": asset1, "amount_in": 100 + intent_id, "min_amount_out": 1},
        )

    intents = [_exact_in(1420 + i) for i in range(9)]
    calls: list[int] = []

    def _fake_subset_dp(order: list[Intent], context: object) -> tuple[Intent, ...]:
        calls.append(len(order))
        return tuple(reversed(order))

    monkeypatch.setattr(batch_clearing_ab_order, "_best_order_by_objective_subset_dp", _fake_subset_dp)
    result = _order_swaps_optimal_ab_bounded(intents, pool_state=pool, balances=balances, reserves=reserves)

    assert calls == [9]
    assert [intent.intent_id for intent in result] == [intent.intent_id for intent in reversed(intents)]


def test_order_swaps_optimal_ab_bounded_non_cpmm_objective_paths(monkeypatch) -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    _pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    pool = replace(pool, curve_tag="CUBIC_SUM_V1", curve_params='{"p":1,"q":1}')
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 10_000)
    reserves = (pool.reserve0, pool.reserve1)

    exact_in = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1332),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 10},
    )
    exact_in_2 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1334),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset_in": asset0, "asset_out": asset1, "amount_in": 120, "min_amount_out": 20},
    )
    exact_out = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(1333),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset_in": asset0, "asset_out": asset1, "amount_out": 50, "max_amount_in": 500},
    )
    exact_out_2 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(1335),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset_in": asset0, "asset_out": asset1, "amount_out": 60, "max_amount_in": 600},
    )

    monkeypatch.setattr(
        batch_clearing_ordering,
        "swap_exact_in_for_pool",
        lambda *_args, **_kwargs: (93, (2_000_100, 1_999_907)),
    )
    result = _order_swaps_optimal_ab_bounded(
        [exact_in, exact_in_2], pool_state=pool, balances=balances, reserves=reserves
    )
    assert sorted(it.intent_id for it in result) == sorted([exact_in.intent_id, exact_in_2.intent_id])

    monkeypatch.setattr(
        batch_clearing_ordering,
        "swap_exact_out_for_pool",
        lambda *_args, **_kwargs: (55, (2_000_055, 1_999_950)),
    )
    result = _order_swaps_optimal_ab_bounded(
        [exact_out, exact_out_2], pool_state=pool, balances=balances, reserves=reserves
    )
    assert sorted(it.intent_id for it in result) == sorted([exact_out.intent_id, exact_out_2.intent_id])

    def _boom(*_args: object, **_kwargs: object) -> object:
        raise ValueError("boom")

    monkeypatch.setattr(batch_clearing_ordering, "swap_exact_out_for_pool", _boom)
    result = _order_swaps_optimal_ab_bounded(
        [exact_out, exact_out_2], pool_state=pool, balances=balances, reserves=reserves
    )
    assert sorted(it.intent_id for it in result) == sorted([exact_out.intent_id, exact_out_2.intent_id])


def test_cow_pair_netting_direct_helper_fallbacks_and_clear_batch_mci_path() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 10_000)

    weird = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(1326),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": asset0, "asset_out": asset1, "amount_out": 100, "max_amount_in": 500},
    )
    bad_asset = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1327),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": 7, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1},
    )
    bad_amount = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1328),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": asset0, "asset_out": asset1, "amount_in": False, "min_amount_out": 1},
    )
    bad_min = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1329),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": False},
    )
    bad_recipient = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1330),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1, "recipient": ""},
    )
    out_of_pair = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1331),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": "0x" + "03" * 32, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1},
    )
    wrong_pool = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1334),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": "0x" + "bb" * 32, "asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1},
    )

    fills, remaining = _cow_pair_netting_exact_in_v1(
        [weird, bad_asset, bad_amount, bad_min, bad_recipient, out_of_pair, wrong_pool],
        pool_state=pool,
        balances=balances,
    )
    assert fills == []
    assert [it.intent_id for it in remaining] == sorted(
        it.intent_id for it in [weird, bad_asset, bad_amount, bad_min, bad_recipient, out_of_pair, wrong_pool]
    )

    mci_intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1332),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={"pool_id": pool_id, "asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1},
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_OUT,
            intent_id=_iid(1333),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={"pool_id": pool_id, "asset_in": asset0, "asset_out": asset1, "amount_out": 100, "max_amount_in": 500},
        ),
    ]
    fills = clear_batch_single_pool(
        mci_intents,
        pool,
        balances,
        LPTable(),
        swap_ordering="mci_ab_global",
    )
    assert sorted(fill.intent_id for fill in fills) == [_iid(1332), _iid(1333)]

    many_side_01 = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1340 + i),
            sender_pubkey="0x" + f"{i + 1:02x}" * 48,
            deadline=9999999999,
            fields={"pool_id": pool_id, "asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1},
        )
        for i in range(5)
    ]
    many_side_10 = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1350 + i),
            sender_pubkey="0x" + f"{i + 16:02x}" * 48,
            deadline=9999999999,
            fields={"pool_id": pool_id, "asset_in": asset1, "asset_out": asset0, "amount_in": 100, "min_amount_out": 1},
        )
        for i in range(5)
    ]
    many_balances = BalanceTable()
    for intent in many_side_01:
        many_balances.set(intent.sender_pubkey, asset0, 1_000)
    for intent in many_side_10:
        many_balances.set(intent.sender_pubkey, asset1, 1_000)
    many_fills, many_remaining = _cow_pair_netting_exact_in_v1(
        many_side_01 + many_side_10,
        pool_state=pool,
        balances=many_balances,
    )
    assert len(many_fills) == 10
    assert many_remaining == []


def test_apply_settlement_additional_event_balance_and_lp_branches() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[BalanceDelta(pubkey=pk, asset=asset0, delta_add=0, delta_sub=5)],
        reserve_deltas=[],
        lp_deltas=[],
        events=[{"type": "NOT_CREATE_POOL"}],
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10)
    apply_settlement(settlement, balances, {pool_id: pool}, None)
    assert balances.get(pk, asset0) == 5

    zero_net_balance = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[
            BalanceDelta(pubkey=pk, asset=asset0, delta_add=5, delta_sub=0),
            BalanceDelta(pubkey=pk, asset=asset0, delta_add=0, delta_sub=5),
        ],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    zero_balances = BalanceTable()
    zero_balances.set(pk, asset0, 10)
    apply_settlement(zero_net_balance, zero_balances, {pool_id: pool}, LPTable())
    assert zero_balances.get(pk, asset0) == 10

    duplicate_event = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=[
            {
                "type": "CREATE_POOL",
                "pool_id": pool_id,
                "asset0": asset0,
                "asset1": asset1,
                "fee_bps": 30,
                "curve_tag": "CPMM",
                "curve_params": "",
                "status": "ACTIVE",
                "created_at": 0,
            }
        ],
    )
    try:
        apply_settlement(duplicate_event, BalanceTable(), {pool_id: pool}, LPTable())
    except ValueError as exc:
        assert str(exc) == f"Pool already exists: {pool_id}"
    else:
        assert False, "expected duplicate pool create to raise"

    wrong_asset_settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[ReserveDelta(pool_id=pool_id, asset="0x" + "03" * 32, delta_add=1, delta_sub=0)],
        lp_deltas=[],
        events=None,
    )
    try:
        apply_settlement(wrong_asset_settlement, BalanceTable(), {pool_id: pool}, LPTable())
    except ValueError as exc:
        assert str(exc) == f"Asset {'0x' + '03' * 32} not in pool {pool_id}"
    else:
        assert False, "expected wrong reserve asset to raise"

    lp_negative_with_balances = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=pk, pool_id=pool_id, delta_add=0, delta_sub=1)],
        events=None,
    )
    lp_balances = LPTable()
    lp_balances.set(pk, pool_id, 2)
    apply_settlement(lp_negative_with_balances, BalanceTable(), {pool_id: replace(pool, lp_supply=5)}, lp_balances)
    assert lp_balances.get(pk, pool_id) == 1

    zero_net_lp = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[
            LPDelta(pubkey=pk, pool_id=pool_id, delta_add=1, delta_sub=0),
            LPDelta(pubkey=pk, pool_id=pool_id, delta_add=0, delta_sub=1),
        ],
        events=None,
    )
    zero_lp = LPTable()
    zero_lp.set(pk, pool_id, 2)
    apply_settlement(zero_net_lp, BalanceTable(), {pool_id: replace(pool, lp_supply=5)}, zero_lp)
    assert zero_lp.get(pk, pool_id) == 2


def test_validate_settlement_ignores_non_create_pool_events() -> None:
    ok, err = validate_settlement(
        Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=[],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            events=[{"type": "NOT_CREATE_POOL"}],
        ),
        BalanceTable(),
        {},
        LPTable(),
    )
    assert ok is True
    assert err is None


def test_clear_batch_single_pool_rejected_liquidity_exercises_non_fill_path() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10)
    balances.set(pk, asset1, 10)
    add_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(1360),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "amount0_desired": 100, "amount1_desired": 100},
    )
    fills = clear_batch_single_pool([add_intent], pool, balances, LPTable(), swap_ordering="limit_price")
    assert len(fills) == 1
    assert fills[0].action == FillAction.REJECT


def test_clear_batch_single_pool_rejects_malformed_liquidity_fill_from_factory(monkeypatch) -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    add_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(1367),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "amount0_desired": 100, "amount1_desired": 100},
    )

    def _bad_process_liquidity_intent(*_args: object, **_kwargs: object) -> Fill:
        return Fill(
            intent_id=add_intent.intent_id,
            action=FillAction.FILL,
            amount0_used=False,
            amount1_used=100,
            lp_minted=100,
        )

    monkeypatch.setattr(batch_clearing_module, "_process_liquidity_intent", _bad_process_liquidity_intent)
    with pytest.raises(TypeError, match="ADD_LIQUIDITY fill.amount0_used must be int"):
        clear_batch_single_pool([add_intent], pool, balances, LPTable(), swap_ordering="limit_price")


def test_clear_batch_single_pool_handles_successful_liquidity_and_reverse_exact_out() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, lp_minted = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    lp_balances = LPTable()
    lp_balances.set(pk, pool_id, lp_minted)

    reverse_exact_out = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(1364),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": asset1, "asset_out": asset0, "amount_out": 100, "max_amount_in": 500},
    )
    add_liq = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(1365),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "amount0_desired": 100, "amount1_desired": 100, "amount0_min": 0, "amount1_min": 0},
    )
    remove_liq = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(1366),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "lp_amount": 10, "amount0_min": 0, "amount1_min": 0},
    )
    fills = clear_batch_single_pool(
        [reverse_exact_out, add_liq, remove_liq],
        pool,
        balances,
        lp_balances,
        swap_ordering="limit_price",
    )
    by_id = {fill.intent_id: fill for fill in fills}
    assert by_id[reverse_exact_out.intent_id].action == FillAction.FILL
    assert by_id[add_liq.intent_id].action == FillAction.FILL
    assert by_id[remove_liq.intent_id].action == FillAction.FILL


def test_get_limit_price_exact_out_zero_and_unknown_kind() -> None:
    exact_out = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(1361),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields={"amount_out": 100, "max_amount_in": 200},
    )
    assert _get_limit_price(exact_out) == (100 * 10**18) // 200

    zero_max = replace(exact_out, intent_id=_iid(1362), fields={"amount_out": 100, "max_amount_in": 0})
    assert _get_limit_price(zero_max) == 0

    unknown = Intent(
        module="TauSwap",
        version="0.1",
        kind="MYSTERY_KIND",
        intent_id=_iid(1363),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields={},
    )
    assert _get_limit_price(unknown) == 0


def test_order_swaps_optimal_ab_bounded_exact_out_exception_path(monkeypatch) -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    _pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    reserves = (pool.reserve0, pool.reserve1)
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_OUT,
            intent_id=_iid(1367),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={"asset_in": asset0, "asset_out": asset1, "amount_out": 100, "max_amount_in": 500},
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_OUT,
            intent_id=_iid(1368),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={"asset_in": asset0, "asset_out": asset1, "amount_out": 110, "max_amount_in": 600},
        ),
    ]

    def _boom(*_args: object, **_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise ValueError("boom")

    monkeypatch.setattr(batch_clearing_ordering, "swap_exact_out_for_pool", _boom)
    result = _order_swaps_optimal_ab_bounded(intents, pool_state=pool, balances=balances, reserves=reserves)
    assert sorted(it.intent_id for it in result) == sorted(it.intent_id for it in intents)


def test_order_swaps_optimal_ab_bounded_skips_unknown_kind_in_objective_loop() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    _pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    reserves = (pool.reserve0, pool.reserve1)

    unknown = Intent(
        module="TauSwap",
        version="0.1",
        kind="MYSTERY_KIND",
        intent_id=_iid(1369),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset_in": asset0, "asset_out": asset1},
    )
    exact_out = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(1370),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset_in": asset0, "asset_out": asset1, "amount_out": 100, "max_amount_in": 500},
    )

    result = _order_swaps_optimal_ab_bounded(
        [unknown, exact_out],
        pool_state=pool,
        balances=balances,
        reserves=reserves,
    )
    assert sorted(it.intent_id for it in result) == [unknown.intent_id, exact_out.intent_id]


def test_cow_pair_netting_bruteforce_prunes_overdrawn_x_sender() -> None:
    pk_a = "0x" + "11" * 48
    pk_b = "0x" + "22" * 48
    pk_c = "0x" + "33" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool = PoolState(
        pool_id="0x" + "aa" * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(pk_a, asset0, 100)
    balances.set(pk_b, asset1, 100)
    balances.set(pk_c, asset1, 100)

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1371),
            sender_pubkey=pk_a,
            deadline=9999999999,
            fields={"pool_id": pool.pool_id, "asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 50},
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1372),
            sender_pubkey=pk_a,
            deadline=9999999999,
            fields={"pool_id": pool.pool_id, "asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 50},
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1373),
            sender_pubkey=pk_b,
            deadline=9999999999,
            fields={"pool_id": pool.pool_id, "asset_in": asset1, "asset_out": asset0, "amount_in": 100, "min_amount_out": 50},
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1374),
            sender_pubkey=pk_c,
            deadline=9999999999,
            fields={"pool_id": pool.pool_id, "asset_in": asset1, "asset_out": asset0, "amount_in": 100, "min_amount_out": 50},
        ),
    ]

    fills, remaining = _cow_pair_netting_exact_in_v1(intents, pool_state=pool, balances=balances)

    assert len(fills) == 2
    assert [fill.intent_id for fill in fills] == [_iid(1371), _iid(1373)]
    assert sorted(it.intent_id for it in remaining) == [_iid(1372), _iid(1374)]


def test_cow_pair_netting_bruteforce_tracks_used_y_and_sender_balance() -> None:
    pk_a = "0x" + "11" * 48
    pk_b = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool = PoolState(
        pool_id="0x" + "ab" * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(pk_a, asset0, 200)
    balances.set(pk_b, asset1, 100)

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1375),
            sender_pubkey=pk_a,
            deadline=9999999999,
            fields={"pool_id": pool.pool_id, "asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 50},
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1376),
            sender_pubkey=pk_a,
            deadline=9999999999,
            fields={"pool_id": pool.pool_id, "asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 50},
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1377),
            sender_pubkey=pk_b,
            deadline=9999999999,
            fields={"pool_id": pool.pool_id, "asset_in": asset1, "asset_out": asset0, "amount_in": 100, "min_amount_out": 50},
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1378),
            sender_pubkey=pk_b,
            deadline=9999999999,
            fields={"pool_id": pool.pool_id, "asset_in": asset1, "asset_out": asset0, "amount_in": 100, "min_amount_out": 50},
        ),
    ]

    fills, remaining = _cow_pair_netting_exact_in_v1(intents, pool_state=pool, balances=balances)

    assert len(fills) == 2
    assert [fill.intent_id for fill in fills] == [_iid(1375), _iid(1377)]
    assert sorted(it.intent_id for it in remaining) == [_iid(1376), _iid(1378)]


def test_cow_pair_netting_bruteforce_tie_breaks_to_smallest_pair_ids() -> None:
    pk_x1 = "0x" + "31" * 48
    pk_x2 = "0x" + "32" * 48
    pk_y1 = "0x" + "41" * 48
    pk_y2 = "0x" + "42" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool = PoolState(
        pool_id="0x" + "ad" * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    for sender in (pk_x1, pk_x2):
        balances.set(sender, asset0, 100)
    balances.set(pk_y1, asset1, 80)
    balances.set(pk_y2, asset1, 120)

    def _swap(intent_id: int, sender: str, asset_in: str, asset_out: str, amount_in: int) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(intent_id),
            sender_pubkey=sender,
            deadline=9999999999,
            fields={"pool_id": pool.pool_id, "asset_in": asset_in, "asset_out": asset_out, "amount_in": amount_in, "min_amount_out": 0},
        )

    intents = [
        _swap(1379, pk_x2, asset0, asset1, 100),
        _swap(1375, pk_x1, asset0, asset1, 100),
        _swap(1378, pk_y2, asset1, asset0, 120),
        _swap(1376, pk_y1, asset1, asset0, 80),
    ]

    fills, remaining = _cow_pair_netting_exact_in_v1(intents, pool_state=pool, balances=balances)

    by_id = {fill.intent_id: fill for fill in fills}
    assert by_id[_iid(1375)].amount_out_filled == 80
    assert by_id[_iid(1379)].amount_out_filled == 120
    assert by_id[_iid(1376)].amount_out_filled == 100
    assert by_id[_iid(1378)].amount_out_filled == 100
    assert remaining == []


def test_cow_assignment_matches_bruteforce_pair_id_tie_on_uncoupled_surface() -> None:
    from src.core.batch_clearing_cow_search import (
        _CowSelectionContext,
        _cow_pair_selection_key,
        _partition_cow_candidates,
        _select_cow_pairs_assignment,
        _select_cow_pairs_bruteforce,
    )

    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool = PoolState(
        pool_id="0x" + "ae" * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()

    def _swap(intent_id: int, sender: str, asset_in: str, asset_out: str, amount_in: int, min_amount_out: int) -> Intent:
        balances.set(sender, asset_in, amount_in)
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(intent_id),
            sender_pubkey=sender,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset_in,
                "asset_out": asset_out,
                "amount_in": amount_in,
                "min_amount_out": min_amount_out,
            },
        )

    intents = [
        _swap(2001, "0x" + "61" * 48, asset0, asset1, 100, 40),
        _swap(2002, "0x" + "62" * 48, asset0, asset1, 120, 40),
        _swap(2003, "0x" + "63" * 48, asset1, asset0, 100, 40),
        _swap(2004, "0x" + "64" * 48, asset1, asset0, 120, 40),
    ]
    partition = _partition_cow_candidates(intents, pool)
    context = _CowSelectionContext(balances=balances, asset0=asset0, asset1=asset1)

    brute_pairs = _select_cow_pairs_bruteforce(partition.side_01, partition.side_10, context=context)
    assignment_pairs = _select_cow_pairs_assignment(partition.side_01, partition.side_10, context=context)

    assert _cow_pair_selection_key(assignment_pairs) == _cow_pair_selection_key(brute_pairs)


def test_cow_pair_netting_capacity_dp_filters_balance_and_feasibility() -> None:
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool = PoolState(
        pool_id="0x" + "ac" * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()

    def _swap(intent_id: int, sender: str, asset_in: str, asset_out: str, amount_in: int, min_amount_out: int) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(intent_id),
            sender_pubkey=sender,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset_in,
                "asset_out": asset_out,
                "amount_in": amount_in,
                "min_amount_out": min_amount_out,
            },
        )

    sx1 = "0x" + "41" * 48
    sx2 = "0x" + "42" * 48
    sx3 = "0x" + "43" * 48
    sx4 = "0x" + "44" * 48
    sx5 = "0x" + "45" * 48
    sy1 = "0x" + "51" * 48
    sy2 = "0x" + "52" * 48
    sy3 = "0x" + "53" * 48
    sy4 = "0x" + "54" * 48

    for sender, amount in ((sx1, 100), (sx2, 100), (sx3, 100), (sx4, 100), (sx5, 100)):
        balances.set(sender, asset0, amount)
    for sender, amount in ((sy1, 100), (sy2, 0), (sy3, 100), (sy4, 100)):
        balances.set(sender, asset1, amount)

    intents = [
        _swap(1380, sx1, asset0, asset1, 150, 90),
        _swap(1381, sx2, asset0, asset1, 100, 80),
        _swap(1382, sx3, asset0, asset1, 100, 300),
        _swap(1383, sx4, asset0, asset1, 100, 50),
        _swap(1384, sx5, asset0, asset1, 100, 40),
        _swap(1385, sy1, asset1, asset0, 100, 50),
        _swap(1386, sy2, asset1, asset0, 100, 50),
        _swap(1387, sy3, asset1, asset0, 10, 200),
        _swap(1388, sy4, asset1, asset0, 10, 200),
    ]

    fills, remaining = _cow_pair_netting_exact_in_v1(intents, pool_state=pool, balances=balances)

    assert [fill.intent_id for fill in fills] == [_iid(1384), _iid(1385)]
    assert sorted(it.intent_id for it in remaining) == sorted(
        [_iid(1380), _iid(1381), _iid(1382), _iid(1383), _iid(1386), _iid(1387), _iid(1388)]
    )


def test_cow_pair_netting_capacity_dp_beats_greedy_for_coupled_sender() -> None:
    from src.core.batch_clearing_cow_search import (
        _CowSelectionContext,
        _assignment_balance_safe,
        _cow_pair_selection_key,
        _is_better_cow_pair_key,
        _partition_cow_candidates,
        _select_cow_pairs,
        _select_cow_pairs_bruteforce,
        _select_cow_pairs_capacity_dp,
        _select_cow_pairs_greedy,
    )

    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool = PoolState(
        pool_id="0x" + "af" * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    coupled_sender = "0x" + "91" * 48
    balances.set(coupled_sender, asset0, 200)
    balances.set("0x" + "a1" * 48, asset1, 90)
    balances.set("0x" + "a2" * 48, asset1, 200)

    def _swap(intent_id: int, sender: str, asset_in: str, asset_out: str, amount_in: int, min_amount_out: int) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(intent_id),
            sender_pubkey=sender,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset_in,
                "asset_out": asset_out,
                "amount_in": amount_in,
                "min_amount_out": min_amount_out,
            },
        )

    intents = [
        _swap(1410, coupled_sender, asset0, asset1, 100, 90),
        _swap(1411, coupled_sender, asset0, asset1, 200, 80),
        _swap(1412, "0x" + "a1" * 48, asset1, asset0, 90, 100),
        _swap(1413, "0x" + "a2" * 48, asset1, asset0, 200, 190),
        _swap(1414, "0x" + "92" * 48, asset0, asset1, 10, 1_000),
        _swap(1415, "0x" + "93" * 48, asset0, asset1, 10, 1_000),
        _swap(1416, "0x" + "94" * 48, asset0, asset1, 10, 1_000),
        _swap(1417, "0x" + "a3" * 48, asset1, asset0, 10, 1_000),
        _swap(1418, "0x" + "a4" * 48, asset1, asset0, 10, 1_000),
    ]
    for sender in ("0x" + "92" * 48, "0x" + "93" * 48, "0x" + "94" * 48):
        balances.set(sender, asset0, 10)
    for sender in ("0x" + "a3" * 48, "0x" + "a4" * 48):
        balances.set(sender, asset1, 10)

    partition = _partition_cow_candidates(intents, pool)
    context = _CowSelectionContext(balances=balances, asset0=asset0, asset1=asset1)

    assert not _assignment_balance_safe(partition.side_01, partition.side_10, context=context)
    greedy_pairs = _select_cow_pairs_greedy(partition.side_01, partition.side_10, context=context)
    dp_pairs = _select_cow_pairs_capacity_dp(partition.side_01, partition.side_10, context=context)
    brute_pairs = _select_cow_pairs_bruteforce(partition.side_01, partition.side_10, context=context)
    selected_pairs = _select_cow_pairs(partition.side_01, partition.side_10, context=context)

    assert _cow_pair_selection_key(dp_pairs) == _cow_pair_selection_key(brute_pairs)
    assert _cow_pair_selection_key(selected_pairs) == _cow_pair_selection_key(brute_pairs)
    assert _is_better_cow_pair_key(_cow_pair_selection_key(dp_pairs), _cow_pair_selection_key(greedy_pairs))
    assert {candidate.intent.intent_id for pair in selected_pairs for candidate in pair} == {_iid(1411), _iid(1413)}


def test_cow_pair_netting_assignment_beats_greedy_above_old_cap() -> None:
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool = PoolState(
        pool_id="0x" + "ae" * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()

    def _swap(intent_id: int, sender: str, asset_in: str, asset_out: str, amount_in: int, min_amount_out: int) -> Intent:
        balances.set(sender, asset_in, amount_in)
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(intent_id),
            sender_pubkey=sender,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset_in,
                "asset_out": asset_out,
                "amount_in": amount_in,
                "min_amount_out": min_amount_out,
            },
        )

    x_high = _swap(1390, "0x" + "61" * 48, asset0, asset1, 100, 80)
    x_low = _swap(1391, "0x" + "62" * 48, asset0, asset1, 50, 80)
    y_small = _swap(1392, "0x" + "71" * 48, asset1, asset0, 80, 50)
    y_hard = _swap(1393, "0x" + "72" * 48, asset1, asset0, 100, 90)
    unmatched = [
        _swap(1394, "0x" + "63" * 48, asset0, asset1, 10, 1_000),
        _swap(1395, "0x" + "64" * 48, asset0, asset1, 10, 1_000),
        _swap(1396, "0x" + "65" * 48, asset0, asset1, 10, 1_000),
        _swap(1397, "0x" + "73" * 48, asset1, asset0, 10, 1_000),
        _swap(1398, "0x" + "74" * 48, asset1, asset0, 10, 1_000),
    ]

    fills, remaining = _cow_pair_netting_exact_in_v1(
        [x_high, x_low, y_small, y_hard, *unmatched],
        pool_state=pool,
        balances=balances,
    )

    by_id = {fill.intent_id: fill for fill in fills}
    assert sorted(by_id) == [_iid(1390), _iid(1391), _iid(1392), _iid(1393)]
    assert by_id[_iid(1390)].amount_out_filled == 100
    assert by_id[_iid(1391)].amount_out_filled == 80
    assert by_id[_iid(1392)].amount_out_filled == 50
    assert by_id[_iid(1393)].amount_out_filled == 100
    assert sorted(intent.intent_id for intent in remaining) == [_iid(n) for n in range(1394, 1399)]


def test_apply_settlement_updates_asset1_reserve_branch() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[ReserveDelta(pool_id=pool_id, asset=asset1, delta_add=5, delta_sub=0)],
        lp_deltas=[],
        events=None,
    )
    apply_settlement(settlement, BalanceTable(), {pool_id: pool}, LPTable())
    assert pool.reserve1 == 2_000_005

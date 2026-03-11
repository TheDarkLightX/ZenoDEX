# [TESTER] v1

from __future__ import annotations

from src.core.batch_clearing import (
    _aggregate_balance_deltas_chunked,
    _aggregate_lp_deltas_chunked,
    _aggregate_reserve_deltas_chunked,
    _parse_create_pool_event_payload,
    apply_settlement,
    apply_settlement_pure,
    clear_batch_single_pool,
    compute_settlement,
    validate_settlement,
)
from src.core.liquidity import create_pool
from src.core.settlement import BalanceDelta, LPDelta, ReserveDelta, Settlement
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus


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

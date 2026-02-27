# [TESTER] v1

from __future__ import annotations

from src.core.batch_clearing import compute_settlement
from src.core.batch_clearing import validate_settlement
from src.core.dex import DexConfig, DexState, step as dex_step
from src.core.liquidity import create_pool
from src.core.settlement import BalanceDelta, Fill, FillAction, ReserveDelta, Settlement
from src.core.settlement_strong_validator import validate_settlement_strong
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus, compute_pool_id


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_legacy_validate_allows_k_decrease_but_strong_rejects() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
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
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )

    # Malicious settlement: drains too much output from the pool (k decreases),
    # but keeps reserves non-negative and passes pure conservation checks.
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                amount_in_filled=100,
                amount_out_filled=200,  # impossible under CPMM reserves=(1000,1000) with fee_bps=30
                fee_paid=1,  # any non-negative value; legacy doesn't check
                reserve_in_before=1_000,
                reserve_out_before=1_000,
            )
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk, asset=asset1, delta_add=200, delta_sub=0),
        ],
        reserve_deltas=[
            ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=100, delta_sub=0),
            ReserveDelta(pool_id=pool_id, asset=asset1, delta_add=0, delta_sub=200),
        ],
        lp_deltas=[],
        events=None,
    )

    ok_legacy, err_legacy = validate_settlement(
        settlement=settlement,
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
    )
    assert ok_legacy is True, err_legacy

    ok_strong, err_strong = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok_strong is False
    assert err_strong is not None


def test_dex_step_preserves_created_pool_curve_config() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, expected_pool, _lp_minted = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
        curve_tag="CUBIC_SUM_V1",
        curve_params={"p": 2, "q": 1},
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    state = DexState(balances=balances, pools={}, lp_balances=LPTable())
    config = DexConfig()

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id=_iid(2),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "asset0": asset0,
                "asset1": asset1,
                "fee_bps": 30,
                "amount0": 2_000_000,
                "amount1": 2_000_000,
                "curve_tag": "CUBIC_SUM_V1",
                "curve_params": {"p": 2, "q": 1},
            },
        )
    ]

    res = dex_step(config, state, intents)
    assert res.ok, res.error
    assert res.state is not None
    assert pool_id in res.state.pools

    got_pool = res.state.pools[pool_id]
    assert got_pool.curve_tag == expected_pool.curve_tag
    assert got_pool.curve_params == expected_pool.curve_params


def test_strong_proof_carrying_requires_swap_reserve_witnesses() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(3),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_out": 10,
            "max_amount_in": 1_000,
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={pool_id: pool_state},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )
    assert len(settlement.fills) == 1

    fill = settlement.fills[0]
    assert fill.reserve_in_before is not None
    assert fill.reserve_out_before is not None
    witness_in = int(fill.reserve_in_before)
    witness_out = int(fill.reserve_out_before)

    ok_replay, err_replay = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok_replay is True, err_replay

    # BVA over witness presence/mismatch:
    # - missing witness: proof-carrying must reject
    # - correct witness: proof-carrying must accept
    # - off-by-one witness: proof-carrying must reject

    fill.reserve_in_before = None
    fill.reserve_out_before = None
    ok_pc, err_pc = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok_pc is False
    assert err_pc is not None

    fill.reserve_in_before = witness_in
    fill.reserve_out_before = witness_out
    ok_pc2, err_pc2 = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok_pc2 is True, err_pc2

    fill.reserve_in_before = witness_in + 1
    fill.reserve_out_before = witness_out
    ok_pc3, err_pc3 = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok_pc3 is False
    assert err_pc3 is not None


def test_strong_validator_rejects_nonconserving_cow_netted_settlement() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk0, asset0, 10_000)
    balances.set(pk0, asset1, 0)
    balances.set(pk1, asset0, 0)
    balances.set(pk1, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(10),
        sender_pubkey=pk0,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "recipient": pk1,
        },
    )

    # Malicious settlement: marks a swap as COW_NETTED but does not include any
    # counterparty transfer. This would violate asset conservation if accepted.
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=100,
                amount_out_filled=200,  # created-from-nothing if no offsetting debit exists
                fee_paid=0,
            )
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk0, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk1, asset=asset1, delta_add=200, delta_sub=0),
        ],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok_strong, err_strong = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok_strong is False
    assert err_strong is not None

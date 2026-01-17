# [TESTER] v1

from __future__ import annotations

import importlib.util
import math
import sys
from pathlib import Path
from typing import Any

import pytest

from src.core.cpmm import MIN_LP_LOCK, swap_exact_in
from src.core.liquidity import add_liquidity, create_pool
from src.state.pools import PoolState, PoolStatus


def _import_kernel(module_name: str, rel_path: str) -> Any:
    try:
        return __import__(module_name, fromlist=["*"])
    except ModuleNotFoundError:
        root = Path(__file__).resolve().parents[2]
        abs_path = root / rel_path
        if not abs_path.exists():
            pytest.skip(f"Reference kernel not found at {abs_path}")
        spec = importlib.util.spec_from_file_location(module_name, abs_path)
        assert spec and spec.loader, f"Could not load spec for {module_name} from {abs_path}"
        module = importlib.util.module_from_spec(spec)
        sys.modules[module_name] = module
        spec.loader.exec_module(module)
        return module


cpmm_v7 = _import_kernel("generated.dex_v7_python.cpmm_swap_v7_ref", "generated/dex_v7_python/cpmm_swap_v7_ref.py")
fee_v7 = _import_kernel(
    "generated.dex_v7_python.fee_calculation_v7_ref", "generated/dex_v7_python/fee_calculation_v7_ref.py"
)
lp_mint_v7 = _import_kernel("generated.dex_v7_python.lp_mint_v7_ref", "generated/dex_v7_python/lp_mint_v7_ref.py")
lp_ratio_v7 = _import_kernel(
    "generated.dex_v7_python.lp_ratio_calculator_v7_ref", "generated/dex_v7_python/lp_ratio_calculator_v7_ref.py"
)
breaker_v7 = _import_kernel(
    "generated.dex_v7_python.circuit_breaker_v7_ref", "generated/dex_v7_python/circuit_breaker_v7_ref.py"
)


def test_cpmm_swap_v7_matches_python_core_no_fee() -> None:
    reserves = [1, 2, 10, 25, 100, 1000, 1_000_000]
    for reserve_in in reserves:
        for reserve_out in reserves:
            state = cpmm_v7.State(
                reserve_in_before=reserve_in,
                reserve_in=reserve_in,
                reserve_out_before=reserve_out,
                reserve_out=reserve_out,
            )

            for amount_in in [1, max(1, reserve_in // 2), reserve_in]:
                res = cpmm_v7.step(
                    state,
                    cpmm_v7.Command(tag="swap", args={"amount_in": amount_in, "min_amount_out": 1}),
                )
                if not res.ok:
                    continue
                assert res.state is not None
                assert res.effects is not None

                amount_out, (new_reserve_in, new_reserve_out) = swap_exact_in(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_in=amount_in,
                    fee_bps=0,
                )

                assert int(res.effects["amount_out"]) == amount_out
                assert res.state.reserve_in == new_reserve_in
                assert res.state.reserve_out == new_reserve_out
                assert int(res.effects["k_before"]) == reserve_in * reserve_out
                assert int(res.effects["k_after"]) == new_reserve_in * new_reserve_out


def test_fee_calculation_v7_matches_expected_math_and_accumulates() -> None:
    def _calc(gross_amount: int, fee_bps: int, protocol_fee_share_bps: int) -> tuple[int, int, int, int]:
        fee = (gross_amount * fee_bps + 9999) // 10000
        net = gross_amount - fee
        protocol_fee = (fee * protocol_fee_share_bps) // 10000
        lp_fee = fee - protocol_fee
        return fee, net, protocol_fee, lp_fee

    state = fee_v7.init_state()
    ok, failed = fee_v7.check_invariants(state)
    assert ok, failed

    total_protocol = 0
    total_lp = 0

    cases = [
        (0, 0, 0),
        (1, 1, 0),
        (10, 30, 2500),
        (1234567, 25, 5000),
        (1000000000, 1000, 10000),
    ]
    for gross_amount, fee_bps, protocol_fee_share_bps in cases:
        res = fee_v7.step(
            state,
            fee_v7.Command(
                tag="calculate_fee",
                args={
                    "gross_amount": gross_amount,
                    "fee_bps": fee_bps,
                    "protocol_fee_share_bps": protocol_fee_share_bps,
                },
            ),
        )
        assert res.ok, res.error
        assert res.state is not None
        assert res.effects is not None

        fee, net, protocol_fee, lp_fee = _calc(gross_amount, fee_bps, protocol_fee_share_bps)
        assert int(res.effects["fee"]) == fee
        assert int(res.effects["net_amount"]) == net
        assert int(res.effects["protocol_fee"]) == protocol_fee
        assert int(res.effects["lp_fee"]) == lp_fee
        assert bool(res.effects["fee_split_ok"]) is True
        assert bool(res.effects["net_ok"]) is True

        total_protocol += protocol_fee
        total_lp += lp_fee
        assert res.state.protocol_fees_collected == total_protocol
        assert res.state.lp_fees_collected == total_lp
        assert res.state.total_fees_collected == total_protocol + total_lp

        state = res.state


def test_lp_ratio_calculator_v7_matches_core_add_liquidity_ratio() -> None:
    # Initial pool: use everything, no refunds.
    init_state = lp_ratio_v7.init_state()
    res = lp_ratio_v7.step(init_state, lp_ratio_v7.Command(tag="calculate_optimal", args={"desired0": 5, "desired1": 7}))
    assert res.ok, res.error
    assert res.effects is not None
    assert bool(res.effects["is_initial"]) is True
    assert int(res.effects["optimal0"]) == 5
    assert int(res.effects["optimal1"]) == 7
    assert int(res.effects["refund0"]) == 0
    assert int(res.effects["refund1"]) == 0
    assert bool(res.effects["sum0_ok"]) is True
    assert bool(res.effects["sum1_ok"]) is True

    # Non-initial: match Python core ratio selection.
    pool_state = PoolState(
        pool_id="0x00",
        asset0="A",
        asset1="B",
        reserve0=100,
        reserve1=250,
        fee_bps=0,
        lp_supply=10_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    desired0, desired1 = 50, 10
    used0, used1, _lp_minted = add_liquidity(pool_state, desired0, desired1, 0, 0)
    st = lp_ratio_v7.State(reserve0=pool_state.reserve0, reserve1=pool_state.reserve1)
    res2 = lp_ratio_v7.step(st, lp_ratio_v7.Command(tag="calculate_optimal", args={"desired0": desired0, "desired1": desired1}))
    assert res2.ok, res2.error
    assert res2.effects is not None
    assert int(res2.effects["optimal0"]) == used0
    assert int(res2.effects["optimal1"]) == used1
    assert int(res2.effects["refund0"]) == desired0 - used0
    assert int(res2.effects["refund1"]) == desired1 - used1


def test_lp_mint_v7_matches_core_create_pool_and_add_liquidity() -> None:
    # Initial mint parity (maps: v7.total_supply == core.lp_supply_total).
    amount0, amount1 = 5000, 7000
    sqrt_product = math.isqrt(amount0 * amount1)
    assert sqrt_product > MIN_LP_LOCK

    s0 = lp_mint_v7.init_state()
    res = lp_mint_v7.step(
        s0,
        lp_mint_v7.Command(tag="mint_initial", args={"amount0": amount0, "amount1": amount1, "sqrt_product": sqrt_product}),
    )
    assert res.ok, res.error
    assert res.state is not None
    assert res.effects is not None

    _pool_id, pool, lp_minted = create_pool(
        asset0="A",
        asset1="B",
        amount0=amount0,
        amount1=amount1,
        fee_bps=0,
        creator_pubkey="creator",
        created_at=0,
    )
    assert int(res.effects["liquidity_minted"]) == lp_minted
    assert int(res.effects["amount0_used"]) == amount0
    assert int(res.effects["amount1_used"]) == amount1
    assert int(res.effects["amount0_refund"]) == 0
    assert int(res.effects["amount1_refund"]) == 0
    assert int(res.effects["total_supply"]) == pool.lp_supply
    assert res.state.locked_liquidity == MIN_LP_LOCK
    assert res.state.reserve0 == pool.reserve0
    assert res.state.reserve1 == pool.reserve1
    assert res.state.lp_supply + res.state.locked_liquidity == pool.lp_supply

    # Subsequent mint parity.
    desired0, desired1 = 1000, 500
    used0, used1, lp_minted_2 = add_liquidity(pool, desired0, desired1, 0, 0)

    v7_state = lp_mint_v7.State(
        reserve0_before=pool.reserve0,
        reserve0=pool.reserve0,
        reserve1_before=pool.reserve1,
        reserve1=pool.reserve1,
        lp_supply_before=pool.lp_supply - MIN_LP_LOCK,
        lp_supply=pool.lp_supply - MIN_LP_LOCK,
        locked_liquidity=MIN_LP_LOCK,
    )
    res2 = lp_mint_v7.step(v7_state, lp_mint_v7.Command(tag="mint", args={"amount0": desired0, "amount1": desired1, "min_liquidity": 0}))
    assert res2.ok, res2.error
    assert res2.state is not None
    assert res2.effects is not None

    assert int(res2.effects["liquidity_minted"]) == lp_minted_2
    assert int(res2.effects["amount0_used"]) == used0
    assert int(res2.effects["amount1_used"]) == used1
    assert int(res2.effects["amount0_refund"]) == desired0 - used0
    assert int(res2.effects["amount1_refund"]) == desired1 - used1

    assert res2.state.reserve0 == pool.reserve0 + used0
    assert res2.state.reserve1 == pool.reserve1 + used1
    assert res2.state.locked_liquidity == MIN_LP_LOCK
    assert res2.state.lp_supply == (pool.lp_supply - MIN_LP_LOCK) + lp_minted_2
    assert int(res2.effects["total_supply"]) == pool.lp_supply + lp_minted_2


def test_circuit_breaker_v7_effects_reflect_post_state() -> None:
    s0 = breaker_v7.init_state()
    res = breaker_v7.step(
        s0,
        breaker_v7.Command(
            tag="add_volume",
            args={"volume": 10, "current_time": 1},
        ),
    )
    assert res.ok, res.error
    assert res.state is not None
    assert res.effects is not None
    assert int(res.effects["volume_after"]) == res.state.volume_accumulated
    assert bool(res.effects["triggered"]) == bool(res.state.breaker_open)
    assert bool(res.effects["can_trade"]) == (not res.state.breaker_open)

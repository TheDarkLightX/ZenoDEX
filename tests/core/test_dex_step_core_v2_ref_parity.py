# [TESTER] v1

from __future__ import annotations

import importlib.util
import math
import sys
from pathlib import Path
from typing import Any, Mapping

import pytest

from src.core import DexConfig, DexState, dex_step
from src.core.settlement import FillAction
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus, compute_pool_id


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


dex_ref = _import_kernel(
    "generated.dex_v8_python.dex_step_core_v2_ref", "generated/dex_v8_python/dex_step_core_v2_ref.py"
)


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


U0 = "0x" + "11" * 48
U1 = "0x" + "22" * 48
LOCK = "0x" + "00" * 48

ASSET_A = "0x" + "01" * 32
ASSET_B = "0x" + "02" * 32
FEE_BPS = 30

POOL_ID = compute_pool_id(ASSET_A, ASSET_B, FEE_BPS)
_PARITY_CONFIG = DexConfig(reject_settlements_with_rejected_intents=False)


def _pk(idx: int) -> str:
    if idx == 0:
        return U0
    if idx == 1:
        return U1
    raise ValueError(f"bad user idx: {idx}")


def _python_state_from_ref(s: dex_ref.State) -> DexState:
    balances = BalanceTable()
    balances.set(U0, ASSET_A, int(s.u0_a))
    balances.set(U0, ASSET_B, int(s.u0_b))
    balances.set(U1, ASSET_A, int(s.u1_a))
    balances.set(U1, ASSET_B, int(s.u1_b))

    pools: dict[str, PoolState] = {}
    lp = LPTable()
    if int(s.pool_initialized) == 1:
        pools[POOL_ID] = PoolState(
            pool_id=POOL_ID,
            asset0=ASSET_A,
            asset1=ASSET_B,
            reserve0=int(s.pool_a),
            reserve1=int(s.pool_b),
            fee_bps=int(s.fee_bps),
            curve_tag="CPMM",
            curve_params="",
            lp_supply=int(s.lp_supply),
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
        if int(s.u0_lp) != 0:
            lp.set(U0, POOL_ID, int(s.u0_lp))
        if int(s.u1_lp) != 0:
            lp.set(U1, POOL_ID, int(s.u1_lp))
        if int(s.lock_lp) != 0:
            lp.set(LOCK, POOL_ID, int(s.lock_lp))

    return DexState(balances=balances, pools=pools, lp_balances=lp)


def _assert_python_matches_ref(ref_state: dex_ref.State, py_state: DexState) -> None:
    pool = py_state.pools.get(POOL_ID)
    py_pool_init = 1 if pool is not None else 0

    assert int(ref_state.pool_initialized) == py_pool_init
    assert py_state.balances.get(U0, ASSET_A) == int(ref_state.u0_a)
    assert py_state.balances.get(U0, ASSET_B) == int(ref_state.u0_b)
    assert py_state.balances.get(U1, ASSET_A) == int(ref_state.u1_a)
    assert py_state.balances.get(U1, ASSET_B) == int(ref_state.u1_b)

    if pool is None:
        assert int(ref_state.pool_a) == 0
        assert int(ref_state.pool_b) == 0
        assert int(ref_state.lp_supply) == 0
        assert py_state.lp_balances.get(U0, POOL_ID) == 0
        assert py_state.lp_balances.get(U1, POOL_ID) == 0
        assert py_state.lp_balances.get(LOCK, POOL_ID) == 0
    else:
        assert pool.fee_bps == int(ref_state.fee_bps)
        assert pool.reserve0 == int(ref_state.pool_a)
        assert pool.reserve1 == int(ref_state.pool_b)
        assert pool.lp_supply == int(ref_state.lp_supply)
        assert py_state.lp_balances.get(U0, POOL_ID) == int(ref_state.u0_lp)
        assert py_state.lp_balances.get(U1, POOL_ID) == int(ref_state.u1_lp)
        assert py_state.lp_balances.get(LOCK, POOL_ID) == int(ref_state.lock_lp)

        # In the core model, all LP lives in {U0,U1,LOCK}.
        assert (
            py_state.lp_balances.get(U0, POOL_ID)
            + py_state.lp_balances.get(U1, POOL_ID)
            + py_state.lp_balances.get(LOCK, POOL_ID)
            == pool.lp_supply
        )

    # Asset conservation (kernel uses explicit total_*_const state vars).
    total_a = py_state.balances.get(U0, ASSET_A) + py_state.balances.get(U1, ASSET_A) + (pool.reserve0 if pool else 0)
    total_b = py_state.balances.get(U0, ASSET_B) + py_state.balances.get(U1, ASSET_B) + (pool.reserve1 if pool else 0)
    assert total_a == int(ref_state.total_a_const)
    assert total_b == int(ref_state.total_b_const)


def _dex_step_single_intent(state: DexState, intent: Intent) -> DexState:
    res = dex_step(DexConfig(), state, [intent])
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _make_intent(kind: IntentKind, sender_idx: int, intent_id: int, fields: Mapping[str, Any]) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id=_iid(intent_id),
        sender_pubkey=_pk(sender_idx),
        deadline=9999999999,
        fields=dict(fields),
    )


def test_dex_step_core_v2_create_pool_bva_parity() -> None:
    # BVA: CREATE_POOL initial mint boundary is floor(sqrt(a*b)) > MIN_LP_LOCK (1000).
    # Kernel domains enforce amount_a/amount_b/sqrt_product >= 1001. We test:
    # - just below: 1000 (should fail)
    # - at: 1001 (should succeed)
    # - just above: 1002 (should succeed)
    amount_cases = [1000, 1001, 1002]

    for creator in [0, 1]:
        for amt in amount_cases:
            ref_pre = dex_ref.init_state()
            py_pre = _python_state_from_ref(ref_pre)

            sqrt_prod = int(math.isqrt(int(amt) * int(amt)))
            ref_cmd = dex_ref.Command(
                tag="create_pool",
                args={"creator": int(creator), "amount_a": int(amt), "amount_b": int(amt), "sqrt_product": sqrt_prod},
            )
            ref_res = dex_ref.step(ref_pre, ref_cmd)

            py_intent = _make_intent(
                IntentKind.CREATE_POOL,
                sender_idx=creator,
                intent_id=1,
                fields={
                    "asset0": ASSET_A,
                    "asset1": ASSET_B,
                    "fee_bps": FEE_BPS,
                    "amount0": int(amt),
                    "amount1": int(amt),
                    "recipient": _pk(creator),  # match kernel's lp_recipient=creator
                },
            )
            py_res = dex_step(_PARITY_CONFIG, py_pre, [py_intent])

            assert py_res.ok, py_res.error
            assert py_res.state is not None
            assert py_res.effects is not None

            settlement = py_res.effects["settlement"]
            action_by_id = dict(settlement.included_intents)
            assert py_intent.intent_id in action_by_id
            expected = FillAction.FILL if ref_res.ok else FillAction.REJECT
            assert action_by_id[py_intent.intent_id] == expected

            if ref_res.ok:
                assert ref_res.state is not None
                _assert_python_matches_ref(ref_res.state, py_res.state)
            else:
                # Rejected intents must be no-ops on the state surface modeled by the kernel.
                _assert_python_matches_ref(ref_pre, py_res.state)


def test_dex_step_core_v2_swap_exact_in_bva_parity() -> None:
    # Setup: create a pool so swap guards are enabled.
    creator = 0
    init_amt = 1_000_000

    ref_s = dex_ref.init_state()
    py_s = _python_state_from_ref(ref_s)

    sqrt_prod = int(math.isqrt(init_amt * init_amt))
    ref_res = dex_ref.step(
        ref_s,
        dex_ref.Command(
            tag="create_pool",
            args={"creator": creator, "amount_a": init_amt, "amount_b": init_amt, "sqrt_product": sqrt_prod},
        ),
    )
    assert ref_res.ok, ref_res.error
    assert ref_res.state is not None
    ref_s = ref_res.state

    py_s = _dex_step_single_intent(
        py_s,
        _make_intent(
            IntentKind.CREATE_POOL,
            sender_idx=creator,
            intent_id=10,
            fields={"asset0": ASSET_A, "asset1": ASSET_B, "fee_bps": FEE_BPS, "amount0": init_amt, "amount1": init_amt},
        ),
    )

    _assert_python_matches_ref(ref_s, py_s)

    # BVA for amount_in boundary at 1: [0,1,2]
    # BVA for min_amount_out boundary at 0: [-1,0,1]
    for trader in [0, 1]:
        for (amount_in, min_out) in [(0, 0), (1, -1), (1, 0), (1, 1), (2, 0)]:
            ref_cmd = dex_ref.Command(
                tag="swap_a_for_b",
                args={"trader": trader, "recipient": trader, "amount_in": int(amount_in), "min_amount_out": int(min_out)},
            )
            ref_res = dex_ref.step(ref_s, ref_cmd)

            py_intent = _make_intent(
                IntentKind.SWAP_EXACT_IN,
                sender_idx=trader,
                intent_id=100 + trader * 10 + amount_in + (min_out + 2),
                fields={
                    "pool_id": POOL_ID,
                    "asset_in": ASSET_A,
                    "asset_out": ASSET_B,
                    "amount_in": int(amount_in),
                    "min_amount_out": int(min_out),
                    "recipient": _pk(trader),
                },
            )
            py_res = dex_step(_PARITY_CONFIG, py_s, [py_intent])

            assert py_res.ok, py_res.error
            assert py_res.state is not None
            assert py_res.effects is not None

            settlement = py_res.effects["settlement"]
            action_by_id = dict(settlement.included_intents)
            assert py_intent.intent_id in action_by_id
            expected = FillAction.FILL if ref_res.ok else FillAction.REJECT
            assert action_by_id[py_intent.intent_id] == expected

            if ref_res.ok:
                assert ref_res.state is not None
                _assert_python_matches_ref(ref_res.state, py_res.state)
            else:
                _assert_python_matches_ref(ref_s, py_res.state)


def test_dex_step_core_v2_swap_exact_out_reserve_boundary_parity() -> None:
    # Setup: create a pool.
    creator = 0
    # Choose the smallest viable pool (>=1001) so (reserve_out - 1) is still fillable under max_amount_in.
    init_amt = 1001

    ref_s = dex_ref.init_state()
    py_s = _python_state_from_ref(ref_s)

    sqrt_prod = int(math.isqrt(init_amt * init_amt))
    ref_res = dex_ref.step(
        ref_s,
        dex_ref.Command(
            tag="create_pool",
            args={"creator": creator, "amount_a": init_amt, "amount_b": init_amt, "sqrt_product": sqrt_prod},
        ),
    )
    assert ref_res.ok, ref_res.error
    assert ref_res.state is not None
    ref_s = ref_res.state

    py_s = _dex_step_single_intent(
        py_s,
        _make_intent(
            IntentKind.CREATE_POOL,
            sender_idx=creator,
            intent_id=20,
            fields={"asset0": ASSET_A, "asset1": ASSET_B, "fee_bps": FEE_BPS, "amount0": init_amt, "amount1": init_amt},
        ),
    )
    _assert_python_matches_ref(ref_s, py_s)

    # Reserve boundary: require amount_out < reserve_out (here reserve_out is pool_b for swap_a_for_b_exact_out).
    reserve_out = init_amt
    amount_out_cases = [reserve_out - 1, reserve_out, reserve_out + 1]

    for trader in [0, 1]:
        for amt_out in amount_out_cases:
            ref_cmd = dex_ref.Command(
                tag="swap_a_for_b_exact_out",
                args={"trader": trader, "recipient": trader, "amount_out": int(amt_out), "max_amount_in": 1_000_000_000},
            )
            ref_res = dex_ref.step(ref_s, ref_cmd)

            py_intent = _make_intent(
                IntentKind.SWAP_EXACT_OUT,
                sender_idx=trader,
                intent_id=200 + trader * 10 + (0 if amt_out == reserve_out - 1 else 1 if amt_out == reserve_out else 2),
                fields={
                    "pool_id": POOL_ID,
                    "asset_in": ASSET_A,
                    "asset_out": ASSET_B,
                    "amount_out": int(amt_out),
                    "max_amount_in": 1_000_000_000,
                    "recipient": _pk(trader),
                },
            )
            py_res = dex_step(_PARITY_CONFIG, py_s, [py_intent])

            assert py_res.ok, py_res.error
            assert py_res.state is not None
            assert py_res.effects is not None

            settlement = py_res.effects["settlement"]
            action_by_id = dict(settlement.included_intents)
            assert py_intent.intent_id in action_by_id
            expected = FillAction.FILL if ref_res.ok else FillAction.REJECT
            assert action_by_id[py_intent.intent_id] == expected

            if ref_res.ok:
                assert ref_res.state is not None
                _assert_python_matches_ref(ref_res.state, py_res.state)
            else:
                _assert_python_matches_ref(ref_s, py_res.state)


def test_dex_step_core_v2_swap_exact_in_bva_parity_b_for_a() -> None:
    # Mirror of swap_a_for_b, swapping B -> A.
    creator = 0
    init_amt = 1_000_000

    ref_s = dex_ref.init_state()
    py_s = _python_state_from_ref(ref_s)

    sqrt_prod = int(math.isqrt(init_amt * init_amt))
    ref_res = dex_ref.step(
        ref_s,
        dex_ref.Command(
            tag="create_pool",
            args={"creator": creator, "amount_a": init_amt, "amount_b": init_amt, "sqrt_product": sqrt_prod},
        ),
    )
    assert ref_res.ok, ref_res.error
    assert ref_res.state is not None
    ref_s = ref_res.state

    py_s = _dex_step_single_intent(
        py_s,
        _make_intent(
            IntentKind.CREATE_POOL,
            sender_idx=creator,
            intent_id=30,
            fields={"asset0": ASSET_A, "asset1": ASSET_B, "fee_bps": FEE_BPS, "amount0": init_amt, "amount1": init_amt},
        ),
    )
    _assert_python_matches_ref(ref_s, py_s)

    # BVA for amount_in boundary at 1: [0,1,2]
    # BVA for min_amount_out boundary at 0: [-1,0,1]
    for trader in [0, 1]:
        for (amount_in, min_out) in [(0, 0), (1, -1), (1, 0), (1, 1), (2, 0)]:
            ref_cmd = dex_ref.Command(
                tag="swap_b_for_a",
                args={"trader": trader, "recipient": trader, "amount_in": int(amount_in), "min_amount_out": int(min_out)},
            )
            ref_res = dex_ref.step(ref_s, ref_cmd)

            py_intent = _make_intent(
                IntentKind.SWAP_EXACT_IN,
                sender_idx=trader,
                intent_id=300 + trader * 10 + amount_in + (min_out + 2),
                fields={
                    "pool_id": POOL_ID,
                    "asset_in": ASSET_B,
                    "asset_out": ASSET_A,
                    "amount_in": int(amount_in),
                    "min_amount_out": int(min_out),
                    "recipient": _pk(trader),
                },
            )
            py_res = dex_step(_PARITY_CONFIG, py_s, [py_intent])

            assert py_res.ok, py_res.error
            assert py_res.state is not None
            assert py_res.effects is not None

            settlement = py_res.effects["settlement"]
            action_by_id = dict(settlement.included_intents)
            assert py_intent.intent_id in action_by_id
            expected = FillAction.FILL if ref_res.ok else FillAction.REJECT
            assert action_by_id[py_intent.intent_id] == expected

            if ref_res.ok:
                assert ref_res.state is not None
                _assert_python_matches_ref(ref_res.state, py_res.state)
            else:
                _assert_python_matches_ref(ref_s, py_res.state)


def test_dex_step_core_v2_add_and_remove_liquidity_bva_parity() -> None:
    # Add/remove liquidity parity for a simple 2-asset CPMM pool.
    creator = 0
    init_amt = 1_000_000

    ref_s = dex_ref.init_state()
    py_s = _python_state_from_ref(ref_s)

    sqrt_prod = int(math.isqrt(init_amt * init_amt))
    ref_res = dex_ref.step(
        ref_s,
        dex_ref.Command(
            tag="create_pool",
            args={"creator": creator, "amount_a": init_amt, "amount_b": init_amt, "sqrt_product": sqrt_prod},
        ),
    )
    assert ref_res.ok, ref_res.error
    assert ref_res.state is not None
    ref_s = ref_res.state

    py_s = _dex_step_single_intent(
        py_s,
        _make_intent(
            IntentKind.CREATE_POOL,
            sender_idx=creator,
            intent_id=40,
            fields={"asset0": ASSET_A, "asset1": ASSET_B, "fee_bps": FEE_BPS, "amount0": init_amt, "amount1": init_amt},
        ),
    )
    _assert_python_matches_ref(ref_s, py_s)

    # ADD_LIQUIDITY BVA:
    # - amount0_desired boundary at 1: [0,1,2]
    # - amount0_min boundary at 0: [-1,0,1]
    add_cases = [
        # Invalid desired (just below boundary).
        {"amount0_desired": 0, "amount1_desired": 1, "amount0_min": 0, "amount1_min": 0},
        # Smallest valid add.
        {"amount0_desired": 1, "amount1_desired": 1, "amount0_min": 0, "amount1_min": 0},
        # Ratio adjustment (desired A > desired B).
        {"amount0_desired": 2, "amount1_desired": 1, "amount0_min": 0, "amount1_min": 0},
        # Violate exactly one constraint: amount0_min too high.
        {"amount0_desired": 2, "amount1_desired": 1, "amount0_min": 2, "amount1_min": 0},
        # Violate exactly one constraint: amount1_min too high.
        {"amount0_desired": 2, "amount1_desired": 1, "amount0_min": 0, "amount1_min": 2},
        # Invalid min (just below boundary).
        {"amount0_desired": 1, "amount1_desired": 1, "amount0_min": -1, "amount1_min": 0},
    ]

    provider = 0
    for i, fields in enumerate(add_cases):
        ref_cmd = dex_ref.Command(
            tag="add_liquidity",
            args={
                "provider": provider,
                "lp_recipient": provider,
                "amount_a_desired": int(fields["amount0_desired"]),
                "amount_b_desired": int(fields["amount1_desired"]),
                "amount_a_min": int(fields["amount0_min"]),
                "amount_b_min": int(fields["amount1_min"]),
            },
        )
        ref_out = dex_ref.step(ref_s, ref_cmd)

        py_intent = _make_intent(
            IntentKind.ADD_LIQUIDITY,
            sender_idx=provider,
            intent_id=500 + i,
            fields={
                "pool_id": POOL_ID,
                "amount0_desired": int(fields["amount0_desired"]),
                "amount1_desired": int(fields["amount1_desired"]),
                "amount0_min": int(fields["amount0_min"]),
                "amount1_min": int(fields["amount1_min"]),
                "recipient": _pk(provider),
            },
        )
        py_out = dex_step(_PARITY_CONFIG, py_s, [py_intent])

        assert py_out.ok, py_out.error
        assert py_out.state is not None
        assert py_out.effects is not None

        action_by_id = dict(py_out.effects["settlement"].included_intents)
        expected = FillAction.FILL if ref_out.ok else FillAction.REJECT
        assert action_by_id[py_intent.intent_id] == expected

        if ref_out.ok:
            assert ref_out.state is not None
            _assert_python_matches_ref(ref_out.state, py_out.state)
        else:
            _assert_python_matches_ref(ref_s, py_out.state)

    # REMOVE_LIQUIDITY BVA:
    # - lp_amount boundary at 1: [0,1,2]
    # - amount*_min boundary at 0: [-1,0,1]
    remove_cases = [
        {"lp_amount": 0, "amount0_min": 0, "amount1_min": 0},
        {"lp_amount": 1, "amount0_min": 0, "amount1_min": 0},
        {"lp_amount": 2, "amount0_min": 0, "amount1_min": 0},
        # Violate exactly one constraint: amount0_min too high.
        {"lp_amount": 1, "amount0_min": 2, "amount1_min": 0},
        # Invalid min (just below boundary).
        {"lp_amount": 1, "amount0_min": -1, "amount1_min": 0},
    ]

    burner = 0
    for i, fields in enumerate(remove_cases):
        ref_cmd = dex_ref.Command(
            tag="remove_liquidity",
            args={
                "burner": burner,
                "recipient": burner,
                "lp_amount": int(fields["lp_amount"]),
                "amount_a_min": int(fields["amount0_min"]),
                "amount_b_min": int(fields["amount1_min"]),
            },
        )
        ref_out = dex_ref.step(ref_s, ref_cmd)

        py_intent = _make_intent(
            IntentKind.REMOVE_LIQUIDITY,
            sender_idx=burner,
            intent_id=600 + i,
            fields={
                "pool_id": POOL_ID,
                "lp_amount": int(fields["lp_amount"]),
                "amount0_min": int(fields["amount0_min"]),
                "amount1_min": int(fields["amount1_min"]),
                "recipient": _pk(burner),
            },
        )
        py_out = dex_step(_PARITY_CONFIG, py_s, [py_intent])

        assert py_out.ok, py_out.error
        assert py_out.state is not None
        assert py_out.effects is not None

        action_by_id = dict(py_out.effects["settlement"].included_intents)
        expected = FillAction.FILL if ref_out.ok else FillAction.REJECT
        assert action_by_id[py_intent.intent_id] == expected

        if ref_out.ok:
            assert ref_out.state is not None
            _assert_python_matches_ref(ref_out.state, py_out.state)
        else:
            _assert_python_matches_ref(ref_s, py_out.state)

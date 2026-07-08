from __future__ import annotations

import importlib.util
import json
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


def _pk_any(idx: int) -> str:
    """Map kernel user indices to deterministic pubkeys.

    The kernel domains use {0,1} for users, but ML-BVA intentionally includes
    out-of-domain values. We represent those as synthetic pubkeys to ensure the
    Python core fail-closed rejects them without crashing.
    """
    if int(idx) == 0:
        return U0
    if int(idx) == 1:
        return U1

    # Deterministic synthetic pubkey (48 bytes). Avoid colliding with U0/U1.
    b = (int(idx) & 0xFF) ^ 0xA5
    return "0x" + (f"{b:02x}" * 48)


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


def _make_intent(kind: IntentKind, *, sender_pk: str, intent_id: str, fields: Mapping[str, Any]) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id=str(intent_id),
        sender_pubkey=str(sender_pk),
        deadline=9999999999,
        fields=dict(fields),
    )


def _intent_from_kernel_action(*, action: str, params: Mapping[str, Any], intent_id: str) -> Intent:
    """Translate a dex_step_core_v2 kernel command into a single Python Intent."""

    if action == "create_pool":
        creator = int(params["creator"])
        amt_a = int(params["amount_a"])
        amt_b = int(params["amount_b"])
        # sqrt_product is a witness in the kernel; Python core recomputes it.
        return _make_intent(
            IntentKind.CREATE_POOL,
            sender_pk=_pk_any(creator),
            intent_id=intent_id,
            fields={
                "asset0": ASSET_A,
                "asset1": ASSET_B,
                "fee_bps": FEE_BPS,
                "amount0": amt_a,
                "amount1": amt_b,
                "recipient": _pk_any(creator),
            },
        )

    if action in {"swap_a_for_b", "swap_b_for_a"}:
        trader = int(params["trader"])
        recipient = int(params["recipient"])
        amount_in = int(params["amount_in"])
        min_amount_out = int(params["min_amount_out"])
        asset_in = ASSET_A if action == "swap_a_for_b" else ASSET_B
        asset_out = ASSET_B if action == "swap_a_for_b" else ASSET_A
        return _make_intent(
            IntentKind.SWAP_EXACT_IN,
            sender_pk=_pk_any(trader),
            intent_id=intent_id,
            fields={
                "pool_id": POOL_ID,
                "asset_in": asset_in,
                "asset_out": asset_out,
                "amount_in": amount_in,
                "min_amount_out": min_amount_out,
                "recipient": _pk_any(recipient),
            },
        )

    if action in {"swap_a_for_b_exact_out", "swap_b_for_a_exact_out"}:
        trader = int(params["trader"])
        recipient = int(params["recipient"])
        amount_out = int(params["amount_out"])
        max_amount_in = int(params["max_amount_in"])
        asset_in = ASSET_A if action == "swap_a_for_b_exact_out" else ASSET_B
        asset_out = ASSET_B if action == "swap_a_for_b_exact_out" else ASSET_A
        return _make_intent(
            IntentKind.SWAP_EXACT_OUT,
            sender_pk=_pk_any(trader),
            intent_id=intent_id,
            fields={
                "pool_id": POOL_ID,
                "asset_in": asset_in,
                "asset_out": asset_out,
                "amount_out": amount_out,
                "max_amount_in": max_amount_in,
                "recipient": _pk_any(recipient),
            },
        )

    if action == "add_liquidity":
        provider = int(params["provider"])
        lp_recipient = int(params["lp_recipient"])
        amt_a_des = int(params["amount_a_desired"])
        amt_b_des = int(params["amount_b_desired"])
        amt_a_min = int(params["amount_a_min"])
        amt_b_min = int(params["amount_b_min"])
        return _make_intent(
            IntentKind.ADD_LIQUIDITY,
            sender_pk=_pk_any(provider),
            intent_id=intent_id,
            fields={
                "pool_id": POOL_ID,
                "amount0_desired": amt_a_des,
                "amount1_desired": amt_b_des,
                "amount0_min": amt_a_min,
                "amount1_min": amt_b_min,
                "recipient": _pk_any(lp_recipient),
            },
        )

    if action == "remove_liquidity":
        burner = int(params["burner"])
        recipient = int(params["recipient"])
        lp_amount = int(params["lp_amount"])
        amt_a_min = int(params["amount_a_min"])
        amt_b_min = int(params["amount_b_min"])
        return _make_intent(
            IntentKind.REMOVE_LIQUIDITY,
            sender_pk=_pk_any(burner),
            intent_id=intent_id,
            fields={
                "pool_id": POOL_ID,
                "lp_amount": lp_amount,
                "amount0_min": amt_a_min,
                "amount1_min": amt_b_min,
                "recipient": _pk_any(recipient),
            },
        )

    raise ValueError(f"unsupported kernel action: {action!r}")


def _ref_state_from_dict(d: Mapping[str, Any]) -> dex_ref.State:
    # Fail-closed: ensure the ML-BVA state surface matches the exported ref type.
    required = set(dex_ref.State.__annotations__.keys())
    missing = [k for k in sorted(required) if k not in d]
    extra = [k for k in sorted(d.keys()) if k not in required]
    assert not missing, f"missing ref state keys: {missing}"
    assert not extra, f"unexpected ref state keys: {extra}"
    return dex_ref.State(**{k: int(d[k]) for k in sorted(required)})


def test_dex_step_core_v2_ml_bva_cases_match_python_core() -> None:
    cases_path = Path("tests/kernels/data/dex_step_core_v2_ml_bva_cases.json")
    obj = json.loads(cases_path.read_text(encoding="utf-8"))
    assert obj.get("schema") == "zenodex/ml-boundary-bva/v1"

    cases = obj.get("cases")
    assert isinstance(cases, list) and cases, "expected non-empty ML-BVA case set"

    for i, row in enumerate(cases):
        assert isinstance(row, dict), f"bad row {i}"
        pre_state = row.get("pre_state")
        action = row.get("action")
        params = row.get("params")
        assert isinstance(pre_state, dict), f"bad pre_state at row {i}"
        assert isinstance(action, str), f"bad action at row {i}"
        assert isinstance(params, dict), f"bad params at row {i}"

        ref_pre = _ref_state_from_dict(pre_state)
        ref_cmd = dex_ref.Command(tag=str(action), args={str(k): int(params[k]) for k in sorted(params.keys())})
        ref_out = dex_ref.step(ref_pre, ref_cmd)

        py_pre = _python_state_from_ref(ref_pre)
        py_intent = _intent_from_kernel_action(action=str(action), params=params, intent_id=_iid(10_000 + i))
        py_out = dex_step(_PARITY_CONFIG, py_pre, [py_intent])

        assert py_out.ok, py_out.error
        assert py_out.state is not None
        assert py_out.effects is not None

        settlement = py_out.effects["settlement"]
        action_by_id = dict(settlement.included_intents)
        assert py_intent.intent_id in action_by_id

        # The kernel model is intentionally bounded: actor params are in {0,1}.
        # Python uses pubkeys and supports arbitrary recipients, so cases that push
        # actor indices out-of-domain are not comparable by parity (they test the
        # kernel's ParamType boundary, not the Python mechanism).
        actor_params_by_action: dict[str, tuple[str, ...]] = {
            "create_pool": ("creator",),
            "swap_a_for_b": ("trader", "recipient"),
            "swap_b_for_a": ("trader", "recipient"),
            "swap_a_for_b_exact_out": ("trader", "recipient"),
            "swap_b_for_a_exact_out": ("trader", "recipient"),
            "add_liquidity": ("provider", "lp_recipient"),
            "remove_liquidity": ("burner", "recipient"),
        }
        actor_keys = actor_params_by_action.get(str(action), tuple())
        comparable = True
        for k in actor_keys:
            v = params.get(k)
            if not isinstance(v, int) or isinstance(v, bool) or int(v) not in (0, 1):
                comparable = False
                break
        # Also restrict parity checks to in-domain numeric params for the bounded
        # kernel model. Python uses unbounded ints and is not required to reject
        # (max+1)/(min-1) values unless the protocol explicitly caps them.
        if comparable:
            MAX_PARAM = 1_000_000_000
            bounds_by_action: dict[str, dict[str, tuple[int, int]]] = {
                "create_pool": {
                    "amount_a": (1001, MAX_PARAM),
                    "amount_b": (1001, MAX_PARAM),
                    "sqrt_product": (1001, MAX_PARAM),
                },
                "swap_a_for_b": {
                    "amount_in": (1, MAX_PARAM),
                    "min_amount_out": (0, MAX_PARAM),
                },
                "swap_b_for_a": {
                    "amount_in": (1, MAX_PARAM),
                    "min_amount_out": (0, MAX_PARAM),
                },
                "swap_a_for_b_exact_out": {
                    "amount_out": (1, MAX_PARAM),
                    "max_amount_in": (0, MAX_PARAM),
                },
                "swap_b_for_a_exact_out": {
                    "amount_out": (1, MAX_PARAM),
                    "max_amount_in": (0, MAX_PARAM),
                },
                "add_liquidity": {
                    "amount_a_desired": (1, MAX_PARAM),
                    "amount_b_desired": (1, MAX_PARAM),
                    "amount_a_min": (0, MAX_PARAM),
                    "amount_b_min": (0, MAX_PARAM),
                },
                "remove_liquidity": {
                    "lp_amount": (1, MAX_PARAM),
                    "amount_a_min": (0, MAX_PARAM),
                    "amount_b_min": (0, MAX_PARAM),
                },
            }
            bounds = bounds_by_action.get(str(action), {})
            for k, (lo, hi) in bounds.items():
                v = params.get(k)
                if not isinstance(v, int) or isinstance(v, bool) or not (int(lo) <= int(v) <= int(hi)):
                    comparable = False
                    break
        # The kernel create_pool is proof-carrying (sqrt witness). Python recomputes
        # sqrt internally, so parity is only meaningful when the witness is correct.
        if comparable and str(action) == "create_pool":
            import math

            a = params.get("amount_a")
            b = params.get("amount_b")
            sp = params.get("sqrt_product")
            if not isinstance(a, int) or isinstance(a, bool):
                comparable = False
            elif not isinstance(b, int) or isinstance(b, bool):
                comparable = False
            elif not isinstance(sp, int) or isinstance(sp, bool):
                comparable = False
            else:
                if int(sp) != int(math.isqrt(int(a) * int(b))):
                    comparable = False
        if not comparable:
            continue

        expected = FillAction.FILL if bool(ref_out.ok) else FillAction.REJECT
        assert action_by_id[py_intent.intent_id] == expected, f"row {i}: fill/reject mismatch"

        if ref_out.ok:
            assert ref_out.state is not None
            _assert_python_matches_ref(ref_out.state, py_out.state)
        else:
            _assert_python_matches_ref(ref_pre, py_out.state)

from __future__ import annotations

import json
from pathlib import Path

import pytest
import yaml

from tools.esso_gpu_semantics import esso_interpreter_available


def _resolve_model_path(raw: str) -> Path:
    p = Path(str(raw))
    if p.exists():
        return p

    repo_root = Path(__file__).resolve().parents[2]
    if not p.is_absolute():
        q = repo_root / p
        if q.exists():
            return q
    else:
        parts = p.parts
        for anchor in ("src", "tests", "docs", "tools"):
            if anchor in parts:
                idx = parts.index(anchor)
                q = repo_root.joinpath(*parts[idx:])
                if q.exists():
                    return q

    raise FileNotFoundError(f"cannot resolve model_path from artifact: {raw!r}")


MAX_RESERVE = 3_000_000_000
MAX_AMOUNT = 1_000_000_000
LOCKED_LIQUIDITY = 1000


def _in_range_int(v: object, *, lo: int, hi: int) -> bool:
    return isinstance(v, int) and not isinstance(v, bool) and int(lo) <= int(v) <= int(hi)


def _lp_mint_v8_native_from_case(*, pre_state: dict[str, object], action: str, params: dict[str, object]) -> dict[str, object]:
    from src.kernels.python.lp_math_v7 import mint_liquidity, mint_liquidity_initial_witness

    if action not in {"mint_initial", "mint"}:
        return {"ok": False, "code": "UnknownAction"}

    try:
        reserve0 = pre_state["reserve0"]
        reserve1 = pre_state["reserve1"]
        lp_supply = pre_state["lp_supply"]
        locked = pre_state["locked_liquidity"]
    except KeyError as exc:
        return {"ok": False, "code": "ParamShape", "error": str(exc)}

    if not _in_range_int(reserve0, lo=0, hi=MAX_RESERVE) or not _in_range_int(reserve1, lo=0, hi=MAX_RESERVE):
        return {"ok": False, "code": "InvalidState"}
    if not _in_range_int(lp_supply, lo=0, hi=MAX_RESERVE) or not _in_range_int(locked, lo=0, hi=LOCKED_LIQUIDITY):
        return {"ok": False, "code": "InvalidState"}

    r0 = int(reserve0)
    r1 = int(reserve1)
    lps = int(lp_supply)
    ll = int(locked)

    if action == "mint_initial":
        amount0 = params.get("amount0")
        amount1 = params.get("amount1")
        sqrt_product = params.get("sqrt_product")
        if (
            not _in_range_int(amount0, lo=1001, hi=MAX_AMOUNT)
            or not _in_range_int(amount1, lo=1001, hi=MAX_AMOUNT)
            or not _in_range_int(sqrt_product, lo=1001, hi=MAX_AMOUNT)
        ):
            return {"ok": False, "code": "ParamType"}

        if not (r0 == 0 and r1 == 0 and lps == 0 and ll == 0):
            return {"ok": False, "code": "GuardFalse"}

        a0 = int(amount0)
        a1 = int(amount1)
        sp = int(sqrt_product)
        try:
            minted, total_supply = mint_liquidity_initial_witness(amount0=a0, amount1=a1, sqrt_product=sp)
        except TypeError:
            return {"ok": False, "code": "ParamType"}
        except ValueError:
            return {"ok": False, "code": "GuardFalse"}

        post_state = dict(pre_state)
        post_state["reserve0_before"] = int(r0)
        post_state["reserve1_before"] = int(r1)
        post_state["lp_supply_before"] = int(lps)
        post_state["reserve0"] = int(a0)
        post_state["reserve1"] = int(a1)
        post_state["lp_supply"] = int(total_supply) - LOCKED_LIQUIDITY
        post_state["locked_liquidity"] = LOCKED_LIQUIDITY

        effects = {
            "liquidity_minted": int(minted),
            "amount0_used": int(a0),
            "amount1_used": int(a1),
            "total_supply": int(total_supply),
            "amount0_refund": 0,
            "amount1_refund": 0,
        }
        return {"ok": True, "state": post_state, "effects": effects}

    amount0 = params.get("amount0")
    amount1 = params.get("amount1")
    min_liquidity = params.get("min_liquidity")
    if (
        not _in_range_int(amount0, lo=1, hi=MAX_AMOUNT)
        or not _in_range_int(amount1, lo=1, hi=MAX_AMOUNT)
        or not _in_range_int(min_liquidity, lo=0, hi=MAX_RESERVE)
    ):
        return {"ok": False, "code": "ParamType"}

    # Kernel guard: mint (non-initial) only.
    if r0 <= 0 or r1 <= 0:
        return {"ok": False, "code": "GuardFalse"}
    if ll != LOCKED_LIQUIDITY:
        return {"ok": False, "code": "GuardFalse"}

    a0 = int(amount0)
    a1 = int(amount1)
    ml = int(min_liquidity)
    total_supply_pre = int(lps) + int(ll)
    try:
        res = mint_liquidity(
            reserve0=int(r0),
            reserve1=int(r1),
            total_supply=int(total_supply_pre),
            amount0_desired=int(a0),
            amount1_desired=int(a1),
            min_liquidity=int(ml),
        )
    except TypeError:
        return {"ok": False, "code": "ParamType"}
    except ValueError:
        return {"ok": False, "code": "GuardFalse"}

    post_state = dict(pre_state)
    post_state["reserve0_before"] = int(r0)
    post_state["reserve1_before"] = int(r1)
    post_state["lp_supply_before"] = int(lps)
    post_state["reserve0"] = int(res.new_reserve0)
    post_state["reserve1"] = int(res.new_reserve1)
    post_state["lp_supply"] = int(res.new_total_supply) - int(ll)
    post_state["locked_liquidity"] = int(ll)

    effects = {
        "liquidity_minted": int(res.liquidity_minted),
        "amount0_used": int(res.amount0_used),
        "amount1_used": int(res.amount1_used),
        "total_supply": int(res.new_total_supply),
        "amount0_refund": int(res.amount0_refund),
        "amount1_refund": int(res.amount1_refund),
    }
    return {"ok": True, "state": post_state, "effects": effects}


def test_lp_mint_v8_ml_bva_cases_match_python_kernel() -> None:
    cases_path = Path("tests/kernels/data/lp_mint_v8_ml_bva_cases.json")
    obj = json.loads(cases_path.read_text(encoding="utf-8"))
    assert obj.get("schema") == "zenodex/ml-boundary-bva/v1"

    cases = obj.get("cases")
    assert isinstance(cases, list) and cases, "expected non-empty ML-BVA case set"

    for i, row in enumerate(cases):
        pre_state = row.get("pre_state")
        action = row.get("action")
        params = row.get("params")
        expected = row.get("expected")
        assert isinstance(pre_state, dict), f"bad pre_state at row {i}"
        assert isinstance(action, str) and action, f"bad action at row {i}"
        assert isinstance(params, dict), f"bad params at row {i}"
        assert isinstance(expected, dict), f"bad expected at row {i}"

        native = _lp_mint_v8_native_from_case(pre_state=dict(pre_state), action=str(action), params=dict(params))
        exp_ok = bool(expected.get("ok", False))
        if exp_ok:
            assert native.get("ok") is True, f"row {i}: expected native success"
            assert native.get("state") == expected.get("state"), f"row {i}: state mismatch"
            assert native.get("effects") == expected.get("effects"), f"row {i}: effects mismatch"
        else:
            assert native.get("ok") is False, f"row {i}: expected native failure"
            assert str(native.get("code", "")) == str(expected.get("code", "")), f"row {i}: error code mismatch"


@pytest.mark.skipif(not esso_interpreter_available(), reason="ESSO interpreter is not installed")
def test_lp_mint_v8_ml_bva_cases_replay_in_interpreter() -> None:
    from ESSO.ir.schema import CandidateIR  # type: ignore
    from ESSO.kernel.interpreter import (  # type: ignore
        Command,
        StepError,
        prepare_step_context,
        step_ctx,
    )

    cases_path = Path("tests/kernels/data/lp_mint_v8_ml_bva_cases.json")
    obj = json.loads(cases_path.read_text(encoding="utf-8"))
    assert obj.get("schema") == "zenodex/ml-boundary-bva/v1"

    model_path = _resolve_model_path(str(obj["model_path"]))
    model_obj = yaml.safe_load(model_path.read_text(encoding="utf-8"))
    assert isinstance(model_obj, dict)

    ir = CandidateIR.from_json_dict(model_obj).canonicalized()
    ctx = prepare_step_context(ir)
    assert not isinstance(ctx, StepError), "invalid kernel context"

    cases = obj.get("cases")
    assert isinstance(cases, list) and cases, "expected non-empty ML-BVA case set"

    for i, row in enumerate(cases):
        pre_state = row["pre_state"]
        action = row["action"]
        params = row["params"]
        expected = row["expected"]
        interp_res = step_ctx(dict(pre_state), Command(tag=action, args=dict(params)), ctx)
        exp_ok = bool(expected.get("ok", False))
        if exp_ok:
            assert not isinstance(interp_res, StepError), f"row {i}: expected interpreter success"
            assert dict(interp_res.state) == expected.get("state"), f"row {i}: interpreter state mismatch"
            assert dict(interp_res.effects) == expected.get("effects"), f"row {i}: interpreter effects mismatch"
        else:
            assert isinstance(interp_res, StepError), f"row {i}: expected interpreter failure"
            assert str(interp_res.code) == str(expected.get("code", "")), f"row {i}: interpreter error code mismatch"

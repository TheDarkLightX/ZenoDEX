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
MAX_DESIRED = 1_000_000_000


def _in_range_int(v: object, *, lo: int, hi: int) -> bool:
    return isinstance(v, int) and not isinstance(v, bool) and int(lo) <= int(v) <= int(hi)


def _lp_ratio_v7_native_from_case(*, pre_state: dict[str, object], params: dict[str, object]) -> dict[str, object]:
    from src.kernels.python.lp_math_v7 import optimal_liquidity

    reserve0 = pre_state.get("reserve0")
    reserve1 = pre_state.get("reserve1")
    desired0 = params.get("desired0")
    desired1 = params.get("desired1")

    if not _in_range_int(reserve0, lo=0, hi=MAX_RESERVE) or not _in_range_int(reserve1, lo=0, hi=MAX_RESERVE):
        return {"ok": False, "code": "InvalidState"}
    if not _in_range_int(desired0, lo=1, hi=MAX_DESIRED) or not _in_range_int(desired1, lo=1, hi=MAX_DESIRED):
        return {"ok": False, "code": "ParamType"}

    r0 = int(reserve0)
    r1 = int(reserve1)
    d0 = int(desired0)
    d1 = int(desired1)

    try:
        opt = optimal_liquidity(reserve0=r0, reserve1=r1, amount0_desired=d0, amount1_desired=d1)
    except TypeError:
        return {"ok": False, "code": "ParamType"}
    except ValueError:
        return {"ok": False, "code": "GuardFalse"}

    is_initial = bool(r0 == 0 and r1 == 0)
    effects = {
        "is_initial": bool(is_initial),
        "optimal0": int(opt.amount0_used),
        "optimal1": int(opt.amount1_used),
        "refund0": int(opt.amount0_refund),
        "refund1": int(opt.amount1_refund),
    }
    effects["refund0_nonneg"] = bool(int(effects["refund0"]) >= 0)
    effects["refund1_nonneg"] = bool(int(effects["refund1"]) >= 0)
    effects["optimal0_le_desired0"] = bool(int(effects["optimal0"]) <= d0)
    effects["optimal1_le_desired1"] = bool(int(effects["optimal1"]) <= d1)
    effects["sum0_ok"] = bool(int(effects["optimal0"]) + int(effects["refund0"]) == d0)
    effects["sum1_ok"] = bool(int(effects["optimal1"]) + int(effects["refund1"]) == d1)

    # Kernel has updates=[], so post-state equals pre-state.
    return {"ok": True, "state": dict(pre_state), "effects": effects}


def test_lp_ratio_calculator_v7_ml_bva_cases_match_python_kernel() -> None:
    cases_path = Path("tests/kernels/data/lp_ratio_calculator_v7_ml_bva_cases.json")
    obj = json.loads(cases_path.read_text(encoding="utf-8"))
    assert obj.get("schema") == "zenodex/ml-boundary-bva/v1"

    cases = obj.get("cases")
    assert isinstance(cases, list) and cases, "expected non-empty ML-BVA case set"

    for i, row in enumerate(cases):
        assert isinstance(row, dict), f"bad row {i}"
        pre_state = row.get("pre_state")
        action = row.get("action")
        params = row.get("params")
        expected = row.get("expected")
        assert isinstance(pre_state, dict), f"bad pre_state at row {i}"
        assert action == "calculate_optimal", f"unexpected action at row {i}: {action!r}"
        assert isinstance(params, dict), f"bad params at row {i}"
        assert isinstance(expected, dict), f"bad expected at row {i}"

        native = _lp_ratio_v7_native_from_case(pre_state=dict(pre_state), params=dict(params))
        exp_ok = bool(expected.get("ok", False))
        if exp_ok:
            assert native.get("ok") is True, f"row {i}: expected native success"
            assert native.get("state") == expected.get("state"), f"row {i}: state mismatch"
            assert native.get("effects") == expected.get("effects"), f"row {i}: effects mismatch"
        else:
            assert native.get("ok") is False, f"row {i}: expected native failure"
            assert str(native.get("code", "")) == str(expected.get("code", "")), f"row {i}: error code mismatch"


@pytest.mark.skipif(not esso_interpreter_available(), reason="ESSO interpreter is not installed")
def test_lp_ratio_calculator_v7_ml_bva_cases_replay_in_interpreter() -> None:
    from ESSO.ir.schema import CandidateIR  # type: ignore
    from ESSO.kernel.interpreter import (  # type: ignore
        Command,
        StepError,
        prepare_step_context,
        step_ctx,
    )

    cases_path = Path("tests/kernels/data/lp_ratio_calculator_v7_ml_bva_cases.json")
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

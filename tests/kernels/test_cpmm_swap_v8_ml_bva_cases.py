from __future__ import annotations

import json
from pathlib import Path

import pytest
import yaml

from tools.esso_gpu_semantics import ensure_esso_on_path


def _esso_available() -> bool:
    try:
        ensure_esso_on_path()
        import ESSO.kernel.interpreter  # type: ignore  # noqa: F401
    except ModuleNotFoundError:
        return False
    return True


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
MAX_BPS = 10_000


def _require_int(v: object) -> int:
    if not isinstance(v, int) or isinstance(v, bool):
        raise TypeError("expected int")
    return int(v)


def _in_range_int(v: object, *, lo: int, hi: int) -> bool:
    return isinstance(v, int) and not isinstance(v, bool) and int(lo) <= int(v) <= int(hi)


def _cpmm_swap_v8_native_from_case(*, pre_state: dict[str, object], params: dict[str, object]) -> dict[str, object]:
    """
    Native (Python-kernel) step attempt for cpmm_swap_v8, classified into ESSO-like results:
      - ok: True, state/effects populated
      - ok: False, code in {ParamType, GuardFalse}

    This intentionally lives in tests (not core) to avoid duplicating consensus-critical logic.
    """
    from src.kernels.python.cpmm_swap_v8 import swap_exact_in

    # State shape/types (artifact should already satisfy these).
    try:
        reserve_in = _require_int(pre_state["reserve_in"])
        reserve_out = _require_int(pre_state["reserve_out"])
        fee_bps = _require_int(pre_state["fee_bps"])
        protocol_share = _require_int(pre_state["protocol_fee_share_bps"])
    except (KeyError, TypeError) as exc:
        return {"ok": False, "code": "ParamShape", "error": str(exc)}

    # Param shape/types.
    try:
        amount_in = params["amount_in"]
        min_amount_out = params["min_amount_out"]
    except KeyError as exc:
        return {"ok": False, "code": "ParamShape", "error": str(exc)}

    if not _in_range_int(amount_in, lo=1, hi=MAX_RESERVE) or not _in_range_int(min_amount_out, lo=1, hi=MAX_RESERVE):
        # Match ESSO interpreter posture: out-of-domain ints are ParamType (not GuardFalse).
        return {"ok": False, "code": "ParamType"}

    if not _in_range_int(reserve_in, lo=1, hi=MAX_RESERVE) or not _in_range_int(reserve_out, lo=1, hi=MAX_RESERVE):
        return {"ok": False, "code": "InvalidState"}
    if not _in_range_int(fee_bps, lo=0, hi=MAX_BPS) or not _in_range_int(protocol_share, lo=0, hi=MAX_BPS):
        return {"ok": False, "code": "InvalidState"}

    ai = int(amount_in)
    mao = int(min_amount_out)
    try:
        r = swap_exact_in(
            reserve_in=int(reserve_in),
            reserve_out=int(reserve_out),
            amount_in=ai,
            fee_bps=int(fee_bps),
            protocol_fee_share_bps=int(protocol_share),
        )
    except TypeError:
        return {"ok": False, "code": "ParamType"}
    except ValueError:
        return {"ok": False, "code": "GuardFalse"}

    # Spec guards not enforced by the raw python kernel.
    if int(r.amount_out) < int(mao):
        return {"ok": False, "code": "GuardFalse"}
    if not (1 <= int(r.new_reserve_in) <= MAX_RESERVE):
        return {"ok": False, "code": "GuardFalse"}
    if not (1 <= int(r.new_reserve_out) <= MAX_RESERVE):
        return {"ok": False, "code": "GuardFalse"}
    if int(r.k_after) < int(r.k_before):
        return {"ok": False, "code": "GuardFalse"}

    post_state = dict(pre_state)
    post_state["reserve_in_before"] = int(reserve_in)
    post_state["reserve_out_before"] = int(reserve_out)
    post_state["reserve_in"] = int(r.new_reserve_in)
    post_state["reserve_out"] = int(r.new_reserve_out)
    post_state["fee_bps"] = int(fee_bps)
    post_state["protocol_fee_share_bps"] = int(protocol_share)

    effects = {
        "amount_out": int(r.amount_out),
        "fee_total": int(r.fee_total),
        "protocol_fee": int(r.protocol_fee),
        "lp_fee": int(r.lp_fee),
        "net_in": int(r.net_in),
        "gross_in": int(r.gross_in),
        "new_reserve_in": int(r.new_reserve_in),
        "new_reserve_out": int(r.new_reserve_out),
        "k_before": int(r.k_before),
        "k_after": int(r.k_after),
        "fee_split_ok": bool(int(r.protocol_fee) + int(r.lp_fee) == int(r.fee_total)),
        "net_ok": bool(int(r.net_in) + int(r.fee_total) == int(r.gross_in)),
    }

    return {"ok": True, "state": post_state, "effects": effects}


def test_cpmm_swap_v8_ml_bva_cases_match_python_kernel() -> None:
    cases_path = Path("tests/kernels/data/cpmm_swap_v8_ml_bva_cases.json")
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
        assert action == "swap", f"unexpected action at row {i}: {action!r}"
        assert isinstance(params, dict), f"bad params at row {i}"
        assert isinstance(expected, dict), f"bad expected at row {i}"

        native = _cpmm_swap_v8_native_from_case(pre_state=dict(pre_state), params=dict(params))
        exp_ok = bool(expected.get("ok", False))
        if exp_ok:
            assert native.get("ok") is True, f"row {i}: expected native success"
            assert native.get("state") == expected.get("state"), f"row {i}: state mismatch"
            assert native.get("effects") == expected.get("effects"), f"row {i}: effects mismatch"
        else:
            assert native.get("ok") is False, f"row {i}: expected native failure"
            assert str(native.get("code", "")) == str(expected.get("code", "")), f"row {i}: error code mismatch"


@pytest.mark.skipif(not _esso_available(), reason="ESSO interpreter is not installed")
def test_cpmm_swap_v8_ml_bva_cases_replay_in_interpreter() -> None:
    from ESSO.ir.schema import CandidateIR  # type: ignore
    from ESSO.kernel.interpreter import Command, StepError, prepare_step_context, step_ctx  # type: ignore

    cases_path = Path("tests/kernels/data/cpmm_swap_v8_ml_bva_cases.json")
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


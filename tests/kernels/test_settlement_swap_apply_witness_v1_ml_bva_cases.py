from __future__ import annotations

import json
from pathlib import Path

import pytest
import yaml

from tools.esso_gpu_semantics import ensure_esso_on_path


def _load_cases_obj(path: Path) -> dict[str, object]:
    if not path.exists():
        pytest.skip(f"{path} is not present on clean main")
    obj = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(obj, dict)
    return obj


def _esso_available() -> bool:
    try:
        ensure_esso_on_path()
        import ESSO.kernel.interpreter  # type: ignore  # noqa: F401
    except (FileNotFoundError, ModuleNotFoundError):
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


def _in_range_int(v: object, *, lo: int, hi: int) -> bool:
    return isinstance(v, int) and not isinstance(v, bool) and int(lo) <= int(v) <= int(hi)


@pytest.mark.skipif(not _esso_available(), reason="ESSO toolchain is not installed")
def test_settlement_swap_apply_witness_v1_ml_bva_cases_match_native_adapter() -> None:
    from ESSO.ir.schema import CandidateIR  # type: ignore
    from ESSO.kernel.interpreter import (  # type: ignore
        Command,
        StepError,
        StepOk,
        prepare_step_context,
    )

    from src.kernels.python.settlement_swap_apply_witness_v1_native_adapter import make_adapter

    cases_path = Path("tests/kernels/data/settlement_swap_apply_witness_v1_ml_bva_cases.json")
    obj = _load_cases_obj(cases_path)
    assert obj.get("schema") == "zenodex/ml-boundary-bva/v1"

    model_path = _resolve_model_path(str(obj["model_path"]))
    model_obj = yaml.safe_load(model_path.read_text(encoding="utf-8"))
    assert isinstance(model_obj, dict)

    ir = CandidateIR.from_json_dict(model_obj).canonicalized()
    ctx = prepare_step_context(ir)
    assert not isinstance(ctx, StepError), "invalid kernel context"

    # Pull param bounds from the kernel (avoid duplicating constants).
    act = next(a for a in ir.actions if str(a.id) == "swap_exact_in_apply")
    ptypes = {str(p.id): p.type for p in act.params}
    bounds = {pid: (int(t.min), int(t.max)) for pid, t in ptypes.items() if str(getattr(t, "kind", "")) == "int"}

    cases = obj.get("cases")
    assert isinstance(cases, list) and cases, "expected non-empty ML-BVA case set"

    adapter = make_adapter(ir)

    for i, row in enumerate(cases):
        assert isinstance(row, dict), f"bad row {i}"
        pre_state = row.get("pre_state")
        action = row.get("action")
        params = row.get("params")
        expected = row.get("expected")
        assert isinstance(pre_state, dict), f"bad pre_state at row {i}"
        assert action == "swap_exact_in_apply", f"unexpected action at row {i}: {action!r}"
        assert isinstance(params, dict), f"bad params at row {i}"
        assert isinstance(expected, dict), f"bad expected at row {i}"

        # Match interpreter posture: out-of-domain params are ParamType (not GuardFalse).
        for pid, (lo, hi) in bounds.items():
            if pid not in params:
                assert expected.get("ok") is False
                assert str(expected.get("code", "")) == "ParamShape"
                break
            if not _in_range_int(params[pid], lo=int(lo), hi=int(hi)):
                assert expected.get("ok") is False
                assert str(expected.get("code", "")) == "ParamType", f"row {i}: expected ParamType"
                break
        else:
            adapter.reset(state=dict(pre_state))
            res = adapter.apply(Command(tag=str(action), args=dict(params)))
            if expected.get("ok", False):
                assert isinstance(res, StepOk), f"row {i}: expected native success"
                assert dict(res.state) == expected.get("state"), f"row {i}: state mismatch"
                assert dict(res.effects) == expected.get("effects"), f"row {i}: effects mismatch"
            else:
                assert isinstance(res, StepError), f"row {i}: expected native failure"
                assert str(res.code) == str(expected.get("code", "")), f"row {i}: error code mismatch"


@pytest.mark.skipif(not _esso_available(), reason="ESSO interpreter is not installed")
def test_settlement_swap_apply_witness_v1_ml_bva_cases_replay_in_interpreter() -> None:
    from ESSO.ir.schema import CandidateIR  # type: ignore
    from ESSO.kernel.interpreter import (  # type: ignore
        Command,
        StepError,
        prepare_step_context,
        step_ctx,
    )

    cases_path = Path("tests/kernels/data/settlement_swap_apply_witness_v1_ml_bva_cases.json")
    obj = _load_cases_obj(cases_path)
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
        interp_res = step_ctx(dict(pre_state), Command(tag=str(action), args=dict(params)), ctx)
        exp_ok = bool(expected.get("ok", False))
        if exp_ok:
            assert not isinstance(interp_res, StepError), f"row {i}: expected interpreter success"
            assert dict(interp_res.state) == expected.get("state"), f"row {i}: interpreter state mismatch"
            assert dict(interp_res.effects) == expected.get("effects"), f"row {i}: interpreter effects mismatch"
        else:
            assert isinstance(interp_res, StepError), f"row {i}: expected interpreter failure"
            assert str(interp_res.code) == str(expected.get("code", "")), f"row {i}: interpreter error code mismatch"

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


@pytest.mark.skipif(not _esso_available(), reason="ESSO interpreter is not installed")
def test_ml_bva_v3_cases_replay_and_native_parity() -> None:
    from ESSO.ir.schema import CandidateIR  # type: ignore
    from ESSO.kernel.interpreter import (  # type: ignore
        Command,
        StepError,
        prepare_step_context,
        step_ctx,
    )

    from src.core.perp_epoch import perp_epoch_isolated_v3_native_apply

    cases_path = Path("tests/kernels/data/perp_epoch_isolated_v3_ml_bva_cases.json")
    obj = json.loads(cases_path.read_text(encoding="utf-8"))
    assert isinstance(obj, dict)
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
        assert isinstance(row, dict), f"bad row {i}"
        pre_state = row.get("pre_state")
        action = row.get("action")
        params = row.get("params")
        expected = row.get("expected")
        assert isinstance(pre_state, dict), f"bad pre_state at row {i}"
        assert isinstance(action, str) and action, f"bad action at row {i}"
        assert isinstance(params, dict), f"bad params at row {i}"
        assert isinstance(expected, dict), f"bad expected at row {i}"

        interp_res = step_ctx(dict(pre_state), Command(tag=action, args=dict(params)), ctx)
        exp_ok = bool(expected.get("ok", False))
        if exp_ok:
            assert not isinstance(interp_res, StepError), f"row {i}: expected interpreter success"
            exp_state = expected.get("state")
            exp_effects = expected.get("effects")
            assert isinstance(exp_state, dict), f"row {i}: bad expected state"
            assert isinstance(exp_effects, dict), f"row {i}: bad expected effects"
            assert dict(interp_res.state) == exp_state, f"row {i}: interpreter state mismatch"
            assert dict(interp_res.effects) == exp_effects, f"row {i}: interpreter effects mismatch"
        else:
            assert isinstance(interp_res, StepError), f"row {i}: expected interpreter failure"
            exp_code = str(expected.get("code", ""))
            assert str(interp_res.code) == exp_code, f"row {i}: interpreter error code mismatch"

        native_res = perp_epoch_isolated_v3_native_apply(state=dict(pre_state), action=action, params=dict(params))
        if exp_ok:
            assert native_res.ok is True, f"row {i}: native expected success"
            assert native_res.state == expected.get("state"), f"row {i}: native state mismatch"
            assert native_res.effects == expected.get("effects"), f"row {i}: native effects mismatch"
        else:
            assert native_res.ok is False, f"row {i}: native expected failure"
            assert str(native_res.code) == str(expected.get("code", "")), f"row {i}: native error code mismatch"


def test_v3_native_settlement_rejects_unusable_oracle_boundaries() -> None:
    """Minimized regression for ML-BVA vector 112 and adjacent oracle edges."""

    from src.core.perp_epoch import (
        perp_epoch_isolated_v3_native_apply,
        perp_epoch_isolated_v3_native_initial_state,
    )

    base = perp_epoch_isolated_v3_native_initial_state()
    base.update(
        {
            "now_epoch": 5,
            "epoch_phase": 1,
            "clearing_price_seen": True,
            "clearing_price_epoch": 5,
            "clearing_price_e8": 100_000_000,
            "oracle_seen": True,
            "oracle_last_update_epoch": 4,
            "index_price_e8": 100_000_000,
            "max_oracle_staleness_epochs": 2,
        }
    )

    cases = {
        "unseen": {"oracle_seen": False},
        "zero_index": {"index_price_e8": 0},
        "stale_by_one": {"oracle_last_update_epoch": 2},
    }
    for patch in cases.values():
        state = {**base, **patch}
        result = perp_epoch_isolated_v3_native_apply(
            state=state,
            action="settle_epoch",
            params={},
        )
        assert result.ok is False
        assert result.code == "GuardFalse"
        assert result.state is None
        assert result.effects is None

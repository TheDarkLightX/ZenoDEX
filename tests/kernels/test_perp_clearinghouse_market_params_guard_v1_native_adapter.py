from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/perp_clearinghouse_market_params_guard_v1.yaml")
ADAPTER = "src.kernels.python.perp_clearinghouse_market_params_guard_v1_native_adapter:make_adapter"


def _install_fake_interpreter(monkeypatch):
    esso_mod = ModuleType("ESSO")
    kernel_mod = ModuleType("ESSO.kernel")
    interp_mod = ModuleType("ESSO.kernel.interpreter")

    class StepOk:
        def __init__(self, *, state, effects):
            self.state = state
            self.effects = effects

    class StepError:
        def __init__(self, *, code: str, message: str):
            self.code = code
            self.message = message

    setattr(interp_mod, "StepOk", StepOk)
    setattr(interp_mod, "StepError", StepError)
    setattr(kernel_mod, "interpreter", interp_mod)
    setattr(esso_mod, "kernel", kernel_mod)

    monkeypatch.setitem(sys.modules, "ESSO", esso_mod)
    monkeypatch.setitem(sys.modules, "ESSO.kernel", kernel_mod)
    monkeypatch.setitem(sys.modules, "ESSO.kernel.interpreter", interp_mod)
    return interp_mod


def _base_state() -> dict[str, int]:
    return {
        "market_kind": 1,
        "operator_ok": 1,
        "epoch_settled_ok": 1,
        "position_base_a": 0,
        "position_base_b": 0,
        "position_base_c": 0,
        "old_liquidation_penalty_bps": 50,
        "new_liquidation_penalty_bps": 50,
        "new_maintenance_margin_bps": 700,
    }


def test_perp_clearinghouse_market_params_guard_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
    lint_path = tmp_path / "shell_lint.json"
    verify_path = tmp_path / "shell_verify.json"

    subprocess.check_call(
        [
            "python3",
            "-m",
            "ESSO",
            "shell-lint",
            str(MODEL),
            "--adapter",
            ADAPTER,
            "--output",
            str(lint_path),
        ]
    )
    lint = json.loads(lint_path.read_text(encoding="utf-8"))
    assert lint.get("ok") is True

    subprocess.check_call(
        [
            "python3",
            "-m",
            "ESSO",
            "verify-shell",
            str(MODEL),
            "--adapter",
            ADAPTER,
            "--traces",
            "16",
            "--max-steps",
            "8",
            "--determinism-trials",
            "2",
            "--output",
            str(verify_path),
        ]
    )
    verify = json.loads(verify_path.read_text(encoding="utf-8"))
    assert verify.get("ok") is True


def test_perp_clearinghouse_market_params_guard_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_clearinghouse_market_params_guard_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state={"before": 1})

    unknown = adapter.apply(SimpleNamespace(tag="unknown"))
    assert isinstance(unknown, interp_mod.StepError)
    assert unknown.code == "UnknownAction"

    effect_key = next(iter(module.EFFECT_HANDLERS))
    monkeypatch.setitem(
        module.ACTION_HANDLERS,
        "synthetic_success",
        lambda _adapter, _command, _interp=interp_mod, _effect_key=effect_key: _interp.StepOk(
            state={"after": "perp_clearinghouse_market_params_guard"},
            effects={_effect_key: True, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "perp_clearinghouse_market_params_guard"}
    assert dict(adapter.drain_effects()) == {effect_key: True}


def test_perp_clearinghouse_market_params_guard_accepts_happy_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_clearinghouse_market_params_guard_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="evaluate_clearinghouse_market_params_guard", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "market_kind_ok": True,
        "positions_open": False,
        "penalty_increase_ok": True,
        "penalty_below_maintenance_ok": True,
        "admission_ok": True,
        "reject_code": "Ok",
    }


def test_perp_clearinghouse_market_params_guard_rejects_penalty_increase_with_open_positions(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_clearinghouse_market_params_guard_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["position_base_a"] = 5
    state["new_liquidation_penalty_bps"] = 60
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_clearinghouse_market_params_guard", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["positions_open"] is True
    assert result.effects["admission_ok"] is False
    assert result.effects["reject_code"] == "PenaltyIncreaseWhileOpen"

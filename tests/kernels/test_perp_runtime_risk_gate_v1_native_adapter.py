from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/perp_runtime_risk_gate_v1.yaml")
ADAPTER = "src.kernels.python.perp_runtime_risk_gate_v1_native_adapter:make_adapter"


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

    interp_mod.StepOk = StepOk
    interp_mod.StepError = StepError
    kernel_mod.interpreter = interp_mod
    esso_mod.kernel = kernel_mod

    monkeypatch.setitem(sys.modules, "ESSO", esso_mod)
    monkeypatch.setitem(sys.modules, "ESSO.kernel", kernel_mod)
    monkeypatch.setitem(sys.modules, "ESSO.kernel.interpreter", interp_mod)
    return interp_mod


def _base_state() -> dict[str, int]:
    return {
        "action_kind": 1,
        "operator_ok": 1,
        "unknown_fields_ok": 1,
        "sender_binding_ok": 1,
        "epoch_settled_ok": 1,
        "positive_price_ok": 1,
        "positions_flat_ok": 1,
        "params_object_ok": 1,
    }


def test_perp_runtime_risk_gate_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_perp_runtime_risk_gate_v1_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_runtime_risk_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state={"before": 1})

    snapshot = dict(adapter.get_state())
    snapshot["before"] = 9
    assert dict(adapter.get_state()) == {"before": 1}

    unknown = adapter.apply(SimpleNamespace(tag="unknown"))
    assert isinstance(unknown, interp_mod.StepError)
    assert unknown.code == "UnknownAction"

    effect_key = next(iter(module.EFFECT_HANDLERS))
    monkeypatch.setitem(
        module.ACTION_HANDLERS,
        "synthetic_success",
        lambda _adapter, _command, _interp=interp_mod, _effect_key=effect_key: _interp.StepOk(
            state={"after": "perp_runtime_risk"},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "perp_runtime_risk"}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


def test_perp_runtime_risk_gate_v1_happy_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_runtime_risk_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="evaluate_runtime_risk_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "action_known": True,
        "operator_required": True,
        "operator_ok": True,
        "unknown_fields_ok": True,
        "sender_binding_required": False,
        "sender_binding_ok": True,
        "epoch_settled_required": True,
        "epoch_settled_ok": True,
        "positive_price_required": False,
        "positive_price_ok": True,
        "positions_flat_required": False,
        "positions_flat_ok": True,
        "params_object_required": False,
        "params_object_ok": True,
        "admission_ok": True,
        "reject_code": 0,
    }


def test_perp_runtime_risk_gate_v1_rejects_positions_open(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_runtime_risk_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["action_kind"] = 5
    state["positions_flat_ok"] = 0
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_runtime_risk_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["admission_ok"] is False
    assert result.effects["reject_code"] == 6


def test_perp_runtime_risk_gate_v1_rejects_noncanonical_flag(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_runtime_risk_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["unknown_fields_ok"] = 2
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_runtime_risk_gate", args={}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"

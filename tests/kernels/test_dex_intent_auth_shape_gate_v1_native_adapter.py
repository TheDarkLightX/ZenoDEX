from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace

MODEL = Path("src/kernels/dex/dex_intent_auth_shape_gate_v1.yaml")
ADAPTER = "src.kernels.python.dex_intent_auth_shape_gate_v1_native_adapter:make_adapter"


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


def _base_state() -> dict[str, object]:
    return {
        "intent_object_mode": False,
        "fields_object_ok": True,
        "explicit_fields_present": True,
        "explicit_fields_mapping_ok": True,
        "salt_present": True,
    }


def test_dex_intent_auth_shape_gate_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
    lint_path = tmp_path / "shell_lint.json"
    verify_path = tmp_path / "verify_shell.json"

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


def test_dex_intent_auth_shape_gate_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import dex_intent_auth_shape_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state={"before": True})

    unknown = adapter.apply(SimpleNamespace(tag="unknown"))
    assert isinstance(unknown, interp_mod.StepError)
    assert unknown.code == "UnknownAction"

    effect_key = next(iter(module.EFFECT_HANDLERS))
    monkeypatch.setitem(
        module.ACTION_HANDLERS,
        "synthetic_success",
        lambda _adapter, _command, _interp=interp_mod, _effect_key=effect_key: _interp.StepOk(
            state={"after": "dex_intent_auth_shape_gate"},
            effects={_effect_key: True, "ignored": False},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "dex_intent_auth_shape_gate"}
    assert dict(adapter.drain_effects()) == {effect_key: True}
    assert dict(adapter.drain_effects()) == {}


def test_dex_intent_auth_shape_gate_projects_explicit_mapping_branch(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import dex_intent_auth_shape_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="evaluate_intent_auth_shape_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "mapping_mode": True,
        "use_object_fields": False,
        "use_explicit_mapping_fields": True,
        "use_transport_flattened_fields": False,
        "include_salt": True,
        "shape_ok": True,
    }


def test_dex_intent_auth_shape_gate_rejects_bad_flag_domain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import dex_intent_auth_shape_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["explicit_fields_present"] = 9
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_intent_auth_shape_gate", args={}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"


def test_dex_intent_auth_shape_gate_reports_invalid_explicit_mapping(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import dex_intent_auth_shape_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["explicit_fields_mapping_ok"] = False
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_intent_auth_shape_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects)["shape_ok"] is False

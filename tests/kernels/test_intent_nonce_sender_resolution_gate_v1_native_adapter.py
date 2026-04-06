from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace

MODEL = Path("src/kernels/dex/intent_nonce_sender_resolution_gate_v1.yaml")
ADAPTER = "src.kernels.python.intent_nonce_sender_resolution_gate_v1_native_adapter:make_adapter"


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


def _base_state() -> dict[str, int | bool]:
    return {
        "strict_increasing": True,
        "contiguous_from_last": True,
        "last_used_nonce": 4,
        "next_last_nonce": 7,
    }


def test_intent_nonce_sender_resolution_gate_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
    lint_path = tmp_path / "shell_lint.json"
    verify_path = tmp_path / "shell_verify.json"

    subprocess.check_call(["python3", "-m", "ESSO", "shell-lint", str(MODEL), "--adapter", ADAPTER, "--output", str(lint_path)])
    lint = json.loads(lint_path.read_text(encoding="utf-8"))
    assert lint.get("ok") is True

    subprocess.check_call([
        "python3", "-m", "ESSO", "verify-shell", str(MODEL), "--adapter", ADAPTER,
        "--traces", "16", "--max-steps", "8", "--determinism-trials", "2", "--output", str(verify_path),
    ])
    verify = json.loads(verify_path.read_text(encoding="utf-8"))
    assert verify.get("ok") is True


def test_intent_nonce_sender_resolution_gate_unknown_action(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import intent_nonce_sender_resolution_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state={"before": 1})
    unknown = adapter.apply(SimpleNamespace(tag="unknown"))
    assert isinstance(unknown, interp_mod.StepError)
    assert unknown.code == "UnknownAction"


def test_intent_nonce_sender_resolution_gate_happy_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import intent_nonce_sender_resolution_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="evaluate_sender_resolution", args={}))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {"sender_ok": True, "resolved_last_nonce": 7, "reject_tag": 0}


def test_intent_nonce_sender_resolution_gate_gap(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import intent_nonce_sender_resolution_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["contiguous_from_last"] = False
    state["next_last_nonce"] = 4
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_sender_resolution", args={}))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {"sender_ok": False, "resolved_last_nonce": 4, "reject_tag": 2}


def test_intent_nonce_sender_resolution_gate_rejects_noncanonical_state(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import intent_nonce_sender_resolution_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["strict_increasing"] = 1
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_sender_resolution", args={}))
    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"

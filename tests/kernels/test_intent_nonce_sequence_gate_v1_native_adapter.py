from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace

MODEL = Path("src/kernels/dex/intent_nonce_sequence_gate_v1.yaml")
ADAPTER = "src.kernels.python.intent_nonce_sequence_gate_v1_native_adapter:make_adapter"


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
        "last_used_nonce": 4,
        "nonce_count": 3,
        "nonce_0": 5,
        "nonce_1": 6,
        "nonce_2": 7,
        "nonce_3": 1,
        "nonce_4": 1,
        "nonce_5": 1,
        "nonce_6": 1,
        "nonce_7": 1,
    }


def test_intent_nonce_sequence_gate_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
    lint_path = tmp_path / "shell_lint.json"
    verify_path = tmp_path / "shell_verify.json"

    subprocess.check_call([
        "python3",
        "-m",
        "ESSO",
        "shell-lint",
        str(MODEL),
        "--adapter",
        ADAPTER,
        "--output",
        str(lint_path),
    ])
    lint = json.loads(lint_path.read_text(encoding="utf-8"))
    assert lint.get("ok") is True

    subprocess.check_call([
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
    ])
    verify = json.loads(verify_path.read_text(encoding="utf-8"))
    assert verify.get("ok") is True


def test_intent_nonce_sequence_gate_unknown_action(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import intent_nonce_sequence_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state={"before": 1})
    unknown = adapter.apply(SimpleNamespace(tag="unknown"))
    assert isinstance(unknown, interp_mod.StepError)
    assert unknown.code == "UnknownAction"


def test_intent_nonce_sequence_gate_happy_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import intent_nonce_sequence_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="evaluate_nonce_sequence", args={}))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "strict_increasing": True,
        "contiguous_from_last": True,
        "sequence_ok": True,
        "next_last_nonce": 7,
    }
    assert dict(adapter.drain_effects()) == dict(result.effects)
    assert adapter.drain_effects() == {}


def test_intent_nonce_sequence_gate_reports_gap_via_effects(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import intent_nonce_sequence_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["nonce_1"] = 7
    state["nonce_2"] = 8
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_nonce_sequence", args={}))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "strict_increasing": True,
        "contiguous_from_last": False,
        "sequence_ok": False,
        "next_last_nonce": 4,
    }


def test_intent_nonce_sequence_gate_rejects_noncanonical_state(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import intent_nonce_sequence_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["nonce_count"] = True
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_nonce_sequence", args={}))
    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/perp_market_version_prefix_guard_v1.yaml")
ADAPTER = "src.kernels.python.perp_market_version_prefix_guard_v1_native_adapter:make_adapter"


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
        "version_is_v0_1": 0,
        "version_is_ch2p": 1,
        "version_is_ch3p": 0,
        "market_has_ch2p_prefix": 1,
        "market_has_ch3p_prefix": 0,
    }


def test_perp_market_version_prefix_guard_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_perp_market_version_prefix_guard_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_market_version_prefix_guard_v1_native_adapter as module

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
            state={"after": "perp_market_version_prefix_guard"},
            effects={_effect_key: True, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "perp_market_version_prefix_guard"}
    assert dict(adapter.drain_effects()) == {effect_key: True}


def test_perp_market_version_prefix_guard_accepts_ch2p_prefix(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_market_version_prefix_guard_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="check_market_version_prefix_guard", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "version_ok": True,
        "isolated_version": False,
        "clearinghouse_2p_version": True,
        "clearinghouse_3p_version": False,
        "market_prefix_ok": True,
        "admission_ok": True,
        "reject_code": "Ok",
    }


def test_perp_market_version_prefix_guard_rejects_missing_ch2p_prefix(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_market_version_prefix_guard_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["market_has_ch2p_prefix"] = 0
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="check_market_version_prefix_guard", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["admission_ok"] is False
    assert result.effects["reject_code"] == "Ch2pPrefixMismatch"


def test_perp_market_version_prefix_guard_rejects_isolated_prefix_conflict(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_market_version_prefix_guard_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["version_is_v0_1"] = 1
    state["version_is_ch2p"] = 0
    state["market_has_ch2p_prefix"] = 1
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="check_market_version_prefix_guard", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["isolated_version"] is True
    assert result.effects["admission_ok"] is False
    assert result.effects["reject_code"] == "IsolatedPrefixConflict"


def test_perp_market_version_prefix_guard_rejects_unknown_version(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_market_version_prefix_guard_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["version_is_ch2p"] = 0
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="check_market_version_prefix_guard", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["version_ok"] is False
    assert result.effects["admission_ok"] is False
    assert result.effects["reject_code"] == "InvalidVersion"

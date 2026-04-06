from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/perp_tau_ingress_stream_v1.yaml")
ADAPTER = "src.kernels.python.perp_tau_ingress_stream_v1_native_adapter:make_adapter"


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
        "upstream_stream_present": 0,
        "legacy_stream_present": 1,
        "legacy_dex_stream_present": 0,
        "legacy_candidate_dex_like": 0,
        "legacy_candidate_perp_like": 1,
    }


def test_perp_tau_ingress_stream_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_perp_tau_ingress_stream_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_tau_ingress_stream_v1_native_adapter as module

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
            state={"after": "perp_tau_ingress_stream"},
            effects={_effect_key: True, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "perp_tau_ingress_stream"}
    assert dict(adapter.drain_effects()) == {effect_key: True}
    assert dict(adapter.drain_effects()) == {}


def test_perp_tau_ingress_stream_accepts_upstream_stream(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_tau_ingress_stream_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["upstream_stream_present"] = 1
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="select_perp_stream", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "upstream_stream_selected": True,
        "legacy_fallback_used": False,
        "legacy_dex_conflict": False,
        "legacy_candidate_dex_like": False,
        "legacy_candidate_perp_like": True,
        "selected": True,
        "reject_code": "Ok",
    }


def test_perp_tau_ingress_stream_accepts_legacy_fallback(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_tau_ingress_stream_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="select_perp_stream", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["legacy_fallback_used"] is True
    assert result.effects["selected"] is True
    assert result.effects["reject_code"] == "Ok"


def test_perp_tau_ingress_stream_rejects_legacy_dex_conflict(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_tau_ingress_stream_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["legacy_dex_stream_present"] = 1
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="select_perp_stream", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["legacy_dex_conflict"] is True
    assert result.effects["selected"] is False
    assert result.effects["reject_code"] == "LegacyDexConflict"


def test_perp_tau_ingress_stream_rejects_legacy_candidate_that_looks_like_dex(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_tau_ingress_stream_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["legacy_candidate_dex_like"] = 1
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="select_perp_stream", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["legacy_candidate_dex_like"] is True
    assert result.effects["selected"] is False
    assert result.effects["reject_code"] == "LegacyLooksLikeDex"


def test_perp_tau_ingress_stream_rejects_non_perp_legacy_candidate(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_tau_ingress_stream_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["legacy_candidate_perp_like"] = 0
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="select_perp_stream", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["selected"] is False
    assert result.effects["reject_code"] == "LegacyNotPerp"

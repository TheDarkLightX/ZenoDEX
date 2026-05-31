from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/perp_signed_surface_guard_v1.yaml")
ADAPTER = "src.kernels.python.perp_signed_surface_guard_v1_native_adapter:make_adapter"


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
        "version_ok": 1,
        "unknown_fields_ok": 1,
        "distinct_accounts_ok": 1,
        "market_accounts_match_ok": 1,
        "net_zero_ok": 1,
        "idle_leg_ok": 1,
        "positive_price_ok": 1,
    }


def test_perp_signed_surface_guard_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_perp_signed_surface_guard_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_signed_surface_guard_v1_native_adapter as module

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
            state={"after": "perp_signed_surface_guard"},
            effects={_effect_key: True, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "perp_signed_surface_guard"}
    assert dict(adapter.drain_effects()) == {effect_key: True}


def test_perp_signed_surface_guard_accepts_valid_surface(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_signed_surface_guard_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="evaluate_signed_surface_guard", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "action_known": True,
        "version_ok": True,
        "unknown_fields_ok": True,
        "distinct_accounts_ok": True,
        "market_accounts_match_ok": True,
        "net_zero_ok": True,
        "idle_leg_ok": True,
        "positive_price_ok": True,
        "signed_surface_ok": True,
        "reject_code": "Ok",
    }


def test_perp_signed_surface_guard_rejects_unknown_fields_before_other_checks(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_signed_surface_guard_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["unknown_fields_ok"] = 0
    state["distinct_accounts_ok"] = 0
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_signed_surface_guard", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["signed_surface_ok"] is False
    assert result.effects["reject_code"] == "UnknownFields"

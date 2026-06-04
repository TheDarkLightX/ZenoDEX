from __future__ import annotations

import json
import importlib.util
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace

import pytest


MODEL = Path("src/kernels/dex/zusd_repay_single_vault_v1.yaml")
ADAPTER = "src.kernels.python.zusd_repay_single_vault_v1_native_adapter:make_adapter"


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
        "debt_e8": 12_000_000_000,
        "free_debt_e8": 9_000_000_000,
    }


def test_zusd_repay_single_vault_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
    if importlib.util.find_spec("ESSO") is None:
        pytest.skip("ESSO CLI module is not installed")

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


def test_zusd_repay_single_vault_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_repay_single_vault_v1_native_adapter as module

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
            state={"after": "zusd_repay"},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "zusd_repay"}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


def test_zusd_repay_single_vault_happy_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_repay_single_vault_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="apply_repay_single_vault", args={"amount_e8": 4_000_000_000}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.state) == {
        "debt_e8": 8_000_000_000,
        "free_debt_e8": 5_000_000_000,
    }
    assert dict(result.effects) == {
        "repaid_zusd_e8": 4_000_000_000,
        "debt_after_e8": 8_000_000_000,
        "free_debt_after_e8": 5_000_000_000,
        "debt_delta_e8": 4_000_000_000,
        "free_debt_delta_e8": 4_000_000_000,
    }


def test_zusd_repay_single_vault_rejects_excess_debt(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_repay_single_vault_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["debt_e8"] = 3_000_000_000
    state["free_debt_e8"] = 3_000_000_000
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="apply_repay_single_vault", args={"amount_e8": 4_000_000_000}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"


def test_zusd_repay_single_vault_rejects_excess_free_debt(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_repay_single_vault_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["debt_e8"] = 12_000_000_000
    state["free_debt_e8"] = 2_000_000_000
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="apply_repay_single_vault", args={"amount_e8": 4_000_000_000}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"


def test_zusd_repay_single_vault_exact_zero_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_repay_single_vault_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state={"debt_e8": 2_000_000_000, "free_debt_e8": 2_000_000_000})
    result = adapter.apply(SimpleNamespace(tag="apply_repay_single_vault", args={"amount_e8": 2_000_000_000}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.state) == {"debt_e8": 0, "free_debt_e8": 0}
    assert dict(result.effects) == {
        "repaid_zusd_e8": 2_000_000_000,
        "debt_after_e8": 0,
        "free_debt_after_e8": 0,
        "debt_delta_e8": 2_000_000_000,
        "free_debt_delta_e8": 2_000_000_000,
    }

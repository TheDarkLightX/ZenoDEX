from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace

import pytest


MODEL = Path("src/kernels/dex/settlement_add_liquidity_ratio_witness_v1.yaml")
ADAPTER = "src.kernels.python.settlement_add_liquidity_ratio_witness_v1_native_adapter:make_adapter"


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


def test_settlement_add_liquidity_ratio_witness_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_add_liquidity_ratio_native_adapter_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import settlement_add_liquidity_ratio_witness_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state={"before": 1})

    snapshot = dict(adapter.get_state())
    snapshot["before"] = 99
    assert dict(adapter.get_state()) == {"before": 1}

    unknown = adapter.apply(SimpleNamespace(tag="unknown"))
    assert isinstance(unknown, interp_mod.StepError)
    assert unknown.code == "UnknownAction"

    effect_key = next(iter(module.EFFECT_HANDLERS))
    monkeypatch.setitem(
        module.ACTION_HANDLERS,
        "synthetic_success",
        lambda _adapter, _command, _interp=interp_mod, _effect_key=effect_key: _interp.StepOk(
            state={"after": "settlement_add_liquidity_ratio"},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "settlement_add_liquidity_ratio"}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


@pytest.mark.parametrize(
    ("state_patch", "args_patch"),
    [
        ({"pool_active": 0}, {}),
        ({}, {"amount0_used": 401}),
        ({}, {"amount0_refund": 1}),
        ({}, {"amount1_used": 799}),
        ({}, {"amount1_used": 201, "amount1_refund": 799}),
    ],
)
def test_add_liquidity_ratio_native_adapter_rejects_guard_edges(
    monkeypatch,
    state_patch: dict[str, int],
    args_patch: dict[str, int],
) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import settlement_add_liquidity_ratio_witness_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "pool_active": 1,
        "reserve0": 1000,
        "reserve1": 2000,
    }
    args = {
        "amount0_desired": 400,
        "amount1_desired": 900,
        "amount0_used": 400,
        "amount1_used": 800,
        "amount0_refund": 0,
        "amount1_refund": 100,
    }
    state.update(state_patch)
    args.update(args_patch)

    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="bind_add_liquidity_ratio", args=args))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert dict(adapter.get_state()) == state
    assert dict(adapter.drain_effects()) == {}


def test_add_liquidity_ratio_native_adapter_commits_left_branch(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import settlement_add_liquidity_ratio_witness_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "pool_active": 1,
        "reserve0": 1000,
        "reserve1": 2000,
    }
    args = {
        "amount0_desired": 400,
        "amount1_desired": 900,
        "amount0_used": 400,
        "amount1_used": 800,
        "amount0_refund": 0,
        "amount1_refund": 100,
    }

    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="bind_add_liquidity_ratio", args=args))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.state) == state
    assert dict(result.effects) == {
        "amount0_used": 400,
        "amount1_used": 800,
        "amount0_refund": 0,
        "amount1_refund": 100,
        "binding_ok": 1,
        "left_branch": True,
    }
    assert dict(adapter.get_state()) == state
    assert dict(adapter.drain_effects()) == dict(result.effects)


def test_add_liquidity_ratio_native_adapter_commits_right_branch(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import settlement_add_liquidity_ratio_witness_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "pool_active": 1,
        "reserve0": 1000,
        "reserve1": 2000,
    }
    args = {
        "amount0_desired": 800,
        "amount1_desired": 300,
        "amount0_used": 150,
        "amount1_used": 300,
        "amount0_refund": 650,
        "amount1_refund": 0,
    }

    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="bind_add_liquidity_ratio", args=args))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.state) == state
    assert dict(result.effects) == {
        "amount0_used": 150,
        "amount1_used": 300,
        "amount0_refund": 650,
        "amount1_refund": 0,
        "binding_ok": 1,
        "left_branch": False,
    }
    assert dict(adapter.get_state()) == state
    assert dict(adapter.drain_effects()) == dict(result.effects)

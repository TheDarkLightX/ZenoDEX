from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace

import pytest


MODEL = Path("src/kernels/dex/settlement_create_pool_apply_witness_v1.yaml")
ADAPTER = "src.kernels.python.settlement_create_pool_apply_witness_v1_native_adapter:make_adapter"


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


def test_settlement_create_pool_apply_witness_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_create_pool_native_adapter_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import settlement_create_pool_apply_witness_v1_native_adapter as module

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
            state={"after": "settlement_create_pool"},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "settlement_create_pool"}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


@pytest.mark.parametrize(
    ("state_patch", "args_patch"),
    [
        ({"pool_initialized": 1}, {}),
        ({"reserve0": 1}, {}),
        ({"creator_asset0": 1000}, {"amount0": 1001}),
        ({"creator_asset1": 1000}, {"amount1": 1001}),
        ({}, {"fee_bps": 10001}),
        ({}, {"sqrt_product": 1000}),
        ({}, {"sqrt_product": 1100, "amount0": 1001, "amount1": 1001}),
        ({}, {"sqrt_product": 1001, "amount0": 2000, "amount1": 2000}),
        ({"creator_lp": 1}, {}),
    ],
)
def test_create_pool_native_adapter_rejects_guard_edges(
    monkeypatch,
    state_patch: dict[str, int],
    args_patch: dict[str, int],
) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import settlement_create_pool_apply_witness_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "pool_initialized": 0,
        "creator_asset0": 2000,
        "creator_asset1": 2000,
        "creator_lp": 0,
        "lock_lp": 0,
        "reserve0": 0,
        "reserve1": 0,
        "lp_supply": 0,
        "total_asset0_const": 2000,
        "total_asset1_const": 2000,
    }
    args = {
        "amount0": 2000,
        "amount1": 2000,
        "fee_bps": 30,
        "sqrt_product": 2000,
    }
    state.update(state_patch)
    args.update(args_patch)

    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="create_pool_apply", args=args))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert dict(adapter.get_state()) == state
    assert dict(adapter.drain_effects()) == {}


def test_create_pool_native_adapter_commits_success_effects(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import settlement_create_pool_apply_witness_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "pool_initialized": 0,
        "creator_asset0": 2000,
        "creator_asset1": 2000,
        "creator_lp": 0,
        "lock_lp": 0,
        "reserve0": 0,
        "reserve1": 0,
        "lp_supply": 0,
        "total_asset0_const": 2000,
        "total_asset1_const": 2000,
    }
    args = {
        "amount0": 2000,
        "amount1": 2000,
        "fee_bps": 30,
        "sqrt_product": 2000,
    }

    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="create_pool_apply", args=args))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.state) == {
        "pool_initialized": 1,
        "creator_asset0": 0,
        "creator_asset1": 0,
        "creator_lp": 1000,
        "lock_lp": 1000,
        "reserve0": 2000,
        "reserve1": 2000,
        "lp_supply": 2000,
        "total_asset0_const": 2000,
        "total_asset1_const": 2000,
    }
    assert dict(result.effects) == {
        "amount0_used": 2000,
        "amount1_used": 2000,
        "lp_minted": 1000,
        "reserve0_after": 2000,
        "reserve1_after": 2000,
        "lp_supply_after": 2000,
        "witness_ok": True,
        "balance_delta_ok": 1,
        "reserve_delta_ok": 1,
        "lp_delta_ok": 1,
    }
    assert dict(adapter.get_state()) == dict(result.state)
    assert dict(adapter.drain_effects()) == dict(result.effects)

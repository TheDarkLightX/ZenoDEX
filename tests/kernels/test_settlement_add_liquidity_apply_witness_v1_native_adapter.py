from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace

import pytest


MODEL = Path("src/kernels/dex/settlement_add_liquidity_apply_witness_v1.yaml")
ADAPTER = "src.kernels.python.settlement_add_liquidity_apply_witness_v1_native_adapter:make_adapter"


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


def test_settlement_add_liquidity_apply_witness_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_add_liquidity_native_adapter_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import settlement_add_liquidity_apply_witness_v1_native_adapter as module

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
            state={"after": "settlement_add_liquidity"},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "settlement_add_liquidity"}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


@pytest.mark.parametrize(
    ("state_patch", "args_patch"),
    [
        ({"pool_active": 0}, {}),
        ({"sender_asset0": 499}, {"amount0_used": 500}),
        ({"sender_asset1": 499}, {"amount1_used": 500}),
        ({}, {"amount0_used": 1001}),
        ({}, {"amount1_used": 1001}),
        ({}, {"lp_minted": 751}),
        ({"recipient_lp": 2501}, {"lp_minted": 500}),
    ],
)
def test_add_liquidity_native_adapter_rejects_guard_edges(
    monkeypatch,
    state_patch: dict[str, int],
    args_patch: dict[str, int],
) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import settlement_add_liquidity_apply_witness_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "pool_active": 1,
        "sender_asset0": 1000,
        "sender_asset1": 1000,
        "recipient_lp": 2000,
        "lock_lp": 1000,
        "reserve0_before": 2000,
        "reserve0": 2000,
        "reserve1_before": 2000,
        "reserve1": 2000,
        "lp_supply_before": 3000,
        "lp_supply": 3000,
        "total_asset0_const": 3000,
        "total_asset1_const": 3000,
    }
    args = {
        "amount0_used": 500,
        "amount1_used": 500,
        "lp_minted": 750,
    }
    state.update(state_patch)
    args.update(args_patch)

    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="add_liquidity_apply", args=args))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert dict(adapter.get_state()) == state
    assert dict(adapter.drain_effects()) == {}


def test_add_liquidity_native_adapter_commits_success_effects(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import settlement_add_liquidity_apply_witness_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "pool_active": 1,
        "sender_asset0": 1000,
        "sender_asset1": 1000,
        "recipient_lp": 2000,
        "lock_lp": 1000,
        "reserve0_before": 2000,
        "reserve0": 2000,
        "reserve1_before": 2000,
        "reserve1": 2000,
        "lp_supply_before": 3000,
        "lp_supply": 3000,
        "total_asset0_const": 3000,
        "total_asset1_const": 3000,
    }
    args = {
        "amount0_used": 500,
        "amount1_used": 500,
        "lp_minted": 750,
    }

    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="add_liquidity_apply", args=args))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.state) == {
        "pool_active": 1,
        "sender_asset0": 500,
        "sender_asset1": 500,
        "recipient_lp": 2750,
        "lock_lp": 1000,
        "reserve0_before": 2000,
        "reserve0": 2500,
        "reserve1_before": 2000,
        "reserve1": 2500,
        "lp_supply_before": 3000,
        "lp_supply": 3750,
        "total_asset0_const": 3000,
        "total_asset1_const": 3000,
    }
    assert dict(result.effects) == {
        "amount0_used": 500,
        "amount1_used": 500,
        "lp_minted": 750,
        "reserve0_after": 2500,
        "reserve1_after": 2500,
        "lp_supply_after": 3750,
        "lp_math_ok": True,
        "balance_delta_ok": 1,
        "reserve_delta_ok": 1,
        "lp_delta_ok": 1,
    }
    assert dict(adapter.get_state()) == dict(result.state)
    assert dict(adapter.drain_effects()) == dict(result.effects)

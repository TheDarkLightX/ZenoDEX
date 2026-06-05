from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


RATIO_MODEL = Path("src/kernels/dex/lp_ratio_calculator_v7.yaml")
RATIO_ADAPTER = "src.kernels.python.lp_ratio_calculator_v7_rust_adapter:make_adapter"
MINT_MODEL = Path("src/kernels/dex/lp_mint_v7.yaml")
MINT_ADAPTER = "src.kernels.python.lp_mint_v7_rust_adapter:make_adapter"


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


def _run_json(cmd: list[str], *, out: Path) -> dict[str, object]:
    subprocess.check_call([*cmd, "--output", str(out)])
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload.get("ok") is True
    return payload


def test_lp_math_v7_rust_adapters_esso_shell_lint_and_verify(tmp_path: Path) -> None:
    _run_json(
        ["python3", "-m", "ESSO", "shell-lint", str(RATIO_MODEL), "--adapter", RATIO_ADAPTER],
        out=tmp_path / "ratio_shell_lint.json",
    )
    _run_json(
        [
            "python3",
            "-m",
            "ESSO",
            "verify-shell",
            str(RATIO_MODEL),
            "--adapter",
            RATIO_ADAPTER,
            "--traces",
            "16",
            "--max-steps",
            "8",
            "--determinism-trials",
            "2",
        ],
        out=tmp_path / "ratio_verify_shell.json",
    )
    _run_json(
        ["python3", "-m", "ESSO", "shell-lint", str(MINT_MODEL), "--adapter", MINT_ADAPTER],
        out=tmp_path / "mint_shell_lint.json",
    )
    _run_json(
        [
            "python3",
            "-m",
            "ESSO",
            "verify-shell",
            str(MINT_MODEL),
            "--adapter",
            MINT_ADAPTER,
            "--traces",
            "16",
            "--max-steps",
            "8",
            "--determinism-trials",
            "2",
        ],
        out=tmp_path / "mint_verify_shell.json",
    )


def test_lp_mint_v7_rust_adapter_rejects_noninitial_mint_on_empty_state(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import lp_mint_v7_rust_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    empty_state = {
        "reserve0_before": 0,
        "reserve0": 0,
        "reserve1_before": 0,
        "reserve1": 0,
        "lp_supply_before": 0,
        "lp_supply": 0,
        "locked_liquidity": 0,
    }
    adapter.reset(state=empty_state)
    result = adapter.apply(
        SimpleNamespace(
            tag="mint",
            args={"amount0": 1_000_000_000, "amount1": 1, "min_liquidity": 3_000_000_000},
        )
    )
    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert dict(adapter.get_state()) == empty_state
    assert dict(adapter.drain_effects()) == {}


def test_lp_ratio_v7_rust_adapter_rejects_mixed_zero_pool_state(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import lp_ratio_calculator_v7_rust_adapter as module

    def fail_if_called(*_args):
        raise AssertionError("mixed-zero states must fail before calling Rust")

    monkeypatch.setattr(module, "run_rust_lp_math", fail_if_called)
    adapter = module.make_adapter(ir={"schema": "fake"})
    mixed_state = {"reserve0": 0, "reserve1": 1}
    adapter.reset(state=mixed_state)
    result = adapter.apply(SimpleNamespace(tag="calculate_optimal", args={"desired0": 10, "desired1": 10}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert dict(adapter.get_state()) == mixed_state
    assert dict(adapter.drain_effects()) == {}


def test_lp_mint_v7_rust_adapter_rejects_noninitial_post_state_outside_model_bounds(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import lp_mint_v7_rust_adapter as module

    def fail_if_called(*_args):
        raise AssertionError("out-of-domain post-states must fail before calling Rust")

    monkeypatch.setattr(module, "run_rust_lp_math", fail_if_called)
    adapter = module.make_adapter(ir={"schema": "fake"})
    edge_state = {
        "reserve0_before": 3_000_000_000,
        "reserve0": 3_000_000_000,
        "reserve1_before": 1,
        "reserve1": 1,
        "lp_supply_before": 1,
        "lp_supply": 1,
        "locked_liquidity": 1000,
    }
    adapter.reset(state=edge_state)
    result = adapter.apply(SimpleNamespace(tag="mint", args={"amount0": 1, "amount1": 1, "min_liquidity": 0}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert dict(adapter.get_state()) == edge_state
    assert dict(adapter.drain_effects()) == {}

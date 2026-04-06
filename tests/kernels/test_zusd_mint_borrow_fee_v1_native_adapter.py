from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/zusd_mint_borrow_fee_v1.yaml")
ADAPTER = "src.kernels.python.zusd_mint_borrow_fee_v1_native_adapter:make_adapter"


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
        "now_epoch": 5,
        "price_e8": 10_000_000_000,
        "collateral_e8": 200_000_000,
        "debt_e8": 0,
        "free_debt_e8": 0,
        "max_debt_e8": 50_000_000_000,
        "max_debt_supply_e8": 50_000_000_000,
        "mcr_bps": 11_000,
        "min_debt_open_e8": 5_000_000_000,
        "base_rate_bps": 100,
        "base_rate_last_epoch": 0,
        "base_rate_decay_per_epoch_bps": 10,
        "base_rate_borrow_bump_bps": 20,
        "borrow_fee_floor_bps": 50,
        "borrow_fee_max_bps": 500,
    }


def test_zusd_mint_borrow_fee_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_zusd_mint_borrow_fee_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_mint_borrow_fee_v1_native_adapter as module

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
            state={"after": "zusd_mint"},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "zusd_mint"}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


def test_zusd_mint_borrow_fee_happy_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_mint_borrow_fee_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="apply_mint_borrow_fee", args={"amount_e8": 10_000_000_000}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.state) == {
        "now_epoch": 5,
        "price_e8": 10_000_000_000,
        "collateral_e8": 200_000_000,
        "debt_e8": 10_100_000_000,
        "free_debt_e8": 10_100_000_000,
        "max_debt_e8": 50_000_000_000,
        "max_debt_supply_e8": 50_000_000_000,
        "mcr_bps": 11_000,
        "min_debt_open_e8": 5_000_000_000,
        "base_rate_bps": 70,
        "base_rate_last_epoch": 5,
        "base_rate_decay_per_epoch_bps": 10,
        "base_rate_borrow_bump_bps": 20,
        "borrow_fee_floor_bps": 50,
        "borrow_fee_max_bps": 500,
    }
    assert dict(result.effects) == {
        "principal_e8": 10_000_000_000,
        "mint_fee_e8": 100_000_000,
        "mint_fee_bps": 100,
        "debt_delta_e8": 10_100_000_000,
        "debt_after_e8": 10_100_000_000,
        "free_debt_after_e8": 10_100_000_000,
        "decayed_base_rate_bps": 50,
        "base_rate_after_bps": 70,
        "base_rate_last_epoch_after": 5,
        "mcr_post_ok": True,
    }


def test_zusd_mint_borrow_fee_rejects_min_open(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_mint_borrow_fee_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="apply_mint_borrow_fee", args={"amount_e8": 4_000_000_000}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"


def test_zusd_mint_borrow_fee_rejects_global_cap(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_mint_borrow_fee_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["free_debt_e8"] = 49_000_000_000
    state["debt_e8"] = 10_000_000_000
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="apply_mint_borrow_fee", args={"amount_e8": 2_000_000_000}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"


def test_zusd_mint_borrow_fee_rejects_post_mcr(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_mint_borrow_fee_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["collateral_e8"] = 50_000_000
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="apply_mint_borrow_fee", args={"amount_e8": 10_000_000_000}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"

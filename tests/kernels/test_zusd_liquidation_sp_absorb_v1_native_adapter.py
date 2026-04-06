from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/zusd_liquidation_sp_absorb_v1.yaml")
ADAPTER = "src.kernels.python.zusd_liquidation_sp_absorb_v1_native_adapter:make_adapter"


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
        "price_pending_e8": 7_000_000_000,
        "collateral_e8": 200_000_000,
        "debt_e8": 15_000_000_000,
        "sp_debt_e8": 15_000_000_000,
        "sp_coll_e8": 0,
        "max_sp_coll_e8": 2_000_000_000_000,
        "mcr_bps": 11_000,
        "debt_before": 0,
        "collateral_before": 0,
    }


def test_zusd_liquidation_sp_absorb_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_zusd_liquidation_sp_absorb_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_liquidation_sp_absorb_v1_native_adapter as module

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
            state={"after": "zusd_liquidation"},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "zusd_liquidation"}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


def test_zusd_liquidation_sp_absorb_happy_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_liquidation_sp_absorb_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="apply_liquidation_sp_absorb", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.state) == {
        "price_pending_e8": 7_000_000_000,
        "collateral_e8": 0,
        "debt_e8": 0,
        "sp_debt_e8": 0,
        "sp_coll_e8": 200_000_000,
        "max_sp_coll_e8": 2_000_000_000_000,
        "mcr_bps": 11_000,
        "debt_before": 15_000_000_000,
        "collateral_before": 200_000_000,
    }
    assert dict(result.effects) == {
        "liquidated_debt_e8": 15_000_000_000,
        "liquidated_collateral_e8": 200_000_000,
        "sp_debt_after": 0,
        "sp_coll_after": 200_000_000,
        "under_mcr": True,
    }


def test_zusd_liquidation_sp_absorb_rejects_not_under_mcr(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_liquidation_sp_absorb_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["price_pending_e8"] = 10_000_000_000
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="apply_liquidation_sp_absorb", args={}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"


def test_zusd_liquidation_sp_absorb_rejects_sp_debt_shortfall(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_liquidation_sp_absorb_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["sp_debt_e8"] = 14_000_000_000
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="apply_liquidation_sp_absorb", args={}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"


def test_zusd_liquidation_sp_absorb_rejects_sp_collateral_cap(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_liquidation_sp_absorb_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["sp_coll_e8"] = 1_999_900_000_000
    state["max_sp_coll_e8"] = 2_000_000_000_000
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="apply_liquidation_sp_absorb", args={}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"

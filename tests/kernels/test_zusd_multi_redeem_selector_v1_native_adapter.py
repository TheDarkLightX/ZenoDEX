from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/zusd_multi_redeem_selector_v1.yaml")
ADAPTER = "src.kernels.python.zusd_multi_redeem_selector_v1_native_adapter:make_adapter"
E8 = 100_000_000


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
        "amount_e8": 50 * E8,
        "price_e8": 100 * E8,
        "mcr_bps": 11_000,
        "vault_a_collateral_e8": 5 * E8,
        "vault_a_debt_e8": 200 * E8,
        "vault_b_collateral_e8": 5 * E8,
        "vault_b_debt_e8": 300 * E8,
    }


def test_zusd_multi_redeem_selector_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_zusd_multi_redeem_selector_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_multi_redeem_selector_v1_native_adapter as module

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
            state={"after": "zusd_multi_redeem_selector"},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "zusd_multi_redeem_selector"}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


def test_zusd_multi_redeem_selector_picks_vault_b(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_multi_redeem_selector_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="select_redeem_vault", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "gross_collateral_e8": 50_000_000,
        "candidate_a_ok": True,
        "candidate_b_ok": True,
        "headroom_a_before_e8": 28_000_000_000_000_000_000_000,
        "headroom_b_before_e8": 17_000_000_000_000_000_000_000,
        "selection_ok": True,
        "selected_vault": "VaultB",
    }


def test_zusd_multi_redeem_selector_tie_breaks_to_vault_a(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_multi_redeem_selector_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["vault_a_collateral_e8"] = 4 * E8
    state["vault_a_debt_e8"] = 200 * E8
    state["vault_b_collateral_e8"] = 4 * E8
    state["vault_b_debt_e8"] = 200 * E8
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="select_redeem_vault", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["selection_ok"] is True
    assert result.effects["selected_vault"] == "VaultA"


def test_zusd_multi_redeem_selector_guard_false_on_tiny_gross(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_multi_redeem_selector_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["amount_e8"] = 1
    state["price_e8"] = 10**30
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="select_redeem_vault", args={}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"

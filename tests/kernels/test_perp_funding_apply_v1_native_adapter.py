from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/perp_funding_apply_v1.yaml")
ADAPTER = "src.kernels.python.perp_funding_apply_v1_native_adapter:make_adapter"


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
        "now_epoch": 10,
        "epoch_phase": 0,
        "auth_ok": 1,
        "index_price_e8": 100_000_000,
        "oracle_last_update_epoch": 9,
        "max_oracle_staleness_epochs": 2,
        "oracle_seen": 1,
        "funding_last_applied_epoch": 9,
        "funding_cap_bps": 100,
        "new_rate_bps": 50,
        "position_base": 1_000,
        "collateral_quote": 100_000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "funding_paid_cumulative": 0,
    }


def test_perp_funding_apply_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_perp_funding_apply_v1_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_funding_apply_v1_native_adapter as module

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
            state={"after": "perp_funding_apply"},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "perp_funding_apply"}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


def test_perp_funding_apply_v1_happy_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_funding_apply_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="evaluate_funding_apply_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "phase_allows_funding": True,
        "auth_ok": True,
        "index_price_ok": True,
        "staleness_param_ok": True,
        "oracle_seen_ok": True,
        "oracle_fresh": True,
        "funding_not_applied_this_epoch": True,
        "rate_within_cap": True,
        "position_open_ok": True,
        "funding_payment_quote": 5,
        "collateral_after_quote": 99_995,
        "collateral_bounds_ok": True,
        "maint_req_quote": 60,
        "maint_margin_ok": True,
        "cumulative_after_quote": 5,
        "cumulative_bounds_ok": True,
        "funding_apply_allowed": True,
    }


def test_perp_funding_apply_v1_rejects_margin_violation(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_funding_apply_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["collateral_quote"] = 6
    state["position_base"] = 100
    state["new_rate_bps"] = 100
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_funding_apply_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["maint_margin_ok"] is False
    assert result.effects["funding_apply_allowed"] is False


def test_perp_funding_apply_v1_rejects_noncanonical_flag(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_funding_apply_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["auth_ok"] = 2
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_funding_apply_gate", args={}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"

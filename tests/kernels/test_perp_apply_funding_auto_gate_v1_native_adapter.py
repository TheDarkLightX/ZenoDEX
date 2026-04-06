from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/perp_apply_funding_auto_gate_v1.yaml")
ADAPTER = "src.kernels.python.perp_apply_funding_auto_gate_v1_native_adapter:make_adapter"


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
        "now_epoch": 3,
        "clearing_price_seen": 1,
        "clearing_price_epoch": 3,
        "oracle_last_update_epoch": 2,
        "oracle_seen": 1,
        "index_price_e8": 100_000_000,
        "max_oracle_staleness_epochs": 2,
        "clearing_price_e8": 102_000_000,
        "max_oracle_move_bps": 1_000,
        "funding_cap_bps": 100,
        "projected_net_funding_quote": 0,
        "any_funding_applied_this_epoch": 0,
    }


def test_perp_apply_funding_auto_gate_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_perp_apply_funding_auto_gate_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_apply_funding_auto_gate_v1_native_adapter as module

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
            state={"after": "perp_apply_funding_auto_gate"},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "perp_apply_funding_auto_gate"}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


def test_perp_apply_funding_auto_gate_happy_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_apply_funding_auto_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="evaluate_apply_funding_auto_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "clearing_price_seen_ok": True,
        "clearing_price_epoch_ok": True,
        "pre_settlement_window_ok": True,
        "oracle_seen_ok": True,
        "index_price_ok": True,
        "staleness_param_ok": True,
        "oracle_fresh": True,
        "clearing_price_ok": True,
        "max_oracle_move_ok": True,
        "funding_cap_ok": True,
        "net_funding_balanced": True,
        "funding_not_applied": True,
        "funding_auto_allowed": True,
    }


def test_perp_apply_funding_auto_gate_rejects_stale_oracle(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_apply_funding_auto_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["now_epoch"] = 6
    state["max_oracle_staleness_epochs"] = 1
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_apply_funding_auto_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["oracle_fresh"] is False
    assert result.effects["funding_auto_allowed"] is False


def test_perp_apply_funding_auto_gate_rejects_net_imbalance(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_apply_funding_auto_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["projected_net_funding_quote"] = 9
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_apply_funding_auto_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["net_funding_balanced"] is False
    assert result.effects["funding_auto_allowed"] is False


def test_perp_apply_funding_auto_gate_rejects_double_apply(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_apply_funding_auto_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["any_funding_applied_this_epoch"] = 1
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_apply_funding_auto_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["funding_not_applied"] is False
    assert result.effects["funding_auto_allowed"] is False

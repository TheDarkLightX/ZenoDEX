from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/zusd_risky_ops_gate_v1.yaml")
ADAPTER = "src.kernels.python.zusd_risky_ops_gate_v1_native_adapter:make_adapter"


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
        "oracle_seen": 1,
        "oracle_last_update_epoch": 4,
        "price_e8": 100_000_000,
        "price_pending_e8": 100_000_000,
        "max_oracle_staleness_epochs": 2,
        "total_collateral_e8": 200_000_000,
        "total_debt_e8": 100_000_000,
        "sp_coll_e8": 0,
        "protocol_collateral_e8": 0,
        "ccr_bps": 15_000,
    }


def test_zusd_risky_ops_gate_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_zusd_risky_ops_gate_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_risky_ops_gate_v1_native_adapter as module

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
            state={"after": "zusd_risky_ops"},
            effects={_effect_key: True, "ignored": False},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "zusd_risky_ops"}
    assert dict(adapter.drain_effects()) == {effect_key: True}
    assert dict(adapter.drain_effects()) == {}


def test_zusd_risky_ops_gate_healthy_case(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_risky_ops_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="check_risky_ops_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "oracle_initialized": True,
        "oracle_fresh": True,
        "pending_matches_active": True,
        "tcr_ok": True,
        "recovery_mode": False,
        "risky_ops_allowed": True,
    }


def test_zusd_risky_ops_gate_blocks_pending_mismatch(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_risky_ops_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["price_pending_e8"] = 90_000_000
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="check_risky_ops_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["oracle_initialized"] is True
    assert result.effects["pending_matches_active"] is False
    assert result.effects["risky_ops_allowed"] is False
    assert result.effects["recovery_mode"] is False


def test_zusd_risky_ops_gate_blocks_stale_oracle(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_risky_ops_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["oracle_last_update_epoch"] = 1
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="check_risky_ops_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["oracle_fresh"] is False
    assert result.effects["risky_ops_allowed"] is False


def test_zusd_risky_ops_gate_reports_recovery_mode(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_risky_ops_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["price_e8"] = 75_000_000
    state["price_pending_e8"] = 75_000_000
    state["total_debt_e8"] = 120_000_000
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="check_risky_ops_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["tcr_ok"] is False
    assert result.effects["recovery_mode"] is True
    assert result.effects["risky_ops_allowed"] is False


def test_zusd_risky_ops_gate_unbootstrapped_oracle(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_risky_ops_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["oracle_seen"] = 0
    state["oracle_last_update_epoch"] = 0
    state["price_e8"] = 0
    state["price_pending_e8"] = 0
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="check_risky_ops_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "oracle_initialized": False,
        "oracle_fresh": False,
        "pending_matches_active": True,
        "tcr_ok": False,
        "recovery_mode": True,
        "risky_ops_allowed": False,
    }

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/zusd_oracle_commit_apply_v1.yaml")
ADAPTER = "src.kernels.python.zusd_oracle_commit_apply_v1_native_adapter:make_adapter"


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
        "oracle_seen": 1,
        "oracle_last_update_epoch": 8,
        "price_e8": 10_000_000_000,
        "price_pending_e8": 9_000_000_000,
        "max_oracle_staleness_epochs": 5,
        "auth_ok": 1,
        "mcr_ok_at_pending": 1,
    }


def test_zusd_oracle_commit_apply_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_zusd_oracle_commit_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_oracle_commit_apply_v1_native_adapter as module

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
            state={"after": "zusd_oracle_commit"},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "zusd_oracle_commit"}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


def test_zusd_oracle_commit_happy_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_oracle_commit_apply_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="apply_oracle_commit", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.state) == {
        "now_epoch": 10,
        "oracle_seen": 1,
        "oracle_last_update_epoch": 10,
        "price_e8": 9_000_000_000,
        "price_pending_e8": 9_000_000_000,
        "max_oracle_staleness_epochs": 5,
        "auth_ok": 1,
        "mcr_ok_at_pending": 1,
    }
    assert dict(result.effects) == {
        "pending_le_active": True,
        "fresh_ok": True,
        "env_ok": True,
        "policy_ok": True,
        "oracle_commit_allowed": True,
        "price_after_e8": 9_000_000_000,
        "oracle_last_update_after": 10,
    }


def test_zusd_oracle_commit_rejects_stale_oracle(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_oracle_commit_apply_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["oracle_last_update_epoch"] = 0
    state["max_oracle_staleness_epochs"] = 5
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="apply_oracle_commit", args={}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"


def test_zusd_oracle_commit_rejects_pending_above_active(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_oracle_commit_apply_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["price_pending_e8"] = 11_000_000_000
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="apply_oracle_commit", args={}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"


def test_zusd_oracle_commit_rejects_policy(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import zusd_oracle_commit_apply_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["auth_ok"] = 0
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="apply_oracle_commit", args={}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"

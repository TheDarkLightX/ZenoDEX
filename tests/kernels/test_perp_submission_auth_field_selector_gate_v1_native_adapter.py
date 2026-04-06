from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/perp_submission_auth_field_selector_gate_v1.yaml")
ADAPTER = "src.kernels.python.perp_submission_auth_field_selector_gate_v1_native_adapter:make_adapter"


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


def _base_state() -> dict[str, object]:
    return {
        "action_tag": 2,
        "has_quote_asset": False,
        "has_account_a_pubkey": True,
        "has_account_b_pubkey": True,
        "has_account_c_pubkey": False,
        "has_new_position_base_a": True,
        "has_new_position_base_b": True,
        "has_new_position_base_c": False,
        "has_price_e8": False,
        "has_deadline": True,
    }


def test_perp_submission_auth_field_selector_gate_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_perp_submission_auth_field_selector_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_submission_auth_field_selector_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state={"before": True})

    unknown = adapter.apply(SimpleNamespace(tag="unknown"))
    assert isinstance(unknown, interp_mod.StepError)
    assert unknown.code == "UnknownAction"

    effect_key = next(iter(module.EFFECT_HANDLERS))
    monkeypatch.setitem(
        module.ACTION_HANDLERS,
        "synthetic_success",
        lambda _adapter, _command, _interp=interp_mod, _effect_key=effect_key: _interp.StepOk(
            state={"after": "perp_submission_auth_field_selector_gate"},
            effects={_effect_key: True, "ignored": False},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "perp_submission_auth_field_selector_gate"}
    assert dict(adapter.drain_effects()) == {effect_key: True}
    assert dict(adapter.drain_effects()) == {}


def test_perp_submission_auth_field_selector_projects_pair_fields(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_submission_auth_field_selector_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="evaluate_field_selector", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "include_quote_asset": False,
        "include_account_a_pubkey": True,
        "include_account_b_pubkey": True,
        "include_account_c_pubkey": False,
        "include_new_position_base_a": True,
        "include_new_position_base_b": True,
        "include_new_position_base_c": False,
        "include_price_e8": False,
        "include_deadline": True,
        "required_fields_present": True,
        "signed_field_count": 5,
    }


def test_perp_submission_auth_field_selector_rejects_bad_action_tag(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_submission_auth_field_selector_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["action_tag"] = 9
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_field_selector", args={}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"


def test_perp_submission_auth_field_selector_reports_missing_required_field(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_submission_auth_field_selector_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["has_deadline"] = False
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_field_selector", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects)["required_fields_present"] is False

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace


MODEL = Path("src/kernels/dex/perp_submission_auth_gate_v1.yaml")
ADAPTER = "src.kernels.python.perp_submission_auth_gate_v1_native_adapter:make_adapter"


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
        "mode_signed": 1,
        "mode_sender_bound": 0,
        "signed_surface_ok": 1,
        "signer_role_set_ok": 1,
        "deadline_ok": 1,
        "nonce_domain_ok": 1,
        "nonce_expected_ok": 1,
        "signature_ok": 1,
        "tx_sender_binding_ok": 1,
    }


def test_perp_submission_auth_gate_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_perp_submission_auth_gate_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_submission_auth_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state={"before": 1})

    unknown = adapter.apply(SimpleNamespace(tag="unknown"))
    assert isinstance(unknown, interp_mod.StepError)
    assert unknown.code == "UnknownAction"

    effect_key = next(iter(module.EFFECT_HANDLERS))
    monkeypatch.setitem(
        module.ACTION_HANDLERS,
        "synthetic_success",
        lambda _adapter, _command, _interp=interp_mod, _effect_key=effect_key: _interp.StepOk(
            state={"after": "perp_submission_auth_gate"},
            effects={_effect_key: True, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "perp_submission_auth_gate"}
    assert dict(adapter.drain_effects()) == {effect_key: True}


def test_perp_submission_auth_gate_accepts_signed_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_submission_auth_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="evaluate_submission_auth_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {
        "mode_ok": True,
        "relay_allowed": True,
        "consume_nonce": True,
        "admission_ok": True,
        "reject_code": "Ok",
    }


def test_perp_submission_auth_gate_rejects_sender_bound_mismatch(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_submission_auth_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["mode_signed"] = 0
    state["mode_sender_bound"] = 1
    state["tx_sender_binding_ok"] = 0
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_submission_auth_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["relay_allowed"] is False
    assert result.effects["consume_nonce"] is False
    assert result.effects["admission_ok"] is False
    assert result.effects["reject_code"] == "SenderBindingInvalid"


def test_perp_submission_auth_gate_rejects_deadline_before_signature(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import perp_submission_auth_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["deadline_ok"] = 0
    state["nonce_expected_ok"] = 0
    state["signature_ok"] = 0
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_submission_auth_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert result.effects["consume_nonce"] is False
    assert result.effects["admission_ok"] is False
    assert result.effects["reject_code"] == "DeadlineExpired"

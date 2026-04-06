from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace

MODEL = Path("src/kernels/dex/quote_receipt_hop_structure_gate_v1.yaml")
ADAPTER = "src.kernels.python.quote_receipt_hop_structure_gate_v1_native_adapter:make_adapter"


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


def _base_state() -> dict[str, bool]:
    return {
        "hop_dict_ok": True,
        "pool_id_ok": True,
        "snapshotted_pool_present": True,
        "working_pool_present": True,
        "assets_shaped_ok": True,
        "is_first_hop": True,
        "first_hop_asset_in_ok": True,
        "hop_asset_chain_ok": True,
        "hop_amounts_ok": True,
        "hop_amount_chain_ok": True,
    }


def test_quote_receipt_hop_structure_gate_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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


def test_quote_receipt_hop_structure_gate_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import quote_receipt_hop_structure_gate_v1_native_adapter as module

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
            state={"after": "quote_receipt_hop_structure_gate"},
            effects={_effect_key: 7, "ignored": False},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": "quote_receipt_hop_structure_gate"}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


def test_quote_receipt_hop_structure_gate_happy_path(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import quote_receipt_hop_structure_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=_base_state())
    result = adapter.apply(SimpleNamespace(tag="evaluate_route_quote_receipt_hop_structure_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {"hop_ok": True, "reject_tag": 0}


def test_quote_receipt_hop_structure_gate_missing_working_pool_wins(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import quote_receipt_hop_structure_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["working_pool_present"] = False
    state["assets_shaped_ok"] = False
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_route_quote_receipt_hop_structure_gate", args={}))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.effects) == {"hop_ok": False, "reject_tag": 4}


def test_quote_receipt_hop_structure_gate_rejects_noncanonical_flag(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import quote_receipt_hop_structure_gate_v1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = _base_state()
    state["hop_dict_ok"] = 2
    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="evaluate_route_quote_receipt_hop_structure_gate", args={}))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace

import pytest


MODEL = Path("src/kernels/dex/funding_rate_settlement_witness_v1_1.yaml")
ADAPTER = "src.kernels.python.funding_rate_settlement_witness_v1_1_native_adapter:make_adapter"


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


def test_funding_rate_settlement_witness_v1_1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
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
            "6",
            "--determinism-trials",
            "2",
            "--output",
            str(verify_path),
        ]
    )
    verify = json.loads(verify_path.read_text(encoding="utf-8"))
    assert verify.get("ok") is True


def test_funding_rate_settlement_witness_adapter_unknown_action_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import funding_rate_settlement_witness_v1_1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state={"rate_long_exposure": 1})

    unknown = adapter.apply(SimpleNamespace(tag="unknown"))
    assert isinstance(unknown, interp_mod.StepError)
    assert unknown.code == "UnknownAction"

    effect_key = next(iter(module.EFFECT_HANDLERS))
    monkeypatch.setitem(
        module.ACTION_HANDLERS,
        "synthetic_success",
        lambda _adapter, _command, _interp=interp_mod, _effect_key=effect_key: _interp.StepOk(
            state={"ok": 1},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"ok": 1}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


@pytest.mark.parametrize(
    "state_patch",
    [
        {"rate_long_exposure": 0, "rate_short_exposure": 0},
        {"rate_long_exposure": 700_000_000_000, "rate_short_exposure": 700_000_000_000},
    ],
)
def test_funding_rate_settlement_witness_adapter_rejects_guard_edges(
    monkeypatch,
    state_patch: dict[str, int],
) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import funding_rate_settlement_witness_v1_1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "rate_long_exposure": 60_000,
        "rate_short_exposure": 40_000,
        "premium_pool": 100_000,
        "implied_rate_bps": 0,
        "funding_cap_bps": 100,
        "protocol_fee_bps": 100,
        "realized_rate_bps": 0,
        "protocol_fee": 0,
        "long_payout": 0,
        "short_payout": 0,
    }
    state.update(state_patch)
    adapter.reset(state=state)

    result = adapter.apply(
        SimpleNamespace(
            tag="compute_settlement",
            args={
                "mark_price_e8": 101_00000000,
                "index_price_e8": 100_00000000,
                "witness_realized_rate_bps": 100,
                "witness_protocol_fee": 1_000,
                "witness_long_payout": 59_400,
                "witness_short_payout": 39_600,
            },
        )
    )
    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"


def test_funding_rate_settlement_witness_adapter_commits_success_effects(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import funding_rate_settlement_witness_v1_1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "rate_long_exposure": 60_000,
        "rate_short_exposure": 40_000,
        "premium_pool": 100_000,
        "implied_rate_bps": 0,
        "funding_cap_bps": 100,
        "protocol_fee_bps": 100,
        "realized_rate_bps": 0,
        "protocol_fee": 0,
        "long_payout": 0,
        "short_payout": 0,
    }
    adapter.reset(state=state)
    result = adapter.apply(
        SimpleNamespace(
            tag="compute_settlement",
            args={
                "mark_price_e8": 101_00000000,
                "index_price_e8": 100_00000000,
                "witness_realized_rate_bps": 100,
                "witness_protocol_fee": 1_000,
                "witness_long_payout": 59_400,
                "witness_short_payout": 39_600,
            },
        )
    )

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.state) == {
        "rate_long_exposure": 60_000,
        "rate_short_exposure": 40_000,
        "premium_pool": 100_000,
        "implied_rate_bps": 0,
        "funding_cap_bps": 100,
        "protocol_fee_bps": 100,
        "realized_rate_bps": 100,
        "protocol_fee": 1_000,
        "long_payout": 59_400,
        "short_payout": 39_600,
    }
    assert dict(result.effects) == {
        "realized_rate_bps": 100,
        "protocol_fee": 1_000,
        "long_payout": 59_400,
        "short_payout": 39_600,
        "winning_long": True,
    }


def test_funding_rate_settlement_witness_adapter_rejects_bad_witness_payload(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import funding_rate_settlement_witness_v1_1_native_adapter as module

    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(
        state={
            "rate_long_exposure": 60_000,
            "rate_short_exposure": 40_000,
            "premium_pool": 100_000,
            "implied_rate_bps": 0,
            "funding_cap_bps": 100,
            "protocol_fee_bps": 100,
            "realized_rate_bps": 0,
            "protocol_fee": 0,
            "long_payout": 0,
            "short_payout": 0,
        }
    )

    result = adapter.apply(
        SimpleNamespace(
            tag="compute_settlement",
            args={
                "mark_price_e8": 101_00000000,
                "index_price_e8": 100_00000000,
                "witness_realized_rate_bps": 99,
                "witness_protocol_fee": 1_000,
                "witness_long_payout": 59_400,
                "witness_short_payout": 39_600,
            },
        )
    )
    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"

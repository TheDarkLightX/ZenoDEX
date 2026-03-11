from __future__ import annotations

import importlib
import sys
from types import ModuleType, SimpleNamespace

import pytest


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


@pytest.mark.parametrize(
    "module_name",
    [
        "src.kernels.python.settlement_swap_apply_witness_v1_native_adapter",
        "src.kernels.python.settlement_swap_exact_out_apply_witness_v1_native_adapter",
    ],
)
def test_native_witness_adapters_cover_unknown_action_and_effect_drain(monkeypatch, module_name: str) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    module = importlib.import_module(module_name)
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
        lambda _adapter, _command, _interp=interp_mod, _effect_key=effect_key, _module_name=module_name: _interp.StepOk(
            state={"after": _module_name},
            effects={_effect_key: 7, "ignored": 9},
        ),
    )
    result = adapter.apply(SimpleNamespace(tag="synthetic_success"))
    assert isinstance(result, interp_mod.StepOk)
    assert dict(adapter.get_state()) == {"after": module_name}
    assert dict(adapter.drain_effects()) == {effect_key: 7}
    assert dict(adapter.drain_effects()) == {}


@pytest.mark.parametrize(
    ("state_patch", "args_patch"),
    [
        ({}, {"witness_reserve_in": 9}),
        ({}, {"witness_reserve_out": 19}),
        ({"trader_in": 4}, {}),
        ({"reserve_in": 46}, {}),
        ({"fee_bps": 10000}, {"amount_in": 1}),
        ({"reserve_in": 49, "reserve_out": 1}, {"amount_in": 1}),
        ({"recipient_out": 145}, {}),
        ({}, {"min_amount_out": 7}),
    ],
)
def test_exact_in_native_adapter_rejects_guard_edges(monkeypatch, state_patch: dict[str, int], args_patch: dict[str, int]) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    module = importlib.import_module("src.kernels.python.settlement_swap_apply_witness_v1_native_adapter")
    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "trader_in": 10,
        "recipient_out": 0,
        "reserve_in": 10,
        "reserve_out": 20,
        "fee_bps": 0,
    }
    args = {
        "amount_in": 5,
        "min_amount_out": 1,
        "witness_reserve_in": 10,
        "witness_reserve_out": 20,
    }
    state.update(state_patch)
    args.update(args_patch)
    if "witness_reserve_in" not in args_patch:
        args["witness_reserve_in"] = state["reserve_in"]
    if "witness_reserve_out" not in args_patch:
        args["witness_reserve_out"] = state["reserve_out"]

    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="swap_exact_in_apply", args=args))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert dict(adapter.get_state()) == state
    assert dict(adapter.drain_effects()) == {}


def test_exact_in_native_adapter_commits_success_effects(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    module = importlib.import_module("src.kernels.python.settlement_swap_apply_witness_v1_native_adapter")
    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "trader_in": 10,
        "recipient_out": 0,
        "reserve_in": 10,
        "reserve_out": 20,
        "fee_bps": 0,
    }
    args = {
        "amount_in": 5,
        "min_amount_out": 1,
        "witness_reserve_in": 10,
        "witness_reserve_out": 20,
    }

    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="swap_exact_in_apply", args=args))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.state) == {
        "trader_in": 5,
        "recipient_out": 6,
        "reserve_in": 15,
        "reserve_out": 14,
        "fee_bps": 0,
        "reserve_in_before": 10,
        "reserve_out_before": 20,
    }
    assert dict(result.effects) == {
        "amount_out": 6,
        "fee_paid": 0,
        "net_in": 5,
        "k_before": 200,
        "k_after": 210,
        "witness_ok": True,
        "slippage_ok": True,
    }
    assert dict(adapter.get_state()) == dict(result.state)
    assert dict(adapter.drain_effects()) == dict(result.effects)


@pytest.mark.parametrize(
    ("state_patch", "args_patch"),
    [
        ({}, {"witness_reserve_in": 9}),
        ({}, {"witness_reserve_out": 19}),
        ({}, {"amount_out": 20}),
        ({"fee_bps": 10000}, {}),
        ({}, {"max_amount_in": 4}),
        ({"trader_in": 4}, {}),
        ({"reserve_in": 46, "trader_in": 100}, {"max_amount_in": 100}),
        ({"recipient_out": 146}, {}),
        ({"reserve_in": 4, "reserve_out": 38, "fee_bps": 801}, {"amount_out": 18, "max_amount_in": 10}),
    ],
)
def test_exact_out_native_adapter_rejects_guard_edges(monkeypatch, state_patch: dict[str, int], args_patch: dict[str, int]) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    module = importlib.import_module("src.kernels.python.settlement_swap_exact_out_apply_witness_v1_native_adapter")
    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "trader_in": 20,
        "recipient_out": 0,
        "reserve_in": 10,
        "reserve_out": 20,
        "fee_bps": 100,
    }
    args = {
        "amount_out": 5,
        "max_amount_in": 10,
        "witness_reserve_in": 10,
        "witness_reserve_out": 20,
    }
    state.update(state_patch)
    args.update(args_patch)
    if "witness_reserve_in" not in args_patch:
        args["witness_reserve_in"] = state["reserve_in"]
    if "witness_reserve_out" not in args_patch:
        args["witness_reserve_out"] = state["reserve_out"]

    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="swap_exact_out_apply", args=args))

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert dict(adapter.get_state()) == state
    assert dict(adapter.drain_effects()) == {}


def test_exact_out_native_adapter_commits_success_effects(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    module = importlib.import_module("src.kernels.python.settlement_swap_exact_out_apply_witness_v1_native_adapter")
    adapter = module.make_adapter(ir={"schema": "fake"})
    state = {
        "trader_in": 20,
        "recipient_out": 0,
        "reserve_in": 10,
        "reserve_out": 20,
        "fee_bps": 100,
    }
    args = {
        "amount_out": 5,
        "max_amount_in": 10,
        "witness_reserve_in": 10,
        "witness_reserve_out": 20,
    }

    adapter.reset(state=state)
    result = adapter.apply(SimpleNamespace(tag="swap_exact_out_apply", args=args))

    assert isinstance(result, interp_mod.StepOk)
    assert dict(result.state) == {
        "trader_in": 15,
        "recipient_out": 5,
        "reserve_in": 15,
        "reserve_out": 15,
        "fee_bps": 100,
        "reserve_in_before": 10,
        "reserve_out_before": 20,
    }
    assert dict(result.effects) == {
        "amount_in": 5,
        "amount_out": 5,
        "amount_out_quote": 5,
        "overdelivery_gap": 0,
        "gap_bps": 0,
        "fee_paid": 1,
        "net_in_actual": 4,
        "k_before": 200,
        "k_after": 225,
        "witness_ok": True,
        "slippage_ok": 1,
    }
    assert dict(adapter.get_state()) == dict(result.state)
    assert dict(adapter.drain_effects()) == dict(result.effects)

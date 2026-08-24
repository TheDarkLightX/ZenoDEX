from __future__ import annotations

import importlib
import sys
from types import ModuleType, SimpleNamespace

PLAIN_ADAPTER_MODULES = [
    "src.kernels.python.dex_global_conservation_v1_adapter",
    "src.kernels.python.proof_mining_manager_v1_adapter",
    "src.kernels.python.perp_epoch_isolated_v1_adapter",
    "src.kernels.python.perp_epoch_isolated_v1_1_adapter",
]

CTX_ADAPTER_MODULES = [
    "src.kernels.python.perp_epoch_isolated_v2_adapter",
    "src.kernels.python.perp_epoch_isolated_v3_adapter",
    "src.kernels.python.perp_epoch_clearinghouse_2p_v0_1_adapter",
]


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
    interp_mod._next_step_result = None
    interp_mod._next_prepare_result = None

    def step(state, command, ir):
        if interp_mod._next_step_result is not None:
            result = interp_mod._next_step_result
            interp_mod._next_step_result = None
            return result
        return StepOk(state=dict(state), effects={})

    def prepare_step_context(ir):
        if interp_mod._next_prepare_result is not None:
            result = interp_mod._next_prepare_result
            interp_mod._next_prepare_result = None
            return result
        return {"ir": ir}

    def step_ctx(state, command, ctx):
        if interp_mod._next_step_result is not None:
            result = interp_mod._next_step_result
            interp_mod._next_step_result = None
            return result
        return StepOk(state=dict(state), effects={})

    interp_mod.step = step
    interp_mod.prepare_step_context = prepare_step_context
    interp_mod.step_ctx = step_ctx

    kernel_mod.interpreter = interp_mod
    esso_mod.kernel = kernel_mod

    monkeypatch.setitem(sys.modules, "ESSO", esso_mod)
    monkeypatch.setitem(sys.modules, "ESSO.kernel", kernel_mod)
    monkeypatch.setitem(sys.modules, "ESSO.kernel.interpreter", interp_mod)
    return interp_mod


def test_plain_adapters_cover_state_commit_and_effect_drain(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)

    for module_name in PLAIN_ADAPTER_MODULES:
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
        effects = {effect_key: 7}
        if module_name != "src.kernels.python.dex_global_conservation_v1_adapter":
            # These legacy adapter generators retain their existing behavior;
            # the global conservation adapter is the value-wide closure fixed
            # by the dedicated reject-no-op test below.
            effects["ignored"] = 9
        interp_mod._next_step_result = interp_mod.StepOk(
            state={"after": module_name},
            effects=effects,
        )
        first_action = next(iter(module.ACTION_HANDLERS))
        result = adapter.apply(SimpleNamespace(tag=first_action))
        assert isinstance(result, interp_mod.StepOk)
        assert dict(adapter.get_state()) == {"after": module_name}
        assert dict(adapter.drain_effects()) == {effect_key: 7}
        assert dict(adapter.drain_effects()) == {}

        interp_mod._next_step_result = interp_mod.StepError(code="Rejected", message="bad step")
        rejected = adapter.apply(SimpleNamespace(tag=first_action))
        assert isinstance(rejected, interp_mod.StepError)

        for action_tag in module.ACTION_HANDLERS:
            interp_mod._next_step_result = interp_mod.StepOk(
                state={"after": action_tag},
                effects={},
            )
            result = adapter.apply(SimpleNamespace(tag=action_tag))
            assert isinstance(result, interp_mod.StepOk)
            assert dict(adapter.get_state()) == {"after": action_tag}


def test_global_conservation_adapter_rejects_unknown_effect_before_state_commit(monkeypatch) -> None:
    # Arrange.
    interp_mod = _install_fake_interpreter(monkeypatch)
    module = importlib.import_module("src.kernels.python.dex_global_conservation_v1_adapter")
    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state={"before": 1})
    interp_mod._next_step_result = interp_mod.StepOk(
        state={"after": 2},
        effects={"total_a": 7, "unregistered_value_effect": 9},
    )

    # Act.
    result = adapter.apply(SimpleNamespace(tag="swap_exact_in"))

    # Assert: effect coverage is validated before any state or effect commit.
    assert isinstance(result, interp_mod.StepError)
    assert result.code == "UnknownEffect"
    assert dict(adapter.get_state()) == {"before": 1}
    assert dict(adapter.drain_effects()) == {}


def test_ctx_adapters_fail_closed_on_prepare_error_and_commit_success(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)

    for module_name in CTX_ADAPTER_MODULES:
        module = importlib.import_module(module_name)

        interp_mod._next_prepare_result = interp_mod.StepError(code="CtxError", message="bad ctx")
        adapter = module.make_adapter(ir={"schema": "fake"})
        adapter.reset(state={"before": 1})
        action_tag = next(iter(module.ACTION_HANDLERS))
        unknown = adapter.apply(SimpleNamespace(tag="unknown"))
        assert isinstance(unknown, interp_mod.StepError)
        assert unknown.code == "UnknownAction"
        failed = adapter.apply(SimpleNamespace(tag=action_tag))
        assert isinstance(failed, interp_mod.StepError)
        assert failed.code == "CtxError"
        assert dict(adapter.get_state()) == {"before": 1}
        assert dict(adapter.drain_effects()) == {}

        adapter = module.make_adapter(ir={"schema": "fake"})
        adapter.reset(state={"before": 1})
        effect_key = next(iter(module.EFFECT_HANDLERS))
        interp_mod._next_step_result = interp_mod.StepOk(
            state={"after": module_name},
            effects={effect_key: 11, "ignored": 5},
        )
        result = adapter.apply(SimpleNamespace(tag=action_tag))
        assert isinstance(result, interp_mod.StepOk)
        assert dict(adapter.get_state()) == {"after": module_name}
        assert dict(adapter.drain_effects()) == {effect_key: 11}
        assert dict(adapter.drain_effects()) == {}

        interp_mod._next_step_result = interp_mod.StepError(code="Rejected", message="bad step")
        rejected = adapter.apply(SimpleNamespace(tag=action_tag))
        assert isinstance(rejected, interp_mod.StepError)

        for action_tag in module.ACTION_HANDLERS:
            interp_mod._next_step_result = interp_mod.StepOk(
                state={"after": action_tag},
                effects={},
            )
            result = adapter.apply(SimpleNamespace(tag=action_tag))
            assert isinstance(result, interp_mod.StepOk)
            assert dict(adapter.get_state()) == {"after": action_tag}

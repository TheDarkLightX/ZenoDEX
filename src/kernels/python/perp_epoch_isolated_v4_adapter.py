"""Adapter for the versioned `perp_epoch_isolated_v4` ESSO kernel.

The adapter is pinned to the canonical v4 IR hash and exposes the same action
and effect ABI as v3. The semantic delta lives entirely in the model's initial
and maintenance risk-margin expressions.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

IR_HASH = "sha256:5981d683dff2c95f6069d52dc1848290b4637d18df69ae31285094e30268ace1"


def _prepare_ctx(ir: Any) -> Any:
    from ESSO.kernel.interpreter import prepare_step_context

    return prepare_step_context(ir)


def _kernel_step_ctx(*, state: Mapping[str, Any], command: Any, ctx: Any) -> Any:
    from ESSO.kernel.interpreter import StepError, step_ctx

    if isinstance(ctx, StepError):
        return ctx
    return step_ctx(dict(state), command, ctx)


@dataclass
class PerpEpochIsolatedV4Adapter:
    ir: Any
    _ctx: Any = field(init=False, repr=False)
    _state: dict[str, Any] = field(default_factory=dict)
    _pending_effects: dict[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        self._ctx = _prepare_ctx(self.ir)

    def reset(self, *, state: Mapping[str, Any]) -> None:
        self._state = dict(state)
        self._pending_effects = {}

    def get_state(self) -> Mapping[str, Any]:
        return dict(self._state)

    def apply(self, command: Any) -> Any:
        self._pending_effects = {}
        handler = ACTION_HANDLERS.get(str(getattr(command, "tag", "")))
        if handler is None:
            from ESSO.kernel.interpreter import StepError

            return StepError(code="UnknownAction", message="no handler for command.tag")
        result = handler(self, command)
        from ESSO.kernel.interpreter import StepOk

        if isinstance(result, StepOk):
            self._state = dict(result.state)
            for effect_id, value in result.effects.items():
                effect_handler = EFFECT_HANDLERS.get(str(effect_id))
                if effect_handler is not None:
                    effect_handler(self, str(effect_id), value)
        return result

    def drain_effects(self) -> Mapping[str, Any]:
        effects = dict(self._pending_effects)
        self._pending_effects = {}
        return effects


def _commit_effect(
    adapter: PerpEpochIsolatedV4Adapter, effect_id: str, value: Any
) -> None:
    adapter._pending_effects[str(effect_id)] = value


def _handle_generic(adapter: PerpEpochIsolatedV4Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


ACTION_HANDLERS: dict[str, Callable[[PerpEpochIsolatedV4Adapter, Any], Any]] = {
    "advance_epoch": _handle_generic,
    "publish_clearing_price": _handle_generic,
    "settle_epoch": _handle_generic,
    "deposit_collateral": _handle_generic,
    "withdraw_collateral": _handle_generic,
    "set_position": _handle_generic,
    "clear_breaker": _handle_generic,
    "apply_funding": _handle_generic,
    "deposit_insurance": _handle_generic,
    "apply_insurance_claim": _handle_generic,
}

EFFECT_HANDLERS: dict[
    str, Callable[[PerpEpochIsolatedV4Adapter, str, Any], None]
] = {
    "event": _commit_effect,
    "oracle_fresh": _commit_effect,
    "notional_quote": _commit_effect,
    "effective_maint_bps": _commit_effect,
    "maint_req_quote": _commit_effect,
    "init_req_quote": _commit_effect,
    "margin_ok": _commit_effect,
    "liquidated": _commit_effect,
    "collateral_after": _commit_effect,
    "fee_pool_after": _commit_effect,
    "insurance_after": _commit_effect,
}


def make_adapter(ir: Any) -> PerpEpochIsolatedV4Adapter:
    return PerpEpochIsolatedV4Adapter(ir=ir)

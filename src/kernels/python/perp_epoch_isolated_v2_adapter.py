"""Adapter for the `perp_epoch_isolated_v2` kernel spec.

This module is used by an optional private kernel toolchain (vendored under
`external/` and git-ignored) to run shell-level checks such as:
- adapter ↔ spec surface compatibility (adapter lint)
- adapter ↔ interpreter consistency on random traces (shell verification)

At runtime, the default perps path uses the native engine in `src/core/perp_v2/`;
this adapter exists to keep the spec-interpreter backend honest and replayable.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bind this adapter to the exact kernel spec version (fail-closed by default).
# Checked by the toolchain's adapter lint step (fail-closed by default).
IR_HASH = "sha256:db1ecdf46c8c9762d938eeb97d8ba7eda3c013bc117367caf72347156194582c"


def _prepare_ctx(ir: Any) -> Any:
    from ESSO.kernel.interpreter import prepare_step_context  # type: ignore

    return prepare_step_context(ir)


def _kernel_step_ctx(*, state: Mapping[str, Any], command: Any, ctx: Any) -> Any:
    from ESSO.kernel.interpreter import StepError, step_ctx  # type: ignore

    if isinstance(ctx, StepError):
        return ctx
    return step_ctx(dict(state), command, ctx)


@dataclass
class PerpEpochIsolatedV2Adapter:
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
        # Fail-closed: never leak effects across steps.
        self._pending_effects = {}
        handler = ACTION_HANDLERS.get(str(getattr(command, "tag", "")))
        if handler is None:
            from ESSO.kernel.interpreter import StepError  # type: ignore

            return StepError(code="UnknownAction", message="no handler for command.tag")
        res = handler(self, command)
        from ESSO.kernel.interpreter import StepOk  # type: ignore

        if isinstance(res, StepOk):
            # Commit post-state.
            self._state = dict(res.state)
            # Commit effects through the shell wiring.
            for eff_id, v in res.effects.items():
                eff_handler = EFFECT_HANDLERS.get(str(eff_id))
                if eff_handler is None:
                    continue
                eff_handler(self, str(eff_id), v)
        return res

    def drain_effects(self) -> Mapping[str, Any]:
        out = dict(self._pending_effects)
        self._pending_effects = {}
        return out


def _commit_effect(adapter: PerpEpochIsolatedV2Adapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


def _handle_advance_epoch(adapter: PerpEpochIsolatedV2Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_publish_clearing_price(adapter: PerpEpochIsolatedV2Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_settle_epoch(adapter: PerpEpochIsolatedV2Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_deposit_collateral(adapter: PerpEpochIsolatedV2Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_withdraw_collateral(adapter: PerpEpochIsolatedV2Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_set_position(adapter: PerpEpochIsolatedV2Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_clear_breaker(adapter: PerpEpochIsolatedV2Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_apply_funding(adapter: PerpEpochIsolatedV2Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_deposit_insurance(adapter: PerpEpochIsolatedV2Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_apply_insurance_claim(adapter: PerpEpochIsolatedV2Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


ACTION_HANDLERS: dict[str, Callable[[PerpEpochIsolatedV2Adapter, Any], Any]] = {
    "advance_epoch": _handle_advance_epoch,
    "publish_clearing_price": _handle_publish_clearing_price,
    "settle_epoch": _handle_settle_epoch,
    "deposit_collateral": _handle_deposit_collateral,
    "withdraw_collateral": _handle_withdraw_collateral,
    "set_position": _handle_set_position,
    "clear_breaker": _handle_clear_breaker,
    "apply_funding": _handle_apply_funding,
    "deposit_insurance": _handle_deposit_insurance,
    "apply_insurance_claim": _handle_apply_insurance_claim,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpEpochIsolatedV2Adapter, str, Any], None]] = {
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


def make_adapter(ir: Any) -> PerpEpochIsolatedV2Adapter:
    return PerpEpochIsolatedV2Adapter(ir=ir)

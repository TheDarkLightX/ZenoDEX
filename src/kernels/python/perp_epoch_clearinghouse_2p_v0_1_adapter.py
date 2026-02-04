"""Adapter for the `perp_epoch_clearinghouse_2p_v0_1` kernel spec.

This module is used by an optional private kernel toolchain (vendored under
`external/` and git-ignored) to run shell-level checks such as:
- adapter ↔ spec surface compatibility (adapter lint)
- adapter ↔ interpreter consistency on random traces (shell verification)

The adapter is intentionally thin: it delegates semantics to the interpreter and
only manages state/effect plumbing for deterministic stepping.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bind this adapter to the exact kernel spec version (fail-closed by default).
# Checked by the toolchain's adapter lint step (fail-closed by default).
IR_HASH = "sha256:9ee41ddd9919f6695fb116f03ba87d802e007bac0f441546513a958bbd8ff38b"


def _prepare_ctx(ir: Any) -> Any:
    from ESSO.kernel.interpreter import prepare_step_context  # type: ignore

    return prepare_step_context(ir)


def _kernel_step_ctx(*, state: Mapping[str, Any], command: Any, ctx: Any) -> Any:
    from ESSO.kernel.interpreter import StepError, step_ctx  # type: ignore

    if isinstance(ctx, StepError):
        return ctx
    return step_ctx(dict(state), command, ctx)


@dataclass
class PerpEpochClearinghouse2pV0_1Adapter:
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


def _commit_effect(adapter: PerpEpochClearinghouse2pV0_1Adapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


def _handle_advance_epoch(adapter: PerpEpochClearinghouse2pV0_1Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_publish_clearing_price(adapter: PerpEpochClearinghouse2pV0_1Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_settle_epoch(adapter: PerpEpochClearinghouse2pV0_1Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_deposit_collateral_a(adapter: PerpEpochClearinghouse2pV0_1Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_deposit_collateral_b(adapter: PerpEpochClearinghouse2pV0_1Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_withdraw_collateral_a(adapter: PerpEpochClearinghouse2pV0_1Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_withdraw_collateral_b(adapter: PerpEpochClearinghouse2pV0_1Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_set_position_pair(adapter: PerpEpochClearinghouse2pV0_1Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


def _handle_clear_breaker(adapter: PerpEpochClearinghouse2pV0_1Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


ACTION_HANDLERS: dict[str, Callable[[PerpEpochClearinghouse2pV0_1Adapter, Any], Any]] = {
    "advance_epoch": _handle_advance_epoch,
    "publish_clearing_price": _handle_publish_clearing_price,
    "settle_epoch": _handle_settle_epoch,
    "deposit_collateral_a": _handle_deposit_collateral_a,
    "deposit_collateral_b": _handle_deposit_collateral_b,
    "withdraw_collateral_a": _handle_withdraw_collateral_a,
    "withdraw_collateral_b": _handle_withdraw_collateral_b,
    "set_position_pair": _handle_set_position_pair,
    "clear_breaker": _handle_clear_breaker,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpEpochClearinghouse2pV0_1Adapter, str, Any], None]] = {
    "event": _commit_effect,
    "oracle_fresh": _commit_effect,
    "liquidated": _commit_effect,
    "collateral_after_a": _commit_effect,
    "collateral_after_b": _commit_effect,
    "fee_pool_after": _commit_effect,
}


def make_adapter(ir: Any) -> PerpEpochClearinghouse2pV0_1Adapter:
    return PerpEpochClearinghouse2pV0_1Adapter(ir=ir)

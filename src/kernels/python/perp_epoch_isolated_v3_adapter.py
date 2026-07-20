"""Adapter for the `perp_epoch_isolated_v3` kernel spec.

This module is used by an optional kernel toolchain (vendored under `external/`
and git-ignored) to run shell-level checks such as:
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
IR_HASH = "sha256:a7d4a4ff80a895b30f1328c62b43d0f7bd3e7d0600bea4b53970a054ddff7310"


def _prepare_ctx(ir: Any) -> Any:
    from ESSO.kernel.interpreter import prepare_step_context  # type: ignore

    return prepare_step_context(ir)


def _kernel_step_ctx(*, state: Mapping[str, Any], command: Any, ctx: Any) -> Any:
    from ESSO.kernel.interpreter import StepError, step_ctx  # type: ignore

    if isinstance(ctx, StepError):
        return ctx
    return step_ctx(dict(state), command, ctx)


@dataclass
class PerpEpochIsolatedV3Adapter:
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


def _commit_effect(adapter: PerpEpochIsolatedV3Adapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


def _handle_generic(adapter: PerpEpochIsolatedV3Adapter, command: Any) -> Any:
    return _kernel_step_ctx(state=adapter._state, command=command, ctx=adapter._ctx)


ACTION_HANDLERS: dict[str, Callable[[PerpEpochIsolatedV3Adapter, Any], Any]] = {
    "bootstrap_oracle": _handle_generic,
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
    "partial_liquidate": _handle_generic,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpEpochIsolatedV3Adapter, str, Any], None]] = {
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


def make_adapter(ir: Any) -> PerpEpochIsolatedV3Adapter:
    return PerpEpochIsolatedV3Adapter(ir=ir)

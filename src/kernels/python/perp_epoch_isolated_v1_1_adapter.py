"""Adapter for the `perp_epoch_isolated_v1_1` kernel spec.

This module is used by an optional private kernel toolchain (vendored under
`external/` and git-ignored) to interpret the YAML kernel and run shell-level
checks (adapter lint + shell verification).

The adapter itself is intentionally thin: it delegates semantics to the kernel
interpreter and only manages deterministic state/effect plumbing for stepping.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bind this adapter to the exact kernel spec version (fail-closed by default).
# Checked by the toolchain's adapter lint step (fail-closed by default).
IR_HASH = "sha256:d85e41c05f9ebbd26334ea5c6c7aebfa2760b79f460e919596d6c410e149d86d"


def _kernel_step(*, state: Mapping[str, Any], command: Any, ir: Any) -> Any:
    from ESSO.kernel.interpreter import step as kernel_step  # type: ignore

    return kernel_step(state, command, ir)


@dataclass
class PerpEpochIsolatedV1_1Adapter:
    ir: Any
    _state: dict[str, Any] = field(default_factory=dict)
    _pending_effects: dict[str, Any] = field(default_factory=dict)

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


def _commit_effect(adapter: PerpEpochIsolatedV1_1Adapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


def _handle_advance_epoch(adapter: PerpEpochIsolatedV1_1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _handle_publish_clearing_price(adapter: PerpEpochIsolatedV1_1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _handle_settle_epoch(adapter: PerpEpochIsolatedV1_1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _handle_deposit_collateral(adapter: PerpEpochIsolatedV1_1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _handle_withdraw_collateral(adapter: PerpEpochIsolatedV1_1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _handle_set_position(adapter: PerpEpochIsolatedV1_1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _handle_clear_breaker(adapter: PerpEpochIsolatedV1_1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


ACTION_HANDLERS: dict[str, Callable[[PerpEpochIsolatedV1_1Adapter, Any], Any]] = {
    "advance_epoch": _handle_advance_epoch,
    "publish_clearing_price": _handle_publish_clearing_price,
    "settle_epoch": _handle_settle_epoch,
    "deposit_collateral": _handle_deposit_collateral,
    "withdraw_collateral": _handle_withdraw_collateral,
    "set_position": _handle_set_position,
    "clear_breaker": _handle_clear_breaker,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpEpochIsolatedV1_1Adapter, str, Any], None]] = {
    "event": _commit_effect,
    "oracle_fresh": _commit_effect,
    "notional_quote": _commit_effect,
    "maint_req_quote": _commit_effect,
    "init_req_quote": _commit_effect,
    "margin_ok": _commit_effect,
    "liquidated": _commit_effect,
    "collateral_after": _commit_effect,
}


def make_adapter(ir: Any) -> PerpEpochIsolatedV1_1Adapter:
    return PerpEpochIsolatedV1_1Adapter(ir=ir)

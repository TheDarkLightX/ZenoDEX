"""Adapter for the `perp_epoch_isolated_v1` kernel spec.

This module is used by the optional kernel-spec toolchain (Python package `ESSO`,
typically vendored under `external/ESSO`) to interpret the YAML kernel and run
shell-level checks such as `python3 -m ESSO verify-shell ...`.

The adapter itself is intentionally thin: it delegates semantics to the kernel
interpreter and only manages deterministic state/effect plumbing for stepping.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bind this adapter to the exact kernel spec version (fail-closed by default).
# Checked by `python3 -m ESSO shell-lint ...`.
IR_HASH = "sha256:6782fec89f2979132ba6e326de34597889980a352d6e3db6deceec8cc3cbf437"


def _kernel_step(*, state: Mapping[str, Any], command: Any, ir: Any) -> Any:
    from ESSO.kernel.interpreter import step as kernel_step  # type: ignore

    return kernel_step(state, command, ir)


@dataclass
class PerpEpochIsolatedV1Adapter:
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


def _commit_effect(adapter: PerpEpochIsolatedV1Adapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


def _handle_advance_epoch(adapter: PerpEpochIsolatedV1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _handle_publish_clearing_price(adapter: PerpEpochIsolatedV1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _handle_settle_epoch(adapter: PerpEpochIsolatedV1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _handle_deposit_collateral(adapter: PerpEpochIsolatedV1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _handle_withdraw_collateral(adapter: PerpEpochIsolatedV1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _handle_set_position(adapter: PerpEpochIsolatedV1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


ACTION_HANDLERS: dict[str, Callable[[PerpEpochIsolatedV1Adapter, Any], Any]] = {
    "advance_epoch": _handle_advance_epoch,
    "publish_clearing_price": _handle_publish_clearing_price,
    "settle_epoch": _handle_settle_epoch,
    "deposit_collateral": _handle_deposit_collateral,
    "withdraw_collateral": _handle_withdraw_collateral,
    "set_position": _handle_set_position,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpEpochIsolatedV1Adapter, str, Any], None]] = {
    "event": _commit_effect,
    "oracle_fresh": _commit_effect,
    "notional_quote": _commit_effect,
    "maint_req_quote": _commit_effect,
    "init_req_quote": _commit_effect,
    "margin_ok": _commit_effect,
    "liquidated": _commit_effect,
    "collateral_after": _commit_effect,
}


def make_adapter(ir: Any) -> PerpEpochIsolatedV1Adapter:
    return PerpEpochIsolatedV1Adapter(ir=ir)

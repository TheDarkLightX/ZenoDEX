"""Adapter for the `lp_mint_v8` kernel spec.

This module is used by the optional ESSO toolchain to run shell-level checks:
- adapter ↔ spec surface compatibility (`shell-lint`)
- adapter ↔ interpreter consistency on random traces (`verify-shell`)

The adapter is intentionally thin: it delegates semantics to the interpreter and
only manages deterministic state/effect plumbing for replayable stepping.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bound to the kernel IR hash of `src/kernels/dex/lp_mint_v8.yaml`.
# Checked by the toolchain's adapter lint step (fail-closed by default).
IR_HASH = "sha256:881e066014e62b64c23592b663d8492dbfb7aee7e647705e3499c67f39ee7c73"


def _kernel_step(*, state: Mapping[str, Any], command: Any, ir: Any) -> Any:
    from ESSO.kernel.interpreter import step as kernel_step  # type: ignore

    return kernel_step(state, command, ir)


@dataclass
class LpMintV8Adapter:
    ir: Any
    _state: dict[str, Any] = field(default_factory=dict)
    _pending_effects: dict[str, Any] = field(default_factory=dict)

    def reset(self, *, state: Mapping[str, Any]) -> None:
        self._state = dict(state)
        self._pending_effects = {}

    def get_state(self) -> Mapping[str, Any]:
        return dict(self._state)

    def apply(self, command: Any) -> Any:
        self._pending_effects = {}
        handler = ACTION_HANDLERS.get(str(getattr(command, "tag", "")))
        if handler is None:
            from ESSO.kernel.interpreter import StepError  # type: ignore

            return StepError(code="UnknownAction", message="no handler for command.tag")
        res = handler(self, command)
        from ESSO.kernel.interpreter import StepOk  # type: ignore

        if isinstance(res, StepOk):
            self._state = dict(res.state)
            for eff_id, value in res.effects.items():
                eff_handler = EFFECT_HANDLERS.get(str(eff_id))
                if eff_handler is not None:
                    eff_handler(self, str(eff_id), value)
        return res

    def drain_effects(self) -> Mapping[str, Any]:
        out = dict(self._pending_effects)
        self._pending_effects = {}
        return out


def _handle_generic(adapter: LpMintV8Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _commit_effect(adapter: LpMintV8Adapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[LpMintV8Adapter, Any], Any]] = {
    "mint_initial": _handle_generic,
    "mint": _handle_generic,
}


EFFECT_HANDLERS: dict[str, Callable[[LpMintV8Adapter, str, Any], None]] = {
    "liquidity_minted": _commit_effect,
    "amount0_used": _commit_effect,
    "amount1_used": _commit_effect,
    "total_supply": _commit_effect,
    "amount0_refund": _commit_effect,
    "amount1_refund": _commit_effect,
}


def make_adapter(ir: Any) -> LpMintV8Adapter:
    return LpMintV8Adapter(ir=ir)

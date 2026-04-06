"""Adapter for the `cpmm_swap_v8` kernel spec.

This module is used by the optional ESSO toolchain to run shell-level checks:
- adapter ↔ spec surface compatibility (`shell-lint`)
- adapter ↔ interpreter consistency on random traces (`verify-shell`)

The adapter is intentionally thin: it delegates semantics to the interpreter and
only manages deterministic state/effect plumbing for replayable stepping.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bound to the kernel IR hash of `src/kernels/dex/cpmm_swap_v8.yaml`.
# Checked by the toolchain's adapter lint step (fail-closed by default).
IR_HASH = "sha256:19968d0f05064a188d422858e1ded2a1baf9d6e7fda04bbef4c6094f6f9ed491"


def _kernel_step(*, state: Mapping[str, Any], command: Any, ir: Any) -> Any:
    from ESSO.kernel.interpreter import step as kernel_step  # type: ignore

    return kernel_step(state, command, ir)


@dataclass
class CpmmSwapV8Adapter:
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


def _handle_swap(adapter: CpmmSwapV8Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _commit_effect(adapter: CpmmSwapV8Adapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[CpmmSwapV8Adapter, Any], Any]] = {
    "swap": _handle_swap,
}


EFFECT_HANDLERS: dict[str, Callable[[CpmmSwapV8Adapter, str, Any], None]] = {
    "amount_out": _commit_effect,
    "fee_total": _commit_effect,
    "protocol_fee": _commit_effect,
    "lp_fee": _commit_effect,
    "net_in": _commit_effect,
    "gross_in": _commit_effect,
    "new_reserve_in": _commit_effect,
    "new_reserve_out": _commit_effect,
    "k_before": _commit_effect,
    "k_after": _commit_effect,
    "fee_split_ok": _commit_effect,
    "net_ok": _commit_effect,
}


def make_adapter(ir: Any) -> CpmmSwapV8Adapter:
    return CpmmSwapV8Adapter(ir=ir)

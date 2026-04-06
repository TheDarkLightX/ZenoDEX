"""Adapter for the `vault_manager` kernel spec.

This module is used by the optional ESSO toolchain to run shell-level checks:
- adapter ↔ spec surface compatibility (`shell-lint`)
- adapter ↔ interpreter consistency on random traces (`verify-shell`)

The adapter is intentionally thin: it delegates semantics to the interpreter and
only manages deterministic state/effect plumbing for replayable stepping.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bound to the kernel IR hash of `src/kernels/dex/vault_manager.yaml`.
# Checked by the toolchain's adapter lint step (fail-closed by default).
IR_HASH = "sha256:2b27f6088aaf33c6c75d07572dfdd8df6ef3c82d947af294c2620d99aea543bb"


def _kernel_step(*, state: Mapping[str, Any], command: Any, ir: Any) -> Any:
    from ESSO.kernel.interpreter import step as kernel_step  # type: ignore

    return kernel_step(state, command, ir)


@dataclass
class VaultManagerAdapter:
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


def _handle_generic(adapter: VaultManagerAdapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _commit_effect(adapter: VaultManagerAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[VaultManagerAdapter, Any], Any]] = {
    "deposit_rewards": _handle_generic,
    "harvest": _handle_generic,
    "stake": _handle_generic,
    "unstake": _handle_generic,
}


EFFECT_HANDLERS: dict[str, Callable[[VaultManagerAdapter, str, Any], None]] = {
    "delta_acc": _commit_effect,
    "harvested_reward": _commit_effect,
}


def make_adapter(ir: Any) -> VaultManagerAdapter:
    return VaultManagerAdapter(ir=ir)

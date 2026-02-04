from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bound to the kernel IR hash of `src/kernels/dex/dex_global_conservation_v1.yaml`.
# Checked by the toolchain's adapter lint step (fail-closed by default).
IR_HASH = "sha256:9ea1cb58898c72b5f809923be0c25e85630101e24f8cead027bd0c5cb96fc06f"


def _kernel_step(*, state: Mapping[str, Any], command: Any, ir: Any) -> Any:
    from ESSO.kernel.interpreter import step as kernel_step  # type: ignore

    return kernel_step(state, command, ir)


@dataclass
class DexGlobalConservationV1Adapter:
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


def _handle_swap_exact_in(adapter: DexGlobalConservationV1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _commit_effect(adapter: DexGlobalConservationV1Adapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[DexGlobalConservationV1Adapter, Any], Any]] = {
    "swap_exact_in": _handle_swap_exact_in,
}

EFFECT_HANDLERS: dict[str, Callable[[DexGlobalConservationV1Adapter, str, Any], None]] = {
    "total_a": _commit_effect,
    "total_b": _commit_effect,
}


def make_adapter(ir: Any) -> DexGlobalConservationV1Adapter:
    return DexGlobalConservationV1Adapter(ir=ir)

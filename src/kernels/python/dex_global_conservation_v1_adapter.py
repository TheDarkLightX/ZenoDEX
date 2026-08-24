from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

# Bound to the kernel IR hash of `src/kernels/dex/dex_global_conservation_v1.yaml`.
# Checked by the toolchain's adapter lint step (fail-closed by default).
IR_HASH = "sha256:49e76918030dafba3123c868342afd395e01a7402de7e664ec7763acda1d426d"


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
        from ESSO.kernel.interpreter import StepError, StepOk  # type: ignore

        if isinstance(res, StepOk):
            if type(res.state) is not dict:
                return StepError(code="MalformedState", message="kernel post-state must be an exact object")
            if type(res.effects) is not dict:
                return StepError(code="MalformedEffects", message="kernel effects must be an exact object")
            pending_handlers: list[tuple[Callable[..., None], str, Any]] = []
            for eff_id, v in res.effects.items():
                if type(eff_id) is not str:
                    return StepError(code="MalformedEffectId", message="effect id must be an exact string")
                eff_handler = EFFECT_HANDLERS.get(eff_id)
                if eff_handler is None:
                    return StepError(code="UnknownEffect", message=f"no handler for effect {eff_id!r}")
                pending_handlers.append((eff_handler, eff_id, v))
            # Commit only after the complete post-state and effect plan is
            # validated. A rejected step is byte-for-byte a no-op to the shell.
            self._state = dict(res.state)
            for eff_handler, eff_id, value in pending_handlers:
                eff_handler(self, eff_id, value)
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

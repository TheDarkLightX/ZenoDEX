from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


IR_HASH = "sha256:6141f0e10bf9c1b621236279516cf3f77551f8e17a20a3d303c7573796b7c31e"


def _kernel_step(*, state: Mapping[str, Any], command: Any, ir: Any) -> Any:
    from ESSO.kernel.interpreter import step as kernel_step  # type: ignore

    return kernel_step(state, command, ir)


@dataclass
class ProofMiningManagerV1Adapter:
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


def _handle_advance_epoch(adapter: ProofMiningManagerV1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _handle_submit_proof(adapter: ProofMiningManagerV1Adapter, command: Any) -> Any:
    return _kernel_step(state=adapter._state, command=command, ir=adapter.ir)


def _commit_effect(adapter: ProofMiningManagerV1Adapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ProofMiningManagerV1Adapter, Any], Any]] = {
    "advance_epoch": _handle_advance_epoch,
    "submit_proof": _handle_submit_proof,
}


EFFECT_HANDLERS: dict[str, Callable[[ProofMiningManagerV1Adapter, str, Any], None]] = {
    "proposal_slot": _commit_effect,
    "prover_id": _commit_effect,
    "reward_amount": _commit_effect,
    "reward_kind": _commit_effect,
    "paid": _commit_effect,
}


def make_adapter(ir: Any) -> ProofMiningManagerV1Adapter:
    return ProofMiningManagerV1Adapter(ir=ir)

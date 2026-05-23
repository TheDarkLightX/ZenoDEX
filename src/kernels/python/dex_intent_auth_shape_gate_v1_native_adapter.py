from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.dex_intent_auth_shape_gate import evaluate_dex_intent_auth_shape_gate

IR_HASH = "sha256:884f6280e0b261f6e951d279bb284aa42d32a00423720e577b68964466b3b286"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class DexIntentAuthShapeGateV1NativeAdapter:
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
                if eff_handler is None:
                    continue
                eff_handler(self, str(eff_id), value)
        return res

    def drain_effects(self) -> Mapping[str, Any]:
        out = dict(self._pending_effects)
        self._pending_effects = {}
        return out


def _handle_evaluate_intent_auth_shape_gate(
    adapter: DexIntentAuthShapeGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_intent_auth_shape_gate"
    try:
        outcome = evaluate_dex_intent_auth_shape_gate(
            intent_object_mode=s["intent_object_mode"],
            fields_object_ok=s["fields_object_ok"],
            explicit_fields_present=s["explicit_fields_present"],
            explicit_fields_mapping_ok=s["explicit_fields_mapping_ok"],
            salt_present=s["salt_present"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "mapping_mode": bool(outcome.mapping_mode),
            "use_object_fields": bool(outcome.use_object_fields),
            "use_explicit_mapping_fields": bool(outcome.use_explicit_mapping_fields),
            "use_transport_flattened_fields": bool(outcome.use_transport_flattened_fields),
            "include_salt": bool(outcome.include_salt),
            "shape_ok": bool(outcome.shape_ok),
        },
    )


def _commit_effect(adapter: DexIntentAuthShapeGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[DexIntentAuthShapeGateV1NativeAdapter, Any], Any]] = {
    "evaluate_intent_auth_shape_gate": _handle_evaluate_intent_auth_shape_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[DexIntentAuthShapeGateV1NativeAdapter, str, Any], None]] = {
    "mapping_mode": _commit_effect,
    "use_object_fields": _commit_effect,
    "use_explicit_mapping_fields": _commit_effect,
    "use_transport_flattened_fields": _commit_effect,
    "include_salt": _commit_effect,
    "shape_ok": _commit_effect,
}


def make_adapter(ir: Any) -> DexIntentAuthShapeGateV1NativeAdapter:
    return DexIntentAuthShapeGateV1NativeAdapter(ir=ir)

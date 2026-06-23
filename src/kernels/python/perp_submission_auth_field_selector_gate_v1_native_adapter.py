from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.perp_submission_auth_field_selector_gate import (
    evaluate_perp_submission_auth_field_selector_gate,
)

IR_HASH = "sha256:87d64d288fa0805d38ef87915174f26a6d46996a009de52b0e9fa6904c818b79"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class PerpSubmissionAuthFieldSelectorGateV1NativeAdapter:
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


def _handle_evaluate_field_selector(
    adapter: PerpSubmissionAuthFieldSelectorGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_field_selector"
    try:
        outcome = evaluate_perp_submission_auth_field_selector_gate(
            action_tag=s["action_tag"],
            has_quote_asset=s["has_quote_asset"],
            has_account_a_pubkey=s["has_account_a_pubkey"],
            has_account_b_pubkey=s["has_account_b_pubkey"],
            has_account_c_pubkey=s["has_account_c_pubkey"],
            has_new_position_base_a=s["has_new_position_base_a"],
            has_new_position_base_b=s["has_new_position_base_b"],
            has_new_position_base_c=s["has_new_position_base_c"],
            has_price_e8=s["has_price_e8"],
            has_deadline=s["has_deadline"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "include_quote_asset": bool(outcome.include_quote_asset),
            "include_account_a_pubkey": bool(outcome.include_account_a_pubkey),
            "include_account_b_pubkey": bool(outcome.include_account_b_pubkey),
            "include_account_c_pubkey": bool(outcome.include_account_c_pubkey),
            "include_new_position_base_a": bool(outcome.include_new_position_base_a),
            "include_new_position_base_b": bool(outcome.include_new_position_base_b),
            "include_new_position_base_c": bool(outcome.include_new_position_base_c),
            "include_price_e8": bool(outcome.include_price_e8),
            "include_deadline": bool(outcome.include_deadline),
            "required_fields_present": bool(outcome.required_fields_present),
            "signed_field_count": int(outcome.signed_field_count),
        },
    )


def _commit_effect(adapter: PerpSubmissionAuthFieldSelectorGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[PerpSubmissionAuthFieldSelectorGateV1NativeAdapter, Any], Any]] = {
    "evaluate_field_selector": _handle_evaluate_field_selector,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpSubmissionAuthFieldSelectorGateV1NativeAdapter, str, Any], None]] = {
    "include_quote_asset": _commit_effect,
    "include_account_a_pubkey": _commit_effect,
    "include_account_b_pubkey": _commit_effect,
    "include_account_c_pubkey": _commit_effect,
    "include_new_position_base_a": _commit_effect,
    "include_new_position_base_b": _commit_effect,
    "include_new_position_base_c": _commit_effect,
    "include_price_e8": _commit_effect,
    "include_deadline": _commit_effect,
    "required_fields_present": _commit_effect,
    "signed_field_count": _commit_effect,
}


def make_adapter(ir: Any) -> PerpSubmissionAuthFieldSelectorGateV1NativeAdapter:
    return PerpSubmissionAuthFieldSelectorGateV1NativeAdapter(ir=ir)

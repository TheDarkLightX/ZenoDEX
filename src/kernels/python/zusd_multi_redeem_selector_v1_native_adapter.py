"""Native (non-interpreter) shell adapter for `zusd_multi_redeem_selector_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/zusd_multi_redeem_selector_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/zusd_multi_redeem_selector_v1.yaml --adapter <this>:make_adapter
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.zusd_multi_redeem_selector import select_multi_redeem_vault


# Derived from:
# `python3 -m ESSO validate src/kernels/dex/zusd_multi_redeem_selector_v1.yaml`.
IR_HASH = "sha256:2fbcdf5c42eb0f14b84f6c481c812ff2d5012472546e8c32a7efe4992f6abae8"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class ZUSDMultiRedeemSelectorV1NativeAdapter:
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


def _handle_select_redeem_vault(adapter: ZUSDMultiRedeemSelectorV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "select_redeem_vault"
    try:
        outcome = select_multi_redeem_vault(
            amount_e8=int(s["amount_e8"]),
            price_e8=int(s["price_e8"]),
            mcr_bps=int(s["mcr_bps"]),
            vault_a_collateral_e8=int(s["vault_a_collateral_e8"]),
            vault_a_debt_e8=int(s["vault_a_debt_e8"]),
            vault_b_collateral_e8=int(s["vault_b_collateral_e8"]),
            vault_b_debt_e8=int(s["vault_b_debt_e8"]),
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    selected_vault = "None"
    if outcome.selected_vault == "a":
        selected_vault = "VaultA"
    elif outcome.selected_vault == "b":
        selected_vault = "VaultB"

    return StepOk(
        state=dict(s),
        effects={
            "gross_collateral_e8": int(outcome.gross_collateral_e8),
            "candidate_a_ok": bool(outcome.candidate_a_ok),
            "candidate_b_ok": bool(outcome.candidate_b_ok),
            "headroom_a_before_e8": int(outcome.headroom_a_before_e8),
            "headroom_b_before_e8": int(outcome.headroom_b_before_e8),
            "selection_ok": bool(outcome.selected_vault is not None),
            "selected_vault": selected_vault,
        },
    )


def _commit_effect(adapter: ZUSDMultiRedeemSelectorV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ZUSDMultiRedeemSelectorV1NativeAdapter, Any], Any]] = {
    "select_redeem_vault": _handle_select_redeem_vault,
}

EFFECT_HANDLERS: dict[str, Callable[[ZUSDMultiRedeemSelectorV1NativeAdapter, str, Any], None]] = {
    "gross_collateral_e8": _commit_effect,
    "candidate_a_ok": _commit_effect,
    "candidate_b_ok": _commit_effect,
    "headroom_a_before_e8": _commit_effect,
    "headroom_b_before_e8": _commit_effect,
    "selection_ok": _commit_effect,
    "selected_vault": _commit_effect,
}


def make_adapter(ir: Any) -> ZUSDMultiRedeemSelectorV1NativeAdapter:
    return ZUSDMultiRedeemSelectorV1NativeAdapter(ir=ir)

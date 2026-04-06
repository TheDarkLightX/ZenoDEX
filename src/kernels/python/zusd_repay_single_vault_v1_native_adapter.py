"""Native (non-interpreter) shell adapter for `zusd_repay_single_vault_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/zusd_repay_single_vault_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/zusd_repay_single_vault_v1.yaml --adapter <this>:make_adapter
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Derived from:
# `python3 -m ESSO validate src/kernels/dex/zusd_repay_single_vault_v1.yaml`.
IR_HASH = "sha256:5498426ee46b48456dad32174dfc063da51b0223b100db420c0e0d238994bc89"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class ZUSDRepaySingleVaultV1NativeAdapter:
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


def _handle_apply_repay_single_vault(adapter: ZUSDRepaySingleVaultV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    args = dict(getattr(command, "args", {}) or {})
    action_id = "apply_repay_single_vault"

    amount_e8 = int(args["amount_e8"])
    debt_e8 = int(s["debt_e8"])
    free_debt_e8 = int(s["free_debt_e8"])

    if amount_e8 > debt_e8:
        return _guard_false(action_id)
    if amount_e8 > free_debt_e8:
        return _guard_false(action_id)

    post = dict(s)
    post["debt_e8"] = debt_e8 - amount_e8
    post["free_debt_e8"] = free_debt_e8 - amount_e8

    effects = {
        "repaid_zusd_e8": int(amount_e8),
        "debt_after_e8": int(post["debt_e8"]),
        "free_debt_after_e8": int(post["free_debt_e8"]),
        "debt_delta_e8": int(amount_e8),
        "free_debt_delta_e8": int(amount_e8),
    }
    return StepOk(state=post, effects=effects)


def _commit_effect(adapter: ZUSDRepaySingleVaultV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ZUSDRepaySingleVaultV1NativeAdapter, Any], Any]] = {
    "apply_repay_single_vault": _handle_apply_repay_single_vault,
}

EFFECT_HANDLERS: dict[str, Callable[[ZUSDRepaySingleVaultV1NativeAdapter, str, Any], None]] = {
    "repaid_zusd_e8": _commit_effect,
    "debt_after_e8": _commit_effect,
    "free_debt_after_e8": _commit_effect,
    "debt_delta_e8": _commit_effect,
    "free_debt_delta_e8": _commit_effect,
}


def make_adapter(ir: Any) -> ZUSDRepaySingleVaultV1NativeAdapter:
    return ZUSDRepaySingleVaultV1NativeAdapter(ir=ir)

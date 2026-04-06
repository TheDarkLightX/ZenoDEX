"""Native (non-interpreter) shell adapter for `zusd_withdraw_collateral_apply_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/zusd_withdraw_collateral_apply_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/zusd_withdraw_collateral_apply_v1.yaml --adapter <this>:make_adapter
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


BPS_SCALE = 10_000
E8 = 100_000_000
# Derived from:
# `python3 -m ESSO validate src/kernels/dex/zusd_withdraw_collateral_apply_v1.yaml`.
IR_HASH = "sha256:250e3f6bdbbd4eff1f556da1cfceb68556d2ec768d9ea3db4d75b8ef6213cc62"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


def _mcr_ok(*, collateral_e8: int, debt_e8: int, price_e8: int, mcr_bps: int) -> bool:
    return (collateral_e8 * price_e8 * BPS_SCALE) >= (debt_e8 * mcr_bps * E8)


@dataclass
class ZUSDWithdrawCollateralApplyV1NativeAdapter:
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


def _handle_apply_withdraw_collateral(adapter: ZUSDWithdrawCollateralApplyV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    args = dict(getattr(command, "args", {}) or {})
    action_id = "apply_withdraw_collateral"

    amount_e8 = int(args["amount_e8"])
    collateral_e8 = int(s["collateral_e8"])
    debt_e8 = int(s["debt_e8"])
    price_e8 = int(s["price_e8"])
    mcr_bps = int(s["mcr_bps"])
    risky_ops_allowed = int(s["risky_ops_allowed"])

    if amount_e8 > collateral_e8:
        return _guard_false(action_id)
    risk_gate_ok = (debt_e8 == 0) or (risky_ops_allowed == 1)
    if not risk_gate_ok:
        return _guard_false(action_id)

    post_collateral_e8 = collateral_e8 - amount_e8
    if not _mcr_ok(collateral_e8=post_collateral_e8, debt_e8=debt_e8, price_e8=price_e8, mcr_bps=mcr_bps):
        return _guard_false(action_id)

    post = dict(s)
    post["collateral_e8"] = post_collateral_e8
    effects = {
        "withdrawn_collateral_e8": int(amount_e8),
        "collateral_after_e8": int(post_collateral_e8),
        "risk_gate_ok": bool(risk_gate_ok),
        "mcr_post_ok": True,
    }
    return StepOk(state=post, effects=effects)


def _commit_effect(adapter: ZUSDWithdrawCollateralApplyV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ZUSDWithdrawCollateralApplyV1NativeAdapter, Any], Any]] = {
    "apply_withdraw_collateral": _handle_apply_withdraw_collateral,
}

EFFECT_HANDLERS: dict[str, Callable[[ZUSDWithdrawCollateralApplyV1NativeAdapter, str, Any], None]] = {
    "withdrawn_collateral_e8": _commit_effect,
    "collateral_after_e8": _commit_effect,
    "risk_gate_ok": _commit_effect,
    "mcr_post_ok": _commit_effect,
}


def make_adapter(ir: Any) -> ZUSDWithdrawCollateralApplyV1NativeAdapter:
    return ZUSDWithdrawCollateralApplyV1NativeAdapter(ir=ir)

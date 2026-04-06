"""Native (non-interpreter) shell adapter for `zusd_risky_ops_gate_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/zusd_risky_ops_gate_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/zusd_risky_ops_gate_v1.yaml --adapter <this>:make_adapter
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


BPS_SCALE = 10_000
E8 = 100_000_000
# Derived from:
# `python3 -m ESSO validate src/kernels/dex/zusd_risky_ops_gate_v1.yaml`.
IR_HASH = "sha256:568e6bba539348c0929aa0056d900db2351e6c0fe19cf4bb9a7e84f3b831dd66"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class ZUSDRiskyOpsGateV1NativeAdapter:
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


def _tcr_ok(state: Mapping[str, Any]) -> bool:
    total_debt = int(state["total_debt_e8"])
    if total_debt == 0:
        return True
    total_coll = int(state["total_collateral_e8"]) + int(state["sp_coll_e8"]) + int(state["protocol_collateral_e8"])
    lhs = total_coll * int(state["price_e8"]) * BPS_SCALE
    rhs = total_debt * int(state["ccr_bps"]) * E8
    return lhs >= rhs


def _handle_check_risky_ops_gate(adapter: ZUSDRiskyOpsGateV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    action_id = "check_risky_ops_gate"

    if int(s["total_collateral_e8"]) < 0 or int(s["total_debt_e8"]) < 0:
        return _guard_false(action_id)
    if int(s["sp_coll_e8"]) < 0 or int(s["protocol_collateral_e8"]) < 0:
        return _guard_false(action_id)

    oracle_initialized = bool(int(s["oracle_seen"]) == 1 and int(s["price_e8"]) > 0 and int(s["price_pending_e8"]) > 0)
    oracle_fresh = bool(
        int(s["oracle_seen"]) == 1
        and (int(s["now_epoch"]) - int(s["oracle_last_update_epoch"])) <= int(s["max_oracle_staleness_epochs"])
    )
    pending_matches_active = bool(int(s["price_pending_e8"]) == int(s["price_e8"]))
    tcr_ok = _tcr_ok(s)
    recovery_mode = bool(int(s["oracle_seen"]) == 0 or int(s["price_e8"]) <= 0 or not tcr_ok)
    risky_ops_allowed = bool(oracle_initialized and oracle_fresh and pending_matches_active and tcr_ok)

    return StepOk(
        state=dict(s),
        effects={
            "oracle_initialized": oracle_initialized,
            "oracle_fresh": oracle_fresh,
            "pending_matches_active": pending_matches_active,
            "tcr_ok": tcr_ok,
            "recovery_mode": recovery_mode,
            "risky_ops_allowed": risky_ops_allowed,
        },
    )


def _commit_effect(adapter: ZUSDRiskyOpsGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ZUSDRiskyOpsGateV1NativeAdapter, Any], Any]] = {
    "check_risky_ops_gate": _handle_check_risky_ops_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[ZUSDRiskyOpsGateV1NativeAdapter, str, Any], None]] = {
    "oracle_initialized": _commit_effect,
    "oracle_fresh": _commit_effect,
    "pending_matches_active": _commit_effect,
    "tcr_ok": _commit_effect,
    "recovery_mode": _commit_effect,
    "risky_ops_allowed": _commit_effect,
}


def make_adapter(ir: Any) -> ZUSDRiskyOpsGateV1NativeAdapter:
    return ZUSDRiskyOpsGateV1NativeAdapter(ir=ir)

"""Native (non-interpreter) shell adapter for `settlement_swap_apply_witness_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/settlement_swap_apply_witness_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/settlement_swap_apply_witness_v1.yaml --adapter <this>:make_adapter

This adapter exists to:
  - pin down proof-carrying settlement math as a small, replayable primitive
  - check wiring/effects determinism end-to-end vs ESSO interpreter semantics
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bind this adapter to the exact kernel spec version (fail-closed by default).
# Derived from: `python3 -m ESSO validate src/kernels/dex/settlement_swap_apply_witness_v1.yaml`.
IR_HASH = "sha256:88422cf011d1e69fab4767dce0d18cfa2799439fe1d8ee428619903ef736194a"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class SettlementSwapApplyWitnessV1NativeAdapter:
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


def _handle_swap_exact_in_apply(adapter: SettlementSwapApplyWitnessV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    args = dict(getattr(command, "args", {}) or {})

    # State vars (all are in-domain per shell verifier).
    trader_in = int(s["trader_in"])
    recipient_out = int(s["recipient_out"])
    reserve_in = int(s["reserve_in"])
    reserve_out = int(s["reserve_out"])
    fee_bps = int(s["fee_bps"])

    # Params (all are in-domain per shell verifier).
    amount_in = int(args["amount_in"])
    min_amount_out = int(args["min_amount_out"])
    witness_reserve_in = int(args["witness_reserve_in"])
    witness_reserve_out = int(args["witness_reserve_out"])

    action_id = "swap_exact_in_apply"

    # Guard: witness freshness.
    if witness_reserve_in != reserve_in:
        return _guard_false(action_id)
    if witness_reserve_out != reserve_out:
        return _guard_false(action_id)

    # Guard: balance feasibility.
    if trader_in < amount_in:
        return _guard_false(action_id)

    # Guard: post-state boundedness (reserve_in max=50).
    if reserve_in + amount_in > 50:
        return _guard_false(action_id)

    # fee_total = ceil(amount_in * fee_bps / 10_000)
    fee_total = (amount_in * fee_bps + 9999) // 10000
    if fee_total > amount_in:
        return _guard_false(action_id)
    net_in = amount_in - fee_total
    if net_in <= 0:
        return _guard_false(action_id)

    denom = reserve_in + net_in
    if denom <= 0:
        return _guard_false(action_id)
    amount_out = (reserve_out * net_in) // denom

    # Guard: non-degenerate output and reserve safety.
    if amount_out < 1:
        return _guard_false(action_id)
    if reserve_out - amount_out < 1:
        return _guard_false(action_id)
    if recipient_out + amount_out > 150:
        return _guard_false(action_id)
    if amount_out < min_amount_out:
        return _guard_false(action_id)

    # State updates (simultaneous pre-state evaluation; assign into post-state dict).
    post = dict(s)
    post["reserve_in_before"] = reserve_in
    post["reserve_out_before"] = reserve_out
    post["trader_in"] = trader_in - amount_in
    post["recipient_out"] = recipient_out + amount_out
    post["reserve_in"] = reserve_in + amount_in
    post["reserve_out"] = reserve_out - amount_out

    effects = {
        "amount_out": int(amount_out),
        "fee_paid": int(fee_total),
        "net_in": int(net_in),
        "k_before": int(reserve_in * reserve_out),
        "k_after": int(post["reserve_in"] * post["reserve_out"]),
        "witness_ok": bool(witness_reserve_in == reserve_in and witness_reserve_out == reserve_out),
        "slippage_ok": bool(amount_out >= min_amount_out),
    }

    return StepOk(state=post, effects=effects)


def _commit_effect(adapter: SettlementSwapApplyWitnessV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[SettlementSwapApplyWitnessV1NativeAdapter, Any], Any]] = {
    "swap_exact_in_apply": _handle_swap_exact_in_apply,
}

EFFECT_HANDLERS: dict[str, Callable[[SettlementSwapApplyWitnessV1NativeAdapter, str, Any], None]] = {
    "amount_out": _commit_effect,
    "fee_paid": _commit_effect,
    "net_in": _commit_effect,
    "k_before": _commit_effect,
    "k_after": _commit_effect,
    "witness_ok": _commit_effect,
    "slippage_ok": _commit_effect,
}


def make_adapter(ir: Any) -> SettlementSwapApplyWitnessV1NativeAdapter:
    return SettlementSwapApplyWitnessV1NativeAdapter(ir=ir)


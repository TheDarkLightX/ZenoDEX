"""Native (non-interpreter) shell adapter for `settlement_swap_exact_out_apply_witness_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/settlement_swap_exact_out_apply_witness_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/settlement_swap_exact_out_apply_witness_v1.yaml --adapter <this>:make_adapter

This adapter exists to:
  - pin down proof-carrying exact-out settlement math as a small primitive
  - check wiring/effects determinism end-to-end vs ESSO interpreter semantics
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bind this adapter to the exact kernel spec version (fail-closed by default).
# Derived from: `python3 -m ESSO validate src/kernels/dex/settlement_swap_exact_out_apply_witness_v1.yaml`.
IR_HASH = "sha256:096d1cf6d275410f3548e3dee6056ab6dce392a0ce0e532409689b0dd0b4900e"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class SettlementSwapExactOutApplyWitnessV1NativeAdapter:
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


def _handle_swap_exact_out_apply(adapter: SettlementSwapExactOutApplyWitnessV1NativeAdapter, command: Any) -> Any:
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
    amount_out = int(args["amount_out"])
    max_amount_in = int(args["max_amount_in"])
    witness_reserve_in = int(args["witness_reserve_in"])
    witness_reserve_out = int(args["witness_reserve_out"])

    action_id = "swap_exact_out_apply"

    # Guard: witness freshness.
    if witness_reserve_in != reserve_in:
        return _guard_false(action_id)
    if witness_reserve_out != reserve_out:
        return _guard_false(action_id)

    # Guard: cannot drain the pool.
    if amount_out >= reserve_out:
        return _guard_false(action_id)
    denom_out = reserve_out - amount_out

    # Guard: fee_den = 10000 - fee_bps must be positive.
    fee_den = 10000 - fee_bps
    if fee_den <= 0:
        return _guard_false(action_id)

    # net_in_required = ceil(reserve_in * amount_out / (reserve_out - amount_out))
    net_in_required = (reserve_in * amount_out + denom_out - 1) // denom_out

    # amount_in = ceil(net_in_required * 10000 / (10000 - fee_bps))
    amount_in = (net_in_required * 10000 + fee_den - 1) // fee_den

    # Guard: amount_in <= max_amount_in and user can pay it.
    if amount_in > max_amount_in:
        return _guard_false(action_id)
    if trader_in < amount_in:
        return _guard_false(action_id)

    # Guard: post reserve_in boundedness (reserve_in max=50).
    if reserve_in + amount_in > 50:
        return _guard_false(action_id)

    # Guard: recipient_out boundedness (recipient_out max=150).
    if recipient_out + amount_out > 150:
        return _guard_false(action_id)

    # fee_total = ceil(amount_in * fee_bps / 10_000)
    fee_total = (amount_in * fee_bps + 9999) // 10000
    net_in_actual = amount_in - fee_total

    denom_quote = reserve_in + net_in_actual
    amount_out_quote = (reserve_out * net_in_actual) // denom_quote

    # By construction, net_in_actual >= net_in_required, so the recomputed
    # exact-in quote cannot undershoot the requested output.
    overdelivery_gap = amount_out_quote - amount_out
    gap_bps = (overdelivery_gap * 10000 + amount_out - 1) // amount_out
    if gap_bps > 200:
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
        "amount_in": int(amount_in),
        "amount_out": int(amount_out),
        "amount_out_quote": int(amount_out_quote),
        "overdelivery_gap": int(overdelivery_gap),
        "gap_bps": int(gap_bps),
        "fee_paid": int(fee_total),
        "net_in_actual": int(net_in_actual),
        "k_before": int(reserve_in * reserve_out),
        "k_after": int(post["reserve_in"] * post["reserve_out"]),
        "witness_ok": bool(witness_reserve_in == reserve_in and witness_reserve_out == reserve_out),
        "slippage_ok": int(1),
    }

    return StepOk(state=post, effects=effects)


def _commit_effect(adapter: SettlementSwapExactOutApplyWitnessV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[SettlementSwapExactOutApplyWitnessV1NativeAdapter, Any], Any]] = {
    "swap_exact_out_apply": _handle_swap_exact_out_apply,
}

EFFECT_HANDLERS: dict[str, Callable[[SettlementSwapExactOutApplyWitnessV1NativeAdapter, str, Any], None]] = {
    "amount_in": _commit_effect,
    "amount_out": _commit_effect,
    "amount_out_quote": _commit_effect,
    "overdelivery_gap": _commit_effect,
    "gap_bps": _commit_effect,
    "fee_paid": _commit_effect,
    "net_in_actual": _commit_effect,
    "k_before": _commit_effect,
    "k_after": _commit_effect,
    "witness_ok": _commit_effect,
    "slippage_ok": _commit_effect,
}


def make_adapter(ir: Any) -> SettlementSwapExactOutApplyWitnessV1NativeAdapter:
    return SettlementSwapExactOutApplyWitnessV1NativeAdapter(ir=ir)

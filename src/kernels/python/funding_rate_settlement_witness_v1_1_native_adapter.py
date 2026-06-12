"""Native shell adapter for ``funding_rate_settlement_witness_v1_1``."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from .funding_rate_settlement_runtime_v1_1 import compute_funding_rate_settlement


IR_HASH = "sha256:be617ba62f6af87965eb5b486b1727f1c15584292b4401d4e4b4545edc1de87d"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class FundingRateSettlementWitnessV11NativeAdapter:
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


def _handle_compute_settlement(adapter: FundingRateSettlementWitnessV11NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    args = dict(getattr(command, "args", {}) or {})
    action_id = "compute_settlement"

    total_exposure = int(s["rate_long_exposure"]) + int(s["rate_short_exposure"])
    if total_exposure <= 0 or total_exposure > 1_000_000_000_000:
        return _guard_false(action_id)

    settlement = compute_funding_rate_settlement(
        rate_long_exposure=int(s["rate_long_exposure"]),
        rate_short_exposure=int(s["rate_short_exposure"]),
        premium_pool=int(s["premium_pool"]),
        implied_rate_bps=int(s["implied_rate_bps"]),
        funding_cap_bps=int(s["funding_cap_bps"]),
        protocol_fee_bps=int(s["protocol_fee_bps"]),
        mark_price_e8=int(args["mark_price_e8"]),
        index_price_e8=int(args["index_price_e8"]),
    )
    if int(args["witness_realized_rate_bps"]) != int(settlement.realized_rate_bps):
        return _guard_false(action_id)
    if int(args["witness_protocol_fee"]) != int(settlement.protocol_fee):
        return _guard_false(action_id)
    if int(args["witness_long_payout"]) != int(settlement.long_payout):
        return _guard_false(action_id)
    if int(args["witness_short_payout"]) != int(settlement.short_payout):
        return _guard_false(action_id)

    post = dict(s)
    post["realized_rate_bps"] = int(settlement.realized_rate_bps)
    post["protocol_fee"] = int(settlement.protocol_fee)
    post["long_payout"] = int(settlement.long_payout)
    post["short_payout"] = int(settlement.short_payout)

    effects = {
        "realized_rate_bps": int(settlement.realized_rate_bps),
        "protocol_fee": int(settlement.protocol_fee),
        "long_payout": int(settlement.long_payout),
        "short_payout": int(settlement.short_payout),
        "winning_long": bool(settlement.winning_long),
    }
    return StepOk(state=post, effects=effects)


def _commit_effect(adapter: FundingRateSettlementWitnessV11NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[FundingRateSettlementWitnessV11NativeAdapter, Any], Any]] = {
    "compute_settlement": _handle_compute_settlement,
}

EFFECT_HANDLERS: dict[str, Callable[[FundingRateSettlementWitnessV11NativeAdapter, str, Any], None]] = {
    "realized_rate_bps": _commit_effect,
    "protocol_fee": _commit_effect,
    "long_payout": _commit_effect,
    "short_payout": _commit_effect,
    "winning_long": _commit_effect,
}


def make_adapter(ir: Any) -> FundingRateSettlementWitnessV11NativeAdapter:
    return FundingRateSettlementWitnessV11NativeAdapter(ir=ir)

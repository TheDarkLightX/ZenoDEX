from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from ..integration.autotrader_signals import (
    QuoteReceiptSignalPacket,
    quote_receipt_signal_packet_from_dict,
)
from ..kernels.python.strategy_budget_guard_v1_adapter import (
    MAX_U32,
    StrategyBudgetState,
    consume_order,
    roll_window,
)
from ..kernels.python.strategy_execution_guard_v1_adapter import check_order_execution
from ..kernels.python.strategy_kill_switch_guard_v1_adapter import check_strategy_kill_switch_guard
from ..kernels.python.strategy_oracle_freshness_guard_v1_adapter import check_oracle_freshness
from ..kernels.python.strategy_signal_provenance_guard_v1_adapter import check_signal_provenance
from .strategy_ir import StrategyIR, strategy_budget_window_id

AUTOTRADER_LOCAL_GUARD_EVALUATION_SCHEMA = "zenodex/autotrader-local-guard-evaluation/v1"


def _require_u32(name: str, value: object, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < minimum or out > MAX_U32:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_text(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    text = value.strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    return text


def _require_optional_u32(name: str, value: object, *, minimum: int = 0) -> int | None:
    if value is None:
        return None
    return _require_u32(name, value, minimum=minimum)


def _require_optional_text(name: str, value: object) -> str | None:
    if value is None:
        return None
    return _require_text(name, value)


def _reason_code(reason: str | None) -> str | None:
    if reason is None:
        return None
    return reason.split(":", 1)[0]


@dataclass(frozen=True)
class AutoTraderLocalGuardInputs:
    current_epoch: int
    order_amount: int
    projected_live_orders: int = 1
    lifetime_spent: int = 0
    spent_in_window: int = 0
    budget_window_id: int | None = None
    kill_switch_active: bool = False
    last_action_epoch: int | None = None
    slippage_bps: int | None = None
    quote_epoch: int | None = None
    signal_packet: QuoteReceiptSignalPacket | None = None

    def __post_init__(self) -> None:
        current_epoch = _require_u32("current_epoch", self.current_epoch)
        order_amount = _require_u32("order_amount", self.order_amount, minimum=1)
        projected_live_orders = _require_u32("projected_live_orders", self.projected_live_orders)
        lifetime_spent = _require_u32("lifetime_spent", self.lifetime_spent)
        spent_in_window = _require_u32("spent_in_window", self.spent_in_window)
        budget_window_id = (
            current_epoch if self.budget_window_id is None else _require_u32("budget_window_id", self.budget_window_id)
        )
        kill_switch_active = _require_bool("kill_switch_active", self.kill_switch_active)
        if self.last_action_epoch is not None:
            _require_u32("last_action_epoch", self.last_action_epoch)
        if self.slippage_bps is not None:
            _require_u32("slippage_bps", self.slippage_bps)
        if self.quote_epoch is not None:
            _require_u32("quote_epoch", self.quote_epoch)
        if self.signal_packet is not None and not isinstance(self.signal_packet, QuoteReceiptSignalPacket):
            raise TypeError("signal_packet must be a QuoteReceiptSignalPacket when present")
        object.__setattr__(self, "current_epoch", current_epoch)
        object.__setattr__(self, "order_amount", order_amount)
        object.__setattr__(self, "projected_live_orders", projected_live_orders)
        object.__setattr__(self, "lifetime_spent", lifetime_spent)
        object.__setattr__(self, "spent_in_window", spent_in_window)
        object.__setattr__(self, "budget_window_id", budget_window_id)
        object.__setattr__(self, "kill_switch_active", kill_switch_active)

    def resolved_quote_epoch(self) -> int | None:
        if self.quote_epoch is not None:
            return int(self.quote_epoch)
        if self.signal_packet is not None:
            return int(self.signal_packet.quote_epoch)
        return None

    def to_dict(self) -> dict[str, Any]:
        budget_window_id = self.budget_window_id
        if budget_window_id is None:
            raise ValueError("budget_window_id must be resolved")
        payload: dict[str, Any] = {
            "current_epoch": int(self.current_epoch),
            "order_amount": int(self.order_amount),
            "projected_live_orders": int(self.projected_live_orders),
            "lifetime_spent": int(self.lifetime_spent),
            "spent_in_window": int(self.spent_in_window),
            "budget_window_id": int(budget_window_id),
            "kill_switch_active": bool(self.kill_switch_active),
            "last_action_epoch": self.last_action_epoch,
            "slippage_bps": self.slippage_bps,
            "quote_epoch": self.quote_epoch,
        }
        if self.signal_packet is not None:
            payload["signal_packet"] = self.signal_packet.to_dict()
        return payload


@dataclass(frozen=True)
class AutoTraderLocalGuardFamilyResult:
    family: str
    checked: bool
    ok: bool
    reason: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.family, str) or not self.family.strip():
            raise ValueError("family must be a non-empty string")
        if not isinstance(self.checked, bool):
            raise TypeError("checked must be a bool")
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be a bool")
        if self.reason is not None and (not isinstance(self.reason, str) or not self.reason.strip()):
            raise ValueError("reason must be a non-empty string when present")
        if not self.checked and not self.ok:
            raise ValueError("unchecked guard families cannot be failing")
        if not self.checked and self.reason is not None:
            raise ValueError("unchecked guard families cannot carry a reason")
        if self.ok and self.reason is not None:
            raise ValueError("passing guard families cannot carry a reason")

    @property
    def blocking(self) -> bool:
        return self.checked and (not self.ok)

    @property
    def reason_code(self) -> str | None:
        return _reason_code(self.reason)

    def to_dict(self) -> dict[str, Any]:
        return {
            "family": self.family,
            "checked": bool(self.checked),
            "ok": bool(self.ok),
            "blocking": bool(self.blocking),
            "reason": self.reason,
            "reason_code": self.reason_code,
        }


@dataclass(frozen=True)
class AutoTraderLocalGuardEvaluation:
    strategy_id: str
    family_results: tuple[AutoTraderLocalGuardFamilyResult, ...]
    inputs: AutoTraderLocalGuardInputs

    def __post_init__(self) -> None:
        if not isinstance(self.strategy_id, str) or not self.strategy_id.strip():
            raise ValueError("strategy_id must be a non-empty string")
        if not isinstance(self.inputs, AutoTraderLocalGuardInputs):
            raise TypeError("inputs must be an AutoTraderLocalGuardInputs")
        if not isinstance(self.family_results, tuple) or not self.family_results:
            raise ValueError("family_results must be a non-empty tuple")
        seen: set[str] = set()
        for result in self.family_results:
            if not isinstance(result, AutoTraderLocalGuardFamilyResult):
                raise TypeError("family_results entries must be AutoTraderLocalGuardFamilyResult instances")
            if result.family in seen:
                raise ValueError(f"duplicate guard family: {result.family}")
            seen.add(result.family)

    @property
    def ok(self) -> bool:
        return all(not result.blocking for result in self.family_results)

    @property
    def blocking_families(self) -> tuple[str, ...]:
        return tuple(result.family for result in self.family_results if result.blocking)

    @property
    def blocking_reason_codes(self) -> tuple[str, ...]:
        return tuple(
            result.reason_code
            for result in self.family_results
            if result.blocking and result.reason_code is not None
        )

    @property
    def first_blocking_reason(self) -> str | None:
        for result in self.family_results:
            if result.blocking:
                return result.reason
        return None

    def family(self, family_id: str) -> AutoTraderLocalGuardFamilyResult:
        for result in self.family_results:
            if result.family == family_id:
                return result
        raise KeyError(f"unknown guard family: {family_id}")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": AUTOTRADER_LOCAL_GUARD_EVALUATION_SCHEMA,
            "strategy_id": self.strategy_id,
            "ok": bool(self.ok),
            "blocking_families": list(self.blocking_families),
            "blocking_reason_codes": list(self.blocking_reason_codes),
            "first_blocking_reason": self.first_blocking_reason,
            "inputs": self.inputs.to_dict(),
            "family_results": [result.to_dict() for result in self.family_results],
        }


def autotrader_local_guard_inputs_from_dict(payload: Mapping[str, Any]) -> AutoTraderLocalGuardInputs:
    if not isinstance(payload, Mapping):
        raise TypeError("guard inputs payload must be an object")
    signal_packet_raw = payload.get("signal_packet")
    signal_packet = None
    if signal_packet_raw is not None:
        if not isinstance(signal_packet_raw, Mapping):
            raise TypeError("signal_packet must be an object when present")
        signal_packet = quote_receipt_signal_packet_from_dict(signal_packet_raw)
    return AutoTraderLocalGuardInputs(
        current_epoch=_require_u32("current_epoch", payload.get("current_epoch")),
        order_amount=_require_u32("order_amount", payload.get("order_amount"), minimum=1),
        projected_live_orders=_require_u32("projected_live_orders", payload.get("projected_live_orders", 1)),
        lifetime_spent=_require_u32("lifetime_spent", payload.get("lifetime_spent", 0)),
        spent_in_window=_require_u32("spent_in_window", payload.get("spent_in_window", 0)),
        budget_window_id=_require_optional_u32("budget_window_id", payload.get("budget_window_id")),
        kill_switch_active=_require_bool("kill_switch_active", payload.get("kill_switch_active", False)),
        last_action_epoch=_require_optional_u32("last_action_epoch", payload.get("last_action_epoch")),
        slippage_bps=_require_optional_u32("slippage_bps", payload.get("slippage_bps")),
        quote_epoch=_require_optional_u32("quote_epoch", payload.get("quote_epoch")),
        signal_packet=signal_packet,
    )


def autotrader_local_guard_family_result_from_dict(
    payload: Mapping[str, Any],
) -> AutoTraderLocalGuardFamilyResult:
    if not isinstance(payload, Mapping):
        raise TypeError("guard family result payload must be an object")
    return AutoTraderLocalGuardFamilyResult(
        family=_require_text("family", payload.get("family")),
        checked=_require_bool("checked", payload.get("checked")),
        ok=_require_bool("ok", payload.get("ok")),
        reason=_require_optional_text("reason", payload.get("reason")),
    )


def autotrader_local_guard_evaluation_from_dict(
    payload: Mapping[str, Any],
) -> AutoTraderLocalGuardEvaluation:
    if not isinstance(payload, Mapping):
        raise TypeError("guard evaluation payload must be an object")
    schema = payload.get("schema")
    if schema is not None and schema != AUTOTRADER_LOCAL_GUARD_EVALUATION_SCHEMA:
        raise ValueError("guard evaluation schema mismatch")
    inputs_raw = payload.get("inputs")
    if not isinstance(inputs_raw, Mapping):
        raise ValueError("guard evaluation inputs must be an object")
    family_results_raw = payload.get("family_results")
    if not isinstance(family_results_raw, list):
        raise ValueError("guard evaluation family_results must be a list")
    evaluation = AutoTraderLocalGuardEvaluation(
        strategy_id=_require_text("strategy_id", payload.get("strategy_id")),
        inputs=autotrader_local_guard_inputs_from_dict(inputs_raw),
        family_results=tuple(
            autotrader_local_guard_family_result_from_dict(row) for row in family_results_raw
        ),
    )
    expected_ok = payload.get("ok")
    if expected_ok is not None and bool(expected_ok) != evaluation.ok:
        raise ValueError("guard evaluation ok mismatch")
    expected_blocking_families = payload.get("blocking_families")
    if expected_blocking_families is not None:
        if tuple(expected_blocking_families) != evaluation.blocking_families:
            raise ValueError("guard evaluation blocking_families mismatch")
    expected_reason_codes = payload.get("blocking_reason_codes")
    if expected_reason_codes is not None:
        if tuple(expected_reason_codes) != evaluation.blocking_reason_codes:
            raise ValueError("guard evaluation blocking_reason_codes mismatch")
    expected_first_reason = payload.get("first_blocking_reason")
    if expected_first_reason is not None and expected_first_reason != evaluation.first_blocking_reason:
        raise ValueError("guard evaluation first_blocking_reason mismatch")
    return evaluation


def _passed(family: str) -> AutoTraderLocalGuardFamilyResult:
    return AutoTraderLocalGuardFamilyResult(family=family, checked=True, ok=True)


def _failed(family: str, reason: str) -> AutoTraderLocalGuardFamilyResult:
    return AutoTraderLocalGuardFamilyResult(family=family, checked=True, ok=False, reason=reason)


def _unchecked(family: str) -> AutoTraderLocalGuardFamilyResult:
    return AutoTraderLocalGuardFamilyResult(family=family, checked=False, ok=True)


def _cadence_epochs(strategy: StrategyIR) -> int:
    raw = strategy.template_params.get("cadence_epochs", 1)
    return _require_u32("template_params.cadence_epochs", raw, minimum=1)


def evaluate_autotrader_local_guards(
    *,
    strategy: StrategyIR,
    inputs: AutoTraderLocalGuardInputs,
) -> AutoTraderLocalGuardEvaluation:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(inputs, AutoTraderLocalGuardInputs):
        raise TypeError("inputs must be an AutoTraderLocalGuardInputs")

    family_results: list[AutoTraderLocalGuardFamilyResult] = []

    controls_result = check_strategy_kill_switch_guard(
        kill_switch_enabled=strategy.controls.kill_switch_enabled,
        kill_switch_active=inputs.kill_switch_active,
    )
    family_results.append(
        _passed("controls") if controls_result.ok else _failed("controls", str(controls_result.error))
    )

    effective_slippage_bps = (
        strategy.risk_limits.max_slippage_bps if inputs.slippage_bps is None else int(inputs.slippage_bps)
    )
    if effective_slippage_bps > strategy.risk_limits.max_slippage_bps:
        family_results.append(
            _failed(
                "slippage",
                f"slippage_limit_exceeded:{effective_slippage_bps}>{strategy.risk_limits.max_slippage_bps}",
            )
        )
    else:
        family_results.append(_passed("slippage"))

    if inputs.signal_packet is None:
        if strategy.risk_limits.require_quote_receipts:
            family_results.append(_failed("provenance", "signal_packet_missing"))
        else:
            family_results.append(_unchecked("provenance"))
    elif inputs.signal_packet.current_epoch != inputs.current_epoch:
        family_results.append(
            _failed(
                "provenance",
                f"signal_packet_epoch_mismatch:{inputs.signal_packet.current_epoch}!={inputs.current_epoch}",
            )
        )
    elif inputs.quote_epoch is not None and inputs.signal_packet.quote_epoch != inputs.quote_epoch:
        family_results.append(
            _failed(
                "provenance",
                f"signal_packet_quote_epoch_mismatch:{inputs.signal_packet.quote_epoch}!={inputs.quote_epoch}",
            )
        )
    else:
        provenance_result = check_signal_provenance(
            packet=inputs.signal_packet,
            require_quote_receipts=strategy.risk_limits.require_quote_receipts,
        )
        family_results.append(
            _passed("provenance") if provenance_result.ok else _failed("provenance", str(provenance_result.error))
        )

    resolved_quote_epoch = inputs.resolved_quote_epoch()
    if resolved_quote_epoch is None:
        family_results.append(_failed("oracle_freshness", "quote_epoch_missing"))
    else:
        oracle_result = check_oracle_freshness(
            current_epoch=inputs.current_epoch,
            quote_epoch=resolved_quote_epoch,
            max_oracle_staleness_epochs=strategy.risk_limits.max_oracle_staleness_epochs,
        )
        family_results.append(
            _passed("oracle_freshness") if oracle_result.ok else _failed("oracle_freshness", str(oracle_result.error))
        )

    execution_result = check_order_execution(
        current_epoch=inputs.current_epoch,
        valid_from_epoch=strategy.strategy_window.valid_from_epoch,
        valid_until_epoch=strategy.strategy_window.valid_until_epoch,
        last_action_epoch=inputs.last_action_epoch,
        cadence_epochs=_cadence_epochs(strategy),
        min_order_spacing_epochs=strategy.strategy_window.min_order_spacing_epochs,
        projected_live_orders=inputs.projected_live_orders,
        max_live_orders=strategy.controls.max_live_orders,
    )
    family_results.append(
        _passed("execution") if execution_result.ok else _failed("execution", str(execution_result.error))
    )

    projected_lifetime_spent = inputs.lifetime_spent + inputs.order_amount
    notional_reason: str | None = None
    if projected_lifetime_spent > strategy.notional_caps.lifetime_max:
        notional_reason = (
            f"lifetime_cap_exceeded:{projected_lifetime_spent}>{strategy.notional_caps.lifetime_max}"
        )
    else:
        # Keep kill-switch reporting isolated in the controls family to avoid double-counting one latch.
        target_budget_window_id = strategy_budget_window_id(strategy.strategy_window, inputs.current_epoch)
        budget_window_id = inputs.budget_window_id
        if budget_window_id is None:
            raise ValueError("budget_window_id must be resolved")
        if budget_window_id == inputs.current_epoch and budget_window_id != target_budget_window_id:
            budget_window_id = target_budget_window_id
        budget_state = StrategyBudgetState(
            window_id=int(budget_window_id),
            spent_in_window=inputs.spent_in_window,
            kill_switch_on=False,
        )
        if target_budget_window_id > budget_state.window_id:
            rolled = roll_window(state=budget_state, new_window_id=target_budget_window_id)
            if not rolled.ok:
                notional_reason = f"budget_window_roll_failed:{rolled.error}"
            else:
                budget_state = rolled.state
        elif target_budget_window_id < budget_state.window_id:
            notional_reason = f"budget_window_regression:{target_budget_window_id}<{budget_state.window_id}"

        if notional_reason is None:
            budget_result = consume_order(
                state=budget_state,
                order_amount=inputs.order_amount,
                per_order_limit=strategy.notional_caps.per_order_max,
                window_budget=strategy.notional_caps.per_window_max,
            )
            if not budget_result.ok:
                notional_reason = str(budget_result.error)

    family_results.append(
        _passed("notional_budget") if notional_reason is None else _failed("notional_budget", notional_reason)
    )

    return AutoTraderLocalGuardEvaluation(
        strategy_id=strategy.strategy_id,
        family_results=tuple(family_results),
        inputs=inputs,
    )


__all__ = [
    "AUTOTRADER_LOCAL_GUARD_EVALUATION_SCHEMA",
    "AutoTraderLocalGuardEvaluation",
    "AutoTraderLocalGuardFamilyResult",
    "AutoTraderLocalGuardInputs",
    "autotrader_local_guard_evaluation_from_dict",
    "autotrader_local_guard_family_result_from_dict",
    "autotrader_local_guard_inputs_from_dict",
    "evaluate_autotrader_local_guards",
]

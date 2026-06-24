from __future__ import annotations

from dataclasses import dataclass

from .strategy_budget_guard_v1_adapter import MAX_U32


def _require_u32(name: str, value: object, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < minimum or out > MAX_U32:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


@dataclass(frozen=True)
class StrategyExecutionResult:
    ok: bool
    within_window_ok: bool
    monotone_epoch_ok: bool
    cadence_ok: bool
    live_orders_ok: bool
    error: str | None = None


def check_order_execution(
    *,
    current_epoch: int,
    valid_from_epoch: int,
    valid_until_epoch: int,
    last_action_epoch: int | None,
    cadence_epochs: int,
    min_order_spacing_epochs: int,
    projected_live_orders: int,
    max_live_orders: int,
) -> StrategyExecutionResult:
    current_epoch = _require_u32("current_epoch", current_epoch)
    valid_from_epoch = _require_u32("valid_from_epoch", valid_from_epoch)
    valid_until_epoch = _require_u32("valid_until_epoch", valid_until_epoch)
    cadence_epochs = _require_u32("cadence_epochs", cadence_epochs, minimum=1)
    min_order_spacing_epochs = _require_u32(
        "min_order_spacing_epochs",
        min_order_spacing_epochs,
    )
    projected_live_orders = _require_u32("projected_live_orders", projected_live_orders)
    max_live_orders = _require_u32("max_live_orders", max_live_orders, minimum=1)
    if valid_from_epoch > valid_until_epoch:
        raise ValueError("valid_from_epoch must be <= valid_until_epoch")

    if last_action_epoch is None:
        monotone_epoch_ok = True
        cadence_ok = True
    else:
        last_action_epoch = _require_u32("last_action_epoch", last_action_epoch)
        monotone_epoch_ok = current_epoch >= last_action_epoch
        if monotone_epoch_ok:
            delta = current_epoch - last_action_epoch
            cadence_ok = delta >= cadence_epochs and delta >= min_order_spacing_epochs
        else:
            cadence_ok = False

    within_window_ok = valid_from_epoch <= current_epoch <= valid_until_epoch
    live_orders_ok = projected_live_orders <= max_live_orders

    if not within_window_ok:
        if current_epoch < valid_from_epoch:
            return StrategyExecutionResult(
                ok=False,
                within_window_ok=False,
                monotone_epoch_ok=monotone_epoch_ok,
                cadence_ok=cadence_ok,
                live_orders_ok=live_orders_ok,
                error=f"strategy_window_not_open:{current_epoch}<{valid_from_epoch}",
            )
        return StrategyExecutionResult(
            ok=False,
            within_window_ok=False,
            monotone_epoch_ok=monotone_epoch_ok,
            cadence_ok=cadence_ok,
            live_orders_ok=live_orders_ok,
            error=f"strategy_window_expired:{current_epoch}>{valid_until_epoch}",
        )

    if last_action_epoch is not None and not monotone_epoch_ok:
        return StrategyExecutionResult(
            ok=False,
            within_window_ok=True,
            monotone_epoch_ok=False,
            cadence_ok=False,
            live_orders_ok=live_orders_ok,
            error=f"non_monotone_epoch:{current_epoch}<{last_action_epoch}",
        )

    if not cadence_ok:
        required_spacing = max(cadence_epochs, min_order_spacing_epochs)
        if last_action_epoch is None:
            raise AssertionError("internal: cadence failed without last_action_epoch")
        delta = current_epoch - last_action_epoch
        return StrategyExecutionResult(
            ok=False,
            within_window_ok=True,
            monotone_epoch_ok=True,
            cadence_ok=False,
            live_orders_ok=live_orders_ok,
            error=f"cadence_not_elapsed:delta={delta},required={required_spacing}",
        )

    if not live_orders_ok:
        return StrategyExecutionResult(
            ok=False,
            within_window_ok=True,
            monotone_epoch_ok=True,
            cadence_ok=True,
            live_orders_ok=False,
            error=f"max_live_orders_reached:{projected_live_orders}>{max_live_orders}",
        )

    return StrategyExecutionResult(
        ok=True,
        within_window_ok=True,
        monotone_epoch_ok=True,
        cadence_ok=True,
        live_orders_ok=True,
    )

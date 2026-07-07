from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .perp_v2.funding_rule import compute_funding_rate_bps
from .perp_v2.math import BPS_SCALE, is_oracle_fresh, settle_price

MARK_PRICE_SOURCE_EXTERNAL_MEDIAN = 1
MARK_PRICE_SOURCE_SPOT_AMM_TWAP = 2
MARK_PRICE_SOURCE_ORACLE_CLAMPED_SPOT = 3
MARK_PRICE_SOURCE_INTERNAL_BATCH_CLEARING = 4

DERIVATIVES_SAFE_MARK_PRICE_SOURCES = frozenset(
    (
        MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
        MARK_PRICE_SOURCE_SPOT_AMM_TWAP,
        MARK_PRICE_SOURCE_ORACLE_CLAMPED_SPOT,
    )
)


@dataclass(frozen=True)
class PerpApplyFundingAutoGateOutcome:
    now_epoch: int
    mark_price_source_ok: bool
    clearing_price_seen_ok: bool
    clearing_price_epoch_ok: bool
    pre_settlement_window_ok: bool
    oracle_seen_ok: bool
    index_price_ok: bool
    staleness_param_ok: bool
    oracle_fresh: bool
    clearing_price_ok: bool
    max_oracle_move_ok: bool
    funding_cap_ok: bool
    projected_net_funding_quote: int
    net_funding_balanced: bool
    fee_pool_quote: int
    fee_income_quote: int
    insurance_balance_quote: int
    max_fee_pool_quote: int
    fee_pool_after_funding_quote: int
    fee_income_after_funding_quote: int
    insurance_after_funding_quote: int
    fee_pool_bounds_ok: bool
    fee_income_bounds_ok: bool
    insurance_bounds_ok: bool
    funding_not_applied: bool
    mark_price_e8: int
    funding_rate_bps: int
    funding_auto_allowed: bool


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_flag(value: Any, *, name: str) -> bool:
    if isinstance(value, bool):
        return bool(value)
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be a bool or 0/1 int")
    if value not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1")
    return bool(value)


def is_derivatives_safe_mark_price_source(source_kind: Any) -> bool:
    source = _require_int(source_kind, name="mark_price_source_kind")
    return source in DERIVATIVES_SAFE_MARK_PRICE_SOURCES


def evaluate_perp_apply_funding_auto_gate(
    *,
    now_epoch: int,
    mark_price_source_kind: int = MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
    clearing_price_seen: Any,
    clearing_price_epoch: int,
    oracle_last_update_epoch: int,
    oracle_seen: Any,
    index_price_e8: int,
    max_oracle_staleness_epochs: int,
    clearing_price_e8: int,
    max_oracle_move_bps: int,
    funding_cap_bps: int,
    projected_net_funding_quote: int,
    any_funding_applied_this_epoch: Any,
    fee_pool_quote: int = 0,
    fee_income_quote: int = 0,
    insurance_balance_quote: int = 0,
    max_fee_pool_quote: int = 1_000_000_000_000_000,
) -> PerpApplyFundingAutoGateOutcome:
    now = _require_int(now_epoch, name="now_epoch")
    mark_source = _require_int(mark_price_source_kind, name="mark_price_source_kind")
    clearing_seen = _require_flag(clearing_price_seen, name="clearing_price_seen")
    clearing_epoch = _require_int(clearing_price_epoch, name="clearing_price_epoch")
    oracle_last = _require_int(oracle_last_update_epoch, name="oracle_last_update_epoch")
    oracle_seen_flag = _require_flag(oracle_seen, name="oracle_seen")
    index_price = _require_int(index_price_e8, name="index_price_e8")
    staleness = _require_int(max_oracle_staleness_epochs, name="max_oracle_staleness_epochs")
    clearing_price = _require_int(clearing_price_e8, name="clearing_price_e8")
    max_move = _require_int(max_oracle_move_bps, name="max_oracle_move_bps")
    funding_cap = _require_int(funding_cap_bps, name="funding_cap_bps")
    projected_net = _require_int(projected_net_funding_quote, name="projected_net_funding_quote")
    funding_applied = _require_flag(any_funding_applied_this_epoch, name="any_funding_applied_this_epoch")
    fee_pool = _require_int(fee_pool_quote, name="fee_pool_quote")
    fee_income = _require_int(fee_income_quote, name="fee_income_quote")
    insurance = _require_int(insurance_balance_quote, name="insurance_balance_quote")
    max_fee_pool = _require_int(max_fee_pool_quote, name="max_fee_pool_quote")

    mark_price_source_ok = mark_source in DERIVATIVES_SAFE_MARK_PRICE_SOURCES
    clearing_price_seen_ok = clearing_seen
    clearing_price_epoch_ok = clearing_epoch == now
    pre_settlement_window_ok = oracle_last < now
    oracle_seen_ok = oracle_seen_flag
    index_price_ok = index_price > 0
    staleness_param_ok = staleness > 0
    oracle_fresh = bool(
        staleness_param_ok
        and is_oracle_fresh(
            now,
            oracle_last,
            staleness,
            oracle_seen_flag,
        )
    )
    clearing_price_ok = clearing_price > 0
    max_oracle_move_ok = 0 <= max_move <= BPS_SCALE
    funding_cap_ok = 0 < funding_cap <= BPS_SCALE
    net_funding_balanced = projected_net == 0
    funding_not_applied = not funding_applied
    fee_pool_after = fee_pool + projected_net
    fee_income_after = fee_income + projected_net
    insurance_after = insurance + projected_net
    fee_pool_bounds_ok = (
        0 <= fee_pool <= max_fee_pool
        and 0 <= fee_pool_after <= max_fee_pool
    )
    fee_income_bounds_ok = (
        0 <= fee_income <= max_fee_pool
        and 0 <= fee_income_after <= max_fee_pool
    )
    insurance_bounds_ok = (
        0 <= insurance <= max_fee_pool
        and 0 <= insurance_after <= max_fee_pool
    )

    mark_price_e8 = 0
    funding_rate_bps = 0
    if index_price_ok and clearing_price_ok and max_oracle_move_ok:
        mark_price_e8 = int(
            settle_price(
                clearing_price_e8=clearing_price,
                index_price_e8=index_price,
                max_oracle_move_bps=max_move,
                oracle_seen=oracle_seen_flag,
            )
        )
        if funding_cap_ok:
            funding_rate_bps = int(
                compute_funding_rate_bps(
                    index_price_e8=index_price,
                    mark_price_e8=mark_price_e8,
                    funding_cap_bps=funding_cap,
                )
            )

    funding_auto_allowed = bool(
        mark_price_source_ok
        and clearing_price_seen_ok
        and clearing_price_epoch_ok
        and pre_settlement_window_ok
        and oracle_seen_ok
        and index_price_ok
        and staleness_param_ok
        and oracle_fresh
        and clearing_price_ok
        and max_oracle_move_ok
        and funding_cap_ok
        and fee_pool_bounds_ok
        and fee_income_bounds_ok
        and insurance_bounds_ok
        and funding_not_applied
    )

    return PerpApplyFundingAutoGateOutcome(
        now_epoch=now,
        mark_price_source_ok=mark_price_source_ok,
        clearing_price_seen_ok=clearing_price_seen_ok,
        clearing_price_epoch_ok=clearing_price_epoch_ok,
        pre_settlement_window_ok=pre_settlement_window_ok,
        oracle_seen_ok=oracle_seen_ok,
        index_price_ok=index_price_ok,
        staleness_param_ok=staleness_param_ok,
        oracle_fresh=oracle_fresh,
        clearing_price_ok=clearing_price_ok,
        max_oracle_move_ok=max_oracle_move_ok,
        funding_cap_ok=funding_cap_ok,
        projected_net_funding_quote=projected_net,
        net_funding_balanced=net_funding_balanced,
        fee_pool_quote=fee_pool,
        fee_income_quote=fee_income,
        insurance_balance_quote=insurance,
        max_fee_pool_quote=max_fee_pool,
        fee_pool_after_funding_quote=fee_pool_after,
        fee_income_after_funding_quote=fee_income_after,
        insurance_after_funding_quote=insurance_after,
        fee_pool_bounds_ok=fee_pool_bounds_ok,
        fee_income_bounds_ok=fee_income_bounds_ok,
        insurance_bounds_ok=insurance_bounds_ok,
        funding_not_applied=funding_not_applied,
        mark_price_e8=mark_price_e8,
        funding_rate_bps=funding_rate_bps,
        funding_auto_allowed=funding_auto_allowed,
    )


def perp_apply_funding_auto_gate_error(outcome: PerpApplyFundingAutoGateOutcome) -> str | None:
    if not outcome.mark_price_source_ok:
        return "cannot apply funding: mark price source is not derivatives-safe"
    if not outcome.clearing_price_seen_ok:
        return "cannot apply funding before clearing price is published"
    if not outcome.clearing_price_epoch_ok:
        return "cannot apply funding: clearing price is not for current epoch"
    if not outcome.pre_settlement_window_ok:
        return "cannot apply funding after settlement"
    if not outcome.oracle_seen_ok:
        return "cannot apply funding before oracle is established"
    if not outcome.index_price_ok:
        return "cannot apply funding: index_price_e8 must be positive"
    if not outcome.staleness_param_ok:
        return "cannot apply funding: invalid max_oracle_staleness_epochs"
    if not outcome.oracle_fresh:
        return "cannot apply funding: oracle is stale"
    if not outcome.clearing_price_ok:
        return "cannot apply funding: clearing_price_e8 must be positive"
    if not outcome.max_oracle_move_ok:
        return "cannot apply funding: invalid max_oracle_move_bps"
    if not outcome.funding_cap_ok:
        return "cannot apply funding: invalid funding_cap_bps"
    if (
        not outcome.fee_pool_bounds_ok
        or not outcome.fee_income_bounds_ok
        or not outcome.insurance_bounds_ok
    ):
        return (
            "apply_funding_auto would violate funding sink bounds "
            f"(net={outcome.projected_net_funding_quote})"
        )
    if not outcome.funding_not_applied:
        return "funding already applied this epoch"
    return None

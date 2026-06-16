from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .perp_v2.math import (
    MAX_COLLATERAL,
    MAX_FUNDING_CUMULATIVE,
    funding_payment,
    is_oracle_fresh,
    maint_margin_req,
)
from .perp_v2.types import EpochPhase

_PHASE_TO_INT = {
    EpochPhase.OPEN: 0,
    EpochPhase.PRICE_PUBLISHED: 1,
    EpochPhase.SETTLED: 2,
}


@dataclass(frozen=True)
class PerpFundingApplyGateOutcome:
    phase_allows_funding: bool
    auth_ok: bool
    index_price_ok: bool
    staleness_param_ok: bool
    oracle_seen_ok: bool
    oracle_fresh: bool
    funding_not_applied_this_epoch: bool
    rate_within_cap: bool
    position_open_ok: bool
    funding_payment_quote: int
    collateral_after_quote: int
    collateral_bounds_ok: bool
    maint_req_quote: int
    maint_margin_ok: bool
    cumulative_after_quote: int
    cumulative_bounds_ok: bool
    funding_apply_allowed: bool


@dataclass(frozen=True)
class _FundingApplyInputs:
    now_epoch: int
    epoch_phase: int
    auth_ok: bool
    index_price_e8: int
    oracle_last_update_epoch: int
    max_oracle_staleness_epochs: int
    oracle_seen: bool
    funding_last_applied_epoch: int
    funding_cap_bps: int
    new_rate_bps: int
    position_base: int
    collateral_quote: int
    maintenance_margin_bps: int
    depeg_buffer_bps: int
    funding_paid_cumulative: int


@dataclass(frozen=True)
class _FundingApplyChecks:
    phase_allows_funding: bool
    index_price_ok: bool
    staleness_param_ok: bool
    oracle_seen_ok: bool
    oracle_fresh: bool
    funding_not_applied_this_epoch: bool
    rate_within_cap: bool
    position_open_ok: bool


@dataclass(frozen=True)
class _FundingApplyQuote:
    funding_payment_quote: int
    collateral_after_quote: int
    cumulative_after_quote: int
    maint_req_quote: int
    collateral_bounds_ok: bool
    maint_margin_ok: bool
    cumulative_bounds_ok: bool


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


def _require_epoch_phase(value: Any, *, name: str) -> int:
    if isinstance(value, EpochPhase):
        return _PHASE_TO_INT[value]
    phase = _require_int(value, name=name)
    if phase < 0 or phase > 2:
        raise ValueError(f"{name} must be in [0, 2]")
    return phase


def _funding_apply_checks(inputs: _FundingApplyInputs) -> _FundingApplyChecks:
    return _FundingApplyChecks(
        phase_allows_funding=inputs.epoch_phase
        in (_PHASE_TO_INT[EpochPhase.OPEN], _PHASE_TO_INT[EpochPhase.PRICE_PUBLISHED]),
        index_price_ok=inputs.index_price_e8 > 0,
        staleness_param_ok=inputs.max_oracle_staleness_epochs > 0,
        oracle_seen_ok=inputs.oracle_seen,
        oracle_fresh=is_oracle_fresh(
            inputs.now_epoch,
            inputs.oracle_last_update_epoch,
            inputs.max_oracle_staleness_epochs,
            inputs.oracle_seen,
        ),
        funding_not_applied_this_epoch=inputs.funding_last_applied_epoch < inputs.now_epoch,
        rate_within_cap=-inputs.funding_cap_bps <= inputs.new_rate_bps <= inputs.funding_cap_bps,
        position_open_ok=inputs.position_base != 0,
    )


def _funding_apply_quote(inputs: _FundingApplyInputs, checks: _FundingApplyChecks) -> _FundingApplyQuote:
    funding_payment_quote = 0
    collateral_after_quote = inputs.collateral_quote
    cumulative_after_quote = inputs.funding_paid_cumulative
    maint_req_quote = 0
    if checks.position_open_ok and checks.index_price_ok:
        funding_payment_quote = funding_payment(inputs.position_base, inputs.index_price_e8, inputs.new_rate_bps)
        collateral_after_quote = inputs.collateral_quote - funding_payment_quote
        cumulative_after_quote = inputs.funding_paid_cumulative + funding_payment_quote
        maint_req_quote = maint_margin_req(
            inputs.position_base,
            inputs.index_price_e8,
            inputs.maintenance_margin_bps,
            inputs.depeg_buffer_bps,
        )

    collateral_bounds_ok = 0 <= collateral_after_quote <= MAX_COLLATERAL
    maint_margin_ok = (not checks.position_open_ok) or (collateral_after_quote >= maint_req_quote)
    cumulative_bounds_ok = -MAX_FUNDING_CUMULATIVE <= cumulative_after_quote <= MAX_FUNDING_CUMULATIVE
    return _FundingApplyQuote(
        funding_payment_quote=funding_payment_quote,
        collateral_after_quote=collateral_after_quote,
        cumulative_after_quote=cumulative_after_quote,
        maint_req_quote=maint_req_quote,
        collateral_bounds_ok=collateral_bounds_ok,
        maint_margin_ok=maint_margin_ok,
        cumulative_bounds_ok=cumulative_bounds_ok,
    )


def _funding_apply_allowed(checks: _FundingApplyChecks, quote: _FundingApplyQuote, *, auth_ok: bool) -> bool:
    return bool(
        checks.phase_allows_funding
        and auth_ok
        and checks.index_price_ok
        and checks.oracle_fresh
        and checks.funding_not_applied_this_epoch
        and checks.rate_within_cap
        and checks.position_open_ok
        and quote.collateral_bounds_ok
        and quote.maint_margin_ok
        and quote.cumulative_bounds_ok
    )


def _funding_apply_outcome(
    inputs: _FundingApplyInputs,
    checks: _FundingApplyChecks,
    quote: _FundingApplyQuote,
) -> PerpFundingApplyGateOutcome:
    return PerpFundingApplyGateOutcome(
        phase_allows_funding=checks.phase_allows_funding,
        auth_ok=inputs.auth_ok,
        index_price_ok=checks.index_price_ok,
        staleness_param_ok=checks.staleness_param_ok,
        oracle_seen_ok=checks.oracle_seen_ok,
        oracle_fresh=checks.oracle_fresh,
        funding_not_applied_this_epoch=checks.funding_not_applied_this_epoch,
        rate_within_cap=checks.rate_within_cap,
        position_open_ok=checks.position_open_ok,
        funding_payment_quote=quote.funding_payment_quote,
        collateral_after_quote=quote.collateral_after_quote,
        collateral_bounds_ok=quote.collateral_bounds_ok,
        maint_req_quote=quote.maint_req_quote,
        maint_margin_ok=quote.maint_margin_ok,
        cumulative_after_quote=quote.cumulative_after_quote,
        cumulative_bounds_ok=quote.cumulative_bounds_ok,
        funding_apply_allowed=_funding_apply_allowed(checks, quote, auth_ok=inputs.auth_ok),
    )


def evaluate_perp_funding_apply_gate(
    *,
    now_epoch: int,
    epoch_phase: Any,
    auth_ok: Any,
    index_price_e8: int,
    oracle_last_update_epoch: int,
    max_oracle_staleness_epochs: int,
    oracle_seen: Any,
    funding_last_applied_epoch: int,
    funding_cap_bps: int,
    new_rate_bps: int,
    position_base: int,
    collateral_quote: int,
    maintenance_margin_bps: int,
    depeg_buffer_bps: int,
    funding_paid_cumulative: int,
) -> PerpFundingApplyGateOutcome:
    inputs = _FundingApplyInputs(
        now_epoch=_require_int(now_epoch, name="now_epoch"),
        epoch_phase=_require_epoch_phase(epoch_phase, name="epoch_phase"),
        auth_ok=_require_flag(auth_ok, name="auth_ok"),
        index_price_e8=_require_int(index_price_e8, name="index_price_e8"),
        oracle_last_update_epoch=_require_int(oracle_last_update_epoch, name="oracle_last_update_epoch"),
        max_oracle_staleness_epochs=_require_int(max_oracle_staleness_epochs, name="max_oracle_staleness_epochs"),
        oracle_seen=_require_flag(oracle_seen, name="oracle_seen"),
        funding_last_applied_epoch=_require_int(funding_last_applied_epoch, name="funding_last_applied_epoch"),
        funding_cap_bps=_require_int(funding_cap_bps, name="funding_cap_bps"),
        new_rate_bps=_require_int(new_rate_bps, name="new_rate_bps"),
        position_base=_require_int(position_base, name="position_base"),
        collateral_quote=_require_int(collateral_quote, name="collateral_quote"),
        maintenance_margin_bps=_require_int(maintenance_margin_bps, name="maintenance_margin_bps"),
        depeg_buffer_bps=_require_int(depeg_buffer_bps, name="depeg_buffer_bps"),
        funding_paid_cumulative=_require_int(funding_paid_cumulative, name="funding_paid_cumulative"),
    )
    checks = _funding_apply_checks(inputs)
    quote = _funding_apply_quote(inputs, checks)
    return _funding_apply_outcome(inputs, checks, quote)


def perp_funding_apply_gate_error(outcome: PerpFundingApplyGateOutcome) -> str | None:
    if not outcome.phase_allows_funding:
        return "apply_funding only allowed during open or price-published phase"
    if not outcome.auth_ok:
        return "apply_funding requires auth"
    if not outcome.index_price_ok:
        return "apply_funding requires positive index_price_e8"
    if not outcome.oracle_seen_ok:
        return "apply_funding requires oracle_seen"
    if not outcome.staleness_param_ok:
        return "apply_funding requires valid max_oracle_staleness_epochs"
    if not outcome.oracle_fresh:
        return "apply_funding requires fresh oracle"
    if not outcome.funding_not_applied_this_epoch:
        return "apply_funding already applied this epoch"
    if not outcome.rate_within_cap:
        return "apply_funding requires new_rate_bps within funding_cap_bps"
    if not outcome.position_open_ok:
        return "apply_funding requires non-zero position"
    if not outcome.collateral_bounds_ok:
        return "apply_funding would violate collateral bounds"
    if not outcome.maint_margin_ok:
        return "apply_funding would violate maintenance margin"
    if not outcome.cumulative_bounds_ok:
        return "apply_funding would violate cumulative funding bounds"
    return None

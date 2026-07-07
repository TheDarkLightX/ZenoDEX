"""Isolated perps market snapshot validation."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

from .perp_apply_funding_auto_gate import is_derivatives_safe_mark_price_source
from .perp_liquidation_envelope import require_perp_liquidation_envelope_bps

Value = bool | int | str


PERP_ACCOUNT_KEYS: set[str] = {
    "position_base",
    "entry_price_e8",
    "collateral_quote",
    "funding_paid_cumulative",
    "funding_last_applied_epoch",
    "liquidated_this_step",
}

PERP_ISOLATED_GLOBAL_KEYS: set[str] = {
    "now_epoch",
    "epoch_phase",
    "breaker_active",
    "breaker_last_trigger_epoch",
    "clearing_price_seen",
    "clearing_price_epoch",
    "clearing_price_e8",
    "mark_price_source_kind",
    "oracle_seen",
    "oracle_last_update_epoch",
    "index_price_e8",
    "max_oracle_staleness_epochs",
    "max_oracle_move_bps",
    "initial_margin_bps",
    "maintenance_margin_bps",
    "depeg_buffer_bps",
    "liquidation_penalty_bps",
    "max_position_abs",
    "fee_pool_quote",
    "funding_rate_bps",
    "funding_cap_bps",
    "insurance_balance",
    "initial_insurance",
    "fee_income",
    "claims_paid",
    "min_notional_for_bounty",
}

PERP_ISOLATED_GLOBAL_BOOL_KEYS: set[str] = {
    "breaker_active",
    "clearing_price_seen",
    "oracle_seen",
}


def validate_isolated_account_state(account: Any) -> None:
    """Validate the isolated account record shape used by PerpAccountState."""
    if not isinstance(account.position_base, int) or isinstance(account.position_base, bool):
        raise TypeError("position_base must be an int")
    if not isinstance(account.entry_price_e8, int) or isinstance(account.entry_price_e8, bool):
        raise TypeError("entry_price_e8 must be an int")
    if not isinstance(account.collateral_quote, int) or isinstance(account.collateral_quote, bool):
        raise TypeError("collateral_quote must be an int")
    if not isinstance(account.funding_paid_cumulative, int) or isinstance(account.funding_paid_cumulative, bool):
        raise TypeError("funding_paid_cumulative must be an int")
    if not isinstance(account.funding_last_applied_epoch, int) or isinstance(account.funding_last_applied_epoch, bool):
        raise TypeError("funding_last_applied_epoch must be an int")
    if not isinstance(account.liquidated_this_step, bool):
        raise TypeError("liquidated_this_step must be a bool")
    if account.entry_price_e8 < 0:
        raise ValueError("entry_price_e8 must be non-negative")
    if account.collateral_quote < 0:
        raise ValueError("collateral_quote must be non-negative")
    if account.funding_last_applied_epoch < 0:
        raise ValueError("funding_last_applied_epoch must be non-negative")


@dataclass(frozen=True)
class _IsolatedValidationContext:
    accounts: Mapping[str, Any]
    now_epoch: int
    epoch_phase: int
    epoch_phase_str: str
    breaker_active: bool
    breaker_last_trigger_epoch: int
    clearing_price_seen: bool
    clearing_price_epoch: int
    clearing_price_e8: int
    mark_price_source_kind: int
    oracle_seen: bool
    oracle_last_update_epoch: int
    index_price_e8: int
    max_oracle_move_bps: int
    initial_margin_bps: int
    maintenance_margin_bps: int
    depeg_buffer_bps: int
    liquidation_penalty_bps: int
    fee_pool_quote: int
    funding_rate_bps: int
    funding_cap_bps: int
    insurance_balance: int
    initial_insurance: int
    fee_income: int
    claims_paid: int


def _read_global_int(global_state: Mapping[str, Value], key: str) -> int:
    value = global_state[key]
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"global_state[{key!r}] must be an int")
    return int(value)


def _read_global_bool(global_state: Mapping[str, Value], key: str) -> bool:
    value = global_state[key]
    if isinstance(value, bool):
        return bool(value)
    if isinstance(value, int) and value in (0, 1):
        return bool(value)
    raise TypeError(f"global_state[{key!r}] must be a bool or 0/1 int")


def _read_account_int(acct: Any, field_name: str) -> int:
    value = getattr(acct, field_name)
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"account {field_name} must be an int")
    return int(value)


def _read_context(
    *,
    global_state: Mapping[str, Value],
    accounts: Mapping[str, Any],
    epoch_phase_int_to_str: Mapping[int, str],
) -> _IsolatedValidationContext:
    now_epoch = _read_global_int(global_state, "now_epoch")
    epoch_phase = _read_global_int(global_state, "epoch_phase")
    epoch_phase_str = epoch_phase_int_to_str.get(epoch_phase, str(epoch_phase))

    return _IsolatedValidationContext(
        accounts=accounts,
        now_epoch=now_epoch,
        epoch_phase=epoch_phase,
        epoch_phase_str=epoch_phase_str,
        breaker_active=_read_global_bool(global_state, "breaker_active"),
        breaker_last_trigger_epoch=_read_global_int(global_state, "breaker_last_trigger_epoch"),
        clearing_price_seen=_read_global_bool(global_state, "clearing_price_seen"),
        clearing_price_epoch=_read_global_int(global_state, "clearing_price_epoch"),
        clearing_price_e8=_read_global_int(global_state, "clearing_price_e8"),
        mark_price_source_kind=_read_global_int(global_state, "mark_price_source_kind"),
        oracle_seen=_read_global_bool(global_state, "oracle_seen"),
        oracle_last_update_epoch=_read_global_int(global_state, "oracle_last_update_epoch"),
        index_price_e8=_read_global_int(global_state, "index_price_e8"),
        max_oracle_move_bps=_read_global_int(global_state, "max_oracle_move_bps"),
        initial_margin_bps=_read_global_int(global_state, "initial_margin_bps"),
        maintenance_margin_bps=_read_global_int(global_state, "maintenance_margin_bps"),
        depeg_buffer_bps=_read_global_int(global_state, "depeg_buffer_bps"),
        liquidation_penalty_bps=_read_global_int(global_state, "liquidation_penalty_bps"),
        fee_pool_quote=_read_global_int(global_state, "fee_pool_quote"),
        funding_rate_bps=_read_global_int(global_state, "funding_rate_bps"),
        funding_cap_bps=_read_global_int(global_state, "funding_cap_bps"),
        insurance_balance=_read_global_int(global_state, "insurance_balance"),
        initial_insurance=_read_global_int(global_state, "initial_insurance"),
        fee_income=_read_global_int(global_state, "fee_income"),
        claims_paid=_read_global_int(global_state, "claims_paid"),
    )


def _validate_temporal_fields(ctx: _IsolatedValidationContext) -> None:
    if ctx.breaker_last_trigger_epoch > ctx.now_epoch:
        raise ValueError("breaker_last_trigger_epoch must be <= now_epoch")
    if ctx.clearing_price_epoch > ctx.now_epoch:
        raise ValueError("clearing_price_epoch must be <= now_epoch")
    if ctx.oracle_last_update_epoch > ctx.now_epoch:
        raise ValueError("oracle_last_update_epoch must be <= now_epoch")


def _validate_breaker_zeroing(ctx: _IsolatedValidationContext) -> None:
    if ctx.breaker_active:
        return
    if ctx.breaker_last_trigger_epoch != 0:
        raise ValueError("breaker_last_trigger_epoch must be 0 when breaker_active is false")


def _clearing_price_fields_are_zero(ctx: _IsolatedValidationContext) -> bool:
    if ctx.clearing_price_epoch != 0:
        return False
    return ctx.clearing_price_e8 == 0


def _validate_clearing_price_zeroing(ctx: _IsolatedValidationContext) -> None:
    if ctx.clearing_price_seen:
        return
    if not _clearing_price_fields_are_zero(ctx):
        raise ValueError("clearing_price fields must be 0 when clearing_price_seen is false")


def _validate_mark_price_source(ctx: _IsolatedValidationContext) -> None:
    if not ctx.clearing_price_seen:
        return
    if not is_derivatives_safe_mark_price_source(ctx.mark_price_source_kind):
        raise ValueError("mark_price_source_kind must be derivatives-safe when clearing_price_seen is true")


def _oracle_fields_are_zero(ctx: _IsolatedValidationContext) -> bool:
    if ctx.oracle_last_update_epoch != 0:
        return False
    return ctx.index_price_e8 == 0


def _validate_oracle_zeroing(ctx: _IsolatedValidationContext) -> None:
    if ctx.oracle_seen:
        return
    if not _oracle_fields_are_zero(ctx):
        raise ValueError("oracle fields must be 0 when oracle_seen is false")


def _validate_oracle_price_seen(ctx: _IsolatedValidationContext) -> None:
    if not ctx.oracle_seen:
        return
    if ctx.index_price_e8 <= 0:
        raise ValueError("index_price_e8 must be positive when oracle_seen is true")


def _validate_zeroing_fields(ctx: _IsolatedValidationContext) -> None:
    _validate_breaker_zeroing(ctx)
    _validate_clearing_price_zeroing(ctx)
    _validate_mark_price_source(ctx)
    _validate_oracle_zeroing(ctx)
    _validate_oracle_price_seen(ctx)


def _validate_margin_params(ctx: _IsolatedValidationContext) -> None:
    eff_maint = ctx.maintenance_margin_bps + ctx.depeg_buffer_bps
    if not (ctx.max_oracle_move_bps <= eff_maint <= ctx.initial_margin_bps):
        raise ValueError("invalid margin params ordering (max_move <= maint+depeg <= initial)")
    if ctx.liquidation_penalty_bps >= eff_maint:
        raise ValueError("invalid liquidation_penalty_bps (must be < maintenance_margin_bps + depeg_buffer_bps)")
    try:
        require_perp_liquidation_envelope_bps(
            initial_margin_bps=ctx.initial_margin_bps,
            max_oracle_move_bps=ctx.max_oracle_move_bps,
            maintenance_margin_bps=ctx.maintenance_margin_bps,
            depeg_buffer_bps=ctx.depeg_buffer_bps,
            liquidation_penalty_bps=ctx.liquidation_penalty_bps,
        )
    except (TypeError, ValueError) as exc:
        raise ValueError(
            "invalid funded liquidation params "
            "(liquidation_penalty_bps * (10000 + max_oracle_move_bps) <= "
            "10000 * (maintenance_margin_bps + depeg_buffer_bps - max_oracle_move_bps))"
        ) from exc


def _validate_funding_bounds(ctx: _IsolatedValidationContext) -> None:
    if abs(ctx.funding_rate_bps) > ctx.funding_cap_bps:
        raise ValueError("funding_rate_bps must be within [-funding_cap_bps, funding_cap_bps]")


def _validate_insurance_accounting(ctx: _IsolatedValidationContext) -> None:
    if ctx.insurance_balance < 0:
        raise ValueError("insurance_balance must be non-negative")
    if ctx.insurance_balance != ctx.initial_insurance + ctx.fee_income - ctx.claims_paid:
        raise ValueError("insurance_balance must equal initial_insurance + fee_income - claims_paid")


def _validate_fee_pool_accounting(ctx: _IsolatedValidationContext) -> None:
    if ctx.fee_pool_quote != ctx.fee_income:
        raise ValueError("fee_pool_quote must equal fee_income")


def _has_current_clearing_price(ctx: _IsolatedValidationContext) -> bool:
    if not ctx.clearing_price_seen:
        return False
    return ctx.clearing_price_epoch == ctx.now_epoch


def _has_current_oracle(ctx: _IsolatedValidationContext) -> bool:
    if not ctx.oracle_seen:
        return False
    return ctx.oracle_last_update_epoch == ctx.now_epoch


def _validate_epoch_open(ctx: _IsolatedValidationContext) -> None:
    if _has_current_clearing_price(ctx):
        raise ValueError("epoch_phase Open inconsistent with clearing_price for current epoch")
    if ctx.now_epoch <= 0:
        return
    if _has_current_oracle(ctx):
        raise ValueError("epoch_phase Open inconsistent with oracle_last_update_epoch == now_epoch")


def _validate_epoch_price_published(ctx: _IsolatedValidationContext) -> None:
    if not _has_current_clearing_price(ctx):
        raise ValueError("epoch_phase PricePublished requires clearing_price for current epoch")
    if _has_current_oracle(ctx):
        raise ValueError("epoch_phase PricePublished requires oracle_last_update_epoch < now_epoch")


def _validate_epoch_settled(ctx: _IsolatedValidationContext) -> None:
    if not _has_current_clearing_price(ctx):
        raise ValueError("epoch_phase Settled requires clearing_price for current epoch")
    if not _has_current_oracle(ctx):
        raise ValueError("epoch_phase Settled requires oracle_last_update_epoch == now_epoch")


def _validate_epoch_phase(ctx: _IsolatedValidationContext) -> None:
    if ctx.epoch_phase == 0:
        _validate_epoch_open(ctx)
        return
    if ctx.epoch_phase == 1:
        _validate_epoch_price_published(ctx)
        return
    if ctx.epoch_phase == 2:
        _validate_epoch_settled(ctx)
        return
    raise ValueError(f"invalid epoch_phase: {ctx.epoch_phase_str!r}")


def _validate_account_key(pk: Any) -> None:
    if not isinstance(pk, str):
        raise TypeError("accounts keys must be non-empty strings")
    if not pk:
        raise TypeError("accounts keys must be non-empty strings")


def _validate_account(ctx: _IsolatedValidationContext, pk: Any, acct: Any) -> None:
    _validate_account_key(pk)
    pos = _read_account_int(acct, "position_base")
    entry = _read_account_int(acct, "entry_price_e8")
    funding_last_applied_epoch = _read_account_int(acct, "funding_last_applied_epoch")
    if funding_last_applied_epoch > ctx.now_epoch:
        raise ValueError("account funding_last_applied_epoch must be <= now_epoch")
    if pos == 0:
        if entry != 0:
            raise ValueError("entry_price_e8 must be 0 when position_base is 0")
        return
    if entry != ctx.index_price_e8:
        raise ValueError("entry_price_e8 must equal index_price_e8 when position_base is non-zero")


def _validate_accounts(ctx: _IsolatedValidationContext) -> None:
    for pk, acct in ctx.accounts.items():
        _validate_account(ctx, pk, acct)


def validate_isolated_state_consistency(
    *,
    global_state: Mapping[str, Value],
    accounts: Mapping[str, Any],
    epoch_phase_int_to_str: Mapping[int, str],
) -> None:
    """Validate consensus-critical invariants on a persistent isolated market."""
    context = _read_context(
        global_state=global_state,
        accounts=accounts,
        epoch_phase_int_to_str=epoch_phase_int_to_str,
    )
    _validate_temporal_fields(context)
    _validate_zeroing_fields(context)
    _validate_margin_params(context)
    _validate_funding_bounds(context)
    _validate_insurance_accounting(context)
    _validate_fee_pool_accounting(context)
    _validate_epoch_phase(context)
    _validate_accounts(context)

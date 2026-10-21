"""Exact isolated-market parameter candidates below the authority boundary.

The operator check belongs to the typed command/authorization pipeline.  This
module consumes only an already-selected immutable market and exact parameter
data, then returns a new immutable market candidate or one typed rejection.
The result carries no receipt or commit authority and cannot publish itself.
"""

from __future__ import annotations

from bisect import bisect_left
from dataclasses import dataclass
from typing import TypeAlias, cast, final

from ..core.perp_v2.math import MAX_COLLATERAL, maint_margin_req
from .perps_state_transitions import (
    CanonicalIsolatedGlobalPatchV1,
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
    _build_optional_global_patch_from_entries,
    _global_entry_value,
    _validated_prestate,
)
from .state_snapshot_values import CommittedPerpMarketStateV1, PerpsValueV1
from .state_transitions import _committed_isolated_market_from_transition_v1

FCIS_MUTABLE_LOCAL_BUFFERS_FORBIDDEN = True

_BPS_SCALE = 10_000
_GlobalEntriesV1: TypeAlias = tuple[tuple[str, PerpsValueV1], ...]
_PARAM_BOUNDS: tuple[tuple[str, int, int], ...] = (
    ("depeg_buffer_bps", 0, 5_000),
    ("funding_cap_bps", 1, 10_000),
    ("initial_margin_bps", 0, 10_000),
    ("liquidation_penalty_bps", 0, 10_000),
    ("maintenance_margin_bps", 0, 10_000),
    ("max_oracle_move_bps", 0, 10_000),
    ("max_oracle_staleness_epochs", 1, 1_000_000),
    ("max_position_abs", 1, 1_000_000),
    ("min_notional_for_bounty", 0, 1_000_000_000_000),
)


def _bound_for(field: str) -> tuple[int, int] | None:
    for declared, lower, upper in _PARAM_BOUNDS:
        if field == declared:
            return lower, upper
    return None


@final
@dataclass(frozen=True, slots=True)
class IsolatedMarketParamsUpdateV1:
    """Canonical, duplicate-free parameter data without operator authority."""

    entries: tuple[tuple[str, int], ...]

    def __post_init__(self) -> None:
        if type(self.entries) is not tuple:
            raise TypeError("market parameter entries must be an exact tuple")
        if len(self.entries) > len(_PARAM_BOUNDS):
            raise ValueError("market parameter update exceeds its field limit")
        previous: str | None = None
        for entry in self.entries:
            if type(entry) is not tuple or len(entry) != 2:
                raise TypeError("market parameter entries must be exact pairs")
            field, value = entry
            if type(field) is not str or type(value) is not int:
                raise TypeError("market parameter fields and values must be exact")
            if previous is not None and previous >= field:
                raise ValueError("market parameter entries must be sorted and duplicate-free")
            bounds = _bound_for(field)
            if bounds is None:
                raise ValueError("market parameter field is not declared")
            if value < bounds[0] or value > bounds[1]:
                raise ValueError("market parameter value is outside its declared domain")
            previous = field


@final
@dataclass(frozen=True, slots=True)
class IsolatedMarketParamsTransitionOkV1:
    """One exact market-parameter candidate and its optional semantic patch."""

    market: CommittedPerpMarketStateV1
    global_patch: CanonicalIsolatedGlobalPatchV1 | None

    def __post_init__(self) -> None:
        if type(self.market) is not CommittedPerpMarketStateV1:
            raise TypeError("market parameter candidate must be exact")
        if (
            self.global_patch is not None
            and type(self.global_patch) is not CanonicalIsolatedGlobalPatchV1
        ):
            raise TypeError("market parameter patch must be exact or None")


IsolatedMarketParamsTransitionResultV1: TypeAlias = (
    IsolatedMarketParamsTransitionOkV1 | IsolatedPerpTransitionRejectV1
)


def _reject(
    code: IsolatedPerpTransitionCodeV1,
    path: tuple[str | int, ...],
    reason: str | None = None,
) -> IsolatedPerpTransitionRejectV1:
    return IsolatedPerpTransitionRejectV1(code, path, reason)


def _funded_liquidation_params_ok(values: _GlobalEntriesV1) -> bool:
    maintenance = cast(int, _global_entry_value(values, "maintenance_margin_bps"))
    depeg = cast(int, _global_entry_value(values, "depeg_buffer_bps"))
    max_move = cast(int, _global_entry_value(values, "max_oracle_move_bps"))
    penalty = cast(int, _global_entry_value(values, "liquidation_penalty_bps"))
    effective_maintenance = maintenance + depeg
    return penalty * (_BPS_SCALE + max_move) <= _BPS_SCALE * (effective_maintenance - max_move)


def _cross_parameter_error(
    values: _GlobalEntriesV1,
    *,
    min_collectible_penalty_quote: int,
) -> str | None:
    max_move = cast(int, _global_entry_value(values, "max_oracle_move_bps"))
    initial = cast(int, _global_entry_value(values, "initial_margin_bps"))
    maintenance = cast(int, _global_entry_value(values, "maintenance_margin_bps"))
    depeg = cast(int, _global_entry_value(values, "depeg_buffer_bps"))
    penalty = cast(int, _global_entry_value(values, "liquidation_penalty_bps"))
    effective_maintenance = maintenance + depeg
    if depeg <= 0:
        return "invalid params: require depeg_buffer_bps > 0"
    if max_move > effective_maintenance:
        return "invalid params: require max_oracle_move_bps <= maintenance_margin_bps + depeg_buffer_bps"
    if effective_maintenance > initial:
        return "invalid params: require maintenance_margin_bps + depeg_buffer_bps <= initial_margin_bps"
    if penalty >= effective_maintenance:
        return "invalid params: require liquidation_penalty_bps < maintenance_margin_bps + depeg_buffer_bps"
    if penalty <= 0:
        return "invalid params: require liquidation_penalty_bps > 0"
    if not _funded_liquidation_params_ok(values):
        return "invalid params: require funded liquidation after max_oracle_move_bps"

    minimum_notional = cast(int, _global_entry_value(values, "min_notional_for_bounty"))
    positive_penalty_floor = (_BPS_SCALE + penalty - 1) // penalty
    if minimum_notional < positive_penalty_floor:
        return "invalid params: require min_notional_for_bounty >= ceil(10000 / liquidation_penalty_bps)"
    if min_collectible_penalty_quote > 0:
        policy_floor = (min_collectible_penalty_quote * _BPS_SCALE + penalty - 1) // penalty
        if minimum_notional < policy_floor:
            return (
                "invalid params: require min_notional_for_bounty >= "
                f"ceil({min_collectible_penalty_quote} * 10000 / liquidation_penalty_bps)"
            )
    return None


def _open_position_update_error(
    pre: CommittedPerpMarketStateV1,
    after: _GlobalEntriesV1,
) -> str | None:
    has_open_positions = any(account.position_base != 0 for _, account in pre.account_entries)
    if not has_open_positions:
        return None
    old_penalty = cast(int, pre.global_value("liquidation_penalty_bps"))
    new_penalty = cast(int, _global_entry_value(after, "liquidation_penalty_bps"))
    if new_penalty > old_penalty:
        return "invalid params: cannot increase liquidation_penalty_bps while positions are open"
    old_minimum = cast(int, pre.global_value("min_notional_for_bounty"))
    new_minimum = cast(int, _global_entry_value(after, "min_notional_for_bounty"))
    if new_minimum < old_minimum:
        return "invalid params: cannot decrease min_notional_for_bounty while positions are open"
    return None


def _account_risk_error(
    pre: CommittedPerpMarketStateV1,
    values: _GlobalEntriesV1,
) -> str | None:
    max_position = cast(int, _global_entry_value(values, "max_position_abs"))
    index_price = cast(int, _global_entry_value(values, "index_price_e8"))
    maintenance = cast(int, _global_entry_value(values, "maintenance_margin_bps"))
    depeg = cast(int, _global_entry_value(values, "depeg_buffer_bps"))
    for account_pubkey, account in pre.account_entries:
        if abs(account.position_base) > max_position:
            return f"invalid params: account {account_pubkey} position exceeds new max_position_abs"
        if account.position_base == 0:
            continue
        requirement = maint_margin_req(
            account.position_base,
            index_price,
            maintenance,
            depeg,
        )
        if account.collateral_quote < requirement:
            return f"invalid params: account {account_pubkey} would be under maintenance margin"
    return None


def _updated_parameter_value(
    update: IsolatedMarketParamsUpdateV1,
    field: str,
    expected: PerpsValueV1,
) -> PerpsValueV1:
    index = bisect_left(update.entries, field, key=lambda entry: entry[0])
    if index < len(update.entries) and update.entries[index][0] == field:
        return update.entries[index][1]
    return expected


def _entries_with_parameter_update(
    before: _GlobalEntriesV1,
    update: IsolatedMarketParamsUpdateV1,
) -> _GlobalEntriesV1:
    return tuple(
        (field, _updated_parameter_value(update, field, expected)) for field, expected in before
    )


def _entries_with_one_value(
    before: _GlobalEntriesV1,
    *,
    field: str,
    replacement: PerpsValueV1,
) -> _GlobalEntriesV1:
    return tuple(
        (entry_field, replacement if entry_field == field else expected)
        for entry_field, expected in before
    )


def _evaluate_update(
    pre: CommittedPerpMarketStateV1,
    update: IsolatedMarketParamsUpdateV1,
    *,
    min_collectible_penalty_quote: int,
) -> _GlobalEntriesV1 | IsolatedPerpTransitionRejectV1:
    values = _entries_with_parameter_update(pre.global_entries, update)
    open_position_error = _open_position_update_error(pre, values)
    if open_position_error is not None:
        return _reject(
            IsolatedPerpTransitionCodeV1.MARKET_PARAMS,
            ("params",),
            open_position_error,
        )

    funding_cap = cast(int, _global_entry_value(values, "funding_cap_bps"))
    funding_rate = cast(int, _global_entry_value(values, "funding_rate_bps"))
    if abs(funding_rate) > funding_cap:
        values = _entries_with_one_value(
            values,
            field="funding_rate_bps",
            replacement=funding_cap if funding_rate >= 0 else -funding_cap,
        )
    error = _cross_parameter_error(
        values,
        min_collectible_penalty_quote=min_collectible_penalty_quote,
    ) or _account_risk_error(pre, values)
    if error is not None:
        return _reject(
            IsolatedPerpTransitionCodeV1.MARKET_PARAMS,
            ("params",),
            error,
        )
    return values


def evaluate_isolated_market_params_v1(
    pre: CommittedPerpMarketStateV1,
    update: object,
    *,
    min_collectible_penalty_quote: int,
) -> IsolatedMarketParamsTransitionResultV1:
    """Evaluate exact parameter data after the shell authorizes its operator."""

    validated = _validated_prestate(pre)
    if type(validated) is IsolatedPerpTransitionRejectV1:
        return validated
    if validated.global_value("oracle_last_update_epoch") != validated.global_value("now_epoch"):
        return _reject(
            IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
            ("gate",),
            "MarketParamsMidEpoch",
        )
    if type(update) is not IsolatedMarketParamsUpdateV1:
        return _reject(IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE, ("params",))
    if (
        type(min_collectible_penalty_quote) is not int
        or min_collectible_penalty_quote < 0
        or min_collectible_penalty_quote > MAX_COLLATERAL
    ):
        return _reject(
            IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
            ("context", "min_collectible_penalty_quote"),
        )
    if not update.entries:
        return IsolatedMarketParamsTransitionOkV1(validated, None)
    after = _evaluate_update(
        validated,
        update,
        min_collectible_penalty_quote=min_collectible_penalty_quote,
    )
    if type(after) is IsolatedPerpTransitionRejectV1:
        return after
    patch = _build_optional_global_patch_from_entries(
        validated.global_entries,
        after,
    )
    if type(patch) is IsolatedPerpTransitionRejectV1:
        return patch
    if patch is None:
        return IsolatedMarketParamsTransitionOkV1(validated, None)
    try:
        candidate = _committed_isolated_market_from_transition_v1(
            validated,
            after,
        )
    except (AttributeError, KeyError, TypeError, ValueError):
        return _reject(IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE, ("state",))
    return IsolatedMarketParamsTransitionOkV1(candidate, patch)

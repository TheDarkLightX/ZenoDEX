"""Pure return-new transitions for exact committed isolated-perps state.

This first slice mounts the three global lifecycle actions that do not change
wallet balances, nonces, or account records. It consumes one exact immutable
market, evaluates the existing frozen scalar risk kernel, and constructs the
successor directly as an exact committed market. It never constructs the
legacy ``PerpMarketState`` aggregate or exposes a mutable projection.

The returned patch is an internal state leaf. It does not issue an aggregate
receipt, authorize shell effects, or replace the expected-pre-root commit
bundle required at the FCIS shell boundary.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, cast, final

from ..core.perp_apply_funding_auto_gate import is_derivatives_safe_mark_price_source
from ..core.perp_runtime_risk_gate import (
    ACTION_ADVANCE_EPOCH,
    ACTION_CLEAR_BREAKER,
    ACTION_PUBLISH_CLEARING_PRICE,
    REJECT_OK,
    evaluate_perp_runtime_risk_gate,
)
from ..core.perp_v2 import step as kernel_step
from ..core.perp_v2.types import Action, ActionParams, EpochPhase, PerpState
from ..core.perps import PERP_ISOLATED_GLOBAL_KEYS
from .state_snapshot_values import (
    CommittedPerpMarketStateV1,
    PerpsValueV1,
)
from .state_transitions import _committed_isolated_market_from_transition_v1

PerpsTransitionPathPartV1: TypeAlias = str | int
PerpsTransitionPathV1: TypeAlias = tuple[PerpsTransitionPathPartV1, ...]


class IsolatedPerpTransitionCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    NONCANONICAL_ACCOUNT = "noncanonical_account"
    INVALID_PRESTATE = "invalid_prestate"
    RUNTIME_GUARD = "runtime_guard"
    MARK_PRICE_SOURCE = "mark_price_source"
    KERNEL_REJECT = "kernel_reject"
    INTERNAL_ACCOUNT_MUTATION = "internal_account_mutation"
    INTERNAL_GLOBAL_MUTATION = "internal_global_mutation"
    INSUFFICIENT_BALANCE = "insufficient_balance"
    BALANCE_PATCH = "balance_patch"
    INVALID_CANDIDATE = "invalid_candidate"
    EMPTY_PATCH = "empty_patch"
    AMOUNT_NOT_POSITIVE = "amount_not_positive"
    MARKET_PARAMS = "market_params"


@final
@dataclass(frozen=True, slots=True)
class IsolatedPerpTransitionRejectV1:
    """Stable no-output rejection for an exact isolated-market leaf."""

    code: IsolatedPerpTransitionCodeV1
    path: PerpsTransitionPathV1
    reason: str | None = None

    def __post_init__(self) -> None:
        if type(self.code) is not IsolatedPerpTransitionCodeV1:
            raise TypeError("isolated perps rejection code must be exact")
        if type(self.path) is not tuple or any(type(part) not in {str, int} for part in self.path):
            raise TypeError("isolated perps rejection path must be exact")
        if self.reason is not None and type(self.reason) is not str:
            raise TypeError("isolated perps rejection reason must be an exact string")


def _reject(
    code: IsolatedPerpTransitionCodeV1,
    path: PerpsTransitionPathV1,
    reason: str | None = None,
) -> IsolatedPerpTransitionRejectV1:
    return IsolatedPerpTransitionRejectV1(code, path, reason)


def _is_exact_perps_value(value: object) -> bool:
    return type(value) in {int, bool}


@final
@dataclass(frozen=True, slots=True)
class IsolatedGlobalWriteV1:
    """One exact compare-and-replace write to the isolated global registry."""

    field: str
    expected: PerpsValueV1
    replacement: PerpsValueV1

    def __post_init__(self) -> None:
        if type(self.field) is not str or self.field not in PERP_ISOLATED_GLOBAL_KEYS:
            raise ValueError("isolated global write field is not declared")
        if not _is_exact_perps_value(self.expected) or not _is_exact_perps_value(self.replacement):
            raise TypeError("isolated global writes require exact scalar values")
        if type(self.expected) is type(self.replacement) and self.expected == self.replacement:
            raise ValueError("isolated global write must change its field")


@final
@dataclass(frozen=True, slots=True)
class CanonicalIsolatedGlobalPatchV1:
    """Nonempty field-sorted patch over one isolated market's global state."""

    writes: tuple[IsolatedGlobalWriteV1, ...]

    def __post_init__(self) -> None:
        if type(self.writes) is not tuple or not self.writes:
            raise ValueError("isolated global patch must be a nonempty exact tuple")
        previous: str | None = None
        for write in self.writes:
            if type(write) is not IsolatedGlobalWriteV1:
                raise TypeError("isolated global patch writes must be exact")
            write.__post_init__()
            if previous is not None and previous >= write.field:
                raise ValueError("isolated global patch must be sorted and duplicate-free")
            previous = write.field


@final
@dataclass(frozen=True, slots=True)
class IsolatedPerpTransitionOkV1:
    """One exact market candidate and the patch that produced it."""

    market: CommittedPerpMarketStateV1
    patch: CanonicalIsolatedGlobalPatchV1

    def __post_init__(self) -> None:
        if type(self.market) is not CommittedPerpMarketStateV1:
            raise TypeError("isolated perps candidate market must be exact")
        if type(self.patch) is not CanonicalIsolatedGlobalPatchV1:
            raise TypeError("isolated perps candidate patch must be exact")


IsolatedPerpTransitionResultV1: TypeAlias = (
    IsolatedPerpTransitionOkV1 | IsolatedPerpTransitionRejectV1
)

_PHASE_BY_ORDINAL = (
    EpochPhase.OPEN,
    EpochPhase.PRICE_PUBLISHED,
    EpochPhase.SETTLED,
)
_PHASE_ORDINAL = {
    EpochPhase.OPEN: 0,
    EpochPhase.PRICE_PUBLISHED: 1,
    EpochPhase.SETTLED: 2,
}


def _validated_prestate(
    pre: object,
) -> CommittedPerpMarketStateV1 | IsolatedPerpTransitionRejectV1:
    if type(pre) is not CommittedPerpMarketStateV1:
        return _reject(IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE, ("state",))
    exact = cast(CommittedPerpMarketStateV1, pre)
    try:
        exact.__post_init__()
    except (AttributeError, KeyError, TypeError, ValueError):
        return _reject(IsolatedPerpTransitionCodeV1.INVALID_PRESTATE, ("state",))
    return exact


def _kernel_state_from_market(pre: CommittedPerpMarketStateV1) -> PerpState:
    values = dict(pre.global_entries)
    phase = _PHASE_BY_ORDINAL[cast(int, values["epoch_phase"])]
    return PerpState(
        now_epoch=cast(int, values["now_epoch"]),
        epoch_phase=phase,
        breaker_active=cast(bool, values["breaker_active"]),
        breaker_last_trigger_epoch=cast(int, values["breaker_last_trigger_epoch"]),
        clearing_price_seen=cast(bool, values["clearing_price_seen"]),
        clearing_price_epoch=cast(int, values["clearing_price_epoch"]),
        clearing_price_e8=cast(int, values["clearing_price_e8"]),
        oracle_seen=cast(bool, values["oracle_seen"]),
        oracle_last_update_epoch=cast(int, values["oracle_last_update_epoch"]),
        index_price_e8=cast(int, values["index_price_e8"]),
        max_oracle_staleness_epochs=cast(int, values["max_oracle_staleness_epochs"]),
        max_oracle_move_bps=cast(int, values["max_oracle_move_bps"]),
        initial_margin_bps=cast(int, values["initial_margin_bps"]),
        maintenance_margin_bps=cast(int, values["maintenance_margin_bps"]),
        depeg_buffer_bps=cast(int, values["depeg_buffer_bps"]),
        liquidation_penalty_bps=cast(int, values["liquidation_penalty_bps"]),
        max_position_abs=cast(int, values["max_position_abs"]),
        fee_pool_quote=cast(int, values["fee_pool_quote"]),
        funding_rate_bps=cast(int, values["funding_rate_bps"]),
        funding_cap_bps=cast(int, values["funding_cap_bps"]),
        insurance_balance=cast(int, values["insurance_balance"]),
        initial_insurance=cast(int, values["initial_insurance"]),
        fee_income=cast(int, values["fee_income"]),
        claims_paid=cast(int, values["claims_paid"]),
        min_notional_for_bounty=cast(int, values["min_notional_for_bounty"]),
    )


def _global_values_from_kernel(
    state: PerpState,
    *,
    mark_price_source_kind: int,
) -> dict[str, PerpsValueV1]:
    return {
        "now_epoch": state.now_epoch,
        "epoch_phase": _PHASE_ORDINAL[state.epoch_phase],
        "breaker_active": state.breaker_active,
        "breaker_last_trigger_epoch": state.breaker_last_trigger_epoch,
        "clearing_price_seen": state.clearing_price_seen,
        "clearing_price_epoch": state.clearing_price_epoch,
        "clearing_price_e8": state.clearing_price_e8,
        "mark_price_source_kind": mark_price_source_kind,
        "oracle_seen": state.oracle_seen,
        "oracle_last_update_epoch": state.oracle_last_update_epoch,
        "index_price_e8": state.index_price_e8,
        "max_oracle_staleness_epochs": state.max_oracle_staleness_epochs,
        "max_oracle_move_bps": state.max_oracle_move_bps,
        "initial_margin_bps": state.initial_margin_bps,
        "maintenance_margin_bps": state.maintenance_margin_bps,
        "depeg_buffer_bps": state.depeg_buffer_bps,
        "liquidation_penalty_bps": state.liquidation_penalty_bps,
        "max_position_abs": state.max_position_abs,
        "fee_pool_quote": state.fee_pool_quote,
        "funding_rate_bps": state.funding_rate_bps,
        "funding_cap_bps": state.funding_cap_bps,
        "insurance_balance": state.insurance_balance,
        "initial_insurance": state.initial_insurance,
        "fee_income": state.fee_income,
        "claims_paid": state.claims_paid,
        "min_notional_for_bounty": state.min_notional_for_bounty,
    }


def _global_entries_from_kernel(
    state: PerpState,
    *,
    mark_price_source_kind: int,
) -> tuple[tuple[str, PerpsValueV1], ...]:
    """Return the kernel globals as one immutable canonical module boundary."""

    values = _global_values_from_kernel(
        state,
        mark_price_source_kind=mark_price_source_kind,
    )
    return tuple(sorted(values.items(), key=lambda item: item[0]))


def _kernel_account_is_unchanged(state: PerpState) -> bool:
    return (
        state.position_base == 0
        and state.entry_price_e8 == 0
        and state.collateral_quote == 0
        and state.funding_paid_cumulative == 0
        and state.funding_last_applied_epoch == 0
        and state.liquidated_this_step is False
    )


def _build_patch(
    before: dict[str, PerpsValueV1],
    after: dict[str, PerpsValueV1],
) -> CanonicalIsolatedGlobalPatchV1 | IsolatedPerpTransitionRejectV1:
    patch = _build_optional_patch(before, after)
    if patch is None:
        return _reject(IsolatedPerpTransitionCodeV1.EMPTY_PATCH, ("patch",))
    return patch


def _build_optional_patch(
    before: dict[str, PerpsValueV1],
    after: dict[str, PerpsValueV1],
) -> CanonicalIsolatedGlobalPatchV1 | IsolatedPerpTransitionRejectV1 | None:
    """Build a canonical global patch when the transition changed globals."""

    writes = tuple(
        IsolatedGlobalWriteV1(field, before[field], after[field])
        for field in sorted(PERP_ISOLATED_GLOBAL_KEYS)
        if type(before[field]) is not type(after[field]) or before[field] != after[field]
    )
    if not writes:
        return None
    try:
        return CanonicalIsolatedGlobalPatchV1(writes)
    except (TypeError, ValueError):
        return _reject(IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE, ("patch",))


def _runtime_gate_reject(
    *,
    action_kind: int,
    operator_authorized: object,
    pre: CommittedPerpMarketStateV1,
    positive_price_ok: bool = True,
) -> IsolatedPerpTransitionRejectV1 | None:
    if type(operator_authorized) is not bool:
        return _reject(
            IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
            ("operator_authorized",),
        )
    values = dict(pre.global_entries)
    positions_flat = all(account.position_base == 0 for _key, account in pre.account_entries)
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=action_kind,
        operator_ok=operator_authorized,
        unknown_fields_ok=True,
        sender_binding_ok=True,
        epoch_settled_ok=(values["oracle_last_update_epoch"] == values["now_epoch"]),
        positive_price_ok=positive_price_ok,
        positions_flat_ok=positions_flat,
        params_object_ok=True,
    )
    if outcome.reject_code != REJECT_OK:
        return _reject(
            IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
            ("gate",),
            outcome.reject_code,
        )
    return None


def _apply_global_kernel_action(
    pre: CommittedPerpMarketStateV1,
    params: ActionParams,
    *,
    mark_price_source_kind: int,
) -> IsolatedPerpTransitionResultV1:
    before = dict(pre.global_entries)
    result = kernel_step(_kernel_state_from_market(pre), params)
    if not result.accepted or result.state is None:
        return _reject(
            IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
            ("kernel",),
            result.rejection or "kernel_rejected",
        )
    if not _kernel_account_is_unchanged(result.state):
        return _reject(
            IsolatedPerpTransitionCodeV1.INTERNAL_ACCOUNT_MUTATION,
            ("kernel", "account"),
        )
    after = _global_values_from_kernel(
        result.state,
        mark_price_source_kind=mark_price_source_kind,
    )
    patch = _build_patch(before, after)
    if type(patch) is IsolatedPerpTransitionRejectV1:
        return patch
    try:
        candidate = _committed_isolated_market_from_transition_v1(
            pre,
            tuple(sorted(after.items(), key=lambda item: item[0])),
        )
    except (AttributeError, KeyError, TypeError, ValueError):
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("state",),
        )
    return IsolatedPerpTransitionOkV1(candidate, patch)


def apply_isolated_advance_epoch_v1(
    pre: CommittedPerpMarketStateV1,
    *,
    delta: int,
    operator_authorized: bool,
) -> IsolatedPerpTransitionResultV1:
    """Advance one fully settled isolated market by the exact kernel delta."""

    validated = _validated_prestate(pre)
    if type(validated) is IsolatedPerpTransitionRejectV1:
        return validated
    gate_reject = _runtime_gate_reject(
        action_kind=ACTION_ADVANCE_EPOCH,
        operator_authorized=operator_authorized,
        pre=validated,
    )
    if gate_reject is not None:
        return gate_reject
    if type(delta) is not int:
        return _reject(IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE, ("delta",))
    mark_source = cast(int, validated.global_value("mark_price_source_kind"))
    return _apply_global_kernel_action(
        validated,
        ActionParams(action=Action.ADVANCE_EPOCH, delta=delta),
        mark_price_source_kind=mark_source,
    )


def apply_isolated_publish_clearing_price_v1(
    pre: CommittedPerpMarketStateV1,
    *,
    price_e8: int,
    mark_price_source_kind: int,
    operator_authorized: bool,
) -> IsolatedPerpTransitionResultV1:
    """Publish one derivatives-safe clearing price into an exact market."""

    validated = _validated_prestate(pre)
    if type(validated) is IsolatedPerpTransitionRejectV1:
        return validated
    initial_gate_reject = _runtime_gate_reject(
        action_kind=ACTION_PUBLISH_CLEARING_PRICE,
        operator_authorized=operator_authorized,
        pre=validated,
    )
    if initial_gate_reject is not None:
        return initial_gate_reject
    if type(price_e8) is not int:
        return _reject(IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE, ("price_e8",))
    if type(mark_price_source_kind) is not int:
        return _reject(
            IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
            ("mark_price_source_kind",),
        )
    if not is_derivatives_safe_mark_price_source(mark_price_source_kind):
        return _reject(
            IsolatedPerpTransitionCodeV1.MARK_PRICE_SOURCE,
            ("mark_price_source_kind",),
        )
    positive_price_gate_reject = _runtime_gate_reject(
        action_kind=ACTION_PUBLISH_CLEARING_PRICE,
        operator_authorized=operator_authorized,
        pre=validated,
        positive_price_ok=price_e8 > 0,
    )
    if positive_price_gate_reject is not None:
        return positive_price_gate_reject
    return _apply_global_kernel_action(
        validated,
        ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=price_e8),
        mark_price_source_kind=mark_price_source_kind,
    )


def apply_isolated_clear_breaker_v1(
    pre: CommittedPerpMarketStateV1,
    *,
    operator_authorized: bool,
) -> IsolatedPerpTransitionResultV1:
    """Clear an active breaker only when every committed account is flat."""

    validated = _validated_prestate(pre)
    if type(validated) is IsolatedPerpTransitionRejectV1:
        return validated
    gate_reject = _runtime_gate_reject(
        action_kind=ACTION_CLEAR_BREAKER,
        operator_authorized=operator_authorized,
        pre=validated,
    )
    if gate_reject is not None:
        return gate_reject
    mark_source = cast(int, validated.global_value("mark_price_source_kind"))
    return _apply_global_kernel_action(
        validated,
        ActionParams(action=Action.CLEAR_BREAKER, auth_ok=operator_authorized),
        mark_price_source_kind=mark_source,
    )

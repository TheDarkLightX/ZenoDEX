"""Exact immutable settlement candidates for isolated perps.

Settlement is an aggregate transition: every account evaluates against the
same committed pre-market, while liquidation penalties accumulate into one
global fee/insurance successor.  This module computes those values in
canonical account-key order and freezes the global and account changes at one
candidate boundary.  No partial account result, receipt, outbox record, or
commit authority can escape on rejection.

Optional external Oracle-adapter verification remains a shell admission
contract.  This leaf consumes the already selected committed Oracle facts and
does not accept a caller-constructible object as proof of external authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias, cast, final

from ..core.perp_runtime_risk_gate import ACTION_SETTLE_EPOCH
from ..core.perp_v2 import step as kernel_step
from ..core.perp_v2.math import MAX_COLLATERAL
from ..core.perp_v2.types import Action, ActionParams, PerpState
from .perps_account_transitions import (
    CanonicalIsolatedAccountPatchV1,
    _account_from_kernel,
    _kernel_state_with_account,
)
from .perps_state_transitions import (
    CanonicalIsolatedGlobalPatchV1,
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
    _build_optional_global_patch_from_entries,
    _global_entries_from_kernel,
    _kernel_account_is_unchanged,
    _kernel_state_from_market,
    _runtime_gate_reject,
    _validated_prestate,
)
from .perps_transition_combinators import (
    _existing_account_patch_and_entries,
    _first_isolated_reject,
)
from .state_snapshot_values import (
    CommittedPerpAccountStateV1,
    CommittedPerpMarketStateV1,
    PerpsValueV1,
)
from .state_transitions import (
    _committed_isolated_market_from_transition_v1,
    _committed_isolated_market_with_globals_and_accounts_from_transition_v1,
)

FCIS_MUTABLE_LOCAL_BUFFERS_FORBIDDEN = True


@final
@dataclass(frozen=True, slots=True)
class IsolatedSettlementTransitionOkV1:
    """One complete exact settlement candidate and its semantic patches."""

    market: CommittedPerpMarketStateV1
    account_patch: CanonicalIsolatedAccountPatchV1 | None
    global_patch: CanonicalIsolatedGlobalPatchV1
    fee_pool_delta_quote: int

    def __post_init__(self) -> None:
        if type(self.market) is not CommittedPerpMarketStateV1:
            raise TypeError("settlement candidate market must be exact")
        if (
            self.account_patch is not None
            and type(self.account_patch) is not CanonicalIsolatedAccountPatchV1
        ):
            raise TypeError("settlement account patch must be exact or None")
        if type(self.global_patch) is not CanonicalIsolatedGlobalPatchV1:
            raise TypeError("settlement global patch must be exact")
        if (
            type(self.fee_pool_delta_quote) is not int
            or self.fee_pool_delta_quote < 0
            or self.fee_pool_delta_quote > MAX_COLLATERAL
        ):
            raise ValueError("settlement fee-pool delta is outside its exact domain")


IsolatedSettlementTransitionResultV1: TypeAlias = (
    IsolatedSettlementTransitionOkV1 | IsolatedPerpTransitionRejectV1
)
_GlobalEntriesV1: TypeAlias = tuple[tuple[str, PerpsValueV1], ...]
_SettledAccountEvaluationV1: TypeAlias = tuple[
    str,
    CommittedPerpAccountStateV1,
    int,
]


def _reject(
    code: IsolatedPerpTransitionCodeV1,
    path: tuple[str | int, ...],
    reason: str | None = None,
) -> IsolatedPerpTransitionRejectV1:
    return IsolatedPerpTransitionRejectV1(code, path, reason)


def _global_settlement_base(
    pre: CommittedPerpMarketStateV1,
) -> tuple[_GlobalEntriesV1, _GlobalEntriesV1] | IsolatedPerpTransitionRejectV1:
    result = kernel_step(
        _kernel_state_from_market(pre),
        ActionParams(action=Action.SETTLE_EPOCH),
    )
    if not result.accepted or result.state is None:
        return _reject(
            IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
            ("kernel", "global"),
            result.rejection or "kernel_rejected",
        )
    if not _kernel_account_is_unchanged(result.state):
        return _reject(
            IsolatedPerpTransitionCodeV1.INTERNAL_ACCOUNT_MUTATION,
            ("kernel", "global", "account"),
        )
    mark_source = cast(int, pre.global_value("mark_price_source_kind"))
    base = _global_entries_from_kernel(
        result.state,
        mark_price_source_kind=mark_source,
    )
    expected_without_accumulators = tuple(
        (
            field,
            pre.global_value(field)
            if field in ("fee_pool_quote", "fee_income", "insurance_balance")
            else value,
        )
        for field, value in base
    )
    return base, expected_without_accumulators


def _flat_account_needs_no_settlement(account: CommittedPerpAccountStateV1) -> bool:
    return (
        account.position_base == 0
        and account.entry_price_e8 == 0
        and account.liquidated_this_step is False
    )


def _normalized_settlement_global_entries(
    pre: CommittedPerpMarketStateV1,
    state: PerpState,
) -> _GlobalEntriesV1:
    mark_source = cast(int, pre.global_value("mark_price_source_kind"))
    entries = _global_entries_from_kernel(
        state,
        mark_price_source_kind=mark_source,
    )
    return tuple(
        (
            field,
            pre.global_value(field)
            if field in ("fee_pool_quote", "fee_income", "insurance_balance")
            else value,
        )
        for field, value in entries
    )


def _settled_account_evaluation(
    pre: CommittedPerpMarketStateV1,
    expected_without_accumulators: _GlobalEntriesV1,
    account_entry: tuple[str, CommittedPerpAccountStateV1],
) -> _SettledAccountEvaluationV1 | IsolatedPerpTransitionRejectV1:
    account_pubkey, account = account_entry
    if _flat_account_needs_no_settlement(account):
        return account_pubkey, account, 0

    pre_fee_pool = cast(int, pre.global_value("fee_pool_quote"))
    pre_fee_income = cast(int, pre.global_value("fee_income"))
    pre_insurance = cast(int, pre.global_value("insurance_balance"))
    result = kernel_step(
        _kernel_state_with_account(pre, account),
        ActionParams(action=Action.SETTLE_EPOCH),
    )
    if not result.accepted or result.state is None:
        return _reject(
            IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
            ("kernel", "accounts", account_pubkey),
            result.rejection or "kernel_rejected",
        )
    if _normalized_settlement_global_entries(pre, result.state) != expected_without_accumulators:
        return _reject(
            IsolatedPerpTransitionCodeV1.INTERNAL_GLOBAL_MUTATION,
            ("kernel", "accounts", account_pubkey, "global"),
        )

    fee_pool_delta = result.state.fee_pool_quote - pre_fee_pool
    fee_income_delta = result.state.fee_income - pre_fee_income
    insurance_delta = result.state.insurance_balance - pre_insurance
    if (
        fee_pool_delta < 0
        or fee_pool_delta != fee_income_delta
        or fee_pool_delta != insurance_delta
    ):
        return _reject(
            IsolatedPerpTransitionCodeV1.INTERNAL_GLOBAL_MUTATION,
            ("kernel", "accounts", account_pubkey, "accumulators"),
        )
    try:
        replacement = _account_from_kernel(result.state)
    except (TypeError, ValueError):
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("state", "accounts", account_pubkey),
        )
    return account_pubkey, replacement, fee_pool_delta


def _settled_account_replacements(
    pre: CommittedPerpMarketStateV1,
    expected_without_accumulators: _GlobalEntriesV1,
) -> (
    tuple[tuple[tuple[str, CommittedPerpAccountStateV1], ...], int] | IsolatedPerpTransitionRejectV1
):
    evaluated = tuple(
        _settled_account_evaluation(
            pre,
            expected_without_accumulators,
            account_entry,
        )
        for account_entry in pre.account_entries
    )
    first_reject = _first_isolated_reject(cast(tuple[object, ...], evaluated))
    if first_reject is not None:
        return first_reject
    exact_evaluations = cast(tuple[_SettledAccountEvaluationV1, ...], evaluated)
    replacements = tuple(
        (account_pubkey, replacement)
        for account_pubkey, replacement, _fee_pool_delta in exact_evaluations
    )
    total_penalty_delta = sum(
        fee_pool_delta for _account_pubkey, _replacement, fee_pool_delta in exact_evaluations
    )
    return replacements, total_penalty_delta


def _settlement_globals_with_accumulators(
    pre: CommittedPerpMarketStateV1,
    base: _GlobalEntriesV1,
    *,
    total_penalty_delta: int,
) -> _GlobalEntriesV1 | IsolatedPerpTransitionRejectV1:
    next_fee_pool = cast(int, pre.global_value("fee_pool_quote")) + total_penalty_delta
    next_fee_income = cast(int, pre.global_value("fee_income")) + total_penalty_delta
    next_insurance = (
        cast(int, pre.global_value("initial_insurance"))
        + next_fee_income
        - cast(int, pre.global_value("claims_paid"))
    )
    if (
        next_fee_pool > MAX_COLLATERAL
        or next_fee_income > MAX_COLLATERAL
        or next_insurance > MAX_COLLATERAL
        or next_insurance < 0
    ):
        return _reject(
            IsolatedPerpTransitionCodeV1.SETTLEMENT_PATH,
            ("state", "global"),
            "fee_or_insurance_out_of_bounds",
        )
    return tuple(
        (
            field,
            next_fee_pool
            if field == "fee_pool_quote"
            else next_fee_income
            if field == "fee_income"
            else next_insurance
            if field == "insurance_balance"
            else value,
        )
        for field, value in base
    )


def _freeze_settlement_candidate(
    pre: CommittedPerpMarketStateV1,
    *,
    after_global_entries: _GlobalEntriesV1,
    replacements: tuple[tuple[str, CommittedPerpAccountStateV1], ...],
    fee_pool_delta_quote: int,
) -> IsolatedSettlementTransitionResultV1:
    account_result = _existing_account_patch_and_entries(pre, replacements)
    if type(account_result) is IsolatedPerpTransitionRejectV1:
        return account_result
    account_patch, account_entries = account_result
    global_patch = _build_optional_global_patch_from_entries(
        pre.global_entries,
        after_global_entries,
    )
    if type(global_patch) is IsolatedPerpTransitionRejectV1:
        return global_patch
    if global_patch is None:
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("patch", "global"),
        )
    try:
        if account_patch is None:
            candidate = _committed_isolated_market_from_transition_v1(
                pre,
                after_global_entries,
            )
        else:
            candidate = _committed_isolated_market_with_globals_and_accounts_from_transition_v1(
                pre,
                after_global_entries,
                account_entries,
            )
    except (AttributeError, KeyError, TypeError, ValueError):
        return _reject(IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE, ("state",))
    return IsolatedSettlementTransitionOkV1(
        market=candidate,
        account_patch=account_patch,
        global_patch=global_patch,
        fee_pool_delta_quote=fee_pool_delta_quote,
    )


def _plan_isolated_settlement_candidate_v1(
    pre: CommittedPerpMarketStateV1,
) -> IsolatedSettlementTransitionResultV1:
    """Plan settlement after authority admission without publishing outputs."""

    base_result = _global_settlement_base(pre)
    if type(base_result) is IsolatedPerpTransitionRejectV1:
        return base_result
    base, expected_without_accumulators = base_result
    account_result = _settled_account_replacements(
        pre,
        expected_without_accumulators,
    )
    if type(account_result) is IsolatedPerpTransitionRejectV1:
        return account_result
    replacements, total_penalty_delta = account_result
    after_global_entries = _settlement_globals_with_accumulators(
        pre,
        base,
        total_penalty_delta=total_penalty_delta,
    )
    if type(after_global_entries) is IsolatedPerpTransitionRejectV1:
        return after_global_entries
    return _freeze_settlement_candidate(
        pre,
        after_global_entries=after_global_entries,
        replacements=replacements,
        fee_pool_delta_quote=total_penalty_delta,
    )


def apply_isolated_settle_epoch_v1(
    pre: CommittedPerpMarketStateV1,
    *,
    operator_authorized: bool,
) -> IsolatedSettlementTransitionResultV1:
    """Return one exact aggregate settlement candidate or a no-output reject."""

    validated = _validated_prestate(pre)
    if type(validated) is IsolatedPerpTransitionRejectV1:
        return validated
    gate_reject = _runtime_gate_reject(
        action_kind=ACTION_SETTLE_EPOCH,
        operator_authorized=operator_authorized,
        pre=validated,
    )
    if gate_reject is not None:
        return gate_reject
    return _plan_isolated_settlement_candidate_v1(validated)

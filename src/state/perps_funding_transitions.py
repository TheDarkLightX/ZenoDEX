"""Exact immutable automatic-funding candidates for isolated perps.

All open accounts are evaluated against one committed market snapshot.  Their
funding replacements and the linked fee-pool, fee-income, and insurance sink
updates are frozen as one candidate.  When funding occurs after a clearing
price is published, the candidate is admitted only if the exact settlement
planner can still produce a valid successor.

This leaf returns no aggregate effect, receipt, outbox record, or commit
authority.  The operator decision remains an explicit admission input until
the typed authority pipeline mounts this transition.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias, cast, final

from ..core.perp_apply_funding_auto_gate import (
    PerpApplyFundingAutoGateOutcome,
    evaluate_perp_apply_funding_auto_gate,
    perp_apply_funding_auto_gate_error,
)
from ..core.perp_runtime_risk_gate import ACTION_APPLY_FUNDING_AUTO
from ..core.perp_v2 import step as kernel_step
from ..core.perp_v2.math import MAX_COLLATERAL, funding_payment
from ..core.perp_v2.types import Action, ActionParams
from .perps_account_transitions import (
    CanonicalIsolatedAccountPatchV1,
    _account_from_kernel,
    _kernel_state_with_account,
)
from .perps_settlement_transitions import _plan_isolated_settlement_candidate_v1
from .perps_state_transitions import (
    CanonicalIsolatedGlobalPatchV1,
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
    _build_optional_global_patch_from_entries,
    _global_entries_from_kernel,
    _runtime_gate_reject,
    _validated_prestate,
)
from .perps_transition_combinators import (
    _existing_account_patch_and_entries,
    _first_isolated_reject,
)
from .state_snapshot_values import (
    MAX_PERPS_ACCOUNTS_V1,
    CommittedPerpAccountStateV1,
    CommittedPerpMarketStateV1,
    PerpsValueV1,
)
from .state_transitions import (
    _committed_isolated_market_from_transition_v1,
    _committed_isolated_market_with_accounts_from_transition_v1,
    _committed_isolated_market_with_globals_and_accounts_from_transition_v1,
)

FCIS_MUTABLE_LOCAL_BUFFERS_FORBIDDEN = True

_PRICE_PUBLISHED_PHASE = 1


@final
@dataclass(frozen=True, slots=True)
class IsolatedFundingTransitionOkV1:
    """One exact automatic-funding candidate and its semantic patches."""

    market: CommittedPerpMarketStateV1
    account_patch: CanonicalIsolatedAccountPatchV1 | None
    global_patch: CanonicalIsolatedGlobalPatchV1 | None
    funding_rate_bps: int
    mark_price_e8: int
    applied_account_count: int
    projected_net_funding_quote: int

    def __post_init__(self) -> None:
        if type(self.market) is not CommittedPerpMarketStateV1:
            raise TypeError("funding candidate market must be exact")
        if (
            self.account_patch is not None
            and type(self.account_patch) is not CanonicalIsolatedAccountPatchV1
        ):
            raise TypeError("funding account patch must be exact or None")
        if (
            self.global_patch is not None
            and type(self.global_patch) is not CanonicalIsolatedGlobalPatchV1
        ):
            raise TypeError("funding global patch must be exact or None")
        if type(self.funding_rate_bps) is not int:
            raise TypeError("funding rate must be an exact int")
        if type(self.mark_price_e8) is not int or self.mark_price_e8 <= 0:
            raise ValueError("funding mark price must be a positive exact int")
        if (
            type(self.applied_account_count) is not int
            or self.applied_account_count < 0
            or self.applied_account_count > MAX_PERPS_ACCOUNTS_V1
        ):
            raise ValueError("funding account count is outside its exact domain")
        if (
            type(self.projected_net_funding_quote) is not int
            or self.projected_net_funding_quote < -MAX_COLLATERAL
            or self.projected_net_funding_quote > MAX_COLLATERAL
        ):
            raise ValueError("projected net funding is outside its exact domain")


IsolatedFundingTransitionResultV1: TypeAlias = (
    IsolatedFundingTransitionOkV1 | IsolatedPerpTransitionRejectV1
)
_GlobalEntriesV1: TypeAlias = tuple[tuple[str, PerpsValueV1], ...]
_AccountEntriesV1: TypeAlias = tuple[tuple[str, CommittedPerpAccountStateV1], ...]


def _reject(
    code: IsolatedPerpTransitionCodeV1,
    path: tuple[str | int, ...],
    reason: str | None = None,
) -> IsolatedPerpTransitionRejectV1:
    return IsolatedPerpTransitionRejectV1(code, path, reason)


def _funding_gate(
    pre: CommittedPerpMarketStateV1,
    *,
    projected_net_funding_quote: int,
    any_funding_applied_this_epoch: bool,
    net_position_base: int,
) -> PerpApplyFundingAutoGateOutcome:
    return evaluate_perp_apply_funding_auto_gate(
        now_epoch=cast(int, pre.global_value("now_epoch")),
        mark_price_source_kind=cast(int, pre.global_value("mark_price_source_kind")),
        clearing_price_seen=cast(bool, pre.global_value("clearing_price_seen")),
        clearing_price_epoch=cast(int, pre.global_value("clearing_price_epoch")),
        oracle_last_update_epoch=cast(
            int,
            pre.global_value("oracle_last_update_epoch"),
        ),
        oracle_seen=cast(bool, pre.global_value("oracle_seen")),
        index_price_e8=cast(int, pre.global_value("index_price_e8")),
        max_oracle_staleness_epochs=cast(
            int,
            pre.global_value("max_oracle_staleness_epochs"),
        ),
        clearing_price_e8=cast(int, pre.global_value("clearing_price_e8")),
        max_oracle_move_bps=cast(int, pre.global_value("max_oracle_move_bps")),
        funding_cap_bps=cast(int, pre.global_value("funding_cap_bps")),
        projected_net_funding_quote=projected_net_funding_quote,
        any_funding_applied_this_epoch=any_funding_applied_this_epoch,
        net_position_base=net_position_base,
        fee_pool_quote=cast(int, pre.global_value("fee_pool_quote")),
        fee_income=cast(int, pre.global_value("fee_income")),
        insurance_balance=cast(int, pre.global_value("insurance_balance")),
    )


def _funding_plan(
    pre: CommittedPerpMarketStateV1,
) -> tuple[PerpApplyFundingAutoGateOutcome, _AccountEntriesV1] | IsolatedPerpTransitionRejectV1:
    gate_result = _funding_gate_and_open_accounts(pre)
    if type(gate_result) is IsolatedPerpTransitionRejectV1:
        return gate_result
    gate, open_accounts = gate_result
    replacements = _funded_account_replacements(pre, gate, open_accounts)
    if type(replacements) is IsolatedPerpTransitionRejectV1:
        return replacements
    return gate, replacements


def _funding_gate_and_open_accounts(
    pre: CommittedPerpMarketStateV1,
) -> tuple[PerpApplyFundingAutoGateOutcome, _AccountEntriesV1] | IsolatedPerpTransitionRejectV1:
    now_epoch = cast(int, pre.global_value("now_epoch"))
    open_accounts = tuple(
        (account_pubkey, account)
        for account_pubkey, account in pre.account_entries
        if account.position_base != 0
    )
    net_position_base = sum(account.position_base for _key, account in open_accounts)
    already_applied = any(
        account.funding_last_applied_epoch >= now_epoch for _key, account in open_accounts
    )
    provisional = _funding_gate(
        pre,
        projected_net_funding_quote=0,
        any_funding_applied_this_epoch=already_applied,
        net_position_base=net_position_base,
    )
    new_rate_bps = provisional.funding_rate_bps
    index_price_e8 = cast(int, pre.global_value("index_price_e8"))
    projected_net_funding = sum(
        funding_payment(account.position_base, index_price_e8, new_rate_bps)
        for _key, account in open_accounts
    )
    gate = _funding_gate(
        pre,
        projected_net_funding_quote=projected_net_funding,
        any_funding_applied_this_epoch=already_applied,
        net_position_base=net_position_base,
    )
    gate_error = perp_apply_funding_auto_gate_error(gate)
    if gate_error is not None:
        return _reject(
            IsolatedPerpTransitionCodeV1.FUNDING_GATE,
            ("gate", "funding"),
            gate_error,
        )
    return gate, open_accounts


def _funded_account_replacements(
    pre: CommittedPerpMarketStateV1,
    gate: PerpApplyFundingAutoGateOutcome,
    open_accounts: _AccountEntriesV1,
) -> _AccountEntriesV1 | IsolatedPerpTransitionRejectV1:
    expected_global_entries = tuple(
        (
            field,
            gate.funding_rate_bps if field == "funding_rate_bps" else value,
        )
        for field, value in pre.global_entries
    )
    evaluated = tuple(
        _funded_account_replacement(
            pre,
            gate,
            expected_global_entries,
            account_entry,
        )
        for account_entry in open_accounts
    )
    first_reject = _first_isolated_reject(cast(tuple[object, ...], evaluated))
    if first_reject is not None:
        return first_reject
    return cast(_AccountEntriesV1, evaluated)


def _funded_account_replacement(
    pre: CommittedPerpMarketStateV1,
    gate: PerpApplyFundingAutoGateOutcome,
    expected_global_entries: _GlobalEntriesV1,
    account_entry: tuple[str, CommittedPerpAccountStateV1],
) -> tuple[str, CommittedPerpAccountStateV1] | IsolatedPerpTransitionRejectV1:
    account_pubkey, account = account_entry
    mark_source = cast(int, pre.global_value("mark_price_source_kind"))
    result = kernel_step(
        _kernel_state_with_account(pre, account),
        ActionParams(
            action=Action.APPLY_FUNDING,
            new_rate_bps=gate.funding_rate_bps,
            auth_ok=True,
        ),
    )
    if not result.accepted or result.state is None:
        return _reject(
            IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
            ("kernel", "accounts", account_pubkey),
            result.rejection or "kernel_rejected",
        )
    if (
        _global_entries_from_kernel(
            result.state,
            mark_price_source_kind=mark_source,
        )
        != expected_global_entries
    ):
        return _reject(
            IsolatedPerpTransitionCodeV1.INTERNAL_GLOBAL_MUTATION,
            ("kernel", "accounts", account_pubkey, "global"),
        )
    try:
        replacement = _account_from_kernel(result.state)
    except (TypeError, ValueError):
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("state", "accounts", account_pubkey),
        )
    return account_pubkey, replacement


def _funding_global_entries(
    pre: CommittedPerpMarketStateV1,
    gate: PerpApplyFundingAutoGateOutcome,
) -> _GlobalEntriesV1:
    return tuple(
        (
            field,
            gate.funding_rate_bps
            if field == "funding_rate_bps"
            else cast(int, value) + gate.projected_net_funding_quote
            if field in ("fee_pool_quote", "fee_income", "insurance_balance")
            else value,
        )
        for field, value in pre.global_entries
    )


def _freeze_funding_candidate(
    pre: CommittedPerpMarketStateV1,
    *,
    gate: PerpApplyFundingAutoGateOutcome,
    replacements: tuple[tuple[str, CommittedPerpAccountStateV1], ...],
) -> IsolatedFundingTransitionResultV1:
    account_result = _existing_account_patch_and_entries(pre, replacements)
    if type(account_result) is IsolatedPerpTransitionRejectV1:
        return account_result
    account_patch, account_entries = account_result
    after_global_entries = _funding_global_entries(pre, gate)
    global_patch = _build_optional_global_patch_from_entries(
        pre.global_entries,
        after_global_entries,
    )
    if type(global_patch) is IsolatedPerpTransitionRejectV1:
        return global_patch

    try:
        if account_patch is None and global_patch is None:
            candidate = pre
        elif account_patch is None:
            candidate = _committed_isolated_market_from_transition_v1(
                pre,
                after_global_entries,
            )
        elif global_patch is None:
            candidate = _committed_isolated_market_with_accounts_from_transition_v1(
                pre,
                account_entries,
            )
        else:
            candidate = _committed_isolated_market_with_globals_and_accounts_from_transition_v1(
                pre,
                after_global_entries,
                account_entries,
            )
    except (AttributeError, KeyError, TypeError, ValueError):
        return _reject(IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE, ("state",))

    if candidate.global_value("epoch_phase") == _PRICE_PUBLISHED_PHASE:
        settlement = _plan_isolated_settlement_candidate_v1(candidate)
        if type(settlement) is IsolatedPerpTransitionRejectV1:
            detail = settlement.reason or settlement.code.value
            return _reject(
                IsolatedPerpTransitionCodeV1.SETTLEMENT_PATH,
                ("state", "settlement") + settlement.path,
                detail,
            )
    return IsolatedFundingTransitionOkV1(
        market=candidate,
        account_patch=account_patch,
        global_patch=global_patch,
        funding_rate_bps=gate.funding_rate_bps,
        mark_price_e8=gate.mark_price_e8,
        applied_account_count=len(replacements),
        projected_net_funding_quote=gate.projected_net_funding_quote,
    )


def apply_isolated_funding_auto_v1(
    pre: CommittedPerpMarketStateV1,
    *,
    operator_authorized: bool,
) -> IsolatedFundingTransitionResultV1:
    """Return the exact post-funding candidate or one typed no-output reject."""

    validated = _validated_prestate(pre)
    if type(validated) is IsolatedPerpTransitionRejectV1:
        return validated
    gate_reject = _runtime_gate_reject(
        action_kind=ACTION_APPLY_FUNDING_AUTO,
        operator_authorized=operator_authorized,
        pre=validated,
    )
    if gate_reject is not None:
        return gate_reject
    plan = _funding_plan(validated)
    if type(plan) is IsolatedPerpTransitionRejectV1:
        return plan
    gate, replacements = plan
    return _freeze_funding_candidate(
        validated,
        gate=gate,
        replacements=replacements,
    )

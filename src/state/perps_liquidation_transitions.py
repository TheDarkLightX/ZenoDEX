"""Atomic partial-liquidation transition over exact isolated-perps state.

Partial liquidation changes one account and may also move a penalty into the
fee-pool, fee-income, and insurance accumulators.  This leaf evaluates those
changes against one immutable pre-state and freezes them as one market
candidate.  A rejection exposes no account-only or globals-only successor.

The leaf validates the mounted sender-bound command relation and the committed
oracle facts consumed by the scalar risk kernel.  Optional external Oracle
adapter verification remains an imperative-shell admission step.  This module
does not accept a caller-constructible boolean as proof of that verification
and issues no aggregate receipt, commit plan, or shell authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias, cast, final

from ..core.perp_runtime_risk_gate import ACTION_PARTIAL_LIQUIDATE
from ..core.perp_v2 import step as kernel_step
from ..core.perp_v2.types import Action, ActionParams, PerpState
from .perps_account_transitions import (
    CanonicalIsolatedAccountPatchV1,
    _account_from_kernel,
    _account_patch_and_entries,
    _empty_account,
    _kernel_state_with_account,
    _validated_sender_bound_pubkeys,
)
from .perps_state_transitions import (
    CanonicalIsolatedGlobalPatchV1,
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
    _build_optional_global_patch_from_entries,
    _global_entries_from_kernel,
    _validated_prestate,
)
from .state_snapshot_values import CommittedPerpMarketStateV1
from .state_transitions import (
    _committed_isolated_market_with_globals_and_accounts_from_transition_v1,
)

FCIS_MUTABLE_LOCAL_BUFFERS_FORBIDDEN = True


@final
@dataclass(frozen=True, slots=True)
class IsolatedPartialLiquidationTransitionOkV1:
    """One exact account-and-global liquidation candidate."""

    market: CommittedPerpMarketStateV1
    account_patch: CanonicalIsolatedAccountPatchV1
    global_patch: CanonicalIsolatedGlobalPatchV1 | None

    def __post_init__(self) -> None:
        if type(self.market) is not CommittedPerpMarketStateV1:
            raise TypeError("liquidation candidate market must be exact")
        if type(self.account_patch) is not CanonicalIsolatedAccountPatchV1:
            raise TypeError("liquidation account patch must be exact")
        if (
            self.global_patch is not None
            and type(self.global_patch) is not CanonicalIsolatedGlobalPatchV1
        ):
            raise TypeError("liquidation global patch must be exact or None")


IsolatedPartialLiquidationTransitionResultV1: TypeAlias = (
    IsolatedPartialLiquidationTransitionOkV1 | IsolatedPerpTransitionRejectV1
)


def _reject(
    code: IsolatedPerpTransitionCodeV1,
    path: tuple[str | int, ...],
    reason: str | None = None,
) -> IsolatedPerpTransitionRejectV1:
    return IsolatedPerpTransitionRejectV1(code, path, reason)


def _evaluate_liquidation_kernel(
    pre: CommittedPerpMarketStateV1,
    *,
    account_pubkey: str,
    fraction_bps: int,
) -> PerpState | IsolatedPerpTransitionRejectV1:
    account = pre.get_account(account_pubkey) or _empty_account()
    result = kernel_step(
        _kernel_state_with_account(pre, account),
        ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=fraction_bps,
            auth_ok=True,
        ),
    )
    if not result.accepted or result.state is None:
        return _reject(
            IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
            ("kernel",),
            result.rejection or "kernel_rejected",
        )
    return result.state


def _freeze_liquidation_candidate(
    pre: CommittedPerpMarketStateV1,
    *,
    account_pubkey: str,
    post: PerpState,
) -> IsolatedPartialLiquidationTransitionResultV1:
    try:
        replacement_account = _account_from_kernel(post)
    except (TypeError, ValueError):
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("state", "accounts", account_pubkey),
        )
    account_patch, account_entries = _account_patch_and_entries(
        pre,
        account_pubkey=account_pubkey,
        replacement=replacement_account,
    )
    if account_patch is None:
        return _reject(
            IsolatedPerpTransitionCodeV1.EMPTY_PATCH,
            ("patch", "accounts"),
        )

    mark_source = cast(int, pre.global_value("mark_price_source_kind"))
    after_globals = _global_entries_from_kernel(
        post,
        mark_price_source_kind=mark_source,
    )
    global_patch = _build_optional_global_patch_from_entries(
        pre.global_entries,
        after_globals,
    )
    if type(global_patch) is IsolatedPerpTransitionRejectV1:
        return global_patch
    try:
        candidate = _committed_isolated_market_with_globals_and_accounts_from_transition_v1(
            pre,
            after_globals,
            account_entries,
        )
    except (AttributeError, KeyError, TypeError, ValueError):
        return _reject(IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE, ("state",))
    return IsolatedPartialLiquidationTransitionOkV1(
        market=candidate,
        account_patch=account_patch,
        global_patch=global_patch,
    )


def apply_isolated_partial_liquidate_v1(
    pre: CommittedPerpMarketStateV1,
    *,
    account_pubkey: str,
    sender_pubkey: str,
    fraction_bps: int = 0,
) -> IsolatedPartialLiquidationTransitionResultV1:
    """Return one exact partial-liquidation candidate or a typed rejection.

    Rejection precedence matches the mounted isolated path after decode:
    exact pre-state, canonical account/sender binding, exact fraction domain,
    then scalar-kernel liquidation eligibility and arithmetic.
    """

    validated = _validated_prestate(pre)
    if type(validated) is IsolatedPerpTransitionRejectV1:
        return validated
    bound_pubkeys = _validated_sender_bound_pubkeys(
        account_pubkey,
        sender_pubkey,
        action_kind=ACTION_PARTIAL_LIQUIDATE,
    )
    if type(bound_pubkeys) is IsolatedPerpTransitionRejectV1:
        return bound_pubkeys
    canonical_account_pubkey, _canonical_sender_pubkey = bound_pubkeys
    if type(fraction_bps) is not int:
        return _reject(
            IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
            ("fraction_bps",),
        )
    post = _evaluate_liquidation_kernel(
        validated,
        account_pubkey=canonical_account_pubkey,
        fraction_bps=fraction_bps,
    )
    if type(post) is IsolatedPerpTransitionRejectV1:
        return post
    return _freeze_liquidation_candidate(
        validated,
        account_pubkey=canonical_account_pubkey,
        post=post,
    )

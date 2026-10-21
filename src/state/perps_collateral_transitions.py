"""Atomic exact wallet/perps collateral transition leaves.

Deposit and withdrawal each touch two committed values: the wallet balance
table and one isolated-perps account map. This module evaluates both candidates
without publication and returns them only as one immutable aggregate. Any
rejection carries neither candidate.

The result remains below the aggregate FCIS authority boundary. It issues no
receipt, commit plan, outbox record, or shell authorization.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias, cast, final

from ..core.perp_runtime_risk_gate import (
    ACTION_DEPOSIT_COLLATERAL,
    ACTION_WITHDRAW_COLLATERAL,
    REJECT_SENDER_BINDING_INVALID,
)
from ..core.perp_v2.types import Action, ActionParams
from .perps_account_transitions import (
    CanonicalIsolatedAccountPatchV1,
    IsolatedAccountTransitionOkV1,
    _apply_account_kernel_action,
    _canonical_pubkey_reject,
    _validated_sender_bound_pubkeys,
)
from .perps_state_transitions import (
    CanonicalIsolatedGlobalPatchV1,
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
    _apply_global_kernel_action,
    _validated_prestate,
)
from .state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedPerpMarketStateV1,
)
from .state_transitions import (
    BalanceDeltaV1,
    BalancePatchApplyOkV1,
    BalancePatchRejectV1,
    CanonicalBalancePatchV1,
    apply_balance_deltas_v1,
    validate_committed_balance_state_v1,
)


@final
@dataclass(frozen=True, slots=True)
class IsolatedCollateralTransitionOkV1:
    """One all-or-none exact collateral candidate and both leaf patches."""

    balances: CommittedBalanceTableV1
    market: CommittedPerpMarketStateV1
    balance_patch: CanonicalBalancePatchV1
    account_patch: CanonicalIsolatedAccountPatchV1

    def __post_init__(self) -> None:
        if type(self.balances) is not CommittedBalanceTableV1:
            raise TypeError("collateral candidate balances must be exact")
        if type(self.market) is not CommittedPerpMarketStateV1:
            raise TypeError("collateral candidate market must be exact")
        if type(self.balance_patch) is not CanonicalBalancePatchV1:
            raise TypeError("collateral candidate balance patch must be exact")
        if type(self.account_patch) is not CanonicalIsolatedAccountPatchV1:
            raise TypeError("collateral candidate account patch must be exact")


IsolatedCollateralTransitionResultV1: TypeAlias = (
    IsolatedCollateralTransitionOkV1 | IsolatedPerpTransitionRejectV1
)


@final
@dataclass(frozen=True, slots=True)
class IsolatedInsuranceDepositTransitionOkV1:
    """One all-or-none wallet debit and insurance-state candidate."""

    balances: CommittedBalanceTableV1
    market: CommittedPerpMarketStateV1
    balance_patch: CanonicalBalancePatchV1
    global_patch: CanonicalIsolatedGlobalPatchV1

    def __post_init__(self) -> None:
        if type(self.balances) is not CommittedBalanceTableV1:
            raise TypeError("insurance candidate balances must be exact")
        if type(self.market) is not CommittedPerpMarketStateV1:
            raise TypeError("insurance candidate market must be exact")
        if type(self.balance_patch) is not CanonicalBalancePatchV1:
            raise TypeError("insurance candidate balance patch must be exact")
        if type(self.global_patch) is not CanonicalIsolatedGlobalPatchV1:
            raise TypeError("insurance candidate global patch must be exact")


IsolatedInsuranceDepositTransitionResultV1: TypeAlias = (
    IsolatedInsuranceDepositTransitionOkV1 | IsolatedPerpTransitionRejectV1
)


def _reject(
    code: IsolatedPerpTransitionCodeV1,
    path: tuple[str | int, ...],
    reason: str | None = None,
) -> IsolatedPerpTransitionRejectV1:
    return IsolatedPerpTransitionRejectV1(code, path, reason)


def _balance_reject(
    reject: BalancePatchRejectV1,
) -> IsolatedPerpTransitionRejectV1:
    return _reject(
        IsolatedPerpTransitionCodeV1.BALANCE_PATCH,
        ("balances",) + reject.path,
        reject.code.value,
    )


def _validated_collateral_prestate(
    market: object,
    balances: object,
) -> tuple[CommittedPerpMarketStateV1, CommittedBalanceTableV1] | IsolatedPerpTransitionRejectV1:
    validated_market = _validated_prestate(market)
    if type(validated_market) is IsolatedPerpTransitionRejectV1:
        return validated_market
    if type(balances) is not CommittedBalanceTableV1:
        return _reject(
            IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
            ("balances",),
        )
    balance_reject = validate_committed_balance_state_v1(balances)
    if balance_reject is not None:
        return _balance_reject(balance_reject)
    return validated_market, balances


def _validated_identity_bound_pubkeys(
    account_pubkey: object,
    sender_pubkey: object,
) -> tuple[str, str] | IsolatedPerpTransitionRejectV1:
    """Validate canonical identities for a sender-bound non-gated action."""

    account_reject = _canonical_pubkey_reject(account_pubkey, ("account_pubkey",))
    if account_reject is not None:
        return account_reject
    sender_reject = _canonical_pubkey_reject(sender_pubkey, ("sender_pubkey",))
    if sender_reject is not None:
        return sender_reject
    account = cast(str, account_pubkey)
    sender = cast(str, sender_pubkey)
    if account != sender:
        return _reject(
            IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
            ("gate",),
            REJECT_SENDER_BINDING_INVALID,
        )
    return account, sender


def _combine_collateral_candidates(
    *,
    pre_balances: CommittedBalanceTableV1,
    account_result: IsolatedAccountTransitionOkV1,
    account_pubkey: str,
    quote_asset: str,
    balance_delta: int,
) -> IsolatedCollateralTransitionResultV1:
    balance_result = apply_balance_deltas_v1(
        pre_balances,
        (BalanceDeltaV1((account_pubkey, quote_asset), balance_delta),),
    )
    if type(balance_result) is BalancePatchRejectV1:
        return _balance_reject(balance_result)
    if (
        type(balance_result) is not BalancePatchApplyOkV1
        or balance_result.patch is None
        or account_result.account_patch is None
    ):
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("state", "collateral"),
        )
    return IsolatedCollateralTransitionOkV1(
        balances=balance_result.state,
        market=account_result.market,
        balance_patch=balance_result.patch,
        account_patch=account_result.account_patch,
    )


def _apply_collateral_kernel_and_balance(
    *,
    market: CommittedPerpMarketStateV1,
    balances: CommittedBalanceTableV1,
    account_pubkey: str,
    amount: int,
    action: Action,
    balance_delta: int,
) -> IsolatedCollateralTransitionResultV1:
    account_result = _apply_account_kernel_action(
        market,
        account_pubkey=account_pubkey,
        params=ActionParams(action=action, amount=amount, auth_ok=True),
    )
    if type(account_result) is IsolatedPerpTransitionRejectV1:
        return account_result
    return _combine_collateral_candidates(
        pre_balances=balances,
        account_result=account_result,
        account_pubkey=account_pubkey,
        quote_asset=market.quote_asset,
        balance_delta=balance_delta,
    )


def _combine_insurance_candidates(
    market: CommittedPerpMarketStateV1,
    balances: CommittedBalanceTableV1,
    account_pubkey: str,
    amount: int,
) -> IsolatedInsuranceDepositTransitionResultV1:
    mark_source = cast(int, market.global_value("mark_price_source_kind"))
    market_result = _apply_global_kernel_action(
        market,
        ActionParams(action=Action.DEPOSIT_INSURANCE, amount=amount),
        mark_price_source_kind=mark_source,
    )
    if type(market_result) is IsolatedPerpTransitionRejectV1:
        return market_result
    balance_result = apply_balance_deltas_v1(
        balances,
        (BalanceDeltaV1((account_pubkey, market.quote_asset), -amount),),
    )
    if type(balance_result) is BalancePatchRejectV1:
        return _balance_reject(balance_result)
    if type(balance_result) is not BalancePatchApplyOkV1 or balance_result.patch is None:
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("state", "insurance"),
        )
    return IsolatedInsuranceDepositTransitionOkV1(
        balances=balance_result.state,
        market=market_result.market,
        balance_patch=balance_result.patch,
        global_patch=market_result.patch,
    )


def apply_isolated_deposit_collateral_v1(
    pre_market: CommittedPerpMarketStateV1,
    pre_balances: CommittedBalanceTableV1,
    *,
    account_pubkey: str,
    sender_pubkey: str,
    amount: int,
) -> IsolatedCollateralTransitionResultV1:
    """Atomically debit wallet quote units and credit perps collateral.

    Exact pre-state validation precedes command checks. Canonical account and
    sender binding precede amount validation; insufficient wallet balance
    precedes scalar-kernel admission, matching the mounted isolated path.
    """

    validated = _validated_collateral_prestate(pre_market, pre_balances)
    if type(validated) is IsolatedPerpTransitionRejectV1:
        return validated
    market, balances = validated
    bound_pubkeys = _validated_sender_bound_pubkeys(
        account_pubkey,
        sender_pubkey,
        action_kind=ACTION_DEPOSIT_COLLATERAL,
    )
    if type(bound_pubkeys) is IsolatedPerpTransitionRejectV1:
        return bound_pubkeys
    canonical_account_pubkey, _canonical_sender_pubkey = bound_pubkeys
    if type(amount) is not int:
        return _reject(IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE, ("amount",))
    if balances.get(canonical_account_pubkey, market.quote_asset) < amount:
        return _reject(
            IsolatedPerpTransitionCodeV1.INSUFFICIENT_BALANCE,
            ("balances", canonical_account_pubkey, market.quote_asset),
        )
    return _apply_collateral_kernel_and_balance(
        market=market,
        balances=balances,
        account_pubkey=canonical_account_pubkey,
        amount=amount,
        action=Action.DEPOSIT_COLLATERAL,
        balance_delta=-amount,
    )


def apply_isolated_withdraw_collateral_v1(
    pre_market: CommittedPerpMarketStateV1,
    pre_balances: CommittedBalanceTableV1,
    *,
    account_pubkey: str,
    sender_pubkey: str,
    amount: int,
) -> IsolatedCollateralTransitionResultV1:
    """Atomically debit perps collateral and credit wallet quote units.

    Exact pre-state validation, canonical account parsing, sender binding, and
    amount typing follow the mounted rejection order. Kernel or balance-patch
    rejection returns no component of the combined candidate.
    """

    validated = _validated_collateral_prestate(pre_market, pre_balances)
    if type(validated) is IsolatedPerpTransitionRejectV1:
        return validated
    market, balances = validated
    bound_pubkeys = _validated_sender_bound_pubkeys(
        account_pubkey,
        sender_pubkey,
        action_kind=ACTION_WITHDRAW_COLLATERAL,
    )
    if type(bound_pubkeys) is IsolatedPerpTransitionRejectV1:
        return bound_pubkeys
    canonical_account_pubkey, _canonical_sender_pubkey = bound_pubkeys
    if type(amount) is not int:
        return _reject(IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE, ("amount",))
    return _apply_collateral_kernel_and_balance(
        market=market,
        balances=balances,
        account_pubkey=canonical_account_pubkey,
        amount=amount,
        action=Action.WITHDRAW_COLLATERAL,
        balance_delta=amount,
    )


def apply_isolated_deposit_insurance_v1(
    pre_market: CommittedPerpMarketStateV1,
    pre_balances: CommittedBalanceTableV1,
    *,
    account_pubkey: str,
    sender_pubkey: str,
    amount: int,
) -> IsolatedInsuranceDepositTransitionResultV1:
    """Atomically debit wallet quote units and increase insurance reserves.

    The global kernel is evaluated against its flat account projection, so an
    unrelated distressed account cannot block the reserve top-up. The exact
    account map remains shared and unchanged. Rejection exposes neither the
    wallet candidate nor the market candidate.
    """

    validated = _validated_collateral_prestate(pre_market, pre_balances)
    if type(validated) is IsolatedPerpTransitionRejectV1:
        return validated
    market, balances = validated
    bound_pubkeys = _validated_identity_bound_pubkeys(account_pubkey, sender_pubkey)
    if type(bound_pubkeys) is IsolatedPerpTransitionRejectV1:
        return bound_pubkeys
    canonical_account_pubkey, _canonical_sender_pubkey = bound_pubkeys
    if type(amount) is not int:
        return _reject(IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE, ("amount",))
    if amount <= 0:
        return _reject(
            IsolatedPerpTransitionCodeV1.AMOUNT_NOT_POSITIVE,
            ("amount",),
        )
    if balances.get(canonical_account_pubkey, market.quote_asset) < amount:
        return _reject(
            IsolatedPerpTransitionCodeV1.INSUFFICIENT_BALANCE,
            ("balances", canonical_account_pubkey, market.quote_asset),
        )

    return _combine_insurance_candidates(
        market,
        balances,
        canonical_account_pubkey,
        amount,
    )

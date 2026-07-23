"""Pure account-scoped transitions over exact isolated-perps state.

This module owns the account-map part of the isolated-perps transition
relation. It accepts an exact committed market and explicit command/context
values, evaluates the existing scalar kernel, and returns either one exact
market candidate plus its canonical compare-and-replace patch or a typed
rejection with no candidate.

These leaf results issue no aggregate receipt or shell authority. PR #478 must
admit an authorized command type and derive aggregate outputs from one complete
candidate before any result can reach the commit boundary.
"""

from __future__ import annotations

from bisect import bisect_left
from dataclasses import dataclass, replace
from typing import TypeAlias, cast, final

from ..core.perp_runtime_risk_gate import (
    ACTION_SET_POSITION,
    REJECT_OK,
    evaluate_perp_runtime_risk_gate,
)
from ..core.perp_v2 import step as kernel_step
from ..core.perp_v2.types import Action, ActionParams, PerpState
from .canonical import canonical_hex_fixed_allow_0x
from .perps_state_transitions import (
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
    _global_entries_from_kernel,
    _kernel_state_from_market,
    _validated_prestate,
)
from .state_snapshot_values import (
    CommittedPerpAccountStateV1,
    CommittedPerpMarketStateV1,
)
from .state_transitions import (
    _committed_isolated_market_with_accounts_from_transition_v1,
)

AccountTransitionPathPartV1: TypeAlias = str | int
AccountTransitionPathV1: TypeAlias = tuple[AccountTransitionPathPartV1, ...]


def _reject(
    code: IsolatedPerpTransitionCodeV1,
    path: AccountTransitionPathV1,
    reason: str | None = None,
) -> IsolatedPerpTransitionRejectV1:
    return IsolatedPerpTransitionRejectV1(code, path, reason)


def _canonical_pubkey_reject(
    value: object,
    path: AccountTransitionPathV1,
) -> IsolatedPerpTransitionRejectV1 | None:
    if type(value) is not str:
        return _reject(IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE, path)
    try:
        canonical = canonical_hex_fixed_allow_0x(value, nbytes=48, name="pubkey")
    except (TypeError, ValueError):
        return _reject(IsolatedPerpTransitionCodeV1.NONCANONICAL_ACCOUNT, path)
    if canonical != value:
        return _reject(IsolatedPerpTransitionCodeV1.NONCANONICAL_ACCOUNT, path)
    return None


@final
@dataclass(frozen=True, slots=True)
class IsolatedAccountWriteV1:
    """One exact compare-and-replace write in an isolated account map."""

    account_pubkey: str
    expected: CommittedPerpAccountStateV1 | None
    replacement: CommittedPerpAccountStateV1

    def __post_init__(self) -> None:
        reject = _canonical_pubkey_reject(self.account_pubkey, ("account_pubkey",))
        if reject is not None:
            if reject.code is IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE:
                raise TypeError("isolated account-write key must be an exact string")
            raise ValueError("isolated account-write key must be canonical")
        if self.expected is not None and type(self.expected) is not CommittedPerpAccountStateV1:
            raise TypeError("isolated account-write expected value must be exact or None")
        if type(self.replacement) is not CommittedPerpAccountStateV1:
            raise TypeError("isolated account-write replacement must be exact")
        if self.expected == self.replacement:
            raise ValueError("isolated account write must change its logical cell")


@final
@dataclass(frozen=True, slots=True)
class CanonicalIsolatedAccountPatchV1:
    """Nonempty canonical account writes sorted by exact public key."""

    writes: tuple[IsolatedAccountWriteV1, ...]

    def __post_init__(self) -> None:
        if type(self.writes) is not tuple or not self.writes:
            raise ValueError("isolated account patch must be a nonempty exact tuple")
        previous: str | None = None
        for write in self.writes:
            if type(write) is not IsolatedAccountWriteV1:
                raise TypeError("isolated account patch writes must be exact")
            write.__post_init__()
            if previous is not None and previous >= write.account_pubkey:
                raise ValueError("isolated account patch must be sorted and duplicate-free")
            previous = write.account_pubkey


@final
@dataclass(frozen=True, slots=True)
class IsolatedAccountTransitionOkV1:
    """One exact account-map candidate and its optional semantic patch."""

    market: CommittedPerpMarketStateV1
    account_patch: CanonicalIsolatedAccountPatchV1 | None

    def __post_init__(self) -> None:
        if type(self.market) is not CommittedPerpMarketStateV1:
            raise TypeError("isolated account candidate market must be exact")
        if (
            self.account_patch is not None
            and type(self.account_patch) is not CanonicalIsolatedAccountPatchV1
        ):
            raise TypeError("isolated account patch must be exact or None")


IsolatedAccountTransitionResultV1: TypeAlias = (
    IsolatedAccountTransitionOkV1 | IsolatedPerpTransitionRejectV1
)


def _sender_gate_reject(
    account_pubkey: str,
    sender_pubkey: str,
) -> IsolatedPerpTransitionRejectV1 | None:
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=ACTION_SET_POSITION,
        operator_ok=True,
        unknown_fields_ok=True,
        sender_binding_ok=account_pubkey == sender_pubkey,
        epoch_settled_ok=True,
        positive_price_ok=True,
        positions_flat_ok=True,
        params_object_ok=True,
    )
    if outcome.reject_code == REJECT_OK:
        return None
    return _reject(
        IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
        ("gate",),
        outcome.reject_code,
    )


def _validated_sender_bound_pubkeys(
    account_pubkey: object,
    sender_pubkey: object,
) -> tuple[str, str] | IsolatedPerpTransitionRejectV1:
    account_reject = _canonical_pubkey_reject(account_pubkey, ("account_pubkey",))
    if account_reject is not None:
        return account_reject
    sender_reject = _canonical_pubkey_reject(sender_pubkey, ("sender_pubkey",))
    if sender_reject is not None:
        return sender_reject
    account = cast(str, account_pubkey)
    sender = cast(str, sender_pubkey)
    gate_reject = _sender_gate_reject(account, sender)
    if gate_reject is not None:
        return gate_reject
    return account, sender


def _empty_account() -> CommittedPerpAccountStateV1:
    return CommittedPerpAccountStateV1(
        position_base=0,
        entry_price_e8=0,
        collateral_quote=0,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )


def _kernel_state_with_account(
    market: CommittedPerpMarketStateV1,
    account: CommittedPerpAccountStateV1,
) -> PerpState:
    return replace(
        _kernel_state_from_market(market),
        position_base=account.position_base,
        entry_price_e8=account.entry_price_e8,
        collateral_quote=account.collateral_quote,
        funding_paid_cumulative=account.funding_paid_cumulative,
        funding_last_applied_epoch=account.funding_last_applied_epoch,
        liquidated_this_step=account.liquidated_this_step,
    )


def _account_from_kernel(state: PerpState) -> CommittedPerpAccountStateV1:
    return CommittedPerpAccountStateV1(
        position_base=state.position_base,
        entry_price_e8=state.entry_price_e8,
        collateral_quote=state.collateral_quote,
        funding_paid_cumulative=state.funding_paid_cumulative,
        funding_last_applied_epoch=state.funding_last_applied_epoch,
        liquidated_this_step=state.liquidated_this_step,
    )


def _account_candidate(
    pre: CommittedPerpMarketStateV1,
    *,
    account_pubkey: str,
    replacement: CommittedPerpAccountStateV1,
) -> IsolatedAccountTransitionOkV1 | IsolatedPerpTransitionRejectV1:
    entries = pre.account_entries
    keys = tuple(key for key, _account in entries)
    index = bisect_left(keys, account_pubkey)
    expected = entries[index][1] if index < len(entries) and keys[index] == account_pubkey else None
    if expected == replacement:
        return IsolatedAccountTransitionOkV1(pre, None)

    write = IsolatedAccountWriteV1(account_pubkey, expected, replacement)
    patch = CanonicalIsolatedAccountPatchV1((write,))
    replacement_entry = ((account_pubkey, replacement),)
    if expected is None:
        candidate_entries = entries[:index] + replacement_entry + entries[index:]
    else:
        candidate_entries = entries[:index] + replacement_entry + entries[index + 1 :]
    try:
        candidate = _committed_isolated_market_with_accounts_from_transition_v1(
            pre,
            candidate_entries,
        )
    except (AttributeError, KeyError, TypeError, ValueError):
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("state", "accounts"),
        )
    return IsolatedAccountTransitionOkV1(candidate, patch)


def _set_position_candidate(
    pre: CommittedPerpMarketStateV1,
    *,
    account_pubkey: str,
    new_position_base: int,
) -> IsolatedAccountTransitionResultV1:
    account = pre.get_account(account_pubkey) or _empty_account()
    result = kernel_step(
        _kernel_state_with_account(pre, account),
        ActionParams(
            action=Action.SET_POSITION,
            new_position_base=new_position_base,
            auth_ok=True,
        ),
    )
    if not result.accepted or result.state is None:
        return _reject(
            IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
            ("kernel",),
            result.rejection or "kernel_rejected",
        )
    mark_source = cast(int, pre.global_value("mark_price_source_kind"))
    if (
        _global_entries_from_kernel(
            result.state,
            mark_price_source_kind=mark_source,
        )
        != pre.global_entries
    ):
        return _reject(
            IsolatedPerpTransitionCodeV1.INTERNAL_GLOBAL_MUTATION,
            ("kernel", "global"),
        )
    try:
        replacement = _account_from_kernel(result.state)
    except (TypeError, ValueError):
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("state", "accounts", account_pubkey),
        )
    return _account_candidate(
        pre,
        account_pubkey=account_pubkey,
        replacement=replacement,
    )


def apply_isolated_set_position_v1(
    pre: CommittedPerpMarketStateV1,
    *,
    account_pubkey: str,
    sender_pubkey: str,
    new_position_base: int,
) -> IsolatedAccountTransitionResultV1:
    """Return the exact set-position candidate or one typed no-output reject.

    The account and sender are canonical 48-byte public-key strings. Position
    units and bounds are those of the mounted isolated-perps scalar kernel.
    Account parsing and sender binding precede position-domain evaluation.
    The global map remains byte-identical and structurally shared on success.
    """

    validated = _validated_prestate(pre)
    if type(validated) is IsolatedPerpTransitionRejectV1:
        return validated
    bound_pubkeys = _validated_sender_bound_pubkeys(account_pubkey, sender_pubkey)
    if type(bound_pubkeys) is IsolatedPerpTransitionRejectV1:
        return bound_pubkeys
    canonical_account_pubkey, _canonical_sender_pubkey = bound_pubkeys
    if type(new_position_base) is not int:
        return _reject(
            IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
            ("new_position_base",),
        )

    return _set_position_candidate(
        validated,
        account_pubkey=canonical_account_pubkey,
        new_position_base=new_position_base,
    )

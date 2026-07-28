"""Pure per-asset protocol-fee distribution over exact committed balances."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, cast, final

from ..state.state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
)
from ..state.state_transitions import (
    BalanceDeltaV1,
    BalancePatchApplyOkV1,
    BalancePatchRejectV1,
    CanonicalBalancePatchV1,
    apply_balance_deltas_v1,
)
from .fcis_fee_custody_values import (
    BPS_DENOMINATOR_V2,
    MAX_FEE_AMOUNT_V2,
    MAX_FEE_BALANCE_DELTAS_V2,
    MAX_FEE_CREDITS_V2,
    MAX_FEE_CUSTODY_KEYS_V2,
    AssetFeeDistributionV2,
    CommittedFeeAccumulatorStateV2,
    FeeCustodyTransitionOkV2,
    FeeDistributionPolicyV2,
    FeeDustEntryV2,
    ProtocolFeeCreditV2,
    _fee_custody_ok_v2,
)

FeeCustodyPathPartV2: TypeAlias = str | int
FeeCustodyPathV2: TypeAlias = tuple[FeeCustodyPathPartV2, ...]
FeeCustodyKeyV2: TypeAlias = tuple[str, str]


class FeeCustodyTransitionCodeV2(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    ITEM_LIMIT = "item_limit"
    OUT_OF_RANGE = "out_of_range"
    INVALID_PRESTATE = "invalid_prestate"
    INVALID_POLICY = "invalid_policy"
    CONSERVATION = "conservation"
    INSUFFICIENT_CUSTODY = "insufficient_custody"
    BALANCE_TRANSITION = "balance_transition"
    UNOWNED_LEGACY_DUST = "unowned_legacy_dust"


@final
@dataclass(frozen=True, slots=True)
class FeeCustodyTransitionRejectV2:
    """Typed rejection with no successor, patch, or distribution authority."""

    code: FeeCustodyTransitionCodeV2
    path: FeeCustodyPathV2

    def __post_init__(self) -> None:
        if type(self.code) is not FeeCustodyTransitionCodeV2:
            raise TypeError("fee custody rejection code must be exact")
        if type(self.path) is not tuple or any(type(part) not in (str, int) for part in self.path):
            raise TypeError("fee custody rejection path must be exact")


FeeCustodyTransitionResultV2: TypeAlias = FeeCustodyTransitionOkV2 | FeeCustodyTransitionRejectV2
FeeAccumulatorMigrationResultV2: TypeAlias = (
    CommittedFeeAccumulatorStateV2 | FeeCustodyTransitionRejectV2
)


def _reject_v2(
    code: FeeCustodyTransitionCodeV2,
    path: FeeCustodyPathV2,
) -> FeeCustodyTransitionRejectV2:
    return FeeCustodyTransitionRejectV2(code, path)


def _validated_policy_v2(
    policy: object,
) -> FeeDistributionPolicyV2 | FeeCustodyTransitionRejectV2:
    if type(policy) is not FeeDistributionPolicyV2:
        return _reject_v2(FeeCustodyTransitionCodeV2.WRONG_EXACT_TYPE, ("policy",))
    try:
        policy.__post_init__()
    except (AttributeError, TypeError, ValueError):
        return _reject_v2(FeeCustodyTransitionCodeV2.INVALID_POLICY, ("policy",))
    return policy


def _validated_credit_v2(
    credit: object,
    index: int,
) -> ProtocolFeeCreditV2 | FeeCustodyTransitionRejectV2:
    path: FeeCustodyPathV2 = ("credits", index)
    if type(credit) is not ProtocolFeeCreditV2:
        return _reject_v2(FeeCustodyTransitionCodeV2.WRONG_EXACT_TYPE, path)
    try:
        credit.__post_init__()
    except (AttributeError, TypeError, ValueError):
        return _reject_v2(FeeCustodyTransitionCodeV2.OUT_OF_RANGE, path)
    return credit


def _validated_credits_v2(
    credits: object,
) -> tuple[ProtocolFeeCreditV2, ...] | FeeCustodyTransitionRejectV2:
    if type(credits) is not tuple:
        return _reject_v2(FeeCustodyTransitionCodeV2.WRONG_EXACT_TYPE, ("credits",))
    if len(credits) > MAX_FEE_CREDITS_V2:
        return _reject_v2(FeeCustodyTransitionCodeV2.ITEM_LIMIT, ("credits",))
    exact: list[ProtocolFeeCreditV2] = []
    for index, credit in enumerate(credits):
        validated = _validated_credit_v2(credit, index)
        if type(validated) is FeeCustodyTransitionRejectV2:
            return validated
        exact.append(validated)
    return tuple(exact)


def _validated_accumulator_v2(
    accumulator: object,
) -> CommittedFeeAccumulatorStateV2 | FeeCustodyTransitionRejectV2:
    if type(accumulator) is not CommittedFeeAccumulatorStateV2:
        return _reject_v2(
            FeeCustodyTransitionCodeV2.WRONG_EXACT_TYPE,
            ("accumulator",),
        )
    try:
        accumulator.__post_init__()
    except (AttributeError, TypeError, ValueError):
        return _reject_v2(
            FeeCustodyTransitionCodeV2.INVALID_PRESTATE,
            ("accumulator",),
        )
    return accumulator


def _validated_balances_v2(
    balances: object,
) -> CommittedBalanceTableV1 | FeeCustodyTransitionRejectV2:
    if type(balances) is not CommittedBalanceTableV1:
        return _reject_v2(
            FeeCustodyTransitionCodeV2.WRONG_EXACT_TYPE,
            ("balances",),
        )
    exact_balances = cast(CommittedBalanceTableV1, balances)
    try:
        exact_balances.__post_init__()
    except (AttributeError, TypeError, ValueError):
        return _reject_v2(
            FeeCustodyTransitionCodeV2.INVALID_PRESTATE,
            ("balances",),
        )
    return exact_balances


def _checked_add_v2(
    left: int,
    right: int,
    path: FeeCustodyPathV2,
) -> int | FeeCustodyTransitionRejectV2:
    total = left + right
    if total > MAX_FEE_AMOUNT_V2:
        return _reject_v2(FeeCustodyTransitionCodeV2.OUT_OF_RANGE, path)
    return total


def _totals_by_key_v2(
    credits: tuple[ProtocolFeeCreditV2, ...],
    accumulator: CommittedFeeAccumulatorStateV2,
) -> dict[FeeCustodyKeyV2, int] | FeeCustodyTransitionRejectV2:
    totals = {entry.custody_key: entry.amount for entry in accumulator.entries}
    for index, credit in enumerate(credits):
        previous = totals.get(credit.custody_key, 0)
        total = _checked_add_v2(
            previous,
            credit.amount,
            ("credits", index, "amount"),
        )
        if type(total) is FeeCustodyTransitionRejectV2:
            return total
        totals[credit.custody_key] = total
    if len(totals) > MAX_FEE_CUSTODY_KEYS_V2:
        return _reject_v2(FeeCustodyTransitionCodeV2.ITEM_LIMIT, ("custody_keys",))
    return totals


def _distribution_v2(
    key: FeeCustodyKeyV2,
    total: int,
    policy: FeeDistributionPolicyV2,
) -> AssetFeeDistributionV2 | FeeCustodyTransitionRejectV2:
    buyback = (total * policy.buyback_bps) // BPS_DENOMINATOR_V2
    treasury = (total * policy.treasury_bps) // BPS_DENOMINATOR_V2
    rewards = (total * policy.rewards_bps) // BPS_DENOMINATOR_V2
    distributed = buyback + treasury + rewards
    if distributed > total:
        return _reject_v2(
            FeeCustodyTransitionCodeV2.CONSERVATION,
            ("distribution", key[0], key[1]),
        )
    return AssetFeeDistributionV2(
        source_custody_pubkey=key[0],
        asset=key[1],
        buyback_custody_pubkey=policy.buyback_custody_pubkey,
        treasury_custody_pubkey=policy.treasury_custody_pubkey,
        rewards_custody_pubkey=policy.rewards_custody_pubkey,
        buyback_amount=buyback,
        treasury_amount=treasury,
        rewards_amount=rewards,
        dust_carried=total - distributed,
    )


def _balance_deltas_v2(
    distributions: tuple[AssetFeeDistributionV2, ...],
    balances: CommittedBalanceTableV1,
) -> tuple[BalanceDeltaV1, ...] | FeeCustodyTransitionRejectV2:
    deltas: list[BalanceDeltaV1] = []
    for index, distribution in enumerate(distributions):
        source_balance = balances.get(
            distribution.source_custody_pubkey,
            distribution.asset,
        )
        required_source_custody = distribution.distributed_amount + distribution.dust_carried
        if source_balance < required_source_custody:
            return _reject_v2(
                FeeCustodyTransitionCodeV2.INSUFFICIENT_CUSTODY,
                ("distributions", index, "source_custody"),
            )
        if distribution.distributed_amount:
            deltas.append(
                BalanceDeltaV1(
                    (distribution.source_custody_pubkey, distribution.asset),
                    -distribution.distributed_amount,
                )
            )
        for destination, amount in (
            (distribution.buyback_custody_pubkey, distribution.buyback_amount),
            (distribution.treasury_custody_pubkey, distribution.treasury_amount),
            (distribution.rewards_custody_pubkey, distribution.rewards_amount),
        ):
            if amount:
                deltas.append(BalanceDeltaV1((destination, distribution.asset), amount))
        if len(deltas) > MAX_FEE_BALANCE_DELTAS_V2:
            return _reject_v2(
                FeeCustodyTransitionCodeV2.ITEM_LIMIT,
                ("balance_deltas",),
            )
    return tuple(deltas)


def _apply_distribution_balances_v2(
    balances: CommittedBalanceTableV1,
    distributions: tuple[AssetFeeDistributionV2, ...],
) -> tuple[CommittedBalanceTableV1, CanonicalBalancePatchV1 | None] | FeeCustodyTransitionRejectV2:
    deltas = _balance_deltas_v2(distributions, balances)
    if type(deltas) is FeeCustodyTransitionRejectV2:
        return deltas
    if not deltas:
        return balances, None
    applied = apply_balance_deltas_v1(balances, deltas)
    if type(applied) is BalancePatchRejectV1:
        return _reject_v2(
            FeeCustodyTransitionCodeV2.BALANCE_TRANSITION,
            ("balances", applied.code.value) + applied.path,
        )
    exact = cast(BalancePatchApplyOkV1, applied)
    return exact.state, exact.patch


def apply_protocol_fee_distribution_v2(
    *,
    credits: object,
    policy: object,
    accumulator: object,
    balances: object,
) -> FeeCustodyTransitionResultV2:
    """Apply one bounded per-custody fee transition with no external effects."""

    exact_credits = _validated_credits_v2(credits)
    if type(exact_credits) is FeeCustodyTransitionRejectV2:
        return exact_credits
    exact_policy = _validated_policy_v2(policy)
    if type(exact_policy) is FeeCustodyTransitionRejectV2:
        return exact_policy
    exact_accumulator = _validated_accumulator_v2(accumulator)
    if type(exact_accumulator) is FeeCustodyTransitionRejectV2:
        return exact_accumulator
    exact_balances = _validated_balances_v2(balances)
    if type(exact_balances) is FeeCustodyTransitionRejectV2:
        return exact_balances
    totals = _totals_by_key_v2(exact_credits, exact_accumulator)
    if type(totals) is FeeCustodyTransitionRejectV2:
        return totals

    distributions: list[AssetFeeDistributionV2] = []
    next_dust: list[FeeDustEntryV2] = []
    for key, total in sorted(totals.items(), key=lambda item: item[0]):
        distribution = _distribution_v2(key, total, exact_policy)
        if type(distribution) is FeeCustodyTransitionRejectV2:
            return distribution
        distributions.append(distribution)
        if distribution.dust_carried:
            next_dust.append(
                FeeDustEntryV2(
                    key[0],
                    key[1],
                    distribution.dust_carried,
                )
            )

    exact_distributions = tuple(distributions)
    applied = _apply_distribution_balances_v2(exact_balances, exact_distributions)
    if type(applied) is FeeCustodyTransitionRejectV2:
        return applied
    next_balances, balance_patch = applied
    return _fee_custody_ok_v2(
        balances=next_balances,
        balance_patch=balance_patch,
        accumulator=CommittedFeeAccumulatorStateV2(tuple(next_dust)),
        distributions=exact_distributions,
    )


def migrate_fee_accumulator_v1_to_v2(
    state: object,
) -> FeeAccumulatorMigrationResultV2:
    """Migrate only the uniquely attributable zero-dust legacy state."""

    if type(state) is not CommittedFeeAccumulatorStateV1:
        return _reject_v2(
            FeeCustodyTransitionCodeV2.WRONG_EXACT_TYPE,
            ("legacy_state",),
        )
    dust = object.__getattribute__(state, "dust")
    if type(dust) is not int or dust < 0:
        return _reject_v2(
            FeeCustodyTransitionCodeV2.INVALID_PRESTATE,
            ("legacy_state", "dust"),
        )
    if dust != 0:
        return _reject_v2(
            FeeCustodyTransitionCodeV2.UNOWNED_LEGACY_DUST,
            ("legacy_state", "dust"),
        )
    return CommittedFeeAccumulatorStateV2(())


__all__ = (
    "FeeAccumulatorMigrationResultV2",
    "FeeCustodyTransitionCodeV2",
    "FeeCustodyTransitionOkV2",
    "FeeCustodyTransitionRejectV2",
    "FeeCustodyTransitionResultV2",
    "apply_protocol_fee_distribution_v2",
    "migrate_fee_accumulator_v1_to_v2",
)

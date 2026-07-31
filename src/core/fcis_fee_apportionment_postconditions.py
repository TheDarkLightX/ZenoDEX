"""Closed SRGD postcondition revalidation for the unmounted FCIS kernel."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, cast, final

from . import fcis_m6_profile_ids
from .fcis_fee_apportionment_transition import FeeQuotaV2, compute_fee_quota_v2
from .fcis_fee_apportionment_values import (
    BPS_DENOMINATOR_V2,
    MAX_FEE_AMOUNT_V2,
    FeeDistributionPolicyV2,
)

EXPECTED_FIXED_ROLE_ORDER_V2: Final[tuple[str, str, str]] = (
    "buyback",
    "treasury",
    "rewards",
)
EXPECTED_FIXED_ROLE_ORDER_ID_V2: Final[str] = (
    "fee-occurrence/role-order/buyback-treasury-rewards/v1"
)


class FeeAllocationPostconditionCodeV2(Enum):
    """Stable failure classes for the independent postcondition relation."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    WRONG_ARITY = "wrong_arity"
    INVALID_ROLE_ORDER = "invalid_role_order"
    INVALID_POLICY = "invalid_policy"
    INVALID_AMOUNT = "invalid_amount"
    INVALID_PRE_DEFICITS = "invalid_pre_deficits"
    INVALID_FRACTIONS = "invalid_fractions"
    INVALID_BONUSES = "invalid_bonuses"
    INVALID_AMOUNTS = "invalid_amounts"
    INVALID_POST_DEFICITS = "invalid_post_deficits"
    QUOTA_RELATION = "quota_relation"
    AMOUNT_CONSERVATION = "amount_conservation"
    ZERO_WEIGHT_SUPPORT = "zero_weight_support"
    LOCAL_QUOTA = "local_quota"
    BONUS_SUPPORT = "bonus_support"
    BONUS_COUNT = "bonus_count"
    BONUS_ORDER = "bonus_order"
    POST_DEFICIT_RECURRENCE = "post_deficit_recurrence"
    POST_DEFICIT_CONSERVATION = "post_deficit_conservation"
    POST_DEFICIT_BOUND = "post_deficit_bound"


@final
@dataclass(frozen=True, slots=True)
class FeeAllocationPostconditionAcceptV2:
    """Evidence that the complete one-asset relation was freshly rechecked."""

    role_order: tuple[str, str, str]
    seat_count: int

    def __post_init__(self) -> None:
        if self.role_order != EXPECTED_FIXED_ROLE_ORDER_V2:
            raise ValueError("postcondition role order is not the fixed profile")
        if type(self.seat_count) is not int or self.seat_count not in (0, 1, 2):
            raise ValueError("postcondition seat count is outside {0,1,2}")


@final
@dataclass(frozen=True, slots=True)
class FeeAllocationPostconditionRejectV2:
    """Typed fail-closed postcondition failure."""

    code: FeeAllocationPostconditionCodeV2
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not FeeAllocationPostconditionCodeV2:
            raise TypeError("postcondition rejection code must be exact")
        if type(self.path) is not tuple or any(
            type(part) is not str for part in self.path
        ):
            raise TypeError("postcondition rejection path must be exact")


FeeAllocationPostconditionResultV2 = (
    FeeAllocationPostconditionAcceptV2 | FeeAllocationPostconditionRejectV2
)


def _reject_v2(
    code: FeeAllocationPostconditionCodeV2,
    path: tuple[str, ...],
) -> FeeAllocationPostconditionRejectV2:
    return FeeAllocationPostconditionRejectV2(code, path)


def _exact_three_tuple_v2(
    name: str,
    value: object,
) -> tuple[object, ...] | FeeAllocationPostconditionRejectV2:
    if type(value) is not tuple:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.WRONG_EXACT_TYPE,
            (name,),
        )
    if len(value) != 3:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.WRONG_ARITY,
            (name,),
        )
    return cast(tuple[object, ...], value)


def _exact_three_int_tuple_v2(
    name: str,
    value: object,
    code: FeeAllocationPostconditionCodeV2,
) -> tuple[int, int, int] | FeeAllocationPostconditionRejectV2:
    exact = _exact_three_tuple_v2(name, value)
    if isinstance(exact, FeeAllocationPostconditionRejectV2):
        return exact
    if any(type(item) is not int for item in exact):
        return _reject_v2(code, (name,))
    return cast(tuple[int, int, int], exact)


def _fixed_role_order_v2() -> (
    tuple[str, str, str] | FeeAllocationPostconditionRejectV2
):
    if fcis_m6_profile_ids.FIXED_ROLE_ORDER_ID_V1 != EXPECTED_FIXED_ROLE_ORDER_ID_V2:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.INVALID_ROLE_ORDER,
            ("role_order_id",),
        )
    if fcis_m6_profile_ids.FIXED_ROLE_ORDER_V1 != EXPECTED_FIXED_ROLE_ORDER_V2:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.INVALID_ROLE_ORDER,
            ("role_order",),
        )
    return EXPECTED_FIXED_ROLE_ORDER_V2


def _expected_bonus_bits_v2(
    deficits: tuple[int, int, int],
    fractions: tuple[int, int, int],
    seat_count: int,
) -> tuple[int, int, int]:
    eligible = [index for index, fraction in enumerate(fractions) if fraction > 0]
    eligible.sort(
        key=lambda index: (-(deficits[index] + fractions[index]), index),
    )
    selected = tuple(eligible[:seat_count])
    return cast(
        tuple[int, int, int],
        tuple(1 if index in selected else 0 for index in range(3)),
    )


def revalidate_fee_allocation_postconditions_v2(
    *,
    amount: object,
    policy: object,
    fractions: object,
    bonuses: object,
    amounts: object,
    deficits_pre: object,
    deficits_post: object,
) -> FeeAllocationPostconditionResultV2:
    """Recompute and check every theorem postcondition before construction."""

    role_order = _fixed_role_order_v2()
    if isinstance(role_order, FeeAllocationPostconditionRejectV2):
        return role_order
    if type(policy) is not FeeDistributionPolicyV2:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.WRONG_EXACT_TYPE,
            ("policy",),
        )
    if type(amount) is not int or not 0 <= amount <= MAX_FEE_AMOUNT_V2:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.INVALID_AMOUNT,
            ("amount",),
        )
    exact_policy = cast(FeeDistributionPolicyV2, policy)
    weights = _exact_three_int_tuple_v2(
        "policy.weights",
        exact_policy.weights,
        FeeAllocationPostconditionCodeV2.INVALID_POLICY,
    )
    if isinstance(weights, FeeAllocationPostconditionRejectV2):
        return weights
    if any(not 0 <= weight <= BPS_DENOMINATOR_V2 for weight in weights):
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.INVALID_POLICY,
            ("policy", "weights"),
        )
    if sum(weights) != BPS_DENOMINATOR_V2:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.INVALID_POLICY,
            ("policy", "weights"),
        )

    exact_pre = _exact_three_int_tuple_v2(
        "deficits_pre",
        deficits_pre,
        FeeAllocationPostconditionCodeV2.INVALID_PRE_DEFICITS,
    )
    if isinstance(exact_pre, FeeAllocationPostconditionRejectV2):
        return exact_pre
    if any(
        not -BPS_DENOMINATOR_V2 < deficit < BPS_DENOMINATOR_V2
        for deficit in exact_pre
    ) or sum(exact_pre) != 0:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.INVALID_PRE_DEFICITS,
            ("deficits_pre",),
        )

    exact_fractions = _exact_three_int_tuple_v2(
        "fractions",
        fractions,
        FeeAllocationPostconditionCodeV2.INVALID_FRACTIONS,
    )
    if isinstance(exact_fractions, FeeAllocationPostconditionRejectV2):
        return exact_fractions
    if any(
        not 0 <= fraction < BPS_DENOMINATOR_V2 for fraction in exact_fractions
    ):
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.INVALID_FRACTIONS,
            ("fractions",),
        )

    exact_bonuses = _exact_three_int_tuple_v2(
        "bonuses",
        bonuses,
        FeeAllocationPostconditionCodeV2.INVALID_BONUSES,
    )
    if isinstance(exact_bonuses, FeeAllocationPostconditionRejectV2):
        return exact_bonuses
    if any(bonus not in (0, 1) for bonus in exact_bonuses):
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.INVALID_BONUSES,
            ("bonuses",),
        )

    exact_amounts = _exact_three_int_tuple_v2(
        "amounts",
        amounts,
        FeeAllocationPostconditionCodeV2.INVALID_AMOUNTS,
    )
    if isinstance(exact_amounts, FeeAllocationPostconditionRejectV2):
        return exact_amounts
    if any(
        not 0 <= role_amount <= MAX_FEE_AMOUNT_V2 for role_amount in exact_amounts
    ):
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.INVALID_AMOUNTS,
            ("amounts",),
        )

    exact_post = _exact_three_int_tuple_v2(
        "deficits_post",
        deficits_post,
        FeeAllocationPostconditionCodeV2.INVALID_POST_DEFICITS,
    )
    if isinstance(exact_post, FeeAllocationPostconditionRejectV2):
        return exact_post

    quota_results = tuple(
        compute_fee_quota_v2(
            amount=amount,
            weight=weight,
            denominator=BPS_DENOMINATOR_V2,
        )
        for weight in weights
    )
    if any(type(quota) is not FeeQuotaV2 for quota in quota_results):
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.QUOTA_RELATION,
            ("quotas",),
        )
    quotas = cast(tuple[FeeQuotaV2, FeeQuotaV2, FeeQuotaV2], quota_results)
    expected_fractions = tuple(quota.remainder for quota in quotas)
    if exact_fractions != expected_fractions:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.QUOTA_RELATION,
            ("fractions",),
        )

    seat_sum, seat_remainder = divmod(sum(exact_fractions), BPS_DENOMINATOR_V2)
    if seat_remainder != 0 or seat_sum not in (0, 1, 2):
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.BONUS_COUNT,
            ("fractions",),
        )
    if sum(exact_bonuses) != seat_sum:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.BONUS_COUNT,
            ("bonuses",),
        )

    for index, weight in enumerate(weights):
        if weight == 0 and (
            exact_fractions[index] != 0
            or exact_bonuses[index] != 0
            or exact_amounts[index] != 0
        ):
            return _reject_v2(
                FeeAllocationPostconditionCodeV2.ZERO_WEIGHT_SUPPORT,
                ("role", str(index)),
            )
    if any(
        bonus and fraction == 0
        for bonus, fraction in zip(exact_bonuses, exact_fractions, strict=True)
    ):
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.BONUS_SUPPORT,
            ("bonuses",),
        )

    expected_bonuses = _expected_bonus_bits_v2(
        exact_pre,
        exact_fractions,
        seat_sum,
    )
    if exact_bonuses != expected_bonuses:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.BONUS_ORDER,
            ("bonuses",),
        )
    expected_amounts = tuple(
        quota.base + bonus for quota, bonus in zip(quotas, exact_bonuses, strict=True)
    )
    if sum(exact_amounts) != amount:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.AMOUNT_CONSERVATION,
            ("amounts",),
        )
    if exact_amounts != expected_amounts:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.LOCAL_QUOTA,
            ("amounts",),
        )

    expected_post = tuple(
        pre + fraction - BPS_DENOMINATOR_V2 * bonus
        for pre, fraction, bonus in zip(
            exact_pre,
            exact_fractions,
            exact_bonuses,
            strict=True,
        )
    )
    if exact_post != expected_post:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.POST_DEFICIT_RECURRENCE,
            ("deficits_post",),
        )
    if sum(exact_post) != 0:
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.POST_DEFICIT_CONSERVATION,
            ("deficits_post",),
        )
    if any(
        not -BPS_DENOMINATOR_V2 < deficit < BPS_DENOMINATOR_V2
        for deficit in exact_post
    ):
        return _reject_v2(
            FeeAllocationPostconditionCodeV2.POST_DEFICIT_BOUND,
            ("deficits_post",),
        )
    return FeeAllocationPostconditionAcceptV2(role_order, seat_sum)


__all__ = (
    "EXPECTED_FIXED_ROLE_ORDER_ID_V2",
    "EXPECTED_FIXED_ROLE_ORDER_V2",
    "FeeAllocationPostconditionAcceptV2",
    "FeeAllocationPostconditionCodeV2",
    "FeeAllocationPostconditionRejectV2",
    "FeeAllocationPostconditionResultV2",
    "revalidate_fee_allocation_postconditions_v2",
)

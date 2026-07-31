"""Typed exact three-role SRGD bonus selection for the unmounted FCIS kernel."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import final

from .fcis_fee_apportionment_values import BPS_DENOMINATOR_V2
from .fcis_m6_profile_ids import FIXED_ROLE_ORDER_V1


class FeeBonusSelectorRejectCodeV2(Enum):
    """Stable rejection classes for the fixed three-role selector."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    WRONG_ARITY = "wrong_arity"
    INVALID_ROLE_ORDER = "invalid_role_order"
    INVALID_DENOMINATOR = "invalid_denominator"
    DEFICIT_OUT_OF_RANGE = "deficit_out_of_range"
    FRACTION_OUT_OF_RANGE = "fraction_out_of_range"
    NONDIVISIBLE_RESIDUALS = "nondivisible_residuals"
    INVALID_SEAT_COUNT = "invalid_seat_count"
    INSUFFICIENT_SUPPORT = "insufficient_support"
    INTERNAL_RELATION_FAILURE = "internal_relation_failure"


@final
@dataclass(frozen=True, slots=True)
class FeeBonusSelectionV2:
    """Validated bonus bits for exactly the reviewed three-role order."""

    deficits: tuple[int, int, int]
    fractions: tuple[int, int, int]
    denominator: int
    seat_count: int
    bonuses: tuple[int, int, int]

    def __post_init__(self) -> None:
        if FIXED_ROLE_ORDER_V1 != ("buyback", "treasury", "rewards"):
            raise ValueError("fee selector role order is not the reviewed order")
        if type(self.deficits) is not tuple or len(self.deficits) != 3:
            raise TypeError("fee selector deficits must be a three-tuple")
        if type(self.fractions) is not tuple or len(self.fractions) != 3:
            raise TypeError("fee selector fractions must be a three-tuple")
        if type(self.bonuses) is not tuple or len(self.bonuses) != 3:
            raise TypeError("fee selector bonuses must be a three-tuple")
        if any(type(value) is not int for value in self.deficits):
            raise TypeError("fee selector deficits must be exact integers")
        if any(type(value) is not int for value in self.fractions):
            raise TypeError("fee selector fractions must be exact integers")
        if type(self.denominator) is not int or self.denominator <= 0:
            raise ValueError("fee selector denominator must be positive")
        if any(
            not -self.denominator < value < self.denominator
            for value in self.deficits
        ):
            raise ValueError("fee selector deficit is outside its strict bound")
        if any(not 0 <= value < self.denominator for value in self.fractions):
            raise ValueError("fee selector fraction is outside its bound")
        if sum(self.fractions) % self.denominator != 0:
            raise ValueError("fee selector fractions are not divisible")
        if type(self.seat_count) is not int or self.seat_count not in (0, 1, 2):
            raise ValueError("fee selector seat count is outside {0,1,2}")
        if self.seat_count != sum(self.fractions) // self.denominator:
            raise ValueError("fee selector seat count is inconsistent")
        if any(type(value) is not int or value not in (0, 1) for value in self.bonuses):
            raise TypeError("fee selector bonuses must be exact bits")
        if sum(self.bonuses) != self.seat_count:
            raise ValueError("fee selector bonus count is inconsistent")
        if any(bonus and fraction == 0 for bonus, fraction in zip(self.bonuses, self.fractions, strict=True)):
            raise ValueError("fee selector bonus violates positive support")


@final
@dataclass(frozen=True, slots=True)
class FeeBonusSelectorRejectV2:
    """Typed fail-closed selector rejection."""

    code: FeeBonusSelectorRejectCodeV2
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not FeeBonusSelectorRejectCodeV2:
            raise TypeError("fee selector rejection code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("fee selector rejection path must be exact")


FeeBonusSelectorResultV2 = FeeBonusSelectionV2 | FeeBonusSelectorRejectV2


def _reject_v2(
    code: FeeBonusSelectorRejectCodeV2,
    path: tuple[str, ...],
) -> FeeBonusSelectorRejectV2:
    return FeeBonusSelectorRejectV2(code, path)


def select_fee_bonuses_v2(
    *,
    deficits: object,
    fractions: object,
    denominator: object = BPS_DENOMINATOR_V2,
) -> FeeBonusSelectorResultV2:
    """Select exactly ``h`` positive-support roles by score and fixed order."""

    if type(deficits) is not tuple:
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.WRONG_EXACT_TYPE,
            ("deficits",),
        )
    if type(fractions) is not tuple:
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.WRONG_EXACT_TYPE,
            ("fractions",),
        )
    if len(deficits) != 3:
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.WRONG_ARITY,
            ("deficits",),
        )
    if len(fractions) != 3:
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.WRONG_ARITY,
            ("fractions",),
        )
    if FIXED_ROLE_ORDER_V1 != ("buyback", "treasury", "rewards"):
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.INVALID_ROLE_ORDER,
            ("role_order",),
        )
    if type(denominator) is not int:
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.WRONG_EXACT_TYPE,
            ("denominator",),
        )
    if denominator <= 0:
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.INVALID_DENOMINATOR,
            ("denominator",),
        )
    exact_deficits = tuple(deficits)
    exact_fractions = tuple(fractions)
    if any(type(value) is not int for value in exact_deficits):
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.WRONG_EXACT_TYPE,
            ("deficits",),
        )
    if any(type(value) is not int for value in exact_fractions):
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.WRONG_EXACT_TYPE,
            ("fractions",),
        )
    typed_deficits = exact_deficits
    typed_fractions = exact_fractions
    if any(
        not -denominator < value < denominator for value in typed_deficits
    ):
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.DEFICIT_OUT_OF_RANGE,
            ("deficits",),
        )
    if any(not 0 <= value < denominator for value in typed_fractions):
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.FRACTION_OUT_OF_RANGE,
            ("fractions",),
        )
    residual_sum = sum(typed_fractions)
    if residual_sum % denominator != 0:
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.NONDIVISIBLE_RESIDUALS,
            ("fractions",),
        )
    seat_count = residual_sum // denominator
    if seat_count not in (0, 1, 2):
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.INVALID_SEAT_COUNT,
            ("seat_count",),
        )
    eligible = [index for index, fraction in enumerate(typed_fractions) if fraction > 0]
    if len(eligible) < seat_count:
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.INSUFFICIENT_SUPPORT,
            ("fractions",),
        )
    eligible.sort(
        key=lambda index: (-(typed_deficits[index] + typed_fractions[index]), index)
    )
    selected_indices = tuple(eligible[:seat_count])
    bonuses: tuple[int, int, int] = (
        1 if 0 in selected_indices else 0,
        1 if 1 in selected_indices else 0,
        1 if 2 in selected_indices else 0,
    )
    try:
        return FeeBonusSelectionV2(
            deficits=typed_deficits,
            fractions=typed_fractions,
            denominator=denominator,
            seat_count=seat_count,
            bonuses=bonuses,
        )
    except (TypeError, ValueError, ArithmeticError):
        return _reject_v2(
            FeeBonusSelectorRejectCodeV2.INTERNAL_RELATION_FAILURE,
            ("relation",),
        )


__all__ = (
    "FeeBonusSelectionV2",
    "FeeBonusSelectorRejectCodeV2",
    "FeeBonusSelectorRejectV2",
    "FeeBonusSelectorResultV2",
    "select_fee_bonuses_v2",
)

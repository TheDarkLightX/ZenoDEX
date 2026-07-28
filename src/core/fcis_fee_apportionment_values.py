"""Closed candidate values for the unmounted SRGD-v1 apportionment kernel."""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import final

from ..state.state_snapshot_values import (
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
)

FEE_APPORTIONMENT_SCHEMA_REVISION_V2 = "zenodex/fcis/fee-apportionment/v2"
FEE_APPORTIONMENT_KEY_SCHEMA_ID_V2 = "zenodex/fcis/fee-apportionment/key/v2"
FEE_AMOUNT_CANDIDATE_SCHEMA_ID_V2 = "zenodex/fcis/fee-apportionment/amount-candidate/v2"
FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_ID_V2 = "zenodex/fcis/fee-apportionment/amount-candidate-batch/v2"
FEE_DEFICIT_ENTRY_SCHEMA_ID_V2 = "zenodex/fcis/fee-apportionment/deficit-entry/v2"
COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2 = "zenodex/fcis/fee-apportionment/committed-state/v2"
FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2 = "zenodex/fcis/fee-distribution/policy/v2"
ASSET_FEE_ALLOCATION_SCHEMA_ID_V2 = "zenodex/fcis/fee-apportionment/asset-allocation/v2"
ASSET_FEE_ALLOCATION_BATCH_SCHEMA_ID_V2 = "zenodex/fcis/fee-apportionment/asset-allocation-batch/v2"
FEE_APPORTIONMENT_TRANSITION_RESULT_SCHEMA_ID_V2 = (
    "zenodex/fcis/fee-apportionment/transition-result/v2"
)

SRGD_ALGORITHM_VERSION_V1 = "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1"
BPS_DENOMINATOR_V2 = 10_000
MAX_FEE_AMOUNT_V2 = (1 << 256) - 1
MAX_FEE_AMOUNT_CANDIDATES_V2 = 256
MAX_FEE_APPORTIONMENT_KEYS_V2 = 50_000

_FEE_APPORTIONMENT_RESULT_TOKEN_V2 = object()


class FCISFeeApportionmentEnumTagV2(Enum):
    """This closed profile intentionally has no enum variants."""


class FCISFeeApportionmentRecordTagV2(Enum):
    KEY = "fee_apportionment_key_v2"
    AMOUNT_CANDIDATE = "fee_amount_candidate_v2"
    DEFICIT_ENTRY = "fee_deficit_entry_v2"
    COMMITTED_STATE = "committed_fee_apportionment_state_v2"
    DISTRIBUTION_POLICY = "fee_distribution_policy_v2"


class FeeApportionmentTransitionCodeV2(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    ITEM_LIMIT = "item_limit"
    NONCANONICAL_IDENTIFIER = "noncanonical_identifier"
    AMOUNT_OUT_OF_RANGE = "amount_out_of_range"
    INVALID_POLICY = "invalid_policy"
    INVALID_PRESTATE = "invalid_prestate"
    AGGREGATE_OVERFLOW = "aggregate_overflow"
    INTERNAL_RELATION_FAILURE = "internal_relation_failure"


@final
@dataclass(frozen=True, slots=True)
class FeeApportionmentKeySourceV2:
    fee_distribution_domain_id: object
    asset: object


@final
@dataclass(frozen=True, slots=True)
class FeeAmountCandidateSourceV2:
    key: object
    amount: object


@final
@dataclass(frozen=True, slots=True)
class FeeDeficitEntrySourceV2:
    key: object
    deficit_buyback: object
    deficit_treasury: object


@final
@dataclass(frozen=True, slots=True)
class CommittedFeeApportionmentStateSourceV2:
    algorithm_version: object
    entries: object


@final
@dataclass(frozen=True, slots=True)
class FeeDistributionPolicySourceV2:
    buyback_bps: object
    treasury_bps: object
    rewards_bps: object
    buyback_destination: object
    treasury_destination: object
    rewards_destination: object


def _require_text_v2(name: str, value: object) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be an exact nonempty string")
    if len(value) > MAX_STATE_STRING_CHARACTERS_V1:
        raise ValueError(f"{name} exceeds its character bound")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValueError(f"{name} must contain Unicode scalar values") from exc
    if len(encoded) > MAX_STATE_STRING_UTF8_BYTES_V1:
        raise ValueError(f"{name} exceeds its UTF-8 bound")
    return value


def _require_exact_int_v2(name: str, value: object) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    return value


def _require_u256_v2(name: str, value: object) -> int:
    exact = _require_exact_int_v2(name, value)
    if not 0 <= exact <= MAX_FEE_AMOUNT_V2:
        raise ValueError(f"{name} must be in the U256 domain")
    return exact


def _require_deficit_v2(name: str, value: object) -> int:
    exact = _require_exact_int_v2(name, value)
    if not -BPS_DENOMINATOR_V2 < exact < BPS_DENOMINATOR_V2:
        raise ValueError(f"{name} must be strictly inside the deficit bound")
    return exact


@final
@dataclass(frozen=True, slots=True)
class FeeApportionmentKeyV2:
    fee_distribution_domain_id: str
    asset: str

    def __post_init__(self) -> None:
        _require_text_v2(
            "fee distribution domain identifier",
            self.fee_distribution_domain_id,
        )
        _require_text_v2("fee apportionment asset", self.asset)

    @property
    def protocol_order_key(self) -> tuple[bytes, bytes]:
        return (
            self.fee_distribution_domain_id.encode("utf-8"),
            self.asset.encode("utf-8"),
        )


@final
@dataclass(frozen=True, slots=True)
class FeeAmountCandidateV2:
    key: FeeApportionmentKeyV2
    amount: int

    def __post_init__(self) -> None:
        if type(self.key) is not FeeApportionmentKeyV2:
            raise TypeError("fee amount candidate key must be exact")
        self.key.__post_init__()
        _require_u256_v2("fee amount candidate amount", self.amount)


@final
@dataclass(frozen=True, slots=True)
class FeeDeficitEntryV2:
    key: FeeApportionmentKeyV2
    deficit_buyback: int
    deficit_treasury: int

    def __post_init__(self) -> None:
        if type(self.key) is not FeeApportionmentKeyV2:
            raise TypeError("fee deficit key must be exact")
        self.key.__post_init__()
        _require_deficit_v2("buyback deficit", self.deficit_buyback)
        _require_deficit_v2("treasury deficit", self.deficit_treasury)
        _require_deficit_v2("rewards deficit", self.deficit_rewards)
        if self.deficits == (0, 0, 0):
            raise ValueError("all-zero fee deficit entries are noncanonical")

    @property
    def deficit_rewards(self) -> int:
        return -self.deficit_buyback - self.deficit_treasury

    @property
    def deficits(self) -> tuple[int, int, int]:
        return (
            self.deficit_buyback,
            self.deficit_treasury,
            self.deficit_rewards,
        )


def _validate_state_entries_v2(entries: object) -> None:
    if type(entries) is not tuple:
        raise TypeError("fee apportionment entries must be an exact tuple")
    if len(entries) > MAX_FEE_APPORTIONMENT_KEYS_V2:
        raise ValueError("fee apportionment state entry limit exceeded")
    previous: tuple[bytes, bytes] | None = None
    for entry in entries:
        if type(entry) is not FeeDeficitEntryV2:
            raise TypeError("fee apportionment state entries must be exact")
        entry.__post_init__()
        current = entry.key.protocol_order_key
        if previous is not None and previous >= current:
            raise ValueError("fee apportionment entries must be in strict protocol order")
        previous = current


@final
@dataclass(frozen=True, slots=True)
class CommittedFeeApportionmentStateV2:
    """Canonical candidate state; authority requires later provenance checks."""

    algorithm_version: str
    entries: tuple[FeeDeficitEntryV2, ...]

    def __post_init__(self) -> None:
        if type(self.algorithm_version) is not str:
            raise TypeError("fee apportionment algorithm version must be exact")
        if self.algorithm_version != SRGD_ALGORITHM_VERSION_V1:
            raise ValueError("unsupported fee apportionment algorithm version")
        _validate_state_entries_v2(self.entries)


@final
@dataclass(frozen=True, slots=True)
class FeeDistributionPolicyV2:
    buyback_bps: int
    treasury_bps: int
    rewards_bps: int
    buyback_destination: str
    treasury_destination: str
    rewards_destination: str

    def __post_init__(self) -> None:
        weights = self.weights
        for role, weight in zip(
            ("buyback", "treasury", "rewards"),
            weights,
            strict=True,
        ):
            exact = _require_exact_int_v2(f"{role} weight", weight)
            if not 0 <= exact <= BPS_DENOMINATOR_V2:
                raise ValueError(f"{role} weight must be in the BPS domain")
        if sum(weights) != BPS_DENOMINATOR_V2:
            raise ValueError("fee distribution weights must sum to 10000")
        for role, destination in zip(
            ("buyback", "treasury", "rewards"),
            self.destinations,
            strict=True,
        ):
            _require_text_v2(f"{role} destination", destination)

    @property
    def weights(self) -> tuple[int, int, int]:
        return self.buyback_bps, self.treasury_bps, self.rewards_bps

    @property
    def destinations(self) -> tuple[str, str, str]:
        return (
            self.buyback_destination,
            self.treasury_destination,
            self.rewards_destination,
        )


@final
@dataclass(frozen=True, slots=True)
class AssetFeeAllocationV2:
    """Evidence for one accepted arithmetic allocation; never an effect."""

    key: FeeApportionmentKeyV2
    amount: int
    buyback_destination: str
    treasury_destination: str
    rewards_destination: str
    buyback_fraction: int
    treasury_fraction: int
    rewards_fraction: int
    buyback_bonus: int
    treasury_bonus: int
    rewards_bonus: int
    buyback_amount: int
    treasury_amount: int
    rewards_amount: int
    deficit_buyback_pre: int
    deficit_treasury_pre: int
    deficit_rewards_pre: int
    deficit_buyback_post: int
    deficit_treasury_post: int
    deficit_rewards_post: int
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _FEE_APPORTIONMENT_RESULT_TOKEN_V2:
            raise TypeError("fee allocation evidence requires controlled derivation")
        self._revalidate()

    def _revalidate(self) -> None:
        if type(self.key) is not FeeApportionmentKeyV2:
            raise TypeError("fee allocation key must be exact")
        self.key.__post_init__()
        _require_u256_v2("fee allocation input amount", self.amount)
        for role, destination in zip(
            ("buyback", "treasury", "rewards"),
            self.destinations,
            strict=True,
        ):
            _require_text_v2(f"{role} allocation destination", destination)
        for fraction in self.fractions:
            exact = _require_exact_int_v2("fee allocation fraction", fraction)
            if not 0 <= exact < BPS_DENOMINATOR_V2:
                raise ValueError("fee allocation fraction is outside [0,10000)")
        for bonus, fraction in zip(self.bonuses, self.fractions, strict=True):
            if type(bonus) is not int or bonus not in (0, 1):
                raise TypeError("fee allocation bonus must be an exact bit")
            if bonus and fraction == 0:
                raise ValueError("fee allocation bonus violates positive support")
        for amount in self.amounts:
            _require_u256_v2("fee allocation role amount", amount)
        if sum(self.amounts) != self.amount:
            raise ValueError("fee allocation does not conserve its input amount")
        for deficit in self.deficits_pre + self.deficits_post:
            _require_deficit_v2("fee allocation deficit", deficit)
        if sum(self.deficits_pre) != 0 or sum(self.deficits_post) != 0:
            raise ValueError("fee allocation deficits must sum to zero")

    @property
    def destinations(self) -> tuple[str, str, str]:
        return (
            self.buyback_destination,
            self.treasury_destination,
            self.rewards_destination,
        )

    @property
    def fractions(self) -> tuple[int, int, int]:
        return (
            self.buyback_fraction,
            self.treasury_fraction,
            self.rewards_fraction,
        )

    @property
    def bonuses(self) -> tuple[int, int, int]:
        return self.buyback_bonus, self.treasury_bonus, self.rewards_bonus

    @property
    def amounts(self) -> tuple[int, int, int]:
        return self.buyback_amount, self.treasury_amount, self.rewards_amount

    @property
    def deficits_pre(self) -> tuple[int, int, int]:
        return (
            self.deficit_buyback_pre,
            self.deficit_treasury_pre,
            self.deficit_rewards_pre,
        )

    @property
    def deficits_post(self) -> tuple[int, int, int]:
        return (
            self.deficit_buyback_post,
            self.deficit_treasury_post,
            self.deficit_rewards_post,
        )


def _validate_allocations_v2(allocations: object) -> None:
    if type(allocations) is not tuple:
        raise TypeError("fee allocations must be an exact tuple")
    if len(allocations) > MAX_FEE_APPORTIONMENT_KEYS_V2:
        raise ValueError("fee allocation count exceeds its bound")
    previous: tuple[bytes, bytes] | None = None
    for allocation in allocations:
        if type(allocation) is not AssetFeeAllocationV2:
            raise TypeError("fee allocations must contain exact values")
        allocation._revalidate()
        current = allocation.key.protocol_order_key
        if previous is not None and previous >= current:
            raise ValueError("fee allocations must be in strict protocol order")
        previous = current


@final
@dataclass(frozen=True, slots=True)
class FeeApportionmentTransitionOkV2:
    state: CommittedFeeApportionmentStateV2
    allocations: tuple[AssetFeeAllocationV2, ...]
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _FEE_APPORTIONMENT_RESULT_TOKEN_V2:
            raise TypeError("fee apportionment result requires controlled derivation")
        self._revalidate()

    def _revalidate(self) -> None:
        if type(self.state) is not CommittedFeeApportionmentStateV2:
            raise TypeError("fee apportionment successor must be exact")
        self.state.__post_init__()
        _validate_allocations_v2(self.allocations)


@final
@dataclass(frozen=True, slots=True)
class FeeApportionmentTransitionRejectV2:
    code: FeeApportionmentTransitionCodeV2
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not FeeApportionmentTransitionCodeV2:
            raise TypeError("fee apportionment reject code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("fee apportionment reject path must be exact")


FeeApportionmentTransitionResultV2 = (
    FeeApportionmentTransitionOkV2 | FeeApportionmentTransitionRejectV2
)


def _asset_fee_allocation_v2(
    *,
    key: FeeApportionmentKeyV2,
    amount: int,
    destinations: tuple[str, str, str],
    fractions: tuple[int, int, int],
    bonuses: tuple[int, int, int],
    amounts: tuple[int, int, int],
    deficits_pre: tuple[int, int, int],
    deficits_post: tuple[int, int, int],
) -> AssetFeeAllocationV2:
    return AssetFeeAllocationV2(
        key,
        amount,
        *destinations,
        *fractions,
        *bonuses,
        *amounts,
        *deficits_pre,
        *deficits_post,
        _FEE_APPORTIONMENT_RESULT_TOKEN_V2,
    )


def _fee_apportionment_ok_v2(
    *,
    state: CommittedFeeApportionmentStateV2,
    allocations: tuple[AssetFeeAllocationV2, ...],
) -> FeeApportionmentTransitionOkV2:
    return FeeApportionmentTransitionOkV2(
        state,
        allocations,
        _FEE_APPORTIONMENT_RESULT_TOKEN_V2,
    )


__all__ = (
    "ASSET_FEE_ALLOCATION_BATCH_SCHEMA_ID_V2",
    "ASSET_FEE_ALLOCATION_SCHEMA_ID_V2",
    "AssetFeeAllocationV2",
    "BPS_DENOMINATOR_V2",
    "COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2",
    "CommittedFeeApportionmentStateSourceV2",
    "CommittedFeeApportionmentStateV2",
    "FCISFeeApportionmentEnumTagV2",
    "FCISFeeApportionmentRecordTagV2",
    "FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_ID_V2",
    "FEE_AMOUNT_CANDIDATE_SCHEMA_ID_V2",
    "FEE_APPORTIONMENT_KEY_SCHEMA_ID_V2",
    "FEE_APPORTIONMENT_SCHEMA_REVISION_V2",
    "FEE_APPORTIONMENT_TRANSITION_RESULT_SCHEMA_ID_V2",
    "FEE_DEFICIT_ENTRY_SCHEMA_ID_V2",
    "FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2",
    "FeeAmountCandidateSourceV2",
    "FeeAmountCandidateV2",
    "FeeApportionmentKeySourceV2",
    "FeeApportionmentKeyV2",
    "FeeApportionmentTransitionCodeV2",
    "FeeApportionmentTransitionOkV2",
    "FeeApportionmentTransitionRejectV2",
    "FeeApportionmentTransitionResultV2",
    "FeeDeficitEntrySourceV2",
    "FeeDeficitEntryV2",
    "FeeDistributionPolicySourceV2",
    "FeeDistributionPolicyV2",
    "MAX_FEE_AMOUNT_CANDIDATES_V2",
    "MAX_FEE_AMOUNT_V2",
    "MAX_FEE_APPORTIONMENT_KEYS_V2",
    "SRGD_ALGORITHM_VERSION_V1",
)

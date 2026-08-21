"""Closed immutable values for the experimental ZDEX hyperdeflation core."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_settlement_types_v1 import (
    _require_atoms_u128,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_global_v1,
)

# 10^38 fits in u128 while 10^39 does not.
MAX_DECIMAL_SCALE_STEP_V1: Final = 38
MAX_ZDEX_PROJECTION_BUCKETS_V1: Final = 1024


class ZDEXBurnRejectCodeV1(str, Enum):
    POLICY_MISMATCH = "POLICY_MISMATCH"
    STATE_OUTSIDE_POLICY = "STATE_OUTSIDE_POLICY"
    STALE_STATE = "STALE_STATE"
    PRECISION_EPOCH_MISMATCH = "PRECISION_EPOCH_MISMATCH"
    BURN_BUDGET_EPOCH_MISMATCH = "BURN_BUDGET_EPOCH_MISMATCH"
    PURCHASE_BINDING_MISMATCH = "PURCHASE_BINDING_MISMATCH"
    SOURCE_BUCKET_UNKNOWN = "SOURCE_BUCKET_UNKNOWN"
    ZERO_PURCHASE = "ZERO_PURCHASE"
    PRECISION_RESCALE_REQUIRED = "PRECISION_RESCALE_REQUIRED"
    SOURCE_RESERVE_FLOOR_REACHED = "SOURCE_RESERVE_FLOOR_REACHED"
    EPOCH_BURN_CAP_REACHED = "EPOCH_BURN_CAP_REACHED"
    ROUTE_OUTPUT_CAP_ZERO = "ROUTE_OUTPUT_CAP_ZERO"
    PURCHASE_EXCEEDS_BURN_CAPACITY = "PURCHASE_EXCEEDS_BURN_CAPACITY"


class ZDEXPrecisionRejectCodeV1(str, Enum):
    POLICY_MISMATCH = "POLICY_MISMATCH"
    STALE_STATE = "STALE_STATE"
    PRECISION_EPOCH_MISMATCH = "PRECISION_EPOCH_MISMATCH"
    ZERO_DECIMAL_STEP = "ZERO_DECIMAL_STEP"
    DECIMAL_STEP_EXCEEDS_POLICY = "DECIMAL_STEP_EXCEEDS_POLICY"
    MAXIMUM_DECIMALS_EXCEEDED = "MAXIMUM_DECIMALS_EXCEEDED"
    EPOCH_COUNTER_EXHAUSTED = "EPOCH_COUNTER_EXHAUSTED"
    ATOM_OVERFLOW = "ATOM_OVERFLOW"


@dataclass(frozen=True, slots=True)
class ZDEXHyperdeflationPolicyV1:
    """Dimensionless contraction policy and bounded precision envelope."""

    asset_id: str
    retained_numerator: int
    retained_denominator: int
    maximum_decimals: int
    maximum_decimal_step: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_root(self.asset_id, name="ZDEX policy asset id")
        numerator = _require_nonnegative_int(
            self.retained_numerator,
            name="ZDEX retained numerator",
        )
        denominator = _require_nonnegative_int(
            self.retained_denominator,
            name="ZDEX retained denominator",
        )
        if numerator == 0 or denominator == 0 or numerator >= denominator:
            raise ValueError(
                "ZDEX retained fraction must satisfy 0 < numerator < denominator"
            )
        _require_nonnegative_int(
            self.maximum_decimals,
            name="ZDEX maximum decimals",
        )
        maximum_step = _require_nonnegative_int(
            self.maximum_decimal_step,
            name="ZDEX maximum decimal step",
        )
        if maximum_step == 0 or maximum_step > MAX_DECIMAL_SCALE_STEP_V1:
            raise ValueError(
                f"ZDEX maximum decimal step must be in 1..{MAX_DECIMAL_SCALE_STEP_V1}"
            )

    @property
    def policy_root(self) -> str:
        self.validate()
        return hash_global_v1("zdex-hyperdeflation-policy-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset_id": self.asset_id,
            "retained_numerator": self.retained_numerator,
            "retained_denominator": self.retained_denominator,
            "maximum_decimals": self.maximum_decimals,
            "maximum_decimal_step": self.maximum_decimal_step,
        }


@dataclass(frozen=True, slots=True, order=True)
class ZDEXAmountBucketV1:
    """One committed live ZDEX amount bucket in the current precision epoch."""

    bucket_id: str
    amount_atoms: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_token(self.bucket_id, name="ZDEX bucket id")
        _require_atoms_u128(self.amount_atoms, name="ZDEX bucket amount")
        if self.amount_atoms == 0:
            raise ValueError("ZDEX state must omit zero amount buckets")

    def to_canonical(self) -> dict[str, object]:
        return {"bucket_id": self.bucket_id, "amount_atoms": self.amount_atoms}


@dataclass(frozen=True, slots=True)
class ZDEXSupplyStateV1:
    """Immutable, canonically ordered live ZDEX amount projection."""

    asset_id: str
    policy_root: str
    decimals: int
    precision_epoch: int
    live_supply_atoms: int
    buckets: tuple[ZDEXAmountBucketV1, ...]
    burn_budget_epoch: int = 0
    remaining_epoch_burn_cap_atoms: int = 0

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_root(self.asset_id, name="ZDEX state asset id")
        _require_root(self.policy_root, name="ZDEX state policy root")
        _require_nonnegative_int(self.decimals, name="ZDEX state decimals")
        _require_nonnegative_int(self.precision_epoch, name="ZDEX precision epoch")
        _require_nonnegative_int(self.burn_budget_epoch, name="ZDEX burn budget epoch")
        _require_atoms_u128(self.live_supply_atoms, name="ZDEX live supply")
        _require_atoms_u128(
            self.remaining_epoch_burn_cap_atoms,
            name="ZDEX committed remaining epoch burn cap",
        )
        if self.live_supply_atoms == 0:
            raise ValueError("ZDEX live supply must be positive")
        if type(self.buckets) is not tuple or not self.buckets:
            raise ValueError("ZDEX state requires a nonempty bucket tuple")
        if len(self.buckets) > MAX_ZDEX_PROJECTION_BUCKETS_V1:
            raise ValueError("ZDEX state bucket projection exceeds the V1 bound")
        if any(type(bucket) is not ZDEXAmountBucketV1 for bucket in self.buckets):
            raise TypeError(
                "ZDEX state buckets must be exact ZDEXAmountBucketV1 values"
            )
        for bucket in self.buckets:
            bucket.validate()
        bucket_ids = tuple(bucket.bucket_id for bucket in self.buckets)
        if bucket_ids != tuple(sorted(bucket_ids)) or len(set(bucket_ids)) != len(
            bucket_ids
        ):
            raise ValueError("ZDEX state buckets must be uniquely ordered by bucket_id")
        if sum(bucket.amount_atoms for bucket in self.buckets) != self.live_supply_atoms:
            raise ValueError("ZDEX live bucket sum must equal live supply")

    @property
    def state_root(self) -> str:
        self.validate()
        return hash_global_v1("zdex-supply-state-v1", self.to_canonical())

    def bucket_atoms(self, bucket_id: str) -> int | None:
        _require_token(bucket_id, name="ZDEX bucket lookup id")
        for bucket in self.buckets:
            if bucket.bucket_id == bucket_id:
                return bucket.amount_atoms
        return None

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset_id": self.asset_id,
            "policy_root": self.policy_root,
            "decimals": self.decimals,
            "precision_epoch": self.precision_epoch,
            "live_supply_atoms": self.live_supply_atoms,
            "buckets": self.buckets,
            "burn_budget_epoch": self.burn_budget_epoch,
            "remaining_epoch_burn_cap_atoms": self.remaining_epoch_burn_cap_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXBurnRouteContextV1:
    """Verifier-supplied route bindings and limits in current-epoch atoms."""

    route_release_id: str
    policy_root: str
    purchase_occurrence_root: str
    burn_source_bucket_id: str
    purchased_zdex_atoms: int
    source_reserve_floor_atoms: int
    remaining_epoch_burn_cap_atoms: int
    route_safe_output_cap_atoms: int
    burn_budget_epoch: int = 0

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_root(self.route_release_id, name="ZDEX burn route release id")
        _require_root(self.policy_root, name="ZDEX burn route policy root")
        _require_root(
            self.purchase_occurrence_root,
            name="ZDEX purchase occurrence root",
        )
        _require_token(
            self.burn_source_bucket_id,
            name="ZDEX route burn source bucket",
        )
        _require_atoms_u128(
            self.purchased_zdex_atoms,
            name="ZDEX route purchased amount",
        )
        if self.purchased_zdex_atoms == 0:
            raise ValueError("ZDEX route purchased amount must be positive")
        _require_atoms_u128(
            self.source_reserve_floor_atoms,
            name="ZDEX source reserve floor",
        )
        _require_atoms_u128(
            self.remaining_epoch_burn_cap_atoms,
            name="ZDEX remaining epoch burn cap",
        )
        _require_atoms_u128(
            self.route_safe_output_cap_atoms,
            name="ZDEX route safe output cap",
        )
        _require_nonnegative_int(
            self.burn_budget_epoch,
            name="ZDEX route burn budget epoch",
        )


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseAndBurnCommandV1:
    expected_pre_state_root: str
    expected_precision_epoch: int
    expected_purchase_occurrence_root: str
    source_bucket_id: str
    purchased_zdex_atoms: int

    def __post_init__(self) -> None:
        _require_root(self.expected_pre_state_root, name="ZDEX burn expected pre-state")
        _require_nonnegative_int(
            self.expected_precision_epoch,
            name="ZDEX burn expected precision epoch",
        )
        _require_root(
            self.expected_purchase_occurrence_root,
            name="ZDEX burn expected purchase occurrence",
        )
        _require_token(self.source_bucket_id, name="ZDEX burn source bucket id")
        _require_atoms_u128(self.purchased_zdex_atoms, name="purchased ZDEX atoms")


@dataclass(frozen=True, slots=True)
class ZDEXBurnCapacityV1:
    retained_supply_atoms: int
    ratio_headroom_atoms: int
    source_headroom_atoms: int
    epoch_headroom_atoms: int
    route_headroom_atoms: int
    maximum_burn_atoms: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        values = (
            self.retained_supply_atoms,
            self.ratio_headroom_atoms,
            self.source_headroom_atoms,
            self.epoch_headroom_atoms,
            self.route_headroom_atoms,
            self.maximum_burn_atoms,
        )
        for value in values:
            _require_atoms_u128(value, name="ZDEX burn capacity amount")
        if self.retained_supply_atoms == 0:
            raise ValueError("ZDEX retained supply capacity must be positive")
        expected = min(
            self.ratio_headroom_atoms,
            self.source_headroom_atoms,
            self.epoch_headroom_atoms,
            self.route_headroom_atoms,
        )
        if self.maximum_burn_atoms != expected:
            raise ValueError("ZDEX maximum burn must equal the minimum headroom")


@dataclass(frozen=True, slots=True)
class ZDEXBurnEffectV1:
    purchase_occurrence_root: str
    source_bucket_id: str
    source_debit_atoms: int
    authorized_burn_atoms: int
    authorized_issue_atoms: int = 0

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_root(
            self.purchase_occurrence_root,
            name="ZDEX burn effect purchase occurrence",
        )
        _require_token(self.source_bucket_id, name="ZDEX burn effect source bucket")
        _require_atoms_u128(self.source_debit_atoms, name="ZDEX burn source debit")
        _require_atoms_u128(self.authorized_burn_atoms, name="ZDEX authorized burn")
        _require_atoms_u128(self.authorized_issue_atoms, name="ZDEX authorized issue")
        if self.source_debit_atoms == 0:
            raise ValueError("ZDEX accepted burn effect must be nonzero")
        if self.source_debit_atoms != self.authorized_burn_atoms:
            raise ValueError("ZDEX purchase debit must equal authorized burn")
        if self.authorized_issue_atoms != 0:
            raise ValueError("ZDEX hyperdeflation burn cannot authorize issuance")


@dataclass(frozen=True, slots=True)
class ZDEXPrecisionRescaleCommandV1:
    expected_pre_state_root: str
    expected_precision_epoch: int
    additional_decimals: int

    def __post_init__(self) -> None:
        _require_root(self.expected_pre_state_root, name="ZDEX rescale expected pre-state")
        _require_nonnegative_int(
            self.expected_precision_epoch,
            name="ZDEX rescale expected precision epoch",
        )
        _require_nonnegative_int(
            self.additional_decimals,
            name="ZDEX additional decimals",
        )


@dataclass(frozen=True, slots=True, order=True)
class ZDEXBucketScaleV1:
    bucket_id: str
    before_atoms: int
    after_atoms: int

    def __post_init__(self) -> None:
        _require_token(self.bucket_id, name="ZDEX scaled bucket id")
        _require_atoms_u128(self.before_atoms, name="ZDEX scaled bucket before")
        _require_atoms_u128(self.after_atoms, name="ZDEX scaled bucket after")


@dataclass(frozen=True, slots=True)
class ZDEXPrecisionEffectV1:
    scale_factor: int
    supply_before_atoms: int
    supply_after_atoms: int
    bucket_scales: tuple[ZDEXBucketScaleV1, ...]
    authorized_issue_atoms: int = 0
    authorized_burn_atoms: int = 0
    burn_budget_remaining_before_atoms: int = 0
    burn_budget_remaining_after_atoms: int = 0

    def __post_init__(self) -> None:
        _require_atoms_u128(self.scale_factor, name="ZDEX precision scale factor")
        _require_atoms_u128(
            self.supply_before_atoms,
            name="ZDEX precision supply before",
        )
        _require_atoms_u128(
            self.supply_after_atoms,
            name="ZDEX precision supply after",
        )
        _require_atoms_u128(
            self.burn_budget_remaining_before_atoms,
            name="ZDEX precision burn budget before",
        )
        _require_atoms_u128(
            self.burn_budget_remaining_after_atoms,
            name="ZDEX precision burn budget after",
        )
        if self.scale_factor <= 1:
            raise ValueError("ZDEX precision scale factor must exceed one")
        if self.supply_after_atoms != self.supply_before_atoms * self.scale_factor:
            raise ValueError("ZDEX precision supply was not scaled exactly")
        if type(self.bucket_scales) is not tuple or not self.bucket_scales:
            raise ValueError("ZDEX precision effect requires bucket scales")
        if len(self.bucket_scales) > MAX_ZDEX_PROJECTION_BUCKETS_V1:
            raise ValueError("ZDEX precision bucket projection exceeds the V1 bound")
        if any(type(row) is not ZDEXBucketScaleV1 for row in self.bucket_scales):
            raise TypeError("ZDEX precision effect bucket scales are not closed")
        bucket_ids = tuple(row.bucket_id for row in self.bucket_scales)
        if bucket_ids != tuple(sorted(bucket_ids)) or len(set(bucket_ids)) != len(
            bucket_ids
        ):
            raise ValueError("ZDEX precision bucket scales must be uniquely ordered")
        for row in self.bucket_scales:
            if row.after_atoms != row.before_atoms * self.scale_factor:
                raise ValueError("ZDEX precision bucket was not scaled exactly")
        if sum(row.before_atoms for row in self.bucket_scales) != self.supply_before_atoms:
            raise ValueError("ZDEX precision before buckets do not sum to supply")
        if sum(row.after_atoms for row in self.bucket_scales) != self.supply_after_atoms:
            raise ValueError("ZDEX precision after buckets do not sum to supply")
        if (
            self.burn_budget_remaining_after_atoms
            != self.burn_budget_remaining_before_atoms * self.scale_factor
        ):
            raise ValueError("ZDEX precision burn budget was not scaled exactly")
        if self.authorized_issue_atoms != 0 or self.authorized_burn_atoms != 0:
            raise ValueError("ZDEX precision rescale cannot authorize issue or burn")


__all__ = [
    "MAX_DECIMAL_SCALE_STEP_V1",
    "MAX_ZDEX_PROJECTION_BUCKETS_V1",
    "ZDEXAmountBucketV1",
    "ZDEXBucketScaleV1",
    "ZDEXBurnCapacityV1",
    "ZDEXBurnEffectV1",
    "ZDEXBurnRejectCodeV1",
    "ZDEXBurnRouteContextV1",
    "ZDEXHyperdeflationPolicyV1",
    "ZDEXPrecisionEffectV1",
    "ZDEXPrecisionRejectCodeV1",
    "ZDEXPrecisionRescaleCommandV1",
    "ZDEXPurchaseAndBurnCommandV1",
    "ZDEXSupplyStateV1",
]

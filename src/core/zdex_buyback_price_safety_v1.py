"""Integer-only price envelope for a governed ZDEX buyback purchase.

The envelope is curve-agnostic.  It compares the authenticated reserve ratio,
Oracle ratio, and realized execution ratio with exact cross multiplication.
All intermediate arithmetic is bounded to unsigned 128-bit values so the
Python reference and Rust core reject the same overflow surface.

This pure SHADOW core selects no production parameters, authenticates no
Oracle, verifies no receipt, and grants no value-moving authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from .global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    MAX_U64_V1,
    _require_atoms_u128,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_global_v1,
)

ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1: Final = (
    "zenodex/zdex-buyback-price-safety-policy/v1"
)
ZDEX_BUYBACK_PRICE_SAFETY_OBSERVATION_SCHEMA_V1: Final = (
    "zenodex/zdex-buyback-price-safety-observation/v1"
)
ZDEX_BUYBACK_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1: Final = (
    "zenodex/zdex-buyback-oracle-price-occurrence/v1"
)
ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1: Final = (
    "zdex_buyback_price_safety_v1"
)
BASIS_POINTS_V1: Final = 10_000
_VERIFIED_PRICE_SAFETY_TOKEN_V1 = object()


class ZDEXBuybackPriceSafetyRejectCodeV1(str, Enum):
    HEIGHT_REGRESSION = "HEIGHT_REGRESSION"
    STALE_ORACLE = "STALE_ORACLE"
    INSUFFICIENT_DEPTH = "INSUFFICIENT_DEPTH"
    ARITHMETIC_OVERFLOW = "ARITHMETIC_OVERFLOW"
    POOL_ORACLE_DEVIATION = "POOL_ORACLE_DEVIATION"
    EXECUTION_IMPACT = "EXECUTION_IMPACT"
    ORACLE_EXECUTION_DEVIATION = "ORACLE_EXECUTION_DEVIATION"
    DERIVED_LIMIT_MISMATCH = "DERIVED_LIMIT_MISMATCH"
    QUOTE_LIMIT_EXCEEDED = "QUOTE_LIMIT_EXCEEDED"
    DERIVED_MINIMUM_OUTPUT_MISMATCH = "DERIVED_MINIMUM_OUTPUT_MISMATCH"
    MINIMUM_OUTPUT_NOT_MET = "MINIMUM_OUTPUT_NOT_MET"
    OUTPUT_EXCEEDS_RESERVE = "OUTPUT_EXCEEDS_RESERVE"


@dataclass(frozen=True, slots=True)
class ZDEXBuybackOraclePriceOccurrenceV1:
    oracle_id: str
    quote_asset_id: str
    zdex_asset_id: str
    quote_numerator_atoms: int
    zdex_denominator_atoms: int
    observed_height: int

    def __post_init__(self) -> None:
        if type(self.oracle_id) is not str:
            raise TypeError("ZDEX buyback Oracle price id must be exact str")
        _require_token(self.oracle_id, name="ZDEX buyback Oracle price id")
        for name in ("quote_asset_id", "zdex_asset_id"):
            value = getattr(self, name)
            if type(value) is not str:
                raise TypeError(f"ZDEX buyback Oracle price {name} must be exact str")
            _require_root(value, name=f"ZDEX buyback Oracle price {name}")
        if self.quote_asset_id == self.zdex_asset_id:
            raise ValueError("ZDEX buyback Oracle price assets must differ")
        for name in ("quote_numerator_atoms", "zdex_denominator_atoms"):
            value = _require_atoms_u128(
                getattr(self, name),
                name=f"ZDEX buyback Oracle price {name}",
            )
            if value == 0:
                raise ValueError(f"ZDEX buyback Oracle price {name} must be positive")
        if type(self.observed_height) is not int or not 0 <= self.observed_height <= MAX_U64_V1:
            raise ValueError("ZDEX buyback Oracle price observed height must fit unsigned 64-bit")

    @property
    def occurrence_root(self) -> str:
        return hash_global_v1(
            "zdex-buyback-oracle-price-occurrence-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_BUYBACK_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1,
            "oracle_id": self.oracle_id,
            "quote_asset_id": self.quote_asset_id,
            "zdex_asset_id": self.zdex_asset_id,
            "quote_numerator_atoms": self.quote_numerator_atoms,
            "zdex_denominator_atoms": self.zdex_denominator_atoms,
            "observed_height": self.observed_height,
        }


@dataclass(frozen=True, slots=True)
class ZDEXBuybackPriceSafetyPolicyV1:
    oracle_id: str
    maximum_oracle_age_blocks: int
    minimum_quote_reserve_atoms: int
    minimum_zdex_reserve_atoms: int
    maximum_pool_oracle_deviation_bps: int
    maximum_execution_impact_bps: int
    maximum_oracle_execution_deviation_bps: int
    maximum_quote_reserve_spend_bps: int

    def __post_init__(self) -> None:
        if type(self.oracle_id) is not str:
            raise TypeError("ZDEX buyback price-safety Oracle id must be exact str")
        _require_token(self.oracle_id, name="ZDEX buyback price-safety Oracle id")
        _require_nonnegative_int(
            self.maximum_oracle_age_blocks,
            name="ZDEX buyback maximum Oracle age",
        )
        for name in (
            "minimum_quote_reserve_atoms",
            "minimum_zdex_reserve_atoms",
        ):
            value = _require_atoms_u128(
                getattr(self, name),
                name=f"ZDEX buyback {name}",
            )
            if value == 0:
                raise ValueError(f"ZDEX buyback {name} must be positive")
        for name in (
            "maximum_pool_oracle_deviation_bps",
            "maximum_execution_impact_bps",
            "maximum_oracle_execution_deviation_bps",
        ):
            value = _require_nonnegative_int(
                getattr(self, name),
                name=f"ZDEX buyback {name}",
            )
            if value >= BASIS_POINTS_V1:
                raise ValueError(f"ZDEX buyback {name} must be below 10000")
        spend_bps = _require_nonnegative_int(
            self.maximum_quote_reserve_spend_bps,
            name="ZDEX buyback maximum quote reserve spend bps",
        )
        if not 0 < spend_bps <= BASIS_POINTS_V1:
            raise ValueError(
                "ZDEX buyback maximum quote reserve spend bps must be in 1..10000"
            )

    @property
    def policy_root(self) -> str:
        return hash_global_v1(
            "zdex-buyback-price-safety-policy-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1,
            "oracle_id": self.oracle_id,
            "maximum_oracle_age_blocks": self.maximum_oracle_age_blocks,
            "minimum_quote_reserve_atoms": self.minimum_quote_reserve_atoms,
            "minimum_zdex_reserve_atoms": self.minimum_zdex_reserve_atoms,
            "maximum_pool_oracle_deviation_bps": self.maximum_pool_oracle_deviation_bps,
            "maximum_execution_impact_bps": self.maximum_execution_impact_bps,
            "maximum_oracle_execution_deviation_bps": self.maximum_oracle_execution_deviation_bps,
            "maximum_quote_reserve_spend_bps": self.maximum_quote_reserve_spend_bps,
        }


@dataclass(frozen=True, slots=True)
class ZDEXBuybackPriceSafetyObservationV1:
    oracle_occurrence_root: str
    current_height: int
    oracle_observed_height: int
    oracle_quote_numerator_atoms: int
    oracle_zdex_denominator_atoms: int
    quote_reserve_atoms: int
    zdex_reserve_atoms: int
    quote_amount_in_atoms: int
    purchased_zdex_atoms: int
    claimed_route_safe_quote_limit_atoms: int
    claimed_minimum_output_atoms: int

    def __post_init__(self) -> None:
        if type(self.oracle_occurrence_root) is not str:
            raise TypeError("ZDEX buyback Oracle occurrence root must be exact str")
        _require_root(
            self.oracle_occurrence_root,
            name="ZDEX buyback Oracle occurrence root",
        )
        for name in ("current_height", "oracle_observed_height"):
            value = getattr(self, name)
            if type(value) is not int or not 0 <= value <= MAX_U64_V1:
                raise ValueError(f"ZDEX buyback {name} must fit unsigned 64-bit")
        for name in (
            "oracle_quote_numerator_atoms",
            "oracle_zdex_denominator_atoms",
            "quote_reserve_atoms",
            "zdex_reserve_atoms",
            "quote_amount_in_atoms",
            "purchased_zdex_atoms",
            "claimed_route_safe_quote_limit_atoms",
            "claimed_minimum_output_atoms",
        ):
            value = _require_atoms_u128(
                getattr(self, name),
                name=f"ZDEX buyback price-safety {name}",
            )
            if value == 0:
                raise ValueError(f"ZDEX buyback price-safety {name} must be positive")
        if (
            self.quote_amount_in_atoms > MAX_DELTA_ATOMS_V1
            or self.purchased_zdex_atoms > MAX_DELTA_ATOMS_V1
        ):
            raise ValueError("ZDEX buyback execution amounts must fit signed effects")

    @property
    def observation_root(self) -> str:
        return hash_global_v1(
            "zdex-buyback-price-safety-observation-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_BUYBACK_PRICE_SAFETY_OBSERVATION_SCHEMA_V1,
            "oracle_occurrence_root": self.oracle_occurrence_root,
            "current_height": self.current_height,
            "oracle_observed_height": self.oracle_observed_height,
            "oracle_quote_numerator_atoms": self.oracle_quote_numerator_atoms,
            "oracle_zdex_denominator_atoms": self.oracle_zdex_denominator_atoms,
            "quote_reserve_atoms": self.quote_reserve_atoms,
            "zdex_reserve_atoms": self.zdex_reserve_atoms,
            "quote_amount_in_atoms": self.quote_amount_in_atoms,
            "purchased_zdex_atoms": self.purchased_zdex_atoms,
            "claimed_route_safe_quote_limit_atoms": (
                self.claimed_route_safe_quote_limit_atoms
            ),
            "claimed_minimum_output_atoms": self.claimed_minimum_output_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXBuybackPriceSafetyRejectedV1:
    code: ZDEXBuybackPriceSafetyRejectCodeV1

    def __post_init__(self) -> None:
        if type(self.code) is not ZDEXBuybackPriceSafetyRejectCodeV1:
            raise TypeError("ZDEX buyback price-safety reject code is not closed")


@dataclass(frozen=True, slots=True)
class _VerifiedZDEXBuybackPriceSafetyFieldsV1:
    policy: ZDEXBuybackPriceSafetyPolicyV1
    observation: ZDEXBuybackPriceSafetyObservationV1
    route_safe_quote_limit_atoms: int
    minimum_output_atoms: int


class VerifiedZDEXBuybackPriceSafetyV1:
    """Opaque witness for one deterministic price-envelope acceptance."""

    _fields: _VerifiedZDEXBuybackPriceSafetyFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        fields: _VerifiedZDEXBuybackPriceSafetyFieldsV1,
    ) -> None:
        if token is not _VERIFIED_PRICE_SAFETY_TOKEN_V1:
            raise TypeError("VerifiedZDEXBuybackPriceSafetyV1 is core-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedZDEXBuybackPriceSafetyV1 is immutable")

    @property
    def policy_root(self) -> str:
        return self._fields.policy.policy_root

    @property
    def observation_root(self) -> str:
        return self._fields.observation.observation_root

    @property
    def route_safe_quote_limit_atoms(self) -> int:
        return self._fields.route_safe_quote_limit_atoms

    @property
    def minimum_output_atoms(self) -> int:
        return self._fields.minimum_output_atoms

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "verified-zdex-buyback-price-safety-v1",
            {
                "policy_root": self.policy_root,
                "observation_root": self.observation_root,
                "route_safe_quote_limit_atoms": self.route_safe_quote_limit_atoms,
                "minimum_output_atoms": self.minimum_output_atoms,
            },
        )


ZDEXBuybackPriceSafetyResultV1: TypeAlias = (
    VerifiedZDEXBuybackPriceSafetyV1 | ZDEXBuybackPriceSafetyRejectedV1
)


def _checked_product_v1(*values: int) -> int | None:
    product = 1
    for value in values:
        if value != 0 and product > MAX_ATOMS_V1 // value:
            return None
        product *= value
    return product


def _ceil_div_v1(numerator: int, denominator: int) -> int:
    return numerator // denominator + int(numerator % denominator != 0)


def verify_zdex_buyback_price_safety_v1(
    policy: ZDEXBuybackPriceSafetyPolicyV1,
    observation: ZDEXBuybackPriceSafetyObservationV1,
) -> ZDEXBuybackPriceSafetyResultV1:
    """Verify one bounded price envelope using exact integer inequalities."""

    if type(policy) is not ZDEXBuybackPriceSafetyPolicyV1:
        raise TypeError("ZDEX buyback price-safety policy must be exact typed data")
    if type(observation) is not ZDEXBuybackPriceSafetyObservationV1:
        raise TypeError("ZDEX buyback price-safety observation must be exact typed data")
    if observation.current_height < observation.oracle_observed_height:
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.HEIGHT_REGRESSION
        )
    if (
        observation.current_height - observation.oracle_observed_height
        > policy.maximum_oracle_age_blocks
    ):
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.STALE_ORACLE
        )
    if (
        observation.quote_reserve_atoms < policy.minimum_quote_reserve_atoms
        or observation.zdex_reserve_atoms < policy.minimum_zdex_reserve_atoms
    ):
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.INSUFFICIENT_DEPTH
        )
    if observation.purchased_zdex_atoms > observation.zdex_reserve_atoms:
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.OUTPUT_EXCEEDS_RESERVE
        )
    products = (
        _checked_product_v1(
            observation.quote_reserve_atoms,
            observation.oracle_zdex_denominator_atoms,
        ),
        _checked_product_v1(
            observation.zdex_reserve_atoms,
            observation.oracle_quote_numerator_atoms,
        ),
        _checked_product_v1(
            observation.quote_reserve_atoms,
            policy.maximum_quote_reserve_spend_bps,
        ),
        _checked_product_v1(
            observation.quote_amount_in_atoms,
            observation.oracle_zdex_denominator_atoms,
            BASIS_POINTS_V1,
        ),
        _checked_product_v1(
            observation.oracle_quote_numerator_atoms,
            BASIS_POINTS_V1 + policy.maximum_oracle_execution_deviation_bps,
        ),
        _checked_product_v1(
            observation.quote_amount_in_atoms,
            observation.zdex_reserve_atoms,
            BASIS_POINTS_V1,
        ),
        _checked_product_v1(
            observation.purchased_zdex_atoms,
            observation.quote_reserve_atoms,
            BASIS_POINTS_V1 + policy.maximum_execution_impact_bps,
        ),
        _checked_product_v1(
            observation.purchased_zdex_atoms,
            observation.oracle_quote_numerator_atoms,
            BASIS_POINTS_V1 + policy.maximum_oracle_execution_deviation_bps,
        ),
    )
    if any(value is None for value in products):
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.ARITHMETIC_OVERFLOW
        )
    exact_products = cast(tuple[int, ...], products)
    (
        pool_price_numerator,
        oracle_pool_numerator,
        safe_limit_product,
        minimum_output_numerator,
        minimum_output_denominator,
        execution_impact_lhs,
        execution_impact_rhs,
        oracle_execution_rhs,
    ) = exact_products
    route_safe_limit = min(
        safe_limit_product // BASIS_POINTS_V1,
        MAX_DELTA_ATOMS_V1,
    )
    minimum_output = _ceil_div_v1(
        minimum_output_numerator,
        minimum_output_denominator,
    )
    if (
        route_safe_limit == 0
        or observation.claimed_route_safe_quote_limit_atoms != route_safe_limit
    ):
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.DERIVED_LIMIT_MISMATCH
        )
    if observation.quote_amount_in_atoms > route_safe_limit:
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.QUOTE_LIMIT_EXCEEDED
        )
    if observation.claimed_minimum_output_atoms != minimum_output:
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.DERIVED_MINIMUM_OUTPUT_MISMATCH
        )
    if observation.purchased_zdex_atoms < minimum_output:
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.MINIMUM_OUTPUT_NOT_MET
        )
    pool_deviation_lhs = _checked_product_v1(
        abs(pool_price_numerator - oracle_pool_numerator),
        BASIS_POINTS_V1,
    )
    pool_deviation_rhs = _checked_product_v1(
        oracle_pool_numerator,
        policy.maximum_pool_oracle_deviation_bps,
    )
    if pool_deviation_lhs is None or pool_deviation_rhs is None:
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.ARITHMETIC_OVERFLOW
        )
    if pool_deviation_lhs > pool_deviation_rhs:
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.POOL_ORACLE_DEVIATION
        )
    if execution_impact_lhs > execution_impact_rhs:
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.EXECUTION_IMPACT
        )
    if minimum_output_numerator > oracle_execution_rhs:
        return ZDEXBuybackPriceSafetyRejectedV1(
            ZDEXBuybackPriceSafetyRejectCodeV1.ORACLE_EXECUTION_DEVIATION
        )
    return VerifiedZDEXBuybackPriceSafetyV1(
        _VERIFIED_PRICE_SAFETY_TOKEN_V1,
        _VerifiedZDEXBuybackPriceSafetyFieldsV1(
            policy,
            observation,
            route_safe_limit,
            minimum_output,
        ),
    )


__all__ = [
    "BASIS_POINTS_V1",
    "ZDEX_BUYBACK_PRICE_SAFETY_OBSERVATION_SCHEMA_V1",
    "ZDEX_BUYBACK_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1",
    "ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1",
    "ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1",
    "VerifiedZDEXBuybackPriceSafetyV1",
    "ZDEXBuybackOraclePriceOccurrenceV1",
    "ZDEXBuybackPriceSafetyObservationV1",
    "ZDEXBuybackPriceSafetyPolicyV1",
    "ZDEXBuybackPriceSafetyRejectCodeV1",
    "ZDEXBuybackPriceSafetyRejectedV1",
    "ZDEXBuybackPriceSafetyResultV1",
    "verify_zdex_buyback_price_safety_v1",
]

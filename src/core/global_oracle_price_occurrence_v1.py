"""Typed price payload binding for finalized GlobalSettlementABI occurrences.

The generic global Oracle table commits an occurrence root and finality facts.
This module proves that one exact, bounded price payload hashes to that root.
The resulting opaque witness grants no release, proof, route-composition,
settlement, or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from threading import Lock
from typing import Final
from weakref import WeakKeyDictionary

from .global_oracle_occurrence_authority_v1 import (
    GlobalOracleOccurrenceAuthorityV1,
)
from .global_settlement_types_v1 import (
    _require_atoms_u128,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_global_v1,
)

GLOBAL_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1: Final = (
    "zenodex/global-oracle-price-occurrence/v1"
)
VERIFIED_GLOBAL_ORACLE_PRICE_SCHEMA_V1: Final = (
    "zenodex/verified-global-oracle-price/v1"
)
_VERIFIED_PRICE_TOKEN = object()


@dataclass(frozen=True, slots=True)
class GlobalOraclePriceOccurrenceV1:
    oracle_id: str
    market_id: str
    base_asset: str
    quote_asset: str
    price_e8: int
    observed_height: int

    def __post_init__(self) -> None:
        for name, value in (
            ("oracle id", self.oracle_id),
            ("market id", self.market_id),
            ("base asset", self.base_asset),
            ("quote asset", self.quote_asset),
        ):
            if type(value) is not str:
                raise TypeError(f"global Oracle price {name} must be exact text")
            _require_token(value, name=f"global Oracle price {name}")
        if self.base_asset == self.quote_asset:
            raise ValueError("global Oracle price assets must be distinct")
        if type(self.price_e8) is not int:
            raise TypeError("global Oracle price must be an exact int")
        _require_atoms_u128(self.price_e8, name="global Oracle price e8")
        if self.price_e8 == 0:
            raise ValueError("global Oracle price must be positive")
        if type(self.observed_height) is not int:
            raise TypeError("global Oracle price observed height must be an exact int")
        _require_nonnegative_int(
            self.observed_height,
            name="global Oracle price observed height",
        )

    @property
    def occurrence_root(self) -> str:
        return hash_global_v1(
            "global-oracle-price-occurrence-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1,
            "oracle_id": self.oracle_id,
            "market_id": self.market_id,
            "base_asset": self.base_asset,
            "quote_asset": self.quote_asset,
            "price_e8": self.price_e8,
            "observed_height": self.observed_height,
        }


@dataclass(frozen=True, slots=True)
class _VerifiedPriceFieldsV1:
    oracle_authority_root: str
    pre_state_root: str
    route_release_id: str
    command_occurrence_id: str
    policy_root: str
    oracle_id: str
    occurrence_root: str
    observed_height: int
    market_id: str
    base_asset: str
    quote_asset: str
    price_e8: int


class VerifiedGlobalOraclePriceV1:
    """Data-slot-free handle for checker-owned typed price authority."""

    __slots__ = ("__weakref__",)

    def __init__(self, token: object, fields: object) -> None:
        if token is not _VERIFIED_PRICE_TOKEN or type(fields) is not _VerifiedPriceFieldsV1:
            raise TypeError("VerifiedGlobalOraclePriceV1 is checker-constructed")
        _register_verified_price_v1(self, fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedGlobalOraclePriceV1 is immutable")

    @property
    def oracle_authority_root(self) -> str:
        return _verified_price_fields_v1(self).oracle_authority_root

    @property
    def pre_state_root(self) -> str:
        return _verified_price_fields_v1(self).pre_state_root

    @property
    def route_release_id(self) -> str:
        return _verified_price_fields_v1(self).route_release_id

    @property
    def command_occurrence_id(self) -> str:
        return _verified_price_fields_v1(self).command_occurrence_id

    @property
    def policy_root(self) -> str:
        return _verified_price_fields_v1(self).policy_root

    @property
    def oracle_id(self) -> str:
        return _verified_price_fields_v1(self).oracle_id

    @property
    def occurrence_root(self) -> str:
        return _verified_price_fields_v1(self).occurrence_root

    @property
    def observed_height(self) -> int:
        return _verified_price_fields_v1(self).observed_height

    @property
    def market_id(self) -> str:
        return _verified_price_fields_v1(self).market_id

    @property
    def base_asset(self) -> str:
        return _verified_price_fields_v1(self).base_asset

    @property
    def quote_asset(self) -> str:
        return _verified_price_fields_v1(self).quote_asset

    @property
    def price_e8(self) -> int:
        return _verified_price_fields_v1(self).price_e8

    @property
    def binding_root(self) -> str:
        fields = _verified_price_fields_v1(self)
        return hash_global_v1(
            "verified-global-oracle-price-v1",
            {
                "schema": VERIFIED_GLOBAL_ORACLE_PRICE_SCHEMA_V1,
                "oracle_authority_root": fields.oracle_authority_root,
                "pre_state_root": fields.pre_state_root,
                "route_release_id": fields.route_release_id,
                "command_occurrence_id": fields.command_occurrence_id,
                "policy_root": fields.policy_root,
                "oracle_id": fields.oracle_id,
                "occurrence_root": fields.occurrence_root,
                "observed_height": fields.observed_height,
                "market_id": fields.market_id,
                "base_asset": fields.base_asset,
                "quote_asset": fields.quote_asset,
                "price_e8": fields.price_e8,
            },
        )


_VERIFIED_PRICE_LOCK_V1 = Lock()
_VERIFIED_PRICES_V1: WeakKeyDictionary[
    VerifiedGlobalOraclePriceV1,
    _VerifiedPriceFieldsV1,
] = WeakKeyDictionary()


def _snapshot_price_occurrence_v1(
    payload: GlobalOraclePriceOccurrenceV1,
) -> GlobalOraclePriceOccurrenceV1:
    if type(payload) is not GlobalOraclePriceOccurrenceV1:
        raise TypeError("global Oracle price payload must be exact typed data")
    return replace(payload)


def _snapshot_verified_price_fields_v1(
    fields: _VerifiedPriceFieldsV1,
) -> _VerifiedPriceFieldsV1:
    if type(fields) is not _VerifiedPriceFieldsV1:
        raise TypeError("verified global Oracle price fields must be exact typed data")
    for name, value in (
        ("authority root", fields.oracle_authority_root),
        ("pre-state root", fields.pre_state_root),
        ("route release id", fields.route_release_id),
        ("command occurrence id", fields.command_occurrence_id),
        ("policy root", fields.policy_root),
        ("occurrence root", fields.occurrence_root),
    ):
        if type(value) is not str:
            raise TypeError(f"verified global Oracle price {name} must be exact text")
        _require_root(value, name=f"verified global Oracle price {name}")
    GlobalOraclePriceOccurrenceV1(
        oracle_id=fields.oracle_id,
        market_id=fields.market_id,
        base_asset=fields.base_asset,
        quote_asset=fields.quote_asset,
        price_e8=fields.price_e8,
        observed_height=fields.observed_height,
    )
    return replace(fields)


def _register_verified_price_v1(
    verified: VerifiedGlobalOraclePriceV1,
    fields: _VerifiedPriceFieldsV1,
) -> None:
    owned = _snapshot_verified_price_fields_v1(fields)
    with _VERIFIED_PRICE_LOCK_V1:
        if verified in _VERIFIED_PRICES_V1:
            raise RuntimeError("verified global Oracle price is already registered")
        _VERIFIED_PRICES_V1[verified] = owned


def _verified_price_fields_v1(
    verified: VerifiedGlobalOraclePriceV1,
) -> _VerifiedPriceFieldsV1:
    if type(verified) is not VerifiedGlobalOraclePriceV1:
        raise TypeError("verified global Oracle price type is not closed")
    with _VERIFIED_PRICE_LOCK_V1:
        fields = _VERIFIED_PRICES_V1.get(verified)
    if fields is None:
        raise TypeError("verified global Oracle price is not checker-registered")
    return _snapshot_verified_price_fields_v1(fields)


def verify_global_oracle_price_occurrence_v1(
    authority: GlobalOracleOccurrenceAuthorityV1,
    payload: GlobalOraclePriceOccurrenceV1,
) -> VerifiedGlobalOraclePriceV1:
    """Bind an exact typed price payload to one finalized occurrence witness."""

    if type(authority) is not GlobalOracleOccurrenceAuthorityV1:
        raise TypeError("global Oracle occurrence authority must be exact typed data")
    owned = _snapshot_price_occurrence_v1(payload)
    if owned.oracle_id != authority.oracle_id:
        raise ValueError("global Oracle price oracle id mismatch")
    if owned.observed_height != authority.observed_height:
        raise ValueError("global Oracle price observed height mismatch")
    if owned.occurrence_root != authority.occurrence_root:
        raise ValueError("global Oracle price occurrence root mismatch")
    return VerifiedGlobalOraclePriceV1(
        _VERIFIED_PRICE_TOKEN,
        _VerifiedPriceFieldsV1(
            oracle_authority_root=authority.authority_root,
            pre_state_root=authority.pre_state_root,
            route_release_id=authority.route_release_id,
            command_occurrence_id=authority.command_occurrence_id,
            policy_root=authority.policy_root,
            oracle_id=owned.oracle_id,
            occurrence_root=owned.occurrence_root,
            observed_height=owned.observed_height,
            market_id=owned.market_id,
            base_asset=owned.base_asset,
            quote_asset=owned.quote_asset,
            price_e8=owned.price_e8,
        ),
    )


__all__ = [
    "GLOBAL_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1",
    "VERIFIED_GLOBAL_ORACLE_PRICE_SCHEMA_V1",
    "GlobalOraclePriceOccurrenceV1",
    "VerifiedGlobalOraclePriceV1",
    "verify_global_oracle_price_occurrence_v1",
]

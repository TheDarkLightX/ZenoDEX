"""Closed route-leg and pool-fingerprint child schemas for FCIS route binding.

This leaf module owns the route-specific primitive and child schemas admitted
through ``INTENT_SCHEMA_V1``.  Dependency direction is acyclic:
``snapshot_combinators`` + ``domain_limits`` -> this module -> ``intent_schema``.
It must never import the intent schema, intent snapshots, intents, or any route
runtime module.
"""

from __future__ import annotations

from ..core.domain_limits import DEX_SWAP_AMOUNT_MAX
from .snapshot_combinators import (
    DeclaredFieldV1,
    ExactInt,
    ExactKeyedMap,
    ExactString,
    MapOf,
    SequenceOf,
    SequenceSourceKind,
    StringRuleV1,
)

ROUTE_LEGS_MAX_V1 = 256
ROUTE_POOL_FINGERPRINTS_MAX_V1 = 256

ROUTE_LEG_SCHEMA_ID_V1 = "zenodex/fcis/authority/route-leg/v1"
ROUTE_POOL_FINGERPRINTS_SCHEMA_ID_V1 = "zenodex/fcis/authority/route-pool-fingerprints/v1"

ROUTE_TEXT_256_V1 = ExactString(StringRuleV1.NON_EMPTY, 1_024, max_characters=256)
ROUTE_HASH_32_V1 = ExactString(
    StringRuleV1.LOWERCASE_0X_HEX,
    66,
    exact_utf8_bytes=66,
    max_characters=66,
)

_LEG_AMOUNT_SCHEMA_V1 = ExactInt(1, DEX_SWAP_AMOUNT_MAX)

ROUTE_LEG_SCHEMA_V1 = ExactKeyedMap(
    (
        DeclaredFieldV1("amount_in", _LEG_AMOUNT_SCHEMA_V1),
        DeclaredFieldV1("amount_out", _LEG_AMOUNT_SCHEMA_V1),
        DeclaredFieldV1("asset_in", ROUTE_TEXT_256_V1),
        DeclaredFieldV1("asset_out", ROUTE_TEXT_256_V1),
        DeclaredFieldV1("pool_id", ROUTE_TEXT_256_V1),
    ),
    ROUTE_LEG_SCHEMA_ID_V1,
    ("amount_in", "amount_out", "asset_in", "asset_out", "pool_id"),
)
ROUTE_LEGS_SCHEMA_V1 = SequenceOf(
    (SequenceSourceKind.EXACT_LIST, SequenceSourceKind.EXACT_TUPLE),
    ROUTE_LEG_SCHEMA_V1,
    1,
    ROUTE_LEGS_MAX_V1,
)
ROUTE_POOL_FINGERPRINTS_SCHEMA_V1 = MapOf(
    ROUTE_TEXT_256_V1,
    ROUTE_HASH_32_V1,
    ROUTE_POOL_FINGERPRINTS_MAX_V1,
    ROUTE_POOL_FINGERPRINTS_SCHEMA_ID_V1,
)

__all__ = (
    "ROUTE_HASH_32_V1",
    "ROUTE_LEGS_MAX_V1",
    "ROUTE_LEGS_SCHEMA_V1",
    "ROUTE_LEG_SCHEMA_ID_V1",
    "ROUTE_LEG_SCHEMA_V1",
    "ROUTE_POOL_FINGERPRINTS_MAX_V1",
    "ROUTE_POOL_FINGERPRINTS_SCHEMA_ID_V1",
    "ROUTE_POOL_FINGERPRINTS_SCHEMA_V1",
    "ROUTE_TEXT_256_V1",
)

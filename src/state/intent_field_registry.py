"""Dependency-light exhaustive field-name registry for mounted DEX intents."""

from __future__ import annotations

from .intents import IntentKind

INTENT_COMMON_FIELD_NAMES_V1 = (
    "nonce",
    "recipient",
    "submission_order",
    "quote_receipt_hash",
    "quote_pool_fingerprint",
    "quote_receipt_leg_index",
    "oracle_authorization",
)

INTENT_KIND_FIELD_NAMES_V1 = (
    (
        IntentKind.CREATE_POOL,
        (
            "asset0",
            "asset1",
            "fee_bps",
            "amount0",
            "amount1",
            "created_at",
            "curve_tag",
            "curve_params",
        ),
    ),
    (
        IntentKind.ADD_LIQUIDITY,
        (
            "pool_id",
            "amount0_desired",
            "amount1_desired",
            "amount0_min",
            "amount1_min",
        ),
    ),
    (
        IntentKind.REMOVE_LIQUIDITY,
        ("pool_id", "lp_amount", "amount0_min", "amount1_min"),
    ),
    (
        IntentKind.SWAP_EXACT_IN,
        ("pool_id", "asset_in", "asset_out", "amount_in", "min_amount_out"),
    ),
    (
        IntentKind.SWAP_EXACT_OUT,
        ("pool_id", "asset_in", "asset_out", "amount_out", "max_amount_in"),
    ),
    (
        IntentKind.ROUTE_EXACT_IN,
        (
            "asset_in",
            "asset_out",
            "leg_indices",
            "total_amount_in",
            "total_min_amount_out",
            "route_legs",
            "route_pool_fingerprints",
        ),
    ),
    (
        IntentKind.ROUTE_EXACT_OUT,
        (
            "asset_in",
            "asset_out",
            "leg_indices",
            "total_amount_out",
            "total_max_amount_in",
            "route_legs",
            "route_pool_fingerprints",
        ),
    ),
)

INTENT_KIND_REQUIRED_FIELD_NAMES_V1 = (
    (IntentKind.CREATE_POOL, ("asset0", "asset1", "fee_bps", "amount0", "amount1")),
    (
        IntentKind.ADD_LIQUIDITY,
        ("pool_id", "amount0_desired", "amount1_desired", "amount0_min", "amount1_min"),
    ),
    (IntentKind.REMOVE_LIQUIDITY, ("pool_id", "lp_amount", "amount0_min", "amount1_min")),
    (
        IntentKind.SWAP_EXACT_IN,
        ("pool_id", "asset_in", "asset_out", "amount_in", "min_amount_out"),
    ),
    (
        IntentKind.SWAP_EXACT_OUT,
        ("pool_id", "asset_in", "asset_out", "amount_out", "max_amount_in"),
    ),
    (
        IntentKind.ROUTE_EXACT_IN,
        ("asset_in", "asset_out", "leg_indices", "total_amount_in", "total_min_amount_out"),
    ),
    (
        IntentKind.ROUTE_EXACT_OUT,
        ("asset_in", "asset_out", "leg_indices", "total_amount_out", "total_max_amount_in"),
    ),
)


def _kind_entry(
    registry: tuple[tuple[IntentKind, tuple[str, ...]], ...],
    kind: IntentKind,
) -> tuple[str, ...]:
    if type(kind) is not IntentKind:
        raise TypeError("intent kind must be exact IntentKind")
    for registered_kind, names in registry:
        if registered_kind is kind:
            return names
    raise ValueError("intent kind registry drift")


def intent_allowed_field_names_v1(kind: IntentKind) -> tuple[str, ...]:
    """Return common and kind-specific fields in mounted protocol order."""

    return INTENT_COMMON_FIELD_NAMES_V1 + _kind_entry(INTENT_KIND_FIELD_NAMES_V1, kind)


def intent_required_field_names_v1(kind: IntentKind) -> tuple[str, ...]:
    """Return required kind-specific fields in mounted protocol order."""

    return _kind_entry(INTENT_KIND_REQUIRED_FIELD_NAMES_V1, kind)

"""Shared fail-closed domain bounds for consensus-critical core paths.

These constants must stay aligned with the authoritative kernel specs:
- ``src/kernels/dex/cpmm_swap_v8.yaml``
- ``src/kernels/dex/lp_mint_v7.yaml``
- ``src/kernels/dex/lp_ratio_calculator_v7.yaml``
- ``src/kernels/dex/perp_epoch_isolated_v3.yaml``
"""

from typing import TypeGuard

DEX_POOL_RESERVE_MAX = 3_000_000_000
DEX_SWAP_AMOUNT_MAX = 3_000_000_000
DEX_LP_AMOUNT_MAX = 1_000_000_000
DEX_LP_SUPPLY_MAX = 3_000_000_000

PERP_PARAM_AMOUNT_MAX = 1_000_000_000_000
PERP_PRICE_E8_MAX = 10_000_000_000_000
PERP_ADVANCE_EPOCH_DELTA_MAX = 10_000
PERP_POSITION_MAX = 1_000_000
PERP_RATE_BPS_MAX = 10_000


def is_strict_int(value: object) -> TypeGuard[int]:
    return isinstance(value, int) and not isinstance(value, bool)


def require_int_range(
    name: str,
    value: object,
    *,
    minimum: int | None = None,
    maximum: int | None = None,
) -> int:
    if not is_strict_int(value):
        raise TypeError(f"{name} must be an int")
    value_int = value
    if minimum is not None and value_int < minimum:
        raise ValueError(f"{name} must be >= {minimum}: {value_int}")
    if maximum is not None and value_int > maximum:
        raise ValueError(f"{name} exceeds kernel domain max {maximum}: {value_int}")
    return value_int

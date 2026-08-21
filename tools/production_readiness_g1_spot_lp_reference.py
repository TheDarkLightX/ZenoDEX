"""Independent integer reference vectors for the inactive G1 Spot/LP candidate."""

from __future__ import annotations

import math
from collections.abc import Mapping
from typing import Any

SWAP_FEE_BPS = 30
PROTOCOL_FEE_SHARE_BPS = 0
BPS_DENOMINATOR = 10_000
MAX_POOL_ATOMS = (1 << 64) - 1


def _ceil_div(numerator: int, denominator: int) -> int:
    if numerator < 0 or denominator <= 0:
        raise ValueError("invalid non-negative ceiling division")
    return numerator // denominator + int(numerator % denominator != 0)


def _pool(
    reserve0: int,
    reserve1: int,
    supply: int,
    status: str = "ACTIVE",
) -> dict[str, Any]:
    return {
        "reserve0_atoms": reserve0,
        "reserve1_atoms": reserve1,
        "lp_supply_atoms": supply,
        "status": status,
    }


def _reference_exact_in(
    reserve_in: int,
    reserve_out: int,
    gross_input: int,
) -> dict[str, int]:
    fee = _ceil_div(gross_input * SWAP_FEE_BPS, BPS_DENOMINATOR)
    net_input = gross_input - fee
    output = reserve_out * net_input // (reserve_in + net_input)
    post_in = reserve_in + gross_input
    post_out = reserve_out - output
    return {
        "gross_input_atoms": gross_input,
        "fee_atoms": fee,
        "net_input_atoms": net_input,
        "output_atoms": output,
        "post_reserve_in_atoms": post_in,
        "post_reserve_out_atoms": post_out,
        "k_before": reserve_in * reserve_out,
        "k_after": post_in * post_out,
    }


def _reference_exact_out(
    reserve_in: int,
    reserve_out: int,
    requested_output: int,
) -> dict[str, int]:
    net_required = _ceil_div(
        reserve_in * requested_output,
        reserve_out - requested_output,
    )
    required_input = _ceil_div(
        net_required * BPS_DENOMINATOR,
        BPS_DENOMINATOR - SWAP_FEE_BPS,
    )
    exact_in = _reference_exact_in(reserve_in, reserve_out, required_input)
    post_out = reserve_out - requested_output
    return {
        "requested_output_atoms": requested_output,
        "required_input_atoms": required_input,
        "fee_atoms": exact_in["fee_atoms"],
        "net_input_atoms": exact_in["net_input_atoms"],
        "quoted_output_atoms": exact_in["output_atoms"],
        "pool_retained_output_atoms": exact_in["output_atoms"] - requested_output,
        "post_reserve_in_atoms": exact_in["post_reserve_in_atoms"],
        "post_reserve_out_atoms": post_out,
        "k_before": reserve_in * reserve_out,
        "k_after": exact_in["post_reserve_in_atoms"] * post_out,
    }


def _reference_create(amount0: int, amount1: int) -> dict[str, Any]:
    minted = math.isqrt(amount0 * amount1)
    return {
        "lp_minted_atoms": minted,
        "amount0_used_atoms": amount0,
        "amount1_used_atoms": amount1,
        "amount0_refund_atoms": 0,
        "amount1_refund_atoms": 0,
        "post_pool": _pool(amount0, amount1, minted),
    }


def _reference_add(
    pool: Mapping[str, Any],
    amount0_desired: int,
    amount1_desired: int,
) -> dict[str, Any]:
    reserve0 = int(pool["reserve0_atoms"])
    reserve1 = int(pool["reserve1_atoms"])
    supply = int(pool["lp_supply_atoms"])
    minted = min(
        amount0_desired * supply // reserve0,
        amount1_desired * supply // reserve1,
    )
    used0 = _ceil_div(minted * reserve0, supply)
    used1 = _ceil_div(minted * reserve1, supply)
    return {
        "lp_minted_atoms": minted,
        "amount0_used_atoms": used0,
        "amount1_used_atoms": used1,
        "amount0_refund_atoms": amount0_desired - used0,
        "amount1_refund_atoms": amount1_desired - used1,
        "post_pool": _pool(reserve0 + used0, reserve1 + used1, supply + minted),
    }


def _reference_remove(pool: Mapping[str, Any], burn: int) -> dict[str, Any]:
    reserve0 = int(pool["reserve0_atoms"])
    reserve1 = int(pool["reserve1_atoms"])
    supply = int(pool["lp_supply_atoms"])
    if burn == supply:
        return {
            "amount0_out_atoms": reserve0,
            "amount1_out_atoms": reserve1,
            "amount0_rounding_numerator": 0,
            "amount1_rounding_numerator": 0,
            "rounding_denominator": supply,
            "terminal_closed": True,
            "post_pool": _pool(0, 0, 0, "CLOSED"),
        }
    product0 = burn * reserve0
    product1 = burn * reserve1
    amount0 = product0 // supply
    amount1 = product1 // supply
    return {
        "amount0_out_atoms": amount0,
        "amount1_out_atoms": amount1,
        "amount0_rounding_numerator": product0 % supply,
        "amount1_rounding_numerator": product1 % supply,
        "rounding_denominator": supply,
        "terminal_closed": False,
        "post_pool": _pool(reserve0 - amount0, reserve1 - amount1, supply - burn),
    }


def _exact_in_vectors() -> list[dict[str, Any]]:
    cases = (
        (10_000, 10_000, 333),
        (10_000, 10_000, 334),
        (10_000, 20_000, 1_000),
        (7, 11, 10_000),
    )
    return [
        {
            "id": f"EXACT_IN_{reserve_in}_{reserve_out}_{gross_input}",
            "input": {
                "reserve_in_atoms": reserve_in,
                "reserve_out_atoms": reserve_out,
                "gross_input_atoms": gross_input,
            },
            "expected": _reference_exact_in(reserve_in, reserve_out, gross_input),
        }
        for reserve_in, reserve_out, gross_input in cases
    ]


def _exact_out_vectors() -> list[dict[str, Any]]:
    cases = ((10_000, 20_000, 1_000), (7, 11, 3))
    return [
        {
            "id": f"EXACT_OUT_{reserve_in}_{reserve_out}_{requested_output}",
            "input": {
                "reserve_in_atoms": reserve_in,
                "reserve_out_atoms": reserve_out,
                "requested_output_atoms": requested_output,
            },
            "expected": _reference_exact_out(
                reserve_in,
                reserve_out,
                requested_output,
            ),
        }
        for reserve_in, reserve_out, requested_output in cases
    ]


def _lp_deposit_vectors() -> list[dict[str, Any]]:
    create_input = {"amount0_atoms": 10_000, "amount1_atoms": 40_000}
    add_pool = _pool(1_000, 2_000, 1_000)
    add_input = {
        "pool": add_pool,
        "amount0_desired_atoms": 400,
        "amount1_desired_atoms": 900,
    }
    rounding_add_pool = _pool(7, 11, 5)
    rounding_add_input = {
        "pool": rounding_add_pool,
        "amount0_desired_atoms": 3,
        "amount1_desired_atoms": 5,
    }
    return [
        {
            "id": "CREATE_NO_PERMANENT_LOCK",
            "operation": "CREATE",
            "input": create_input,
            "expected": _reference_create(10_000, 40_000),
        },
        {
            "id": "ADD_NON_DILUTING_REFUND_EXCESS",
            "operation": "ADD",
            "input": add_input,
            "expected": _reference_add(add_pool, 400, 900),
        },
        {
            "id": "ADD_CEIL_REQUIRED_ASSET_USE",
            "operation": "ADD",
            "input": rounding_add_input,
            "expected": _reference_add(rounding_add_pool, 3, 5),
        },
    ]


def _lp_withdrawal_vectors() -> list[dict[str, Any]]:
    partial_pool = _pool(1_001, 2_003, 1_000)
    final_pool = _pool(17, 29, 3)
    return [
        {
            "id": "REMOVE_PARTIAL_ROUNDING_REMAINS",
            "operation": "REMOVE",
            "input": {"pool": partial_pool, "lp_burn_atoms": 333},
            "expected": _reference_remove(partial_pool, 333),
        },
        {
            "id": "REMOVE_FINAL_DRAINS_AND_CLOSES",
            "operation": "REMOVE",
            "input": {"pool": final_pool, "lp_burn_atoms": 3},
            "expected": _reference_remove(final_pool, 3),
        },
    ]


def build_differential_vectors() -> dict[str, list[dict[str, Any]]]:
    return {
        "exact_in": _exact_in_vectors(),
        "exact_out": _exact_out_vectors(),
        "lp_lifecycle": [*_lp_deposit_vectors(), *_lp_withdrawal_vectors()],
    }

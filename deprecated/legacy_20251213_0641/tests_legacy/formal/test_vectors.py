"""
Deterministic test vectors for formal verification.

These test vectors provide inputs → expected post-state mappings
that can be used to verify Tau Language specifications.
"""

from typing import Dict, Any, List
from dataclasses import dataclass


@dataclass
class TestVector:
    """A test vector with input and expected output."""
    name: str
    input_state: Dict[str, Any]
    operations: List[Dict[str, Any]]
    expected_output_state: Dict[str, Any]
    description: str = ""


# Test vectors for CPMM swaps
CPMM_TEST_VECTORS = [
    TestVector(
        name="swap_exact_in_no_fee",
        input_state={
            "pool": {
                "pool_id": "0x" + "12" * 32,
                "asset0": "0x" + "00" * 32,
                "asset1": "0x" + "11" * 32,
                "reserve0": 1000000,
                "reserve1": 1000000,
                "fee_bps": 0,
            },
            "user_balance": {
                "asset0": 50000,
                "asset1": 0,
            },
        },
        operations=[
            {
                "kind": "SWAP_EXACT_IN",
                "amount_in": 10000,
                "min_amount_out": 9000,
            }
        ],
        expected_output_state={
            "pool": {
                "reserve0": 1010000,  # 1000000 + 10000
                "reserve1": 990099,   # 1000000 - 9901 (approx)
            },
            "user_balance": {
                "asset0": 40000,  # 50000 - 10000
                "asset1": 9901,   # 0 + 9901 (approx)
            },
        },
        description="Exact-in swap with no fee",
    ),
    TestVector(
        name="swap_exact_in_with_fee",
        input_state={
            "pool": {
                "pool_id": "0x" + "12" * 32,
                "asset0": "0x" + "00" * 32,
                "asset1": "0x" + "11" * 32,
                "reserve0": 1000000,
                "reserve1": 1000000,
                "fee_bps": 30,  # 0.3%
            },
            "user_balance": {
                "asset0": 50000,
                "asset1": 0,
            },
        },
        operations=[
            {
                "kind": "SWAP_EXACT_IN",
                "amount_in": 10000,
                "min_amount_out": 9900,
            }
        ],
        expected_output_state={
            "pool": {
                "reserve0": 1010000,  # 1000000 + 10000
                "reserve1": 990099,   # Slightly less due to fee
            },
            "user_balance": {
                "asset0": 40000,
                "asset1": 9901,  # Slightly less due to fee
            },
        },
        description="Exact-in swap with 30 bps fee",
    ),
]

# Test vectors for batch clearing
BATCH_CLEARING_TEST_VECTORS = [
    TestVector(
        name="batch_two_swaps",
        input_state={
            "pool": {
                "pool_id": "0x" + "12" * 32,
                "asset0": "0x" + "00" * 32,
                "asset1": "0x" + "11" * 32,
                "reserve0": 1000000,
                "reserve1": 1000000,
                "fee_bps": 30,
            },
            "users": [
                {"pubkey": "0x" + "aa" * 96, "asset0": 20000, "asset1": 0},
                {"pubkey": "0x" + "bb" * 96, "asset0": 20000, "asset1": 0},
            ],
        },
        operations=[
            {
                "user": "0x" + "aa" * 96,
                "kind": "SWAP_EXACT_IN",
                "amount_in": 5000,
                "min_amount_out": 4900,
            },
            {
                "user": "0x" + "bb" * 96,
                "kind": "SWAP_EXACT_IN",
                "amount_in": 5000,
                "min_amount_out": 4900,
            },
        ],
        expected_output_state={
            "pool": {
                "reserve0": 1010000,  # Increased by both swaps
                "reserve1": 980198,   # Decreased by both outputs
            },
            "users": [
                {"asset0": 15000, "asset1": 4950},  # Approx
                {"asset0": 15000, "asset1": 4950},  # Approx
            ],
        },
        description="Batch clearing with two swaps",
    ),
]

# Test vectors for liquidity operations
LIQUIDITY_TEST_VECTORS = [
    TestVector(
        name="create_pool",
        input_state={
            "creator_balance": {
                "asset0": 100000,
                "asset1": 100000,
            },
        },
        operations=[
            {
                "kind": "CREATE_POOL",
                "asset0": "0x" + "00" * 32,
                "asset1": "0x" + "11" * 32,
                "amount0": 10000,
                "amount1": 10000,
                "fee_bps": 30,
            }
        ],
        expected_output_state={
            "pool": {
                "reserve0": 10000,
                "reserve1": 10000,
                "lp_supply": 10000,  # floor(sqrt(10000*10000)) - MIN_LP_LOCK
            },
            "creator_balance": {
                "asset0": 90000,
                "asset1": 90000,
            },
        },
        description="Create new pool with initial liquidity",
    ),
]


def get_all_test_vectors() -> List[TestVector]:
    """Get all test vectors."""
    return (
        CPMM_TEST_VECTORS
        + BATCH_CLEARING_TEST_VECTORS
        + LIQUIDITY_TEST_VECTORS
    )


def get_test_vector_by_name(name: str) -> TestVector:
    """Get a test vector by name."""
    all_vectors = get_all_test_vectors()
    for vector in all_vectors:
        if vector.name == name:
            return vector
    raise ValueError(f"Test vector not found: {name}")


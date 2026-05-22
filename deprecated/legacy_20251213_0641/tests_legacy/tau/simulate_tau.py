#!/usr/bin/env python3
"""
Simulate Tau Language validation to test specs before Tau is installed.
This implements the logic from our Tau specs to verify correctness.
"""

from typing import Tuple, Dict, Any, List


def is_non_negative(hi: int, lo: int) -> bool:
    """Check if value (hi/lo representation) is non-negative."""
    return hi > 0 or (hi == 0 and lo >= 0)


def is_positive(hi: int, lo: int) -> bool:
    """Check if value is positive (strictly greater than zero)."""
    return hi > 0 or (hi == 0 and lo > 0)


def value_gte(hi1: int, lo1: int, hi2: int, lo2: int) -> bool:
    """Compare: (hi1, lo1) >= (hi2, lo2)."""
    if hi1 > hi2:
        return True
    if hi1 < hi2:
        return False
    return lo1 >= lo2


def fee_bps_valid(fee: int) -> bool:
    """Check if fee_bps is in valid range [0, 10000]."""
    return 0 <= fee <= 10000


def validate_cpmm_swap(
    reserve_in_hi: int, reserve_in_lo: int,
    reserve_out_hi: int, reserve_out_lo: int,
    amount_in_hi: int, amount_in_lo: int,
    fee_bps: int,
    amount_out_hi: int, amount_out_lo: int,
) -> bool:
    """
    Validate CPMM swap constraints.
    
    Returns True if all constraints are satisfied.
    
    Constraints:
    1. Reserves must be positive (not just non-negative) for swaps to work
    2. amount_in must be positive
    3. fee_bps must be in valid range
    4. amount_out must be positive
    5. amount_out cannot exceed reserve_out
    """
    return (
        is_positive(reserve_in_hi, reserve_in_lo) and  # Reserve must be positive, not just non-negative
        is_positive(reserve_out_hi, reserve_out_lo) and  # Reserve must be positive
        is_positive(amount_in_hi, amount_in_lo) and
        fee_bps_valid(fee_bps) and
        is_positive(amount_out_hi, amount_out_lo) and
        value_gte(reserve_out_hi, reserve_out_lo, amount_out_hi, amount_out_lo)
    )


def validate_balance_safety(
    balance_before_hi: int, balance_before_lo: int,
    delta_add_hi: int, delta_add_lo: int,
    delta_sub_hi: int, delta_sub_lo: int,
) -> bool:
    """
    Validate balance delta safety.
    
    Returns True if:
    1. All inputs are non-negative (deltas cannot be negative)
    2. The external computation result will be validated separately
    
    Note: For negative deltas, the hi/lo split might not catch it if
    the negative value is represented in two's complement. We rely on
    the Python layer to provide non-negative hi/lo pairs.
    """
    # Check all inputs are non-negative
    # In practice, Python layer should never provide negative deltas
    # as hi/lo pairs, but we validate what we can
    return (
        is_non_negative(balance_before_hi, balance_before_lo) and
        is_non_negative(delta_add_hi, delta_add_lo) and
        is_non_negative(delta_sub_hi, delta_sub_lo)
    )


def split_256bit(value: int) -> Tuple[int, int]:
    """Split 256-bit value into hi/lo 16-bit components."""
    lo = value & 0xFFFF
    hi = (value >> 16) & 0xFFFF
    return hi, lo


# Test vectors
TEST_CASES = [
    {
        "name": "valid_swap",
        "inputs": {
            "reserve_in": 1000000,
            "reserve_out": 1000000,
            "amount_in": 10000,
            "fee_bps": 30,
            "amount_out": 9871,
        },
        "expected": True,
    },
    {
        "name": "zero_reserve",
        "inputs": {
            "reserve_in": 0,
            "reserve_out": 1000000,
            "amount_in": 10000,
            "fee_bps": 30,
            "amount_out": 9871,
        },
        "expected": False,
    },
    {
        "name": "amount_exceeds_reserve",
        "inputs": {
            "reserve_in": 1000000,
            "reserve_out": 1000000,
            "amount_in": 10000,
            "fee_bps": 30,
            "amount_out": 2000000,  # Exceeds reserve_out
        },
        "expected": False,
    },
    {
        "name": "zero_amount_in",
        "inputs": {
            "reserve_in": 1000000,
            "reserve_out": 1000000,
            "amount_in": 0,
            "fee_bps": 30,
            "amount_out": 0,
        },
        "expected": False,
    },
    {
        "name": "invalid_fee_bps",
        "inputs": {
            "reserve_in": 1000000,
            "reserve_out": 1000000,
            "amount_in": 10000,
            "fee_bps": 10001,  # Exceeds max
            "amount_out": 9871,
        },
        "expected": False,
    },
]


def test_cpmm_validation():
    """Test CPMM validation logic."""
    print("Testing CPMM Swap Validation")
    print("=" * 60)
    
    passed = 0
    failed = 0
    
    for tc in TEST_CASES:
        inputs = tc["inputs"]
        
        # Split into hi/lo components
        reserve_in_hi, reserve_in_lo = split_256bit(inputs["reserve_in"])
        reserve_out_hi, reserve_out_lo = split_256bit(inputs["reserve_out"])
        amount_in_hi, amount_in_lo = split_256bit(inputs["amount_in"])
        amount_out_hi, amount_out_lo = split_256bit(inputs["amount_out"])
        
        # Validate
        result = validate_cpmm_swap(
            reserve_in_hi, reserve_in_lo,
            reserve_out_hi, reserve_out_lo,
            amount_in_hi, amount_in_lo,
            inputs["fee_bps"],
            amount_out_hi, amount_out_lo,
        )
        
        # Check result
        if result == tc["expected"]:
            print(f"✓ {tc['name']}: Expected {tc['expected']}, got {result}")
            passed += 1
        else:
            print(f"✗ {tc['name']}: Expected {tc['expected']}, got {result}")
            print(f"  Inputs: reserve_in={inputs['reserve_in']}, "
                  f"reserve_out={inputs['reserve_out']}, "
                  f"amount_in={inputs['amount_in']}, "
                  f"fee_bps={inputs['fee_bps']}, "
                  f"amount_out={inputs['amount_out']}")
            failed += 1
    
    print()
    print(f"Results: {passed} passed, {failed} failed")
    print("=" * 60)
    return passed, failed


if __name__ == "__main__":
    test_cpmm_validation()


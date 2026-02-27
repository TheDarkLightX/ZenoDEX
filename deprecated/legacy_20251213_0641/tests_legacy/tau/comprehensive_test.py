#!/usr/bin/env python3
"""
Comprehensive test suite for Tau Language specifications.
Tests multiple approaches and validates outputs match expected inputs.
"""

import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from simulate_tau import (
    validate_cpmm_swap,
    validate_balance_safety,
    split_256bit,
    TEST_CASES,
)


def test_cpmm_approaches():
    """Test different approaches to CPMM validation."""
    print("=" * 60)
    print("Testing Different CPMM Validation Approaches")
    print("=" * 60)
    print()
    
    # Approach 1: Current (positive reserves required)
    print("Approach 1: Positive Reserves Required")
    print("-" * 60)
    passed1 = 0
    failed1 = 0
    
    for tc in TEST_CASES:
        inputs = tc["inputs"]
        reserve_in_hi, reserve_in_lo = split_256bit(inputs["reserve_in"])
        reserve_out_hi, reserve_out_lo = split_256bit(inputs["reserve_out"])
        amount_in_hi, amount_in_lo = split_256bit(inputs["amount_in"])
        amount_out_hi, amount_out_lo = split_256bit(inputs["amount_out"])
        
        result = validate_cpmm_swap(
            reserve_in_hi, reserve_in_lo,
            reserve_out_hi, reserve_out_lo,
            amount_in_hi, amount_in_lo,
            inputs["fee_bps"],
            amount_out_hi, amount_out_lo,
        )
        
        if result == tc["expected"]:
            print(f"  ✓ {tc['name']}")
            passed1 += 1
        else:
            print(f"  ✗ {tc['name']}: Expected {tc['expected']}, got {result}")
            failed1 += 1
    
    print(f"  Results: {passed1} passed, {failed1} failed")
    print()
    
    # Approach 2: Test with edge cases
    print("Approach 2: Edge Case Testing")
    print("-" * 60)
    
    edge_cases = [
        {
            "name": "very_small_amounts",
            "reserve_in": 1000,
            "reserve_out": 1000,
            "amount_in": 1,
            "fee_bps": 0,
            "amount_out": 0,  # Very small, might round to 0
            "expected": False,  # amount_out must be positive
        },
        {
            "name": "max_fee_bps",
            "reserve_in": 1000000,
            "reserve_out": 1000000,
            "amount_in": 10000,
            "fee_bps": 10000,  # Max fee
            "amount_out": 0,  # All taken as fee
            "expected": False,  # amount_out must be positive
        },
        {
            "name": "equal_reserves_equal_amounts",
            "reserve_in": 1000000,
            "reserve_out": 1000000,
            "amount_in": 1000000,  # Large swap
            "fee_bps": 30,
            "amount_out": 970000,  # Approximate
            "expected": True,  # Should be valid
        },
    ]
    
    passed2 = 0
    failed2 = 0
    
    for tc in edge_cases:
        reserve_in_hi, reserve_in_lo = split_256bit(tc["reserve_in"])
        reserve_out_hi, reserve_out_lo = split_256bit(tc["reserve_out"])
        amount_in_hi, amount_in_lo = split_256bit(tc["amount_in"])
        amount_out_hi, amount_out_lo = split_256bit(tc["amount_out"])
        
        result = validate_cpmm_swap(
            reserve_in_hi, reserve_in_lo,
            reserve_out_hi, reserve_out_lo,
            amount_in_hi, amount_in_lo,
            tc["fee_bps"],
            amount_out_hi, amount_out_lo,
        )
        
        if result == tc["expected"]:
            print(f"  ✓ {tc['name']}")
            passed2 += 1
        else:
            print(f"  ✗ {tc['name']}: Expected {tc['expected']}, got {result}")
            failed2 += 1
    
    print(f"  Results: {passed2} passed, {failed2} failed")
    print()
    
    return passed1 + passed2, failed1 + failed2


def test_output_consistency():
    """Test that outputs are consistent with inputs."""
    print("=" * 60)
    print("Testing Output Consistency")
    print("=" * 60)
    print()
    
    # Test: If inputs are valid, output should be True
    # Test: If inputs are invalid, output should be False
    
    consistency_tests = [
        {
            "name": "valid_inputs_produce_true",
            "reserve_in": 1000000,
            "reserve_out": 1000000,
            "amount_in": 10000,
            "fee_bps": 30,
            "amount_out": 9871,
            "should_be_valid": True,
        },
        {
            "name": "invalid_fee_produces_false",
            "reserve_in": 1000000,
            "reserve_out": 1000000,
            "amount_in": 10000,
            "fee_bps": 10001,  # Invalid
            "amount_out": 9871,
            "should_be_valid": False,
        },
    ]
    
    passed = 0
    failed = 0
    
    for tc in consistency_tests:
        reserve_in_hi, reserve_in_lo = split_256bit(tc["reserve_in"])
        reserve_out_hi, reserve_out_lo = split_256bit(tc["reserve_out"])
        amount_in_hi, amount_in_lo = split_256bit(tc["amount_in"])
        amount_out_hi, amount_out_lo = split_256bit(tc["amount_out"])
        
        result = validate_cpmm_swap(
            reserve_in_hi, reserve_in_lo,
            reserve_out_hi, reserve_out_lo,
            amount_in_hi, amount_in_lo,
            tc["fee_bps"],
            amount_out_hi, amount_out_lo,
        )
        
        if result == tc["should_be_valid"]:
            print(f"✓ {tc['name']}: Output matches expected ({result})")
            passed += 1
        else:
            print(f"✗ {tc['name']}: Expected {tc['should_be_valid']}, got {result}")
            failed += 1
    
    print()
    print(f"Results: {passed} passed, {failed} failed")
    print("=" * 60)
    return passed, failed


def main():
    """Run all tests."""
    print()
    print("TauSwap Tau Language Specification Test Suite")
    print("=" * 60)
    print()
    
    # Test CPMM approaches
    cpmm_passed, cpmm_failed = test_cpmm_approaches()
    
    # Test output consistency
    consistency_passed, consistency_failed = test_output_consistency()
    
    # Summary
    print()
    print("=" * 60)
    print("Test Summary")
    print("=" * 60)
    print(f"CPMM Tests: {cpmm_passed} passed, {cpmm_failed} failed")
    print(f"Consistency Tests: {consistency_passed} passed, {consistency_failed} failed")
    print(f"Total: {cpmm_passed + consistency_passed} passed, {cpmm_failed + consistency_failed} failed")
    print("=" * 60)
    
    if cpmm_failed + consistency_failed == 0:
        print("✓ All tests passed!")
        return 0
    else:
        print("✗ Some tests failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())


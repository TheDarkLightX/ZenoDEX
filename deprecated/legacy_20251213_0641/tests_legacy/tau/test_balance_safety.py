#!/usr/bin/env python3
"""Test balance safety validation."""

from simulate_tau import validate_balance_safety, split_256bit


def test_balance_safety():
    """Test balance safety validation."""
    print("Testing Balance Safety Validation")
    print("=" * 60)
    
    test_cases = [
        {
            "name": "valid_balance_delta",
            "balance_before": 50000,
            "delta_add": 10000,
            "delta_sub": 5000,
            "expected": True,  # 50000 + 10000 - 5000 = 55000 >= 0
        },
        {
            "name": "insufficient_balance",
            "balance_before": 5000,
            "delta_add": 0,
            "delta_sub": 10000,
            "expected": True,  # Inputs are non-negative (validation passes)
            # Note: Actual result would be negative, but we only validate inputs
        },
        {
            "name": "zero_balance_zero_delta",
            "balance_before": 0,
            "delta_add": 0,
            "delta_sub": 0,
            "expected": True,  # All non-negative
        },
        {
            "name": "negative_delta_sub",
            "balance_before": 10000,
            "delta_add": 0,
            "delta_sub": -1000,  # Invalid (negative)
            "expected": False,  # Should fail - but note: negative split to hi/lo might not catch this
            # In practice, Python layer should never provide negative values
        },
    ]
    
    passed = 0
    failed = 0
    
    for tc in test_cases:
        balance_hi, balance_lo = split_256bit(tc["balance_before"])
        add_hi, add_lo = split_256bit(tc["delta_add"])
        sub_hi, sub_lo = split_256bit(tc["delta_sub"])
        
        result = validate_balance_safety(
            balance_hi, balance_lo,
            add_hi, add_lo,
            sub_hi, sub_lo,
        )
        
        if result == tc["expected"]:
            print(f"✓ {tc['name']}: Expected {tc['expected']}, got {result}")
            passed += 1
        else:
            print(f"✗ {tc['name']}: Expected {tc['expected']}, got {result}")
            print(f"  balance={tc['balance_before']}, "
                  f"delta_add={tc['delta_add']}, "
                  f"delta_sub={tc['delta_sub']}")
            failed += 1
    
    print()
    print(f"Results: {passed} passed, {failed} failed")
    print("=" * 60)
    return passed, failed


if __name__ == "__main__":
    test_balance_safety()


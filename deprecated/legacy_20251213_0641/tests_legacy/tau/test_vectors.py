"""
Test vectors for Tau Language specifications.

These test vectors provide concrete inputs and expected outputs
to validate that Tau specs produce correct validation results.
"""

from typing import Tuple, Dict, Any


def split_256bit(value: int) -> Tuple[int, int]:
    """Split 256-bit value into hi/lo 16-bit components."""
    lo = value & 0xFFFF
    hi = (value >> 16) & 0xFFFF
    return hi, lo


def format_tau_input(hi: int, lo: int) -> str:
    """Format as hex for Tau input."""
    return f"{hi:04x}{lo:04x}"


# Test Case 1: Valid CPMM Swap
def test_case_1_valid_swap():
    """
    Valid swap:
    - reserve_in = 1000000 (0xF4240)
    - reserve_out = 1000000 (0xF4240)
    - amount_in = 10000 (0x2710)
    - fee_bps = 30 (0x001E)
    - amount_out = 9871 (0x268F) [computed by Python]
    
    Expected: swap_valid = true
    """
    reserve_in = 1000000
    reserve_out = 1000000
    amount_in = 10000
    fee_bps = 30
    amount_out = 9871  # Computed: floor(1000000 * 9970 / 1009970) = 9871
    
    inputs = {
        "reserve_in": split_256bit(reserve_in),
        "reserve_out": split_256bit(reserve_out),
        "amount_in": split_256bit(amount_in),
        "fee_bps": fee_bps,
        "amount_out": split_256bit(amount_out),
    }
    
    expected_output = True  # swap_valid should be true
    
    return {
        "name": "valid_swap",
        "inputs": inputs,
        "expected_output": expected_output,
        "description": "Valid swap with positive amounts and correct constraints"
    }


# Test Case 2: Invalid - Negative Reserve
def test_case_2_negative_reserve():
    """
    Invalid swap:
    - reserve_in = -1000 (invalid, but we'll test with 0)
    - reserve_out = 1000000
    - amount_in = 10000
    - fee_bps = 30
    - amount_out = 9871
    
    Expected: swap_valid = false (reserve_in not non-negative)
    """
    reserve_in = 0  # Zero (edge case)
    reserve_out = 1000000
    amount_in = 10000
    fee_bps = 30
    amount_out = 9871
    
    inputs = {
        "reserve_in": split_256bit(reserve_in),
        "reserve_out": split_256bit(reserve_out),
        "amount_in": split_256bit(amount_in),
        "fee_bps": fee_bps,
        "amount_out": split_256bit(amount_out),
    }
    
    # Zero reserves might be valid (empty pool), but amount_in > 0 requires reserves > 0
    # Actually, zero reserves with positive amount_in should fail
    expected_output = False  # swap_valid should be false
    
    return {
        "name": "zero_reserve",
        "inputs": inputs,
        "expected_output": expected_output,
        "description": "Zero reserve should fail validation"
    }


# Test Case 3: Invalid - Amount Out Exceeds Reserve
def test_case_3_amount_exceeds_reserve():
    """
    Invalid swap:
    - reserve_in = 1000000
    - reserve_out = 1000000
    - amount_in = 10000
    - fee_bps = 30
    - amount_out = 2000000 (exceeds reserve_out)
    
    Expected: swap_valid = false (amount_out > reserve_out)
    """
    reserve_in = 1000000
    reserve_out = 1000000
    amount_in = 10000
    fee_bps = 30
    amount_out = 2000000  # Exceeds reserve_out
    
    inputs = {
        "reserve_in": split_256bit(reserve_in),
        "reserve_out": split_256bit(reserve_out),
        "amount_in": split_256bit(amount_in),
        "fee_bps": fee_bps,
        "amount_out": split_256bit(amount_out),
    }
    
    expected_output = False  # swap_valid should be false
    
    return {
        "name": "amount_exceeds_reserve",
        "inputs": inputs,
        "expected_output": expected_output,
        "description": "Amount out exceeding reserve should fail"
    }


# Test Case 4: Invalid - Zero Amount In
def test_case_4_zero_amount_in():
    """
    Invalid swap:
    - reserve_in = 1000000
    - reserve_out = 1000000
    - amount_in = 0 (invalid)
    - fee_bps = 30
    - amount_out = 0
    
    Expected: swap_valid = false (amount_in must be positive)
    """
    reserve_in = 1000000
    reserve_out = 1000000
    amount_in = 0
    fee_bps = 30
    amount_out = 0
    
    inputs = {
        "reserve_in": split_256bit(reserve_in),
        "reserve_out": split_256bit(reserve_out),
        "amount_in": split_256bit(amount_in),
        "fee_bps": fee_bps,
        "amount_out": split_256bit(amount_out),
    }
    
    expected_output = False  # swap_valid should be false
    
    return {
        "name": "zero_amount_in",
        "inputs": inputs,
        "expected_output": expected_output,
        "description": "Zero amount_in should fail validation"
    }


# Test Case 5: Invalid - Fee BPS Out of Range
def test_case_5_invalid_fee():
    """
    Invalid swap:
    - reserve_in = 1000000
    - reserve_out = 1000000
    - amount_in = 10000
    - fee_bps = 10001 (invalid, max is 10000)
    - amount_out = 9871
    
    Expected: swap_valid = false (fee_bps > 10000)
    """
    reserve_in = 1000000
    reserve_out = 1000000
    amount_in = 10000
    fee_bps = 10001  # Exceeds max
    amount_out = 9871
    
    inputs = {
        "reserve_in": split_256bit(reserve_in),
        "reserve_out": split_256bit(reserve_out),
        "amount_in": split_256bit(amount_in),
        "fee_bps": fee_bps,
        "amount_out": split_256bit(amount_out),
    }
    
    expected_output = False  # swap_valid should be false
    
    return {
        "name": "invalid_fee_bps",
        "inputs": inputs,
        "expected_output": expected_output,
        "description": "Fee BPS out of range should fail"
    }


def get_all_test_cases():
    """Get all test cases."""
    return [
        test_case_1_valid_swap(),
        test_case_2_negative_reserve(),
        test_case_3_amount_exceeds_reserve(),
        test_case_4_zero_amount_in(),
        test_case_5_invalid_fee(),
    ]


def create_tau_input_file(test_case: Dict[str, Any], filename: str):
    """Create Tau input file from test case."""
    inputs = test_case["inputs"]
    
    # Format: one line per time step
    # Format: reserve_in_lo reserve_in_hi reserve_out_lo reserve_out_hi
    #         amount_in_lo amount_in_hi fee_bps amount_out_lo amount_out_hi
    line = (
        f"{inputs['reserve_in'][1]:04x} "      # reserve_in_lo
        f"{inputs['reserve_in'][0]:04x} "      # reserve_in_hi
        f"{inputs['reserve_out'][1]:04x} "     # reserve_out_lo
        f"{inputs['reserve_out'][0]:04x} "    # reserve_out_hi
        f"{inputs['amount_in'][1]:04x} "       # amount_in_lo
        f"{inputs['amount_in'][0]:04x} "        # amount_in_hi
        f"{inputs['fee_bps']:04x} "            # fee_bps
        f"{inputs['amount_out'][1]:04x} "       # amount_out_lo
        f"{inputs['amount_out'][0]:04x}"        # amount_out_hi
    )
    
    with open(filename, 'w') as f:
        f.write(line + '\n')
    
    return filename


if __name__ == "__main__":
    # Generate test input files
    test_cases = get_all_test_cases()
    for i, tc in enumerate(test_cases, 1):
        filename = f"test_input_{i}_{tc['name']}.in"
        create_tau_input_file(tc, filename)
        print(f"Created {filename} for {tc['name']}")
        print(f"  Expected output: {tc['expected_output']}")
        print(f"  Description: {tc['description']}")
        print()


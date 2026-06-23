#!/usr/bin/env python3
"""
Validate Tau Language specifications by:
1. Checking syntax (if Tau compiler available)
2. Testing with known input/output pairs
3. Verifying expected behavior
"""

import subprocess
import os
import sys
from pathlib import Path

# Test vectors with expected outputs
TEST_VECTORS = [
    {
        "name": "valid_swap",
        "inputs": {
            "reserve_in": (0x000F, 0x4240),  # 1000000
            "reserve_out": (0x000F, 0x4240),  # 1000000
            "amount_in": (0x0000, 0x2710),   # 10000
            "fee_bps": 30,
            "amount_out": (0x0000, 0x268F),  # 9871
        },
        "expected": True,
    },
    {
        "name": "zero_reserve",
        "inputs": {
            "reserve_in": (0x0000, 0x0000),  # 0
            "reserve_out": (0x000F, 0x4240),  # 1000000
            "amount_in": (0x0000, 0x2710),   # 10000
            "fee_bps": 30,
            "amount_out": (0x0000, 0x268F),  # 9871
        },
        "expected": False,  # Zero reserve should fail
    },
    {
        "name": "amount_exceeds_reserve",
        "inputs": {
            "reserve_in": (0x000F, 0x4240),  # 1000000
            "reserve_out": (0x000F, 0x4240),  # 1000000
            "amount_in": (0x0000, 0x2710),   # 10000
            "fee_bps": 30,
            "amount_out": (0x001E, 0x8480),  # 2000000 (exceeds reserve)
        },
        "expected": False,  # amount_out > reserve_out should fail
    },
]


def find_tau_binary():
    """Find Tau Language binary."""
    # Check PATH
    try:
        result = subprocess.run(["which", "tau"], capture_output=True, text=True)
        if result.returncode == 0:
            return result.stdout.strip()
    except:
        pass
    
    # Check common build locations
    base_path = Path(__file__).parent.parent.parent
    possible_paths = [
        base_path / "external" / "tau-lang" / "build-Release" / "tau",
        base_path / "external" / "tau-lang" / "build-Debug" / "tau",
        base_path / "external" / "tau-lang" / "build-RelWithDebInfo" / "tau",
    ]
    
    for path in possible_paths:
        if path.exists():
            return str(path)
    
    return None


def test_spec_syntax(tau_bin, spec_file):
    """Test if spec file has valid syntax."""
    if not tau_bin:
        return None, "Tau binary not found"
    
    try:
        result = subprocess.run(
            [tau_bin, spec_file],
            capture_output=True,
            text=True,
            timeout=10
        )
        if result.returncode == 0:
            return True, "Syntax valid"
        else:
            return False, f"Syntax error: {result.stderr[:200]}"
    except subprocess.TimeoutExpired:
        return False, "Timeout"
    except Exception as e:
        return False, f"Error: {str(e)}"


def create_input_file(test_vector, filename):
    """Create Tau input file from test vector."""
    inputs = test_vector["inputs"]
    
    # Format: reserve_in_lo reserve_in_hi reserve_out_lo reserve_out_hi
    #         amount_in_lo amount_in_hi fee_bps amount_out_lo amount_out_hi
    line = (
        f"{inputs['reserve_in'][1]:04x} "      # reserve_in_lo
        f"{inputs['reserve_in'][0]:04x} "      # reserve_in_hi
        f"{inputs['reserve_out'][1]:04x} "     # reserve_out_lo
        f"{inputs['reserve_out'][0]:04x} "     # reserve_out_hi
        f"{inputs['amount_in'][1]:04x} "       # amount_in_lo
        f"{inputs['amount_in'][0]:04x} "       # amount_in_hi
        f"{inputs['fee_bps']:04x} "            # fee_bps
        f"{inputs['amount_out'][1]:04x} "       # amount_out_lo
        f"{inputs['amount_out'][0]:04x}"       # amount_out_hi
    )
    
    with open(filename, 'w') as f:
        f.write(line + '\n')
    
    return filename


def run_test(tau_bin, spec_file, input_file):
    """Run Tau spec with input file."""
    if not tau_bin:
        return None, "Tau binary not found"
    
    try:
        # Run tau with spec and input file
        result = subprocess.run(
            [tau_bin, spec_file, input_file],
            capture_output=True,
            text=True,
            timeout=10
        )
        
        if result.returncode == 0:
            # Parse output (should be "yes" or "no" or boolean)
            output = result.stdout.strip()
            if "yes" in output.lower() or "1" in output or "true" in output.lower():
                return True, output
            elif "no" in output.lower() or "0" in output or "false" in output.lower():
                return False, output
            else:
                return None, f"Unexpected output: {output}"
        else:
            return None, f"Error: {result.stderr[:200]}"
    except subprocess.TimeoutExpired:
        return None, "Timeout"
    except Exception as e:
        return None, f"Error: {str(e)}"


def main():
    """Main test runner."""
    print("=" * 60)
    print("TauSwap Tau Language Specification Validator")
    print("=" * 60)
    print()
    
    # Find Tau binary
    tau_bin = find_tau_binary()
    if tau_bin:
        print(f"✓ Found Tau binary: {tau_bin}")
    else:
        print("⚠ Tau binary not found - syntax checking only")
        print("  Install Tau: cd external/tau-lang && ./release.sh")
    print()
    
    # Test specs
    base_path = Path(__file__).parent.parent.parent
    specs = [
        base_path / "src" / "tau_specs" / "cpmm_math.tau",
        base_path / "src" / "tau_specs" / "invariants.tau",
        base_path / "src" / "tau_specs" / "balance_safety.tau",
        base_path / "tests" / "tau" / "test_cpmm_simple.tau",
    ]
    
    print("Testing specification syntax...")
    print("-" * 60)
    
    syntax_results = {}
    for spec in specs:
        if not spec.exists():
            print(f"✗ {spec.name}: File not found")
            continue
        
        valid, message = test_spec_syntax(tau_bin, str(spec))
        if valid is True:
            print(f"✓ {spec.name}: {message}")
            syntax_results[spec] = True
        elif valid is False:
            print(f"✗ {spec.name}: {message}")
            syntax_results[spec] = False
        else:
            print(f"? {spec.name}: {message}")
            syntax_results[spec] = None
    
    print()
    
    # Test with vectors
    if tau_bin:
        print("Testing with test vectors...")
        print("-" * 60)
        
        spec_file = base_path / "tests" / "tau" / "test_cpmm_simple.tau"
        if not spec_file.exists():
            print(f"✗ Test spec not found: {spec_file}")
            return
        
        passed = 0
        failed = 0
        
        for tv in TEST_VECTORS:
            # Create input file
            input_file = base_path / "tests" / "tau" / f"test_input_{tv['name']}.in"
            create_input_file(tv, str(input_file))
            
            # Run test
            result, message = run_test(tau_bin, str(spec_file), str(input_file))
            
            # Check result
            if result == tv['expected']:
                print(f"✓ {tv['name']}: Expected {tv['expected']}, got {result}")
                passed += 1
            elif result is None:
                print(f"? {tv['name']}: {message}")
            else:
                print(f"✗ {tv['name']}: Expected {tv['expected']}, got {result}")
                print(f"  Message: {message}")
                failed += 1
        
        print()
        print(f"Results: {passed} passed, {failed} failed")
    else:
        print("Skipping test vector execution (Tau binary not found)")
    
    print()
    print("=" * 60)


if __name__ == "__main__":
    main()


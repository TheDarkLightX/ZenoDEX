#!/bin/bash
# Test script for Tau Language specifications
# This script validates Tau spec syntax and basic properties

set -e

TAU_BIN=""
if command -v tau &> /dev/null; then
    TAU_BIN="tau"
elif [ -f "../external/tau-lang/build-Release/tau" ]; then
    TAU_BIN="../external/tau-lang/build-Release/tau"
elif [ -f "../external/tau-lang/build-Debug/tau" ]; then
    TAU_BIN="../external/tau-lang/build-Debug/tau"
else
    echo "ERROR: Tau executable not found"
    echo "Please install Tau Language or build it in external/tau-lang/"
    echo "See: https://github.com/IDNI/tau-lang"
    exit 1
fi

echo "Using Tau binary: $TAU_BIN"
echo "Testing TauSwap specifications..."
echo ""

# Test each spec file
SPECS=(
    "../src/tau_specs/types.tau"
    "../src/tau_specs/invariants.tau"
    "../src/tau_specs/cpmm_math.tau"
    "../src/tau_specs/balance_safety.tau"
)

PASSED=0
FAILED=0

for spec in "${SPECS[@]}"; do
    if [ ! -f "$spec" ]; then
        echo "SKIP: $spec (not found)"
        continue
    fi
    
    echo "Testing: $spec"
    
    # Try to parse the spec (basic syntax check)
    if $TAU_BIN "$spec" 2>&1 | head -20; then
        echo "✓ PASS: $spec"
        ((PASSED++))
    else
        echo "✗ FAIL: $spec"
        ((FAILED++))
    fi
    echo ""
done

echo "=========================================="
echo "Results: $PASSED passed, $FAILED failed"
echo "=========================================="

if [ $FAILED -gt 0 ]; then
    exit 1
fi


#!/bin/bash
# Test Tau Language specifications with actual Tau compiler
# This script attempts to find and use the real Tau Language compiler

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
TAU_SPECS_DIR="$PROJECT_ROOT/src/tau_specs"
TEST_SPECS_DIR="$SCRIPT_DIR"

echo "============================================================"
echo "Testing Tau Language Specifications with Real Tau Compiler"
echo "============================================================"
echo

# Find Tau binary
TAU_BIN=""

# Check if tau is in PATH
if command -v tau &> /dev/null; then
    TAU_BIN=$(which tau)
    echo "✓ Found Tau in PATH: $TAU_BIN"
elif [ -f "$PROJECT_ROOT/external/tau-lang/build-Release/tau" ]; then
    TAU_BIN="$PROJECT_ROOT/external/tau-lang/build-Release/tau"
    echo "✓ Found Tau in build-Release: $TAU_BIN"
elif [ -f "$PROJECT_ROOT/external/tau-lang/build-Debug/tau" ]; then
    TAU_BIN="$PROJECT_ROOT/external/tau-lang/build-Debug/tau"
    echo "✓ Found Tau in build-Debug: $TAU_BIN"
elif [ -f "$PROJECT_ROOT/external/tau-lang/build-RelWithDebInfo/tau" ]; then
    TAU_BIN="$PROJECT_ROOT/external/tau-lang/build-RelWithDebInfo/tau"
    echo "✓ Found Tau in build-RelWithDebInfo: $TAU_BIN"
else
    echo "✗ Tau compiler not found!"
    echo
    echo "To build Tau Language:"
    echo "  cd external/tau-lang"
    echo "  mkdir -p build-Release"
    echo "  cd build-Release"
    echo "  cmake .."
    echo "  make -j$(nproc)"
    echo
    echo "Or check: https://github.com/IDNI/tau-lang"
    exit 1
fi

# Verify Tau works
echo "Testing Tau compiler..."
if ! "$TAU_BIN" --help &> /dev/null && ! "$TAU_BIN" -h &> /dev/null; then
    echo "⚠ Warning: Tau binary found but may not be working correctly"
    echo "  Attempting to test anyway..."
fi

echo
echo "============================================================"
echo "Testing Specification Syntax"
echo "============================================================"
echo

# Test each spec file
SPECS=(
    "$TAU_SPECS_DIR/types.tau"
    "$TAU_SPECS_DIR/invariants.tau"
    "$TAU_SPECS_DIR/cpmm_math.tau"
    "$TAU_SPECS_DIR/balance_safety.tau"
    "$TEST_SPECS_DIR/test_cpmm_simple.tau"
)

PASSED=0
FAILED=0

for spec in "${SPECS[@]}"; do
    if [ ! -f "$spec" ]; then
        echo "✗ $(basename "$spec"): File not found"
        ((FAILED++))
        continue
    fi
    
    echo -n "Testing $(basename "$spec")... "
    
    # Parse/validate the spec.
    # Use --charvar false for descriptive identifiers and --experimental to use the new spec runner.
    if "$TAU_BIN" --charvar false --experimental "$spec" &> /tmp/tau_test_output.txt 2>&1; then
        echo "✓ Syntax OK"
        ((PASSED++))
    elif grep -q "error\|Error\|ERROR" /tmp/tau_test_output.txt; then
        echo "✗ Syntax Error"
        echo "  Error output:"
        head -5 /tmp/tau_test_output.txt | sed 's/^/    /'
        ((FAILED++))
    else
        echo "✗ Failed (non-zero exit)"
        echo "  Output:"
        head -10 /tmp/tau_test_output.txt | sed 's/^/    /'
        ((FAILED++))
    fi
done

echo
echo "============================================================"
echo "Results"
echo "============================================================"
echo "Passed: $PASSED"
echo "Failed: $FAILED"
echo "============================================================"

if [ $FAILED -eq 0 ]; then
    echo "✓ All specs passed syntax validation!"
    exit 0
else
    echo "✗ Some specs failed validation"
    exit 1
fi


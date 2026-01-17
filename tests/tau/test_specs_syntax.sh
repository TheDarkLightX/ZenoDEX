#!/bin/bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

TAU_BIN=""
if [ -x "$PROJECT_ROOT/external/tau-nightly/usr/bin/tau" ]; then
  TAU_BIN="$PROJECT_ROOT/external/tau-nightly/usr/bin/tau"
elif [ -f "$PROJECT_ROOT/external/tau-lang/build-Release/tau" ]; then
  TAU_BIN="$PROJECT_ROOT/external/tau-lang/build-Release/tau"
elif [ -f "$PROJECT_ROOT/external/tau-lang/build-Debug/tau" ]; then
  TAU_BIN="$PROJECT_ROOT/external/tau-lang/build-Debug/tau"
elif command -v tau >/dev/null 2>&1; then
  TAU_BIN="$(command -v tau)"
else
  echo "Tau compiler not found. Build it at external/tau-lang/build-Release/tau" >&2
  exit 1
fi

SPECS_DIR="$PROJECT_ROOT/src/tau_specs"

TIMEOUT_SECONDS="${TAU_TIMEOUT_SECONDS:-60}"
PASSED=0
FAILED=0

for spec in "$SPECS_DIR"/*.tau; do
  if [ ! -f "$spec" ]; then
    continue
  fi

  name="$(basename "$spec")"
  echo -n "Checking $name... "

  status=0
  if ! timeout "$TIMEOUT_SECONDS" "$TAU_BIN" "$spec" --severity error --charvar false -x </dev/null >/tmp/tau_spec_check_out.txt 2>&1; then
    status=$?
  fi
  if grep -q "(Error)" /tmp/tau_spec_check_out.txt; then
    echo "FAIL"
    head -20 /tmp/tau_spec_check_out.txt | sed 's/^/  /'
    FAILED=$((FAILED + 1))
  else
    echo "OK"
    PASSED=$((PASSED + 1))
  fi
done

echo "Passed: $PASSED"
echo "Failed: $FAILED"

if [ "$FAILED" -ne 0 ]; then
  exit 1
fi

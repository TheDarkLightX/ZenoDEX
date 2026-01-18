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

strip_ansi() {
  python3 -c 'import re,sys; sys.stdout.write(re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", sys.stdin.read()))' || cat
}

for spec in "$SPECS_DIR"/*.tau; do
  if [ ! -f "$spec" ]; then
    continue
  fi

  name="$(basename "$spec")"
  echo -n "Checking $name... "

  tmp_out="$(mktemp)"
  tmp_spec="$(mktemp)"
  # Tau's file-runner does not accept repo-local REPL directives like `set charvar off`,
  # and is also stricter about multi-line `always` blocks. Normalize the spec the same
  # way our Python runner does for reproducible execution-based parsing.
  #
  # NOTE: This is a syntax-by-execution check, not a semantic/correctness check.
  if ! PYTHONPATH="$PROJECT_ROOT" python3 -c 'from pathlib import Path; import sys; from src.integration.tau_runner import normalize_spec_text; p=Path(sys.argv[1]); sys.stdout.write(normalize_spec_text(p.read_text(encoding="utf-8")))' "$spec" >"$tmp_spec"; then
    echo "FAIL (normalize)"
    FAILED=$((FAILED + 1))
    rm -f "$tmp_out" "$tmp_spec"
    continue
  fi

  status=0
  # Send a single newline to terminate immediately after the first prompt.
  if ! timeout "$TIMEOUT_SECONDS" bash -lc "printf '\n' | \"$TAU_BIN\" \"$tmp_spec\" --severity error --charvar false -x" >"$tmp_out" 2>&1; then
    status=$?
  fi

  # Tau prints colored `(Error)` markers; normalize before matching.
  clean_out="$(strip_ansi <"$tmp_out")"
  if [ "$status" -ne 0 ] || echo "$clean_out" | grep -q "Syntax Error"; then
    echo "FAIL (rc=$status)"
    echo "$clean_out" | head -20 | sed 's/^/  /'
    FAILED=$((FAILED + 1))
  else
    echo "OK"
    PASSED=$((PASSED + 1))
  fi

  rm -f "$tmp_out" "$tmp_spec"
done

echo "Passed: $PASSED"
echo "Failed: $FAILED"

if [ "$FAILED" -ne 0 ]; then
  exit 1
fi

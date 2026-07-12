#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

if [[ -n "${PYTHON:-}" ]]; then
  PY="$PYTHON"
elif [[ -x "$ROOT_DIR/.venv/bin/python" ]]; then
  PY="$ROOT_DIR/.venv/bin/python"
else
  PY="python3"
fi

require_cmd() {
  local command_name="$1"
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "error: missing required command '$command_name'" >&2
    exit 2
  fi
}

require_cmd "julia"
require_cmd "lake"

echo "== partial-liquidation-semantics-v1: generated artifact drift =="
"$PY" tools/build_perp_partial_liquidation_semantics_v1.py --check

echo "== partial-liquidation-semantics-v1: Python + Julia + Lean parity =="
"$PY" tools/check_perp_partial_liquidation_semantics_v1.py \
  --julia "$(command -v julia)" \
  --lake "$(command -v lake)"

echo "== partial-liquidation-semantics-v1: regression tests =="
"$PY" -m pytest -q \
  tests/test_check_perp_partial_liquidation_semantics_v1.py \
  tests/formal/test_lean_perp_partial_liquidation_exact.py \
  tests/formal/test_lean_perp_margin_rounding_safety.py \
  tests/core/test_perp_v2/test_partial_liquidate.py

echo "ok"

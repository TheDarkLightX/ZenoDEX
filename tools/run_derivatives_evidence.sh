#!/usr/bin/env bash
set -euo pipefail

# Evidence runner for derivative kernels (non-perps).
#
# Goal: provide a single, deterministic entrypoint to run the current evidence
# gates for derivative-market kernels in this repo:
# - pytest correctness/determinism checks
# - YAML kernel inductiveness checks (via the optional kernel toolchain)
#
# Notes:
# - This script is fail-closed: missing toolchains are treated as errors.

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

if [[ -n "${PYTHON:-}" ]]; then
  PY="$PYTHON"
elif [[ -x "$ROOT_DIR/.venv/bin/python" ]]; then
  PY="$ROOT_DIR/.venv/bin/python"
else
  PY="python3"
fi

if [[ ! -d "$ROOT_DIR/external/ESSO" ]]; then
  echo "error: missing external toolchain at $ROOT_DIR/external/ESSO" >&2
  echo "hint: clone it into external/ (external/ is git-ignored by design)" >&2
  exit 2
fi

export PYTHONPATH="$ROOT_DIR/external/ESSO${PYTHONPATH:+:$PYTHONPATH}"

echo "== derivatives: claims registry format check =="
"$PY" "$ROOT_DIR/tools/check_claims_registry.py"

echo "== derivatives: pytest =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/core/test_derivatives_generated_refs.py" \
  "$ROOT_DIR/tests/core/test_funding_rate_market.py" \
  "$ROOT_DIR/tests/core/test_funding_rate_market_ref_parity.py" \
  "$ROOT_DIR/tests/core/test_il_futures.py" \
  "$ROOT_DIR/tests/core/test_curve_selection.py"

echo "== derivatives: kernel inductiveness (verify-multi) =="
"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/funding_rate_market_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/funding_rate_market_v1_1.yaml" \
  --solvers z3 \
  --timeout-ms 60000 \
  --determinism-trials 2

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/il_futures_market_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/curve_selection_market_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2

echo "ok"

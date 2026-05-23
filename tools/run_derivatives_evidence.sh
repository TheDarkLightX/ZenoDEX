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

RUN_SUPPLEMENTAL_FUNDING_RATE_MARKET_V1_1_MONOLITH="${RUN_SUPPLEMENTAL_FUNDING_RATE_MARKET_V1_1_MONOLITH:-0}"

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

VERIFY_ROOT="$ROOT_DIR/internal/esso_verify/derivatives"
mkdir -p "$VERIFY_ROOT"

echo "== derivatives: claims registry format check =="
"$PY" "$ROOT_DIR/tools/check_claims_registry.py"

echo "== derivatives: pytest =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/core/test_derivatives_generated_refs.py" \
  "$ROOT_DIR/tests/core/test_funding_rate_market.py" \
  "$ROOT_DIR/tests/core/test_funding_rate_market_ref_parity.py" \
  "$ROOT_DIR/tests/core/test_funding_rate_settlement_runtime_v1_1.py" \
  "$ROOT_DIR/tests/core/test_il_futures.py" \
  "$ROOT_DIR/tests/core/test_curve_selection.py" \
  "$ROOT_DIR/tests/core/test_volatility_tier.py" \
  "$ROOT_DIR/tests/core/test_volatility_tier_ref_parity.py" \
  "$ROOT_DIR/tests/kernels/test_funding_rate_settlement_witness_v1_1_native_adapter.py"

echo "== derivatives: kernel inductiveness (verify-multi) =="
"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/funding_rate_market_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/funding_rate_market_v1" \
  --write-report

echo "== derivatives: funding_rate_settlement_witness_v1_1 dual-solver proof =="
"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/funding_rate_settlement_witness_v1_1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/funding_rate_settlement_witness_v1_1" \
  --write-report

echo "== derivatives: funding_rate_settlement_witness_v1_1 shell assurance =="
"$PY" -m ESSO shell-lint \
  "$ROOT_DIR/src/kernels/dex/funding_rate_settlement_witness_v1_1.yaml" \
  --adapter src.kernels.python.funding_rate_settlement_witness_v1_1_native_adapter:make_adapter \
  --output "$VERIFY_ROOT/funding_rate_settlement_witness_v1_1_shell_lint.json"
"$PY" -m ESSO verify-shell \
  "$ROOT_DIR/src/kernels/dex/funding_rate_settlement_witness_v1_1.yaml" \
  --adapter src.kernels.python.funding_rate_settlement_witness_v1_1_native_adapter:make_adapter \
  --traces 16 \
  --max-steps 6 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/funding_rate_settlement_witness_v1_1_shell_verify.json"

if [[ "$RUN_SUPPLEMENTAL_FUNDING_RATE_MARKET_V1_1_MONOLITH" == "1" ]]; then
  echo "== derivatives: funding_rate_market_v1_1 supplemental monolith check (z3-only) ==" >&2
  echo "note: this is a supplementary parity/reference check only; it is not part of the published formal release lane." >&2
  "$PY" -m ESSO verify-multi \
    "$ROOT_DIR/src/kernels/dex/funding_rate_market_v1_1.yaml" \
    --solvers z3 \
    --timeout-ms 60000 \
    --determinism-trials 2 \
    --output "$VERIFY_ROOT/funding_rate_market_v1_1" \
    --write-report
fi

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/il_futures_market_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/il_futures_market_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/curve_selection_market_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/curve_selection_market_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/volatility_tier_controller_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/volatility_tier_controller_v1" \
  --write-report

echo "== derivatives: manifest check =="
"$PY" "$ROOT_DIR/tools/check_derivatives_evidence_manifest.py"

echo "ok"

#!/usr/bin/env bash
set -euo pipefail

# Evidence runner for spot DEX (swap + liquidity + vault).
#
# Goal: provide a single, deterministic entrypoint to run the current evidence
# gates for the spot/AMM functional core:
# - pytest correctness/determinism checks (incl. parity + BVA)
# - UPBA certificate and bounded price-grid verifier checks
# - YAML kernel inductiveness checks (verify-multi)
#
# Notes:
# - Fail-closed: missing toolchains are treated as errors.
# - These checks are necessary but not sufficient for "no bugs"; the CBC posture
#   relies on keeping consensus-critical logic kernel-backed and minimizing glue.

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

if [[ -n "${PYTHON:-}" ]]; then
  PY="$PYTHON"
elif [[ -x "$ROOT_DIR/.venv/bin/python" ]]; then
  PY="$ROOT_DIR/.venv/bin/python"
else
  PY="python3"
fi

if [[ -d "$ROOT_DIR/external/ESSO" ]]; then
  export PYTHONPATH="$ROOT_DIR/external/ESSO${PYTHONPATH:+:$PYTHONPATH}"
else
  # Allow running against an installed ESSO module (e.g., CI/dev venv).
  if ! "$PY" -c "import importlib.util as u; raise SystemExit(0 if u.find_spec('ESSO') else 1)"; then
    echo "error: missing ESSO toolchain (expected either $ROOT_DIR/external/ESSO or an importable ESSO module)" >&2
    exit 2
  fi
fi

require_file() {
  local label="$1"
  local path="$2"
  if [[ ! -f "$path" ]]; then
    echo "error: missing required file for $label: $path" >&2
    exit 2
  fi
}

require_file "cpmm exported ref" "$ROOT_DIR/generated/cpmm_python/cpmm_swap_ref.py"
require_file "dex v7 cpmm exported ref" "$ROOT_DIR/generated/dex_v7_python/cpmm_swap_v7_ref.py"
require_file "dex v7 fee exported ref" "$ROOT_DIR/generated/dex_v7_python/fee_calculation_v7_ref.py"
require_file "dex v7 lp mint exported ref" "$ROOT_DIR/generated/dex_v7_python/lp_mint_v7_ref.py"
require_file "dex v7 lp ratio exported ref" "$ROOT_DIR/generated/dex_v7_python/lp_ratio_calculator_v7_ref.py"
require_file "dex v7 circuit breaker exported ref" "$ROOT_DIR/generated/dex_v7_python/circuit_breaker_v7_ref.py"
require_file "dex step core exported ref" "$ROOT_DIR/generated/dex_v8_python/dex_step_core_v2_ref.py"
require_file "vault exported ref" "$ROOT_DIR/generated/vault_python/vault_manager_ref.py"
require_file "batch auction exported ref" "$ROOT_DIR/generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py"

echo "== spot: claims registry format check =="
"$PY" "$ROOT_DIR/tools/check_claims_registry.py"

echo "== spot: pytest =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/core/test_cpmm.py" \
  "$ROOT_DIR/tests/core/test_cpmm_ref_parity.py" \
  "$ROOT_DIR/tests/core/test_cpmm_u256_safety.py" \
  "$ROOT_DIR/tests/core/test_batch_clearing.py" \
  "$ROOT_DIR/tests/core/test_batch_clearing_coverage_edges.py" \
  "$ROOT_DIR/tests/core/test_batch_clearing_properties.py" \
  "$ROOT_DIR/tests/core/test_batch_clearing_b_refinement.py" \
  "$ROOT_DIR/tests/core/test_batch_clearing_global_refinement.py" \
  "$ROOT_DIR/tests/core/test_batch_greedy.py" \
  "$ROOT_DIR/tests/core/test_batch_auction_settler_v1_ref_parity.py" \
  "$ROOT_DIR/tests/core/test_batch_auction_settler_v1_witness.py" \
  "$ROOT_DIR/tests/core/test_uniform_batch_clearing.py" \
  "$ROOT_DIR/tests/core/test_uniform_batch_optimality.py" \
  "$ROOT_DIR/tests/core/test_uniform_batch_price_grid_table.py" \
  "$ROOT_DIR/tests/core/test_settlement_swap_runtime_v1.py" \
  "$ROOT_DIR/tests/core/test_settlement_normal_form.py" \
  "$ROOT_DIR/tests/core/test_settlement_strong_validator.py" \
  "$ROOT_DIR/tests/core/test_dex_step.py" \
  "$ROOT_DIR/tests/core/test_dex_step_candidate_settlement.py" \
  "$ROOT_DIR/tests/core/test_dex_step_core_v2_ref_parity.py" \
  "$ROOT_DIR/tests/core/test_dex_step_core_v2_ml_bva_parity.py" \
  "$ROOT_DIR/tests/core/test_vault_ref_parity.py" \
  "$ROOT_DIR/tests/integration/test_dex_engine_uniform_batch_certificate.py"

echo "== spot: kernel inductiveness (verify-multi) =="
"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/cpmm_swap_v8.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/lp_mint_v8.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/vault_manager.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/dex_step_core_v2.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/batch_auction_settler_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$ROOT_DIR/internal/esso_verify/batch_auction_settler_v1" \
  --write-report

echo "ok"

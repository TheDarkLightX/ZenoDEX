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

require_module() {
  local module="$1"
  local package_hint="$2"
  if ! "$PY" -c "import importlib.util as u, sys; sys.exit(0 if u.find_spec('$module') else 1)"; then
    echo "error: missing python module '$module'" >&2
    echo "hint: install dev tooling with '$PY -m pip install --require-hashes -r requirements-dev.lock.txt'" >&2
    echo "hint: expected package: $package_hint" >&2
    exit 2
  fi
}

require_module "pytest" "pytest"
require_module "pytest_cov" "pytest-cov"
require_module "ruff" "ruff"
require_module "mypy" "mypy"

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
require_file "volatility tier exported ref" "$ROOT_DIR/generated/volatility_tier_controller_v1_python_ref/volatility_tier_controller_v1_ref.py"
require_file "batch auction exported ref" "$ROOT_DIR/generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py"

CRITICAL_TESTS=(
  tests/test_check_test_hygiene_v1.py
  tests/test_run_test_hygiene_gate_v1.py
  tests/core/test_domain_bounds.py
  tests/core/test_functional_core_no_floats.py
  tests/core/test_cpmm.py
  tests/core/test_cpmm_ref_parity.py
  tests/core/test_cpmm_u256_safety.py
  tests/core/test_liquidity.py
  tests/core/test_dex_v7_ref_parity.py
  tests/core/test_fees_bva.py
  tests/core/test_oracle_freshness_bva.py
  tests/core/test_vault_ref_parity.py
  tests/core/test_batch_clearing.py
  tests/core/test_batch_clearing_coverage_edges.py
  tests/core/test_batch_auction_settler_v1_ref_parity.py
  tests/core/test_batch_auction_settler_v1_witness.py
  tests/core/test_settlement_swap_runtime_v1.py
  tests/core/test_batch_clearing_properties.py
  tests/core/test_batch_greedy.py
  tests/core/test_batch_clearing_b_refinement.py
  tests/core/test_batch_clearing_global_refinement.py
  tests/core/test_dex_step.py
  tests/core/test_dex_step_candidate_settlement.py
  tests/core/test_dex_state_immutability.py
  tests/core/test_quote_receipts.py
  tests/core/test_settlement.py
  tests/core/test_settlement_strong_validator.py
  tests/core/test_volatility_tier.py
  tests/core/test_volatility_tier_ref_parity.py
  tests/core/test_perp_v2
  tests/integration/test_perps_api.py
  tests/integration/test_tau_gate_boundary.py
  tests/integration/test_validation_uses_strong_settlement_gate.py
  tests/state/test_balances.py
  tests/state/test_intents.py
  tests/state/test_lp.py
  tests/state/test_volatility.py
)

COVERAGE_TARGETS=(
  --cov=src.core.domain_limits
  --cov=src.core.cpmm
  --cov=src.core.liquidity
  --cov=src.core.batch_clearing
  --cov=src.core.dex
  --cov=src.core.quote_receipts
  --cov=src.core.settlement
  --cov=src.core.settlement_strong_validator
  --cov=src.core.volatility_tier
  --cov=src.core.perp_v2
  --cov=src.integration.perps_api
  --cov=src.integration.validation
  --cov=src.kernels.python.batch_auction_settler_v1_witness
  --cov=src.kernels.python.settlement_swap_runtime_v1
  --cov=src.state.balances
  --cov=src.state.immutable_collections
  --cov=src.state.intents
  --cov=src.state.lp
  --cov=src.state.nonces
  --cov=src.state.pools
  --cov=src.state.state_snapshots
  --cov=src.state.volatility
)

echo "== critical: ruff =="
"$PY" -m ruff check \
  tools/acceptance_tcb_mutation_harness.py \
  tools/check_acceptance_tcb_coverage.py \
  tools/check_test_hygiene_v1.py \
  tools/run_test_hygiene_gate_v1.py \
  tools/test_hygiene_evidence_v1.py \
  tools/test_hygiene_model_v1.py \
  src/core/domain_limits.py \
  src/core/cpmm.py \
  src/core/liquidity.py \
  src/core/batch_clearing.py \
  src/core/dex.py \
  src/core/fees.py \
  src/core/oracle.py \
  src/core/perps.py \
  src/core/quote_receipts.py \
  src/core/settlement.py \
  src/core/settlement_strong_validator.py \
  src/core/vault.py \
  src/core/volatility_tier.py \
  src/core/perp_v2 \
  src/integration/perps_api.py \
  src/integration/validation.py \
  src/kernels/python/batch_auction_settler_v1_witness.py \
  src/kernels/python/settlement_swap_runtime_v1.py \
  src/state/balances.py \
  src/state/immutable_collections.py \
  src/state/intents.py \
  src/state/lp.py \
  src/state/nonces.py \
  src/state/pools.py \
  src/state/state_snapshots.py \
  src/state/volatility.py \
  tests/core/test_domain_bounds.py \
  tests/test_check_test_hygiene_v1.py \
  tests/test_run_test_hygiene_gate_v1.py \
  tests/core/test_batch_clearing_properties.py \
  tests/core/test_batch_clearing_coverage_edges.py \
  tests/core/test_batch_auction_settler_v1_ref_parity.py \
  tests/core/test_batch_auction_settler_v1_witness.py \
  tests/core/test_settlement_swap_runtime_v1.py \
  tests/core/test_quote_receipts.py \
  tests/core/test_quote_receipts_fuzz.py \
  tests/core/test_settlement.py \
  tests/core/test_liquidity.py \
  tests/core/test_perp_v2/test_submodules.py \
  tests/core/test_settlement_strong_validator.py \
  tests/core/test_intent_normal_form.py \
  tests/core/test_support_root.py \
  tests/core/test_volatility_tier.py \
  tests/core/test_volatility_tier_ref_parity.py \
  tests/core/test_dex_step.py \
  tests/core/test_dex_step_candidate_settlement.py \
  tests/core/test_dex_state_immutability.py \
  tests/integration/test_dex_engine_helpers.py \
  tests/integration/test_operations_fuzz.py \
  tests/integration/test_proof_verifier_fuzz.py \
  tests/integration/test_proof_verifier_unit.py \
  tests/integration/test_replay_protection.py \
  tests/integration/test_tau_testnet_dex_plugin_recovery.py \
  tests/integration/test_tau_gate_boundary.py \
  tests/integration/test_validation_uses_strong_settlement_gate.py \
  tests/state/test_balances.py \
  tests/state/test_nonces.py \
  tests/state/test_intents.py \
  tests/state/test_lp.py \
  tests/state/test_volatility.py

echo "== critical: shell syntax =="
bash -n \
  "$ROOT_DIR/tools/run_acceptance_tcb_gate.sh" \
  "$ROOT_DIR/tools/run_acceptance_tcb_mutation_gate.sh" \
  "$ROOT_DIR/tools/run_acceptance_tcb_fuzz_gate.sh" \
  "$ROOT_DIR/tools/run_spot_proof_assurance_gate.sh" \
  "$ROOT_DIR/tools/run_snapshot_recovery_gate.sh" \
  "$ROOT_DIR/tools/run_critical_quality_gate.sh" \
  "$ROOT_DIR/tools/run_release_gate.sh"

echo "== critical: mypy =="
"$PY" -m mypy

echo "== critical: test hygiene contract =="
"$PY" tools/check_test_hygiene_v1.py

echo "== critical: acceptance TCB gate =="
bash "$ROOT_DIR/tools/run_acceptance_tcb_gate.sh"

echo "== critical: pytest + coverage =="
PYTEST_COVERAGE_CMD=(
  "$PY"
  -m
  pytest
  -q
  "${COVERAGE_TARGETS[@]}"
  --cov-branch
  --cov-report=term-missing:skip-covered
  "${CRITICAL_TESTS[@]}"
)
"${PYTEST_COVERAGE_CMD[@]}"

echo "ok"

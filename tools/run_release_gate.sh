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

if [[ -n "${LAKE:-}" ]]; then
  LAKE_BIN="$LAKE"
elif command -v lake >/dev/null 2>&1; then
  LAKE_BIN="lake"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  LAKE_BIN="$HOME/.elan/bin/lake"
else
  LAKE_BIN="lake"
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

require_file() {
  local label="$1"
  local path="$2"
  if [[ ! -f "$path" ]]; then
    echo "error: missing required file for $label: $path" >&2
    exit 2
  fi
}

run_if_present() {
  local label="$1"
  local path="$2"
  if [[ ! -f "$path" ]]; then
    echo "error: expected artifact runner '$path' for $label" >&2
    exit 2
  fi
  echo "== release: $label =="
  bash "$path"
}

require_module "pytest" "pytest"
require_module "pip_audit" "pip-audit"
require_file "runtime dependency lock" "$ROOT_DIR/requirements-core.lock.txt"
require_file "agent dependency lock" "$ROOT_DIR/requirements-agents.lock.txt"
require_file "dev dependency lock" "$ROOT_DIR/requirements-dev.lock.txt"

echo "== release: python dependency hash locks =="
"$PY" "$ROOT_DIR/tools/check_python_hash_locks.py"
"$PY" -m pytest -q "$ROOT_DIR/tests/test_check_python_hash_locks.py"

echo "== release: proof toolchain lock =="
"$PY" "$ROOT_DIR/tools/check_proof_toolchain_lock.py"

echo "== release: critical quality gate =="
bash "$ROOT_DIR/tools/run_critical_quality_gate.sh"

echo "== release: public assurance snapshot docs =="
"$PY" "$ROOT_DIR/tools/render_assurance_release_snapshot.py" --check

echo "== release: public claim scope =="
"$PY" "$ROOT_DIR/tools/check_public_claim_scope.py"

echo "== release: ZenoLedger proof coverage matrix =="
"$PY" "$ROOT_DIR/tools/check_zeno_ledger_proof_coverage_matrix.py"
"$PY" -m pytest -q "$ROOT_DIR/tests/tools/test_check_zeno_ledger_proof_coverage_matrix.py"

echo "== release: disaster-axis status manifest =="
"$PY" "$ROOT_DIR/tools/check_disaster_axis_status_manifest.py" --root "$ROOT_DIR"
"$PY" -m pytest -q "$ROOT_DIR/tests/tools/test_check_disaster_axis_status_manifest.py"

echo "== release: ZenoDEX host-independent coverage =="
"$PY" "$ROOT_DIR/tools/check_zenodex_host_independent_coverage.py"
"$PY" "$ROOT_DIR/tools/measure_zenodex_zk_transition_coverage.py"
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/tools/test_check_zenodex_host_independent_coverage.py" \
  "$ROOT_DIR/tests/tools/test_measure_zenodex_zk_transition_coverage.py"

echo "== release: ZenoLedger two-machine evidence archive tooling =="
"$PY" -m py_compile \
  "$ROOT_DIR/tools/build_zeno_ledger_two_machine_evidence.py" \
  "$ROOT_DIR/tools/check_zeno_ledger_two_machine_evidence.py" \
  "$ROOT_DIR/tests/tools/test_build_zeno_ledger_two_machine_evidence.py" \
  "$ROOT_DIR/tests/tools/test_check_zeno_ledger_two_machine_evidence.py"
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/tools/test_build_zeno_ledger_two_machine_evidence.py" \
  "$ROOT_DIR/tests/tools/test_check_zeno_ledger_two_machine_evidence.py"

echo "== release: covered user interface boundary =="
"$PY" "$ROOT_DIR/tools/check_covered_user_interface_boundary.py" \
  "$ROOT_DIR/internal/covered_user_interface/COVERED_USER_INTERFACE_BOUNDARY_V0.json"
"$PY" -m pytest -q "$ROOT_DIR/tests/tools/test_check_covered_user_interface_boundary.py"

echo "== release: internal ZENO economic games boundary =="
"$PY" "$ROOT_DIR/tools/check_zeno_economic_games_boundary.py" \
  "$ROOT_DIR/internal/tokenomics/ZENO_ECONOMIC_GAMES_BOUNDARY_V0.json"
"$PY" -m pytest -q "$ROOT_DIR/tests/tools/test_check_zeno_economic_games_boundary.py"

echo "== release: internal ZENO treasury custody boundary =="
"$PY" "$ROOT_DIR/tools/check_zeno_treasury_custody_boundary.py" \
  "$ROOT_DIR/internal/tokenomics/ZENO_TREASURY_CUSTODY_BOUNDARY_V0.json"
"$PY" -m pytest -q "$ROOT_DIR/tests/tools/test_check_zeno_treasury_custody_boundary.py"

echo "== release: internal tokenomics candidate model =="
"$PY" "$ROOT_DIR/tools/check_tokenomics_candidate_model.py" \
  "$ROOT_DIR/internal/tokenomics/ZENO_TOKENOMICS_CANDIDATE_MODEL_V0.json"
"$PY" "$ROOT_DIR/tools/check_burn_indexed_unlock_accelerator.py" \
  "$ROOT_DIR/internal/tokenomics/ZENO_BURN_INDEXED_UNLOCK_ACCELERATOR_V0.json"
"$PY" "$ROOT_DIR/tools/check_tokenomics_reward_safety_envelope.py" \
  "$ROOT_DIR/internal/tokenomics/ZENO_TOKENOMICS_REWARD_SAFETY_ENVELOPE_V0.json"
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/tools/test_check_tokenomics_candidate_model.py" \
  "$ROOT_DIR/tests/tools/test_check_burn_indexed_unlock_accelerator.py" \
  "$ROOT_DIR/tests/tools/test_check_tokenomics_reward_safety_envelope.py"

echo "== release: internal gamification manifest =="
"$PY" "$ROOT_DIR/tools/check_gamification_manifest.py" \
  "$ROOT_DIR/internal/gamification/GAMIFICATION_MANIFEST_V0.json"
"$PY" -m pytest -q "$ROOT_DIR/tests/tools/test_check_gamification_manifest.py"

echo "== release: internal staking share safety proofs =="
(
  cd "$ROOT_DIR/lean-mathlib"
  "$LAKE_BIN" env lean Proofs/ZenoDEXStakingShareSafety.lean
)
"$PY" -m pytest -q "$ROOT_DIR/tests/formal/test_lean_zenodex_staking_share_safety.py"

echo "== release: UPBA v1 grid economic profiles =="
"$PY" "$ROOT_DIR/tools/upba_v1_grid_economic_profile.py"
"$PY" -m pytest -q "$ROOT_DIR/tests/tools/test_upba_v1_grid_economic_profile.py"

echo "== release: UPBA bounded-grid optimality =="
(
  cd "$ROOT_DIR/lean-mathlib"
  "$LAKE_BIN" env lean Proofs/UniformBatchOptimality.lean
)
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/core/test_uniform_batch_optimality.py" \
  "$ROOT_DIR/tests/integration/test_dex_engine_uniform_batch_certificate.py"

echo "== release: Risc0 proof metadata adapter =="
"$PY" -m py_compile \
  "$ROOT_DIR/tools/zeno_ledger_risc0_proof_metadata.py" \
  "$ROOT_DIR/tools/zeno_ledger_risc0_real_proof_smoke.py" \
  "$ROOT_DIR/tools/check_zeno_ledger_risc0_real_proof_smoke_report.py" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_risc0_proof_metadata.py" \
  "$ROOT_DIR/tests/test_check_zeno_ledger_risc0_real_proof_smoke_report.py"
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_risc0_proof_metadata.py" \
  "$ROOT_DIR/tests/test_check_zeno_ledger_risc0_real_proof_smoke_report.py"

echo "== release: TEE proof metadata adapter =="
cargo test --manifest-path "$ROOT_DIR/tools/confidential_attestation_verifier_rust/Cargo.toml"
"$PY" -m pytest -q "$ROOT_DIR/tests/integration/test_zeno_ledger_tee_proof_metadata.py"

echo "== release: Rust runtime parity =="
bash "$ROOT_DIR/tools/run_rust_runtime_parity_gate.sh"

echo "== release: confidential route quote binding =="
"$PY" -m pytest -q "$ROOT_DIR/tests/tools/test_check_confidential_route_quote_bundle.py"

echo "== release: ZenoCover regulatory boundary =="
"$PY" "$ROOT_DIR/tools/check_zenocover_regulatory_boundary.py" \
  "$ROOT_DIR/internal/zenocover/REGULATORY_BOUNDARY_MANIFEST_V0.json"
"$PY" -m pytest -q "$ROOT_DIR/tests/tools/test_check_zenocover_regulatory_boundary.py"

echo "== release: ZenoCover LP loss cover and reserve suite =="
"$PY" "$ROOT_DIR/tools/check_zenocover_lp_loss_cover.py"
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/tools/test_check_zenocover_lp_loss_cover.py" \
  "$ROOT_DIR/tests/tools/test_check_zenocover_reserve_solvency.py" \
  "$ROOT_DIR/tests/tools/test_check_zenocover_claim_verifier_model.py" \
  "$ROOT_DIR/tests/tools/test_check_zenocover_reserve_withdrawal_safety.py"
(
  cd "$ROOT_DIR/lean-mathlib"
  lake env lean Proofs/ZenoCoverPayoutCap.lean
)
"$PY" -m pytest -q "$ROOT_DIR/tests/formal/test_lean_zenocover_payout_cap.py"

echo "== release: ZenoCover attack queries =="
"$PY" "$ROOT_DIR/tools/check_zenocover_attack_queries.py" \
  "$ROOT_DIR/internal/zenocover/ATTACK_QUERY_MANIFEST_V0.json"
"$PY" -m pytest -q "$ROOT_DIR/tests/tools/test_check_zenocover_attack_queries.py"

echo "== release: production boundary =="
"$PY" "$ROOT_DIR/tools/check_production_boundary.py"

echo "== release: candidate supported runtime path =="
"$PY" "$ROOT_DIR/tools/render_rc1_supported_runtime_path.py" --check

echo "== release: tau supported runtime subset =="
"$PY" "$ROOT_DIR/tools/check_tau_supported_runtime_subset.py"

echo "== release: tau experiment promotion candidates =="
"$PY" "$ROOT_DIR/tools/check_tau_experiment_promotion_candidates.py"

echo "== release: candidate verified surface matrix =="
"$PY" "$ROOT_DIR/tools/render_rc1_verified_surface_matrix.py" --check

echo "== release: acceptance mutation gate =="
bash "$ROOT_DIR/tools/run_acceptance_tcb_mutation_gate.sh"

echo "== release: acceptance fuzz gate (fast default lane) =="
bash "$ROOT_DIR/tools/run_acceptance_tcb_fuzz_gate.sh"

echo "== release: snapshot recovery gate =="
bash "$ROOT_DIR/tools/run_snapshot_recovery_gate.sh"

echo "== release: ZenoLedger local hardening =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_v0.py::test_validator_set_hash_is_order_invariant_and_schedule_is_weighted" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_v0.py::test_validator_set_rejects_duplicate_ids_and_zero_voting_power" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_v0.py::test_header_and_body_validator_schedule_binding" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_v0.py::test_validate_body_rejects_batch_cutoff_chain_id_mismatch" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_v0.py::test_validate_body_rejects_batch_cutoff_height_mismatch" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_v0.py::test_validate_body_rejects_ingress_receipt_context_mismatch" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_v0.py::test_validate_body_rejects_forced_inclusion_chain_id_mismatch" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_v0.py::test_detect_header_equivocations_reports_conflicting_height" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_v0.py::test_header_fork_choice_selects_highest_anchored_tip" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_v0.py::test_header_fork_choice_tie_breaks_by_lowest_tip_hash" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_pull_rejects_peer_before_live_fetch_on_admission_mismatch" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_node_public_operator_rejects_inline_auth_tokens" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_node_public_operator_rejects_public_fixture_endpoints" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_node_public_operator_accepts_local_env_auth_forwarding"

echo "== release: tau syntax =="
bash "$ROOT_DIR/tests/tau/test_specs_syntax.sh"

echo "== release: tau traces =="
"$PY" -m pytest -q "$ROOT_DIR/tests/tau/test_spec_registry_traces.py"

echo "== release: tau spec assurance =="
"$PY" -m pytest -q "$ROOT_DIR/tests/tau/test_tau_spec_assurance.py"

echo "== release: tla/tlc shadow models =="
"$PY" "$ROOT_DIR/tools/run_tla_models.py"

echo "== release: tla claim summary =="
"$PY" "$ROOT_DIR/tools/render_tla_claim_summary.py" --check

echo "== release: tau shadow assurance =="
"$PY" "$ROOT_DIR/tools/check_tau_shadow_assurance.py"

run_if_present "perps evidence" "$ROOT_DIR/tools/run_perps_evidence.sh"
run_if_present "spot proof assurance" "$ROOT_DIR/tools/run_spot_proof_assurance_gate.sh"
run_if_present "spot evidence" "$ROOT_DIR/tools/run_spot_evidence.sh"
run_if_present "derivatives evidence" "$ROOT_DIR/tools/run_derivatives_evidence.sh"

echo "== release: coverage map refresh =="
"$PY" "$ROOT_DIR/tools/zenodex_core_coverage_map.py"

require_file "system-spec lint" "$ROOT_DIR/tools/system_spec_lint.py"
require_file "system-spec compose" "$ROOT_DIR/src/kernels/dex/zenodex_system_compose_v2.yaml"
echo "== release: system-spec lint =="
"$PY" "$ROOT_DIR/tools/system_spec_lint.py" "$ROOT_DIR/src/kernels/dex/zenodex_system_compose_v2.yaml"

echo "== release: dependency audit =="
"$PY" -m pip_audit -r "$ROOT_DIR/requirements-core.lock.txt"
"$PY" -m pip_audit -r "$ROOT_DIR/requirements-agents.lock.txt"
"$PY" -m pip_audit -r "$ROOT_DIR/requirements-dev.lock.txt"

echo "ok"

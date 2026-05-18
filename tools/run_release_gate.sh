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
    echo "hint: install dev tooling with '$PY -m pip install -r requirements-dev.txt'" >&2
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

echo "== release: shape v1 ratchet =="
"$PY" "$ROOT_DIR/tools/check_shape_v1_ratchet.py"

echo "== release: negative knowledge ratchet =="
"$PY" "$ROOT_DIR/tools/check_negative_knowledge_ratchet.py"

echo "== release: critical quality gate =="
bash "$ROOT_DIR/tools/run_critical_quality_gate.sh"

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

echo "== release: UPBA grid economic sufficiency =="
"$PY" -m py_compile \
  "$ROOT_DIR/tools/check_upba_grid_policy.py" \
  "$ROOT_DIR/tests/tools/test_check_upba_grid_policy.py"
"$PY" "$ROOT_DIR/tools/check_upba_grid_policy.py"
"$PY" -m pytest -q "$ROOT_DIR/tests/tools/test_check_upba_grid_policy.py"

echo "== release: acceptance mutation gate =="
bash "$ROOT_DIR/tools/run_acceptance_tcb_mutation_gate.sh"

echo "== release: acceptance fuzz gate =="
bash "$ROOT_DIR/tools/run_acceptance_tcb_fuzz_gate.sh"

echo "== release: snapshot recovery gate =="
bash "$ROOT_DIR/tools/run_snapshot_recovery_gate.sh"

echo "== release: tau syntax =="
bash "$ROOT_DIR/tests/tau/test_specs_syntax.sh"

echo "== release: tau traces =="
"$PY" -m pytest -q "$ROOT_DIR/tests/tau/test_spec_registry_traces.py"

echo "== release: tau spec assurance =="
"$PY" -m pytest -q "$ROOT_DIR/tests/tau/test_tau_spec_assurance.py"

echo "== release: tla/tlc shadow models =="
"$PY" "$ROOT_DIR/tools/run_tla_models.py"

echo "== release: tau shadow assurance =="
"$PY" "$ROOT_DIR/tools/check_tau_shadow_assurance.py"

run_if_present "tau provenance formal gate" "$ROOT_DIR/tools/run_tau_provenance_formal_gate.sh"
run_if_present "perps evidence" "$ROOT_DIR/tools/run_perps_evidence.sh"
run_if_present "spot proof assurance" "$ROOT_DIR/tools/run_spot_proof_assurance_gate.sh"
run_if_present "spot evidence" "$ROOT_DIR/tools/run_spot_evidence.sh"
run_if_present "derivatives evidence" "$ROOT_DIR/tools/run_derivatives_evidence.sh"

echo "== release: coverage map refresh =="
"$PY" "$ROOT_DIR/tools/zenodex_core_coverage_map.py"

echo "== release: production traceability matrix =="
"$PY" "$ROOT_DIR/tools/check_production_traceability_matrix.py"

echo "== release: DEX value-moving entrypoints =="
"$PY" "$ROOT_DIR/tools/check_dex_value_moving_entrypoints.py"

echo "== release: dependency pinning status =="
"$PY" "$ROOT_DIR/tools/check_dependency_pinning_status.py"

echo "== release: proof toolchain lock =="
"$PY" "$ROOT_DIR/tools/check_proof_toolchain_lock.py"
"$PY" -m pytest -q "$ROOT_DIR/tests/test_check_proof_toolchain_lock.py"

echo "== release: API surface profiles =="
"$PY" "$ROOT_DIR/tools/check_api_surface_profiles.py"

echo "== release: ZenoLedger anti-equivocation =="
"$PY" "$ROOT_DIR/tools/check_zeno_ledger_anti_equivocation.py"

require_file "system-spec lint" "$ROOT_DIR/tools/system_spec_lint.py"
require_file "system-spec compose" "$ROOT_DIR/src/kernels/dex/zenodex_system_compose_v2.yaml"
echo "== release: system-spec lint =="
"$PY" "$ROOT_DIR/tools/system_spec_lint.py" "$ROOT_DIR/src/kernels/dex/zenodex_system_compose_v2.yaml"

echo "== release: dependency audit =="
"$PY" -m pip_audit -r "$ROOT_DIR/requirements.txt"

echo "ok"

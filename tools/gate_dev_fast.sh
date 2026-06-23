#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
PY="${PYTHON:-python3}"

echo "[dev-fast] py_compile operational hardening tools"
"$PY" -m py_compile \
  tools/zenoctl.py \
  tools/check_deployment_profiles.py \
  tools/check_zeno_ledger_proof_profiles.py \
  tools/check_upba_policy_profiles.py \
  tools/zeno_ledger_network_scenario.py \
  tools/zeno_ledger_chaos_harness.py \
  tools/zeno_ops_status.py \
  tools/zeno_key_manager.py \
  src/integration/zeno_key_manager_v0.py \
  src/integration/zeno_key_import_v0.py \
  src/integration/zeno_key_recovery_v0.py \
  src/integration/metrics_v0.py

echo "[dev-fast] focused operational tests"
"$PY" -m pytest -q \
  tests/integration/test_zenoctl_operator.py \
  tests/integration/test_zeno_key_manager_v0.py \
  tests/integration/test_operational_hardening_properties.py \
  tests/integration/test_zeno_ledger_chaos_harness.py \
  tests/integration/test_zeno_ops_observability.py \
  tests/integration/test_proof_and_upba_profiles.py

echo "[dev-fast] focused typecheck"
bash tools/gate_typecheck.sh

echo "[dev-fast] PASS"

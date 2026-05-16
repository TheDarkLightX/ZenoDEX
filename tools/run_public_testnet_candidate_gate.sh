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

if [[ -d "$ROOT_DIR/external/ESSO" ]]; then
  export PYTHONPATH="$ROOT_DIR/external/ESSO${PYTHONPATH:+:$PYTHONPATH}"
fi

OUT_DIR="${ZENO_PUBLIC_TESTNET_GATE_OUT:-/tmp/zenodex_public_testnet_candidate_gate}"
rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR"

echo "== public-testnet: zeno ledger tests =="
"$PY" -m pytest -q \
  tests/integration/test_zeno_ledger_v0.py \
  tests/integration/test_zeno_ledger_verify_cli.py \
  tests/integration/test_zeno_ledger_profile.py \
  tests/integration/test_zeno_ledger_tau_export.py \
  tests/integration/test_zeno_ledger_machine_a_host.py \
  tests/integration/test_zeno_ledger_node.py \
  tests/integration/test_zeno_ledger_scaling_v0.py \
  tests/integration/test_zeno_ledger_conflict_graph_v0.py \
  tests/integration/test_zeno_ledger_risc0_proof_metadata.py \
  tests/integration/test_zeno_ledger_tee_proof_metadata.py

echo "== public-testnet: proof-mining tests =="
"$PY" -m pytest -q \
  tests/core/test_proof_mining_claimability_gate.py \
  tests/core/test_proof_mining_manager.py \
  tests/kernels/test_proof_mining_manager_v1_adapter.py \
  tests/integration/test_api_server_proof_mining_status.py \
  tests/integration/test_proof_mining_claimability.py \
  tests/integration/test_proof_mining_context_edges.py \
  tests/integration/test_proof_mining_runtime.py \
  tests/tau/test_proof_mining_reward_gate.py

echo "== public-testnet: UPBA tests =="
"$PY" -m pytest -q \
  tests/core/test_uniform_batch_clearing.py \
  tests/core/test_uniform_batch_optimality.py \
  tests/core/test_uniform_batch_price_grid_table.py \
  tests/integration/test_dex_engine_uniform_batch_certificate.py

echo "== public-testnet: deployment profile check =="
"$PY" tools/check_dex_deployment_profiles.py \
  > "$OUT_DIR/deployment_profiles.json"

echo "== public-testnet: public bundle =="
"$PY" tools/zeno_ledger_make_public_testnet_bundle.py \
  --out-dir "$OUT_DIR/public_bundle"

echo "== public-testnet: dual-operator rehearsal =="
"$PY" tools/zeno_ledger_dual_operator_rehearsal.py \
  --out-dir "$OUT_DIR/dual_operator_rehearsal"

echo "== public-testnet: local public-network smoke =="
"$PY" tools/zeno_ledger_public_network_smoke.py \
  --out-dir "$OUT_DIR/public_network_smoke"

echo "ok"

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

GATE_OUT_DIR="${GATE_OUT_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/zenodex-public-testnet-gate.XXXXXX")}"
mkdir -p "$GATE_OUT_DIR"
SMOKE_OUT_DIR="$(mktemp -d "$GATE_OUT_DIR/public-network-smoke.XXXXXX")"

echo "== public-testnet: syntax =="
"$PY" -m py_compile \
  "$ROOT_DIR/tools/zeno_ledger_node.py" \
  "$ROOT_DIR/tools/zeno_ledger_make_public_testnet_bundle.py" \
  "$ROOT_DIR/tools/zeno_ledger_public_network_smoke.py" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py" \
  "$ROOT_DIR/tests/integration/test_zenoctl_operator.py"

if [[ -f "$ROOT_DIR/tools/check_tau_experiment_promotion_candidates.py" ]]; then
  echo "== public-testnet: Tau experiment promotion metadata =="
  "$PY" "$ROOT_DIR/tools/check_tau_experiment_promotion_candidates.py"

  if [[ -f "$ROOT_DIR/generated/tau_lang_optimization_traces/report.json" ]]; then
    echo "== public-testnet: Tau experiment generated trace report =="
    "$PY" "$ROOT_DIR/tools/check_tau_experiment_promotion_candidates.py" --require-trace-report
  else
    echo "== public-testnet: Tau experiment generated trace report skipped =="
    echo "missing generated/tau_lang_optimization_traces/report.json"
  fi
else
  echo "== public-testnet: Tau experiment promotion metadata skipped =="
  echo "missing tools/check_tau_experiment_promotion_candidates.py"
fi

echo "== public-testnet: local two-node smoke =="
"$PY" "$ROOT_DIR/tools/zeno_ledger_public_network_smoke.py" \
  --out-dir "$SMOKE_OUT_DIR" \
  --network-id zeno-ledger-public-testnet-gate \
  --chain-id zeno-ledger-public-testnet-gate \
  --report-out "$GATE_OUT_DIR/public-network-smoke-report.json"

echo "== public-testnet: node and promotion regression tests =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_node_syncs_replays_bundle_and_serves_status" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_node_syncs_pinned_bundle_archive" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py::test_public_network_config_carries_live_follow_policy" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_pull_rejects_peer_before_live_fetch_on_admission_mismatch" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_node_strict_exposure_rejects_public_testnet_endpoints" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_node_public_operator_rejects_inline_auth_tokens" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_node_public_operator_rejects_public_fixture_endpoints" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_node_public_operator_accepts_local_env_auth_forwarding" \
  "$ROOT_DIR/tests/integration/test_zenoctl_operator.py::test_zenoctl_testnet_up_local_dry_run" \
  "$ROOT_DIR/tests/integration/test_zenoctl_operator.py::test_zenoctl_testnet_publish_config_dry_run"

echo "ok: public testnet candidate gate passed"
echo "artifacts: $GATE_OUT_DIR"

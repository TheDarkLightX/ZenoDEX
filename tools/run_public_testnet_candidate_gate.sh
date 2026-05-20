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

echo "== public-testnet: syntax =="
"$PY" -m py_compile \
  "$ROOT_DIR/tools/zeno_ledger_node.py" \
  "$ROOT_DIR/tools/zeno_ledger_public_network_smoke.py" \
  "$ROOT_DIR/tools/check_tau_experiment_promotion_candidates.py" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_public_network_smoke.py" \
  "$ROOT_DIR/tests/tau/test_tau_experiment_promotion_candidates.py"

echo "== public-testnet: Tau experiment promotion metadata =="
"$PY" "$ROOT_DIR/tools/check_tau_experiment_promotion_candidates.py"

if [[ -f "$ROOT_DIR/generated/tau_lang_optimization_traces/report.json" ]]; then
  echo "== public-testnet: Tau experiment generated trace report =="
  "$PY" "$ROOT_DIR/tools/check_tau_experiment_promotion_candidates.py" --require-trace-report
else
  echo "== public-testnet: Tau experiment generated trace report skipped =="
  echo "missing generated/tau_lang_optimization_traces/report.json"
fi

echo "== public-testnet: local two-node smoke =="
"$PY" "$ROOT_DIR/tools/zeno_ledger_public_network_smoke.py" \
  --out-dir "$GATE_OUT_DIR/public-network-smoke" \
  --network-id zeno-ledger-public-testnet-gate \
  --chain-id zeno-ledger-public-testnet-gate \
  --report-out "$GATE_OUT_DIR/public-network-smoke-report.json"

echo "== public-testnet: node and promotion regression tests =="
"$PY" -m pytest -q \
  -p no:cacheprovider \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_public_network_smoke.py" \
  "$ROOT_DIR/tests/tau/test_tau_experiment_promotion_candidates.py"

echo "ok: public testnet candidate gate passed"
echo "artifacts: $GATE_OUT_DIR"

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
  "$ROOT_DIR/tools/zeno_ledger_machine_b_acceptance.py" \
  "$ROOT_DIR/tools/zeno_ledger_public_network_smoke.py" \
  "$ROOT_DIR/tools/check_public_testnet_v0_1_16_evidence.py" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_machine_b_acceptance.py" \
  "$ROOT_DIR/tests/tools/test_check_public_testnet_v0_1_16_evidence.py"

echo "== public-testnet: local two-node smoke =="
"$PY" "$ROOT_DIR/tools/zeno_ledger_public_network_smoke.py" \
  --out-dir "$GATE_OUT_DIR/public-network-smoke" \
  --network-id zeno-ledger-public-testnet-gate \
  --chain-id zeno-ledger-public-testnet-gate \
  --report-out "$GATE_OUT_DIR/public-network-smoke-report.json"

echo "== public-testnet: node and promotion regression tests =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_node.py" \
  "$ROOT_DIR/tests/integration/test_zeno_ledger_machine_b_acceptance.py" \
  "$ROOT_DIR/tests/tools/test_check_public_testnet_v0_1_16_evidence.py" \
  "$ROOT_DIR/tests/test_zeno_sdk_browser_bundle.py::test_browser_sdk_verifies_python_built_bundle_hashes"

echo "ok: public testnet candidate gate passed"
echo "artifacts: $GATE_OUT_DIR"

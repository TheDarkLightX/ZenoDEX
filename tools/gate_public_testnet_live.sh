#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
PY="${PYTHON:-python3}"

echo "[public-testnet-live] adversarial model harness"
"$PY" tools/zeno_ledger_chaos_harness.py --json >/tmp/zeno-ledger-chaos-harness.json

echo "[public-testnet-live] candidate gate"
bash tools/run_public_testnet_candidate_gate.sh

echo "[public-testnet-live] PASS"

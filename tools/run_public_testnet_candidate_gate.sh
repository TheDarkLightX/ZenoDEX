#!/usr/bin/env bash
set -euo pipefail
PYTHON_BIN="${PYTHON_BIN:-${PYTHON:-}}"
if [ -z "$PYTHON_BIN" ]; then
  if command -v python3.11 >/dev/null 2>&1; then
    PYTHON_BIN=python3.11
  else
    PYTHON_BIN=python3
  fi
fi
"$PYTHON_BIN" tools/zenoctl.py testnet up --profile local --out-dir "${GATE_OUT_DIR:-/tmp/zenoctl-public-testnet}"

#!/usr/bin/env bash
# Assurance gate for the funding-auto zero-sum bounded-sink ESSO model.
#
# Wires src/kernels/dex/perp_funding_auto_sink_v1.yaml into the perps evidence
# path: validates the model, multi-solver-verifies its conservation and
# sink-bounds invariants, and runs the Python funding-auto regression. This is
# the formal/regression evidence backing the bounded-sink funding settlement
# (no counterparty residual; no Σ position_base == 0 requirement).
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

require_py_module() {
  local module="$1"
  if ! "$PY" -c "import importlib.util as u; raise SystemExit(0 if u.find_spec('$module') else 1)"; then
    echo "error: missing python module '$module'" >&2
    exit 2
  fi
}

ensure_esso() {
  if [[ -d "$ROOT_DIR/external/ESSO" ]]; then
    export PYTHONPATH="$ROOT_DIR/external/ESSO${PYTHONPATH:+:$PYTHONPATH}"
    return
  fi
  if ! "$PY" -c "import importlib.util as u; raise SystemExit(0 if u.find_spec('ESSO') else 1)"; then
    echo "error: missing ESSO toolchain (expected $ROOT_DIR/external/ESSO or an importable ESSO module)" >&2
    exit 2
  fi
}

ensure_esso
require_py_module "pytest"

MODEL_PATH="$ROOT_DIR/src/kernels/dex/perp_funding_auto_sink_v1.yaml"
VERIFY_ROOT="$ROOT_DIR/internal/esso_verify/perp_funding_auto_sink_v1"
mkdir -p "$VERIFY_ROOT"

echo "== perp-funding-auto-sink: validate =="
"$PY" -m ESSO validate "$MODEL_PATH" >"$VERIFY_ROOT/validate.json"

echo "== perp-funding-auto-sink: verify-multi (conservation + sink bounds) =="
"$PY" -m ESSO verify-multi \
  "$MODEL_PATH" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT" \
  --write-report \
  >/dev/null

echo "== perp-funding-auto-sink: regression =="
"$PY" -m pytest -q \
  tests/core/test_perp_apply_funding_auto_gate.py \
  tests/integration/test_perp_engine.py \
  -k 'funding'

echo "ok"

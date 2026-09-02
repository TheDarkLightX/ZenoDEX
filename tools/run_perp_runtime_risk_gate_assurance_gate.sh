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

require_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "error: missing required command '$cmd'" >&2
    exit 2
  fi
}

require_py_module() {
  local module="$1"
  local package_hint="$2"
  if ! "$PY" -c "import importlib.util as u; raise SystemExit(0 if u.find_spec('$module') else 1)"; then
    echo "error: missing python module '$module'" >&2
    echo "hint: install dev tooling with '$PY -m pip install -r requirements-dev.txt'" >&2
    echo "hint: expected package: $package_hint" >&2
    exit 2
  fi
}

ensure_esso() {
  if [[ -d "$ROOT_DIR/external/ESSO" ]]; then
    export PYTHONPATH="$ROOT_DIR/external/ESSO${PYTHONPATH:+:$PYTHONPATH}"
    return
  fi
  if ! "$PY" -c "import importlib.util as u; raise SystemExit(0 if u.find_spec('ESSO') else 1)"; then
    echo "error: missing ESSO toolchain (expected either $ROOT_DIR/external/ESSO or an importable ESSO module)" >&2
    exit 2
  fi
}

require_cmd "git"
ensure_esso
require_py_module "pytest" "pytest"

MODEL_PATH="$ROOT_DIR/src/kernels/dex/perp_runtime_risk_gate_v1.yaml"
ADAPTER_SPEC="src.kernels.python.perp_runtime_risk_gate_v1_native_adapter:make_adapter"
VERIFY_ROOT="$ROOT_DIR/internal/esso_verify/perp_runtime_risk_gate_v1"
mkdir -p "$VERIFY_ROOT"

echo "== perp-runtime-risk-gate: validate =="
"$PY" -m ESSO validate "$MODEL_PATH" >"$VERIFY_ROOT/validate.json"

echo "== perp-runtime-risk-gate: shell-lint =="
"$PY" -m ESSO shell-lint \
  "$MODEL_PATH" \
  --adapter "$ADAPTER_SPEC" \
  --output "$VERIFY_ROOT/shell_lint.json"

echo "== perp-runtime-risk-gate: verify-shell =="
"$PY" -m ESSO verify-shell \
  "$MODEL_PATH" \
  --adapter "$ADAPTER_SPEC" \
  --traces 16 \
  --max-steps 8 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/verify_shell.json" \
  >/dev/null

echo "== perp-runtime-risk-gate: verify-multi =="
"$PY" -m ESSO verify-multi \
  "$MODEL_PATH" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT" \
  --write-report \
  >/dev/null

echo "== perp-runtime-risk-gate: regression net =="
"$PY" -m pytest -q \
  tests/core/test_perp_runtime_risk_gate.py \
  tests/integration/test_perp_engine_runtime_gate.py \
  tests/integration/test_perp_engine.py \
  tests/kernels/test_perp_runtime_risk_gate_v1_native_adapter.py \
  -k 'runtime_risk_gate or runtime_gate or clear_breaker or operator_cannot_skip_settlement or publish_clearing_price_rejects_zero_price or apply_funding_auto or set_market_params_mid_epoch_guard_and_margin_safety or set_position_rejects_malformed_oracle_snapshot_zero_index'

echo "== perp-runtime-risk-gate: manifest check =="
"$PY" "$ROOT_DIR/tools/check_perp_runtime_risk_gate_assurance_manifest.py"

echo "ok"

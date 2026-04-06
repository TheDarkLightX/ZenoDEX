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

MODEL_PATH="$ROOT_DIR/src/kernels/dex/zusd_repay_single_vault_v1.yaml"
ADAPTER_SPEC="src.kernels.python.zusd_repay_single_vault_v1_native_adapter:make_adapter"
VERIFY_ROOT="$ROOT_DIR/internal/esso_verify/zusd_repay_single_vault_v1"
mkdir -p "$VERIFY_ROOT"

echo "== zusd-repay: validate =="
"$PY" -m ESSO validate "$MODEL_PATH" >"$VERIFY_ROOT/validate.json"

echo "== zusd-repay: shell-lint =="
"$PY" -m ESSO shell-lint \
  "$MODEL_PATH" \
  --adapter "$ADAPTER_SPEC" \
  --output "$VERIFY_ROOT/shell_lint.json"

echo "== zusd-repay: verify-shell =="
"$PY" -m ESSO verify-shell \
  "$MODEL_PATH" \
  --adapter "$ADAPTER_SPEC" \
  --traces 16 \
  --max-steps 8 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/verify_shell.json" \
  >/dev/null

echo "== zusd-repay: verify-multi =="
"$PY" -m ESSO verify-multi \
  "$MODEL_PATH" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT" \
  --write-report \
  >/dev/null

echo "== zusd-repay: adapter regression net =="
"$PY" -m pytest -q tests/kernels/test_zusd_repay_single_vault_v1_native_adapter.py

echo "== zusd-repay: manifest check =="
"$PY" "$ROOT_DIR/tools/check_zusd_repay_assurance_manifest.py"

echo "ok"

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
    echo "hint: install dev tooling with '$PY -m pip install --require-hashes -r requirements-dev.lock.txt'" >&2
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

MODEL_PATH="$ROOT_DIR/src/kernels/dex/perp_funding_apply_v1.yaml"
ADAPTER_SPEC="src.kernels.python.perp_funding_apply_v1_native_adapter:make_adapter"
VERIFY_ROOT="$ROOT_DIR/internal/esso_verify/perp_funding_apply_v1"
mkdir -p "$VERIFY_ROOT"

echo "== perp-funding-apply: validate =="
"$PY" -m ESSO validate "$MODEL_PATH" >"$VERIFY_ROOT/validate.json"

echo "== perp-funding-apply: shell-lint =="
"$PY" -m ESSO shell-lint \
  "$MODEL_PATH" \
  --adapter "$ADAPTER_SPEC" \
  --output "$VERIFY_ROOT/shell_lint.json"

echo "== perp-funding-apply: verify-shell =="
"$PY" -m ESSO verify-shell \
  "$MODEL_PATH" \
  --adapter "$ADAPTER_SPEC" \
  --traces 16 \
  --max-steps 8 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/verify_shell.json" \
  >/dev/null

echo "== perp-funding-apply: verify-multi =="
"$PY" -m ESSO verify-multi \
  "$MODEL_PATH" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT" \
  --write-report \
  >/dev/null

echo "== perp-funding-apply: regression net =="
"$PY" -m pytest -q \
  tests/core/test_perp_funding_apply_gate.py \
  tests/core/test_perp_v2/test_submodules.py \
  tests/core/test_perp_v2/test_engine.py \
  tests/core/test_perp_v2/test_engine_boundary_bva.py \
  tests/kernels/test_perp_funding_apply_v1_native_adapter.py \
  -k 'funding_apply_gate or apply_funding'

MANIFEST_PATH="$ROOT_DIR/tools/perp_funding_apply_assurance_manifest.json"
if [[ -f "$MANIFEST_PATH" ]]; then
  echo "== perp-funding-apply: manifest check =="
  "$PY" "$ROOT_DIR/tools/check_perp_funding_apply_assurance_manifest.py"
else
  echo "== perp-funding-apply: manifest check skipped (no pinned manifest in this tree) =="
fi

echo "ok"

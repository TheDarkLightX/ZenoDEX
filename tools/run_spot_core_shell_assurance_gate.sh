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

VERIFY_ROOT="$ROOT_DIR/internal/esso_verify/spot_core_shell_assurance"
mkdir -p "$VERIFY_ROOT"

run_shell_assurance() {
  local model_id="$1"
  local kernel_path="$2"
  local adapter_spec="$3"
  local out_dir="$VERIFY_ROOT/$model_id"

  mkdir -p "$out_dir"

  echo "== spot-core-shell: shell-lint $model_id =="
  "$PY" -m ESSO shell-lint \
    "$ROOT_DIR/$kernel_path" \
    --adapter "$adapter_spec" \
    --output "$out_dir/shell_lint.json"

  echo "== spot-core-shell: verify-shell $model_id =="
  "$PY" -m ESSO verify-shell \
    "$ROOT_DIR/$kernel_path" \
    --adapter "$adapter_spec" \
    --traces 16 \
    --max-steps 8 \
    --determinism-trials 2 \
    --output "$out_dir/verify_shell.json" \
    >/dev/null
}

run_shell_assurance \
  "cpmm_swap_v8" \
  "src/kernels/dex/cpmm_swap_v8.yaml" \
  "src.kernels.python.cpmm_swap_v8_adapter:make_adapter"

run_shell_assurance \
  "lp_mint_v8" \
  "src/kernels/dex/lp_mint_v8.yaml" \
  "src.kernels.python.lp_mint_v8_adapter:make_adapter"

run_shell_assurance \
  "vault_manager" \
  "src/kernels/dex/vault_manager.yaml" \
  "src.kernels.python.vault_manager_adapter:make_adapter"

run_shell_assurance \
  "dex_step_core_v2" \
  "src/kernels/dex/dex_step_core_v2.yaml" \
  "src.kernels.python.dex_step_core_v2_adapter:make_adapter"

echo "== spot-core-shell: regression net =="
"$PY" -m pytest -q \
  tests/core/test_dex_v8_ref_parity.py \
  tests/core/test_vault_ref_parity.py \
  tests/core/test_dex_step_core_v2_ref_parity.py \
  tests/core/test_dex_step_core_v2_ml_bva_parity.py \
  tests/kernels/test_cpmm_swap_v8_ml_bva_cases.py \
  tests/kernels/test_lp_mint_v8_ml_bva_cases.py \
  tests/kernels/test_python_adapter_wrappers.py \
  tests/kernels/test_spot_core_shell_adapters.py

echo "== spot-core-shell: manifest check =="
"$PY" "$ROOT_DIR/tools/check_spot_core_shell_assurance_manifest.py"

echo "ok"

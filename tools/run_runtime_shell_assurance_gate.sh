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

VERIFY_ROOT="$ROOT_DIR/internal/esso_verify/runtime_shell_assurance"
mkdir -p "$VERIFY_ROOT"

run_shell_assurance() {
  local model_id="$1"
  local kernel_path="$2"
  local adapter_spec="$3"
  local out_dir="$VERIFY_ROOT/$model_id"

  mkdir -p "$out_dir"

  echo "== runtime-shell: shell-lint $model_id =="
  "$PY" -m ESSO shell-lint \
    "$ROOT_DIR/$kernel_path" \
    --adapter "$adapter_spec" \
    --output "$out_dir/shell_lint.json"

  echo "== runtime-shell: verify-shell $model_id =="
  "$PY" -m ESSO verify-shell \
    "$ROOT_DIR/$kernel_path" \
    --adapter "$adapter_spec" \
    --traces 32 \
    --max-steps 16 \
    --determinism-trials 2 \
    --output "$out_dir/verify_shell.json" \
    >/dev/null
}

run_shell_assurance \
  "perp_epoch_isolated_v3" \
  "src/kernels/dex/perp_epoch_isolated_v3.yaml" \
  "src.kernels.python.perp_epoch_isolated_v3_adapter:make_adapter"

run_shell_assurance \
  "perp_epoch_clearinghouse_2p_v0_1" \
  "src/kernels/dex/perp_epoch_clearinghouse_2p_v0_1.yaml" \
  "src.kernels.python.perp_epoch_clearinghouse_2p_v0_1_adapter:make_adapter"

run_shell_assurance \
  "perp_epoch_clearinghouse_3p_transfer_v0_1" \
  "src/kernels/dex/perp_epoch_clearinghouse_3p_transfer_v0_1.yaml" \
  "src.kernels.python.perp_epoch_clearinghouse_3p_transfer_v0_1_adapter:make_adapter"

run_shell_assurance \
  "proof_mining_manager_v1" \
  "src/kernels/dex/proof_mining_manager_v1.yaml" \
  "src.kernels.python.proof_mining_manager_v1_adapter:make_adapter"

run_shell_assurance \
  "dex_global_conservation_v1" \
  "src/kernels/dex/dex_global_conservation_v1.yaml" \
  "src.kernels.python.dex_global_conservation_v1_adapter:make_adapter"

echo "== runtime-shell: adapter regression net =="
"$PY" -m pytest -q \
  tests/core/test_perp_v2/test_oracle_equiv.py \
  tests/core/test_perp_v2/test_parity_with_generated_ref.py \
  tests/kernels/test_perp_epoch_isolated_v3_generated_ref_sync.py \
  tests/kernels/test_python_adapter_wrappers.py \
  tests/kernels/test_proof_mining_manager_v1_adapter.py \
  tests/kernels/test_runtime_shell_adapters.py

echo "== runtime-shell: manifest check =="
"$PY" "$ROOT_DIR/tools/check_runtime_shell_assurance_manifest.py"

echo "ok"

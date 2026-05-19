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

require_module() {
  local module="$1"
  local package_hint="$2"
  if ! "$PY" -c "import importlib.util as u, sys; sys.exit(0 if u.find_spec('$module') else 1)"; then
    echo "error: missing python module '$module'" >&2
    echo "hint: expected package: $package_hint" >&2
    exit 2
  fi
}

require_path() {
  local label="$1"
  local path="$2"
  if [[ ! -e "$path" ]]; then
    echo "error: missing required path for $label: $path" >&2
    exit 2
  fi
}

require_cmd "lake"
require_cmd "java"
require_module "pytest" "pytest"
require_module "py_ecc.bls" "py-ecc"

if [[ -d "$ROOT_DIR/external/ESSO" ]]; then
  export PYTHONPATH="$ROOT_DIR/external/ESSO${PYTHONPATH:+:$PYTHONPATH}"
fi
require_module "ESSO" "ESSO"

TLA_TOOLS_JAR="${TLA_JAR:-$ROOT_DIR/external/tla-tools/tla2tools.jar}"
require_path "TLA tools" "$TLA_TOOLS_JAR"
export TLA_JAR="$TLA_TOOLS_JAR"
require_path "mathlib4 checkout" "$ROOT_DIR/external/mathlib4"
require_path "Lean proof root" "$ROOT_DIR/lean-mathlib"
require_path "Tau provenance ESSO kernel" "$ROOT_DIR/src/kernels/dex/tau_state_app_hash_provenance_guard_v1.yaml"

echo "== tau provenance formal gate =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/formal/test_esso_tau_state_app_hash_provenance_guard.py" \
  "$ROOT_DIR/tests/formal/test_tla_tau_state_app_hash_provenance_bridge.py" \
  "$ROOT_DIR/tests/formal/test_tla_tau_state_app_hash_stable_window.py" \
  "$ROOT_DIR/tests/formal/test_lean_tau_state_app_hash_provenance.py" \
  "$ROOT_DIR/tests/formal/test_lean_tau_state_app_hash_stable_window.py" \
  "$ROOT_DIR/tests/formal/test_lean_tau_tcp_view_contracts.py" \
  "$ROOT_DIR/tests/formal/test_lean_tau_state_app_hash_composition.py" \
  "$ROOT_DIR/tests/integration/test_tau_net_client.py" \
  "$ROOT_DIR/tests/integration/test_tau_tcp_view_contract_parity.py" \
  "$ROOT_DIR/tests/integration/test_settlement_signer_registry.py"

echo "ok"

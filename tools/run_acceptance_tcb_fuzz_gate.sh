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

require_module() {
  local module="$1"
  local package_hint="$2"
  if ! "$PY" -c "import importlib.util as u, sys; sys.exit(0 if u.find_spec('$module') else 1)"; then
    echo "error: missing python module '$module'" >&2
    echo "hint: install dev tooling with '$PY -m pip install --require-hashes -r requirements-dev.lock.txt'" >&2
    echo "hint: expected package: $package_hint" >&2
    exit 2
  fi
}

require_module "pytest" "pytest"
require_module "hypothesis" "hypothesis"

echo "== acceptance-tcb: structure-aware fuzz (fast) =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/integration/test_operations_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_operations_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_api_server_request_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_quote_receipt_transport_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_nonce_replay_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_dex_engine_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_boundary_concolic_determinism.py" \
  "$ROOT_DIR/tests/integration/test_api_server_boundary_concolic.py" \
  "$ROOT_DIR/tests/integration/test_receipt_boundary_concolic.py" \
  "$ROOT_DIR/tests/integration/test_state_boundary_concolic.py" \
  "$ROOT_DIR/tests/core/test_quote_receipts_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_proof_verifier_fuzz.py"

echo "ok"

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
require_module "pytest_cov" "pytest-cov"

REPORT_DIR="$ROOT_DIR/internal/coverage_gates"
REPORT_PATH="$REPORT_DIR/acceptance_tcb_coverage.json"
mkdir -p "$REPORT_DIR"

ACCEPTANCE_TESTS=(
  tests/integration/test_dex_engine.py
  tests/integration/test_dex_engine_anomaly.py
  tests/integration/test_dex_engine_helpers.py
  tests/integration/test_operations_parsing.py
  tests/integration/test_validation_uses_strong_settlement_gate.py
  tests/integration/test_proof_verifier.py
  tests/integration/test_proof_verifier_unit.py
  tests/integration/test_recompute_batch_proof_verifier.py
  tests/integration/test_replay_protection.py
  tests/integration/test_quote_receipt_intents.py
  tests/core/test_settlement_strong_validator.py
  tests/core/test_quote_receipts.py
  tests/core/test_intent_normal_form.py
  tests/core/test_support_root.py
  tests/state/test_nonces.py
  tests/state/test_canonical_size_bounds.py
  tests/state/test_state_root_determinism.py
)

COVERAGE_TARGETS=(
  --cov=src.integration.dex_engine
  --cov=src.core.settlement_strong_validator
  --cov=src.integration.operations
  --cov=src.integration.validation
  --cov=src.integration.proof_verifier
  --cov=src.core.intent_normal_form
  --cov=src.core.quote_receipts
  --cov=src.state.canonical
  --cov=src.state.state_root
  --cov=src.state.support_root
  --cov=src.state.nonces
)

echo "== acceptance-tcb: pytest + branch coverage =="
"$PY" -m pytest -q \
  "${ACCEPTANCE_TESTS[@]}" \
  "${COVERAGE_TARGETS[@]}" \
  --cov-branch \
  --cov-report=term-missing:skip-covered \
  --cov-report="json:$REPORT_PATH"

echo "== acceptance-tcb: floor check =="
"$PY" "$ROOT_DIR/tools/check_acceptance_tcb_coverage.py" "$REPORT_PATH"

echo "ok"

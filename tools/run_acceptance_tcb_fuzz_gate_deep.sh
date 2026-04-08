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
    echo "hint: install dev tooling with '$PY -m pip install -r requirements-dev.txt'" >&2
    echo "hint: expected package: $package_hint" >&2
    exit 2
  fi
}

require_module "pytest" "pytest"
require_module "hypothesis" "hypothesis"
require_module "mypy" "mypy"

MYPY_TARGETS=(
  "$ROOT_DIR/tools/api_server_boundary_concolic_stateful.py"
  "$ROOT_DIR/tools/receipt_boundary_concolic_stateful.py"
  "$ROOT_DIR/tools/state_boundary_concolic_stateful.py"
  "$ROOT_DIR/tools/acceptance_tcb_fuzz_campaign.py"
  "$ROOT_DIR/tools/stateful_feedback.py"
  "$ROOT_DIR/tools/stateful_semantics.py"
  "$ROOT_DIR/tools/route_certificate_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tools/settlement_attestation_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tools/operations_signature_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tools/quote_receipt_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tools/quote_receipt_cross_surface_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tools/quote_receipt_route_canonicalization_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tools/stale_settlement_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tests/integration/test_stateful_feedback.py"
  "$ROOT_DIR/tests/integration/test_api_server_boundary_concolic_stateful.py"
  "$ROOT_DIR/tests/integration/test_receipt_boundary_concolic_stateful.py"
  "$ROOT_DIR/tests/integration/test_state_boundary_concolic_stateful.py"
  "$ROOT_DIR/tests/integration/test_route_certificate_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tests/integration/test_settlement_attestation_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tests/integration/test_operations_signature_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tests/integration/test_quote_receipt_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tests/integration/test_quote_receipt_route_canonicalization_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tests/integration/test_stale_settlement_sequence_grammar_fuzz.py"
  "$ROOT_DIR/tests/integration/test_acceptance_tcb_fuzz_campaign.py"
)

echo "== acceptance-tcb: stateful tooling mypy =="
"$PY" -m mypy "${MYPY_TARGETS[@]}"

echo "== acceptance-tcb: structure-aware fuzz (deep stateful) =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/integration/test_operations_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_operations_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_api_server_request_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_quote_receipt_transport_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_nonce_replay_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_dex_engine_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_dex_engine_quote_receipt_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_dex_engine_settlement_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_boundary_concolic_determinism.py" \
  "$ROOT_DIR/tests/integration/test_api_server_boundary_concolic.py" \
  "$ROOT_DIR/tests/integration/test_receipt_boundary_concolic.py" \
  "$ROOT_DIR/tests/integration/test_state_boundary_concolic.py" \
  "$ROOT_DIR/tests/integration/test_stateful_feedback.py" \
  "$ROOT_DIR/tests/integration/test_api_server_boundary_concolic_stateful.py" \
  "$ROOT_DIR/tests/integration/test_receipt_boundary_concolic_stateful.py" \
  "$ROOT_DIR/tests/integration/test_state_boundary_concolic_stateful.py" \
  "$ROOT_DIR/tests/integration/test_route_certificate_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_settlement_attestation_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_operations_signature_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_quote_receipt_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_quote_receipt_route_canonicalization_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_stale_settlement_sequence_grammar_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_acceptance_tcb_fuzz_campaign.py" \
  "$ROOT_DIR/tests/core/test_quote_receipts_fuzz.py" \
  "$ROOT_DIR/tests/integration/test_proof_verifier_fuzz.py"

echo "ok"

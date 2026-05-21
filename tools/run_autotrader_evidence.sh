#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

if [[ -n "${PYTHON:-}" ]]; then
  PY="$PYTHON"
elif [[ -x "$ROOT_DIR/.venv/bin/python" ]]; then
  PY="$ROOT_DIR/.venv/bin/python"
else
  PY="python3"
fi

if [[ -n "${ESSO_ROOT:-}" ]]; then
  if [[ ! -d "$ESSO_ROOT" ]]; then
    echo "error: ESSO_ROOT does not exist: $ESSO_ROOT" >&2
    exit 2
  fi
  export PYTHONPATH="$ESSO_ROOT${PYTHONPATH:+:$PYTHONPATH}"
elif [[ -d "$ROOT_DIR/external/ESSO" ]]; then
  export PYTHONPATH="$ROOT_DIR/external/ESSO${PYTHONPATH:+:$PYTHONPATH}"
else
  if ! "$PY" -c "import importlib.util as u; raise SystemExit(0 if u.find_spec('ESSO') else 1)"; then
    echo "error: missing ESSO toolchain (expected either external/ESSO, ESSO_ROOT, or an importable ESSO module)" >&2
    exit 2
  fi
fi

echo "== autotrader: pytest =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/agents/test_strategy_ir.py" \
  "$ROOT_DIR/tests/agents/test_local_policy.py" \
  "$ROOT_DIR/tests/agents/test_krr_policy_advisor.py" \
  "$ROOT_DIR/tests/agents/test_autotrader_chatbot_agent_advisor.py" \
  "$ROOT_DIR/tests/agents/test_krr_policy_history.py" \
  "$ROOT_DIR/tests/agents/test_krr_bundle_artifacts.py" \
  "$ROOT_DIR/tests/agents/test_policy_artifacts.py" \
  "$ROOT_DIR/tests/agents/test_policy_compiler.py" \
  "$ROOT_DIR/tests/agents/test_policy_text_compiler.py" \
  "$ROOT_DIR/tests/agents/test_tau_policy_adapter.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_signal_registry.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_signals.py" \
  "$ROOT_DIR/tests/core/test_strategy_compilation_witness_v1_adapter.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_decision.py" \
  "$ROOT_DIR/tests/core/test_strategy_compile_contract_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_budget_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_candidate_set_contract_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_policy_contracts_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_external_signal_contract_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_external_signal_source_registry_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_execution_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_emit_finalize_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_live_admission_bundle_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_session_state_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_session_capability_binding_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_submit_bundle_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_tx_envelope_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_nonce_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_observation_packet_contract_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_oracle_freshness_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_signer_binding_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_system_compose_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_signal_provenance_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_wallet_capability_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/core/test_strategy_wallet_outbound_guard_v1_adapter.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_controller.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_krr_bundle_build_cli.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_krr_history_cli.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_krr_import_source_cli.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_krr_import_wikidata_cli.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_live.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_live_api.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_live_cli.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_policy_compile_cli.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_policy_sign_verify_cli.py" \
  "$ROOT_DIR/tests/integration/test_autotrader_shadow_cli.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_compilation_witness.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_compile_contract.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_budget_guard.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_execution_guard.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_external_signal_source_registry_guard.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_live_admission_bundle.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_emit_finalize.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_session_state_guard.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_session_capability_binding_guard.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_submit_bundle_guard.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_tx_envelope_guard.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_nonce_guard.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_observation_packet_contract.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_oracle_freshness_guard.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_signal_provenance_guard.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_system_compose.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_wallet_capability_guard.py" \
  "$ROOT_DIR/tests/integration/test_tau_witness_autotrader_wallet_outbound_guard.py" \
  "$ROOT_DIR/tests/integration/test_tau_user_policy.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_budget_guard.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_compilation_witness.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_compile_contract.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_execution_guard.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_external_signal_source_registry_guard.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_live_admission_bundle.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_emit_finalize.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_session_state_guard.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_session_capability_binding_guard.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_submit_bundle_guard.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_tx_envelope_guard.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_nonce_guard.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_observation_packet_contract.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_oracle_freshness_guard.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_signal_provenance_guard.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_system_compose.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_wallet_capability_guard.py" \
  "$ROOT_DIR/tests/tau/test_autotrader_wallet_outbound_guard.py"

echo "== autotrader: chatbot advisor promotion check =="
"$PY" "$ROOT_DIR/tools/check_autotrader_chatbot_advisor.py" >/dev/null

echo "== autotrader: chatbot provider deterministic evaluation =="
"$PY" "$ROOT_DIR/tools/evaluate_autotrader_chatbot_providers.py" >/dev/null

echo "== autotrader: chatbot provider config validation =="
"$PY" "$ROOT_DIR/tools/check_autotrader_chatbot_provider_config.py" \
  --config "$ROOT_DIR/config/autotrader_llm_provider.local.example.json" >/dev/null

echo "== autotrader: chatbot production readiness =="
"$PY" "$ROOT_DIR/tools/check_autotrader_chatbot_production_readiness.py" \
  --provider-config "$ROOT_DIR/config/autotrader_llm_provider.local.example.json" >/dev/null

VERIFY_ROOT="$ROOT_DIR/internal/esso_verify"
mkdir -p "$VERIFY_ROOT"

echo "== autotrader: kernel inductiveness (verify-multi) =="
"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_budget_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_budget_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_candidate_set_contract_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_candidate_set_contract_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_compilation_witness_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_compilation_witness_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_compile_contract_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_compile_contract_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_decision_kernel_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_decision_kernel_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_external_signal_contract_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_external_signal_contract_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_external_signal_source_registry_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_external_signal_source_registry_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_execution_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_execution_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_kill_switch_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_kill_switch_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_live_admission_bundle_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_live_admission_bundle_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_emit_finalize_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_emit_finalize_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_session_state_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_session_state_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_session_capability_binding_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_session_capability_binding_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_tx_envelope_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_tx_envelope_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_oracle_freshness_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_oracle_freshness_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_policy_artifact_contract_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_policy_artifact_contract_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_policy_bundle_contract_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_policy_bundle_contract_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_signer_binding_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_signer_binding_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_system_compose_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_system_compose_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_submit_bundle_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_submit_bundle_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_signal_provenance_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_signal_provenance_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_wallet_capability_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_wallet_capability_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_wallet_outbound_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_wallet_outbound_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_nonce_guard_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_nonce_guard_v1" \
  --write-report

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/strategy_observation_packet_contract_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/strategy_observation_packet_contract_v1" \
  --write-report

echo "ok"

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

if [[ -d "$ROOT_DIR/external/ESSO" ]]; then
  export PYTHONPATH="$ROOT_DIR/external/ESSO${PYTHONPATH:+:$PYTHONPATH}"
fi

MODEL_PATH="$ROOT_DIR/src/kernels/dex/intent_nonce_batch_policy_gate_v1.yaml"
ADAPTER_SPEC="src.kernels.python.intent_nonce_batch_policy_gate_v1_native_adapter:make_adapter"
VERIFY_ROOT="$ROOT_DIR/internal/esso_verify/intent_nonce_batch_policy_gate_v1"
mkdir -p "$VERIFY_ROOT"

"$PY" -m ESSO validate "$MODEL_PATH" >"$VERIFY_ROOT/validate.json"
"$PY" -m ESSO shell-lint "$MODEL_PATH" --adapter "$ADAPTER_SPEC" --output "$VERIFY_ROOT/shell_lint.json"
"$PY" -m ESSO verify-shell "$MODEL_PATH" --adapter "$ADAPTER_SPEC" --traces 16 --max-steps 8 --determinism-trials 2 --output "$VERIFY_ROOT/verify_shell.json" >/dev/null
"$PY" -m ESSO verify-multi "$MODEL_PATH" --solvers z3,cvc5 --timeout-ms 60000 --determinism-trials 2 --output "$VERIFY_ROOT" --write-report >/dev/null
"$PY" -m pytest -q tests/state/test_intent_nonce_batch_policy_gate.py tests/state/test_nonces.py tests/tau/test_replay_semantic_lane.py tests/kernels/test_intent_nonce_batch_policy_gate_v1_native_adapter.py
"$PY" "$ROOT_DIR/tools/check_intent_nonce_batch_policy_gate_assurance_manifest.py"

echo "ok"

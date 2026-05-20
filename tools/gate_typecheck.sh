#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ -n "${PYTHON:-}" ]]; then
  PY="$PYTHON"
elif [[ -x "$ROOT/.venv/bin/python" ]]; then
  PY="$ROOT/.venv/bin/python"
else
  PY="python3"
fi

if ! "$PY" -c "import importlib.util as u, sys; sys.exit(0 if u.find_spec('mypy') else 1)"; then
  echo "error: mypy is not installed for $PY" >&2
  echo "hint: $PY -m pip install --require-hashes -r requirements-dev.lock.txt" >&2
  exit 2
fi

"$PY" -m mypy \
  src/integration/zeno_key_manager_v0.py \
  src/integration/zeno_key_import_v0.py \
  src/integration/zeno_key_recovery_v0.py \
  src/integration/metrics_v0.py \
  tools/zenoctl.py \
  tools/zeno_ledger_network_scenario.py \
  tools/zeno_ledger_chaos_harness.py \
  tools/zeno_ops_status.py \
  tools/zeno_key_manager.py \
  tools/check_deployment_profiles.py \
  tools/check_zeno_ledger_proof_profiles.py \
  tools/check_upba_policy_profiles.py

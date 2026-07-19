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

echo "== zusd: pytest =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/core/test_zusd.py" \
  "$ROOT_DIR/tests/core/test_zusd_coverage_edges.py" \
  "$ROOT_DIR/tests/integration/test_zusd_monetary_wallet_api.py" \
  "$ROOT_DIR/tests/integration/test_zusd_tau_wallet_api.py" \
  "$ROOT_DIR/tests/integration/test_zusd_tau_gate.py" \
  "$ROOT_DIR/tests/integration/test_zusd_tau_gate_edges.py" \
  "$ROOT_DIR/tests/integration/test_zusd_tau_token.py" \
  "$ROOT_DIR/tests/integration/test_zusd_tau_wallet_cli.py" \
  "$ROOT_DIR/tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_accepts_tau_raw_sender_native_balance" \
  "$ROOT_DIR/tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_mint_feeds_transferable_perps_collateral" \
  "$ROOT_DIR/tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_stability_pool_liquidation_and_claim" \
  "$ROOT_DIR/tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_liquidation_compensation_pays_keeper" \
  "$ROOT_DIR/tests/integration/test_tau_testnet_dex_plugin.py::test_zusd_monetary_liquidation_fee_comp_env_aliases_prefer_fee_names" \
  "$ROOT_DIR/tests/integration/test_tau_testnet_dex_plugin.py::test_zusd_monetary_liquidation_fee_comp_env_aliases_accept_legacy_gas_names" \
  "$ROOT_DIR/tests/tau/test_zusd_tau_specs.py"

VERIFY_ROOT="$ROOT_DIR/internal/esso_verify"
mkdir -p "$VERIFY_ROOT"

echo "== zusd: protocol token inductiveness (verify-multi) =="
"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/protocol_token_v1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2 \
  --output "$VERIFY_ROOT/protocol_token_v1" \
  --write-report

echo "== zusd: risky-ops gate assurance =="
bash "$ROOT_DIR/tools/run_zusd_risky_ops_assurance_gate.sh"

echo "== zusd: redeem fee/collateral assurance =="
bash "$ROOT_DIR/tools/run_zusd_redeem_assurance_gate.sh"

echo "== zusd: liquidation SP absorb assurance =="
bash "$ROOT_DIR/tools/run_zusd_liquidation_assurance_gate.sh"

echo "== zusd: repay assurance =="
bash "$ROOT_DIR/tools/run_zusd_repay_assurance_gate.sh"

echo "== zusd: mint/borrow-fee assurance =="
bash "$ROOT_DIR/tools/run_zusd_mint_assurance_gate.sh"

echo "== zusd: withdraw-collateral assurance =="
bash "$ROOT_DIR/tools/run_zusd_withdraw_collateral_assurance_gate.sh"

echo "== zusd: oracle-commit assurance =="
bash "$ROOT_DIR/tools/run_zusd_oracle_commit_assurance_gate.sh"

echo "ok"

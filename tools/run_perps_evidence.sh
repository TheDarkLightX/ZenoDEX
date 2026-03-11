#!/usr/bin/env bash
set -euo pipefail

# Evidence runner for perpetuals (perps).
#
# Goal: provide a single, deterministic entrypoint to run the *current* perps
# evidence gates in this repo:
# - pytest correctness/determinism checks
# - YAML kernel inductiveness checks (via the optional external toolchain)
# - Lean proofs for math claims
#
# Notes:
# - This script is fail-closed: missing toolchains are treated as errors.

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ -n "${PYTHON:-}" ]]; then
  PY="$PYTHON"
elif [[ -x "$ROOT_DIR/.venv/bin/python" ]]; then
  PY="$ROOT_DIR/.venv/bin/python"
else
  PY="python3"
fi

if [[ -d "$ROOT_DIR/external/ESSO" ]]; then
  export PYTHONPATH="$ROOT_DIR/external/ESSO${PYTHONPATH:+:$PYTHONPATH}"
else
  # Allow running against an installed ESSO module (e.g., in CI or a dev venv).
  if ! "$PY" -c "import importlib.util as u; raise SystemExit(0 if u.find_spec('ESSO') else 1)"; then
    echo "error: missing ESSO toolchain (expected either $ROOT_DIR/external/ESSO or an importable ESSO module)" >&2
    echo "hint: external/ is git-ignored by design; clone ESSO into external/ or install it into your python env" >&2
    exit 2
  fi
fi

echo "== perps: claims registry format check =="
"$PY" "$ROOT_DIR/tools/check_claims_registry.py"

echo "== perps: pytest =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/core/test_perp_v2" \
  "$ROOT_DIR/tests/core/test_perp_math_hazards.py" \
  "$ROOT_DIR/tests/core/test_perp_incentive_hazards.py" \
  "$ROOT_DIR/tests/core/test_perp_clearinghouse_2p" \
  "$ROOT_DIR/tests/core/test_perp_clearinghouse_3p_transfer" \
  "$ROOT_DIR/tests/formal/test_perp_epoch_scheduler_ltlf.py::test_ltlf_scheduler_can_reach_epoch_2_settled" \
  "$ROOT_DIR/tests/integration/test_perp_engine.py" \
  "$ROOT_DIR/tests/integration/test_perp_engine_market_params_clearinghouse.py" \
  "$ROOT_DIR/tests/integration/test_perp_engine_clearinghouse_2p.py" \
  "$ROOT_DIR/tests/integration/test_perp_engine_clearinghouse_3p_transfer.py"

echo "== perps: kernel inductiveness (verify-multi) =="
"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/perp_epoch_isolated_v3.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/perp_epoch_clearinghouse_2p_v0_1.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/perp_epoch_clearinghouse_3p_transfer_v0_1.yaml" \
  --solvers cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/perp_game_theory_v2.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2

if [[ ! -d "$ROOT_DIR/lean-mathlib" ]]; then
  echo "error: missing Lean workspace at $ROOT_DIR/lean-mathlib" >&2
  exit 2
fi

echo "== perps: Lean proofs =="
(cd "$ROOT_DIR/lean-mathlib" && lake build Proofs.PerpEpochSafety Proofs.PerpFundingRateSafety Proofs.PerpInsuranceSafety Proofs.PerpGameTheory)

echo "ok"

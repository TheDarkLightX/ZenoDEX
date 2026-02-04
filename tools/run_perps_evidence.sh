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

if [[ ! -d "$ROOT_DIR/external/ESSO" ]]; then
  echo "error: missing external toolchain at $ROOT_DIR/external/ESSO" >&2
  echo "hint: clone it into external/ (external/ is git-ignored by design)" >&2
  exit 2
fi

export PYTHONPATH="$ROOT_DIR/external/ESSO${PYTHONPATH:+:$PYTHONPATH}"

echo "== perps: claims registry format check =="
"$PY" "$ROOT_DIR/tools/check_claims_registry.py"

echo "== perps: pytest =="
"$PY" -m pytest -q \
  "$ROOT_DIR/tests/core/test_perp_v2" \
  "$ROOT_DIR/tests/core/test_perp_math_hazards.py" \
  "$ROOT_DIR/tests/core/test_perp_clearinghouse_2p" \
  "$ROOT_DIR/tests/formal/test_perp_epoch_scheduler_ltlf.py::test_ltlf_scheduler_can_reach_epoch_2_settled" \
  "$ROOT_DIR/tests/integration/test_perp_engine.py::test_settle_epoch_is_order_independent" \
  "$ROOT_DIR/tests/integration/test_perp_engine_clearinghouse_2p.py"

echo "== perps: kernel inductiveness (verify-multi) =="
"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/perp_epoch_isolated_v2.yaml" \
  --solvers z3,cvc5 \
  --timeout-ms 60000 \
  --determinism-trials 2

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/perp_epoch_clearinghouse_2p_v0_1.yaml" \
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

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

require_py_module() {
  local module="$1"
  local package_hint="$2"
  if ! "$PY" -c "import importlib.util as u; raise SystemExit(0 if u.find_spec('$module') else 1)"; then
    echo "error: missing python module '$module'" >&2
    echo "hint: install dev tooling with '$PY -m pip install --require-hashes -r requirements-dev.lock.txt'" >&2
    echo "hint: expected package: $package_hint" >&2
    exit 2
  fi
}

ensure_esso() {
  if [[ -d "$ROOT_DIR/external/ESSO" ]]; then
    export PYTHONPATH="$ROOT_DIR/external/ESSO${PYTHONPATH:+:$PYTHONPATH}"
    return
  fi
  if ! "$PY" -c "import importlib.util as u; raise SystemExit(0 if u.find_spec('ESSO') else 1)"; then
    echo "error: missing ESSO toolchain (expected either $ROOT_DIR/external/ESSO or an importable ESSO module)" >&2
    exit 2
  fi
}

require_cmd "lake"
ensure_esso
require_py_module "pytest" "pytest"

LEAN_DIR="$ROOT_DIR/lean-mathlib"
if [[ ! -d "$LEAN_DIR" ]]; then
  echo "error: missing lean project at $LEAN_DIR" >&2
  exit 2
fi
if [[ ! -e "$ROOT_DIR/external/mathlib4" ]]; then
  echo "error: missing mathlib dependency at $ROOT_DIR/external/mathlib4" >&2
  exit 2
fi

LEAN_FILES=(
  "lean-mathlib/Proofs/ZenoDEXNonces.lean"
  "lean-mathlib/Proofs/FeeCeilDecomposition.lean"
  "lean-mathlib/Proofs/CpmmSwapV8ExactOutMinimality.lean"
  "lean-mathlib/Proofs/CPMMSettlement.lean"
  "lean-mathlib/Proofs/BatchAuctionCanonical.lean"
  "lean-mathlib/Proofs/CPMMInvariants.lean"
  "lean-mathlib/Proofs/SettlementAlgebra.lean"
)

LEAN_MODULES=(
  "Proofs.ZenoDEXNonces"
  "Proofs.FeeCeilDecomposition"
  "Proofs.CpmmSwapV8ExactOutMinimality"
  "Proofs.CPMMSettlement"
  "Proofs.BatchAuctionCanonical"
)

echo "== spot-proof: lean no-sorry check =="
if command -v rg >/dev/null 2>&1; then
  if rg -n '\bsorry\b' "${LEAN_FILES[@]}"; then
    echo "error: selected Lean proof files contain 'sorry'" >&2
    exit 1
  fi
else
  if grep -nH -w "sorry" "${LEAN_FILES[@]}"; then
    echo "error: selected Lean proof files contain 'sorry'" >&2
    exit 1
  fi
fi

echo "== spot-proof: lean build =="
(
  cd "$LEAN_DIR"
  for module in "${LEAN_MODULES[@]}"; do
    echo "  lake build $module"
    lake build "$module"
  done
)

VERIFY_MULTI_COMMON=(
  --solvers z3,cvc5
  --timeout-ms 60000
  --determinism-trials 2
)

VERIFY_ROOT="$ROOT_DIR/internal/esso_verify"
mkdir -p "$VERIFY_ROOT"

check_verify_multi_report() {
  local report_json="$1"
  local expected_model_id="$2"
  "$PY" - "$report_json" "$expected_model_id" <<'PY'
import json
import sys

report_path, expected_model_id = sys.argv[1:]
with open(report_path, "r", encoding="utf-8") as fh:
    report = json.load(fh)

if report.get("model_id") != expected_model_id:
    raise SystemExit(
        f"error: verify-multi model_id mismatch in {report_path}: "
        f"{report.get('model_id')!r} != {expected_model_id!r}"
    )
if report.get("verdict") != "VERIFIED":
    raise SystemExit(f"error: verify-multi verdict was {report.get('verdict')!r} in {report_path}")
if not report.get("solvers_agreed", False):
    raise SystemExit(f"error: verify-multi solvers_agreed=false in {report_path}")
if int(report.get("failed_queries", 0)) != 0:
    raise SystemExit(f"error: verify-multi failed_queries != 0 in {report_path}")
if int(report.get("inconclusive_queries", 0)) != 0:
    raise SystemExit(f"error: verify-multi inconclusive_queries != 0 in {report_path}")

scope = report.get("scope") or {}
if scope.get("kind") != "inductive" or int(scope.get("k", -1)) != 1:
    raise SystemExit(f"error: verify-multi scope is not inductive(k=1) in {report_path}")
PY
}

check_verify_shell_report() {
  local report_json="$1"
  local expected_model="$2"
  local expected_adapter="$3"
  "$PY" - "$report_json" "$expected_model" "$expected_adapter" <<'PY'
import json
import sys

report_path, expected_model, expected_adapter = sys.argv[1:]
with open(report_path, "r", encoding="utf-8") as fh:
    data = json.load(fh)

if not data.get("ok", False):
    raise SystemExit(f"error: verify-shell did not report ok=true in {report_path}")
if data.get("model") != expected_model:
    raise SystemExit(
        f"error: verify-shell model mismatch in {report_path}: "
        f"{data.get('model')!r} != {expected_model!r}"
    )

adapter = data.get("adapter") or {}
if adapter.get("spec") != expected_adapter:
    raise SystemExit(
        f"error: verify-shell adapter mismatch in {report_path}: "
        f"{adapter.get('spec')!r} != {expected_adapter!r}"
    )

determinism = data.get("determinism") or {}
if not determinism.get("ok", False):
    raise SystemExit(f"error: verify-shell determinism.ok=false in {report_path}")

fingerprints = determinism.get("fingerprints") or []
if len(fingerprints) < 2:
    raise SystemExit(f"error: verify-shell recorded fewer than 2 fingerprints in {report_path}")
if len(set(fingerprints)) != 1:
    raise SystemExit(f"error: verify-shell fingerprints diverged in {report_path}")
if int(data.get("traces", 0)) <= 0:
    raise SystemExit(f"error: verify-shell traces <= 0 in {report_path}")
PY
}

echo "== spot-proof: settlement witness inductiveness =="
"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/settlement_create_pool_apply_witness_v1.yaml" \
  "${VERIFY_MULTI_COMMON[@]}" \
  --output "$VERIFY_ROOT/settlement_create_pool_apply_witness_v1" \
  --write-report

check_verify_multi_report \
  "$VERIFY_ROOT/settlement_create_pool_apply_witness_v1/verification_report.json" \
  "settlement_create_pool_apply_witness_v1"

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/settlement_add_liquidity_ratio_witness_v1.yaml" \
  "${VERIFY_MULTI_COMMON[@]}" \
  --output "$VERIFY_ROOT/settlement_add_liquidity_ratio_witness_v1" \
  --write-report

check_verify_multi_report \
  "$VERIFY_ROOT/settlement_add_liquidity_ratio_witness_v1/verification_report.json" \
  "settlement_add_liquidity_ratio_witness_v1"

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/settlement_add_liquidity_apply_witness_v1.yaml" \
  "${VERIFY_MULTI_COMMON[@]}" \
  --output "$VERIFY_ROOT/settlement_add_liquidity_apply_witness_v1" \
  --write-report

check_verify_multi_report \
  "$VERIFY_ROOT/settlement_add_liquidity_apply_witness_v1/verification_report.json" \
  "settlement_add_liquidity_apply_witness_v1"

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/settlement_remove_liquidity_apply_witness_v1.yaml" \
  "${VERIFY_MULTI_COMMON[@]}" \
  --output "$VERIFY_ROOT/settlement_remove_liquidity_apply_witness_v1" \
  --write-report

check_verify_multi_report \
  "$VERIFY_ROOT/settlement_remove_liquidity_apply_witness_v1/verification_report.json" \
  "settlement_remove_liquidity_apply_witness_v1"

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/settlement_swap_apply_witness_v1.yaml" \
  "${VERIFY_MULTI_COMMON[@]}" \
  --output "$VERIFY_ROOT/settlement_swap_apply_witness_v1" \
  --write-report

check_verify_multi_report \
  "$VERIFY_ROOT/settlement_swap_apply_witness_v1/verification_report.json" \
  "settlement_swap_apply_witness_v1"

"$PY" -m ESSO verify-multi \
  "$ROOT_DIR/src/kernels/dex/settlement_swap_exact_out_apply_witness_v1.yaml" \
  "${VERIFY_MULTI_COMMON[@]}" \
  --output "$VERIFY_ROOT/settlement_swap_exact_out_apply_witness_v1" \
  --write-report

check_verify_multi_report \
  "$VERIFY_ROOT/settlement_swap_exact_out_apply_witness_v1/verification_report.json" \
  "settlement_swap_exact_out_apply_witness_v1"

echo "== spot-proof: settlement witness shell verification =="
"$PY" -m ESSO shell-lint \
  "$ROOT_DIR/src/kernels/dex/settlement_create_pool_apply_witness_v1.yaml" \
  --adapter src.kernels.python.settlement_create_pool_apply_witness_v1_native_adapter:make_adapter \
  | tee "$VERIFY_ROOT/settlement_create_pool_apply_witness_v1/shell_lint.json"

"$PY" -m ESSO shell-lint \
  "$ROOT_DIR/src/kernels/dex/settlement_add_liquidity_ratio_witness_v1.yaml" \
  --adapter src.kernels.python.settlement_add_liquidity_ratio_witness_v1_native_adapter:make_adapter \
  | tee "$VERIFY_ROOT/settlement_add_liquidity_ratio_witness_v1/shell_lint.json"

"$PY" -m ESSO shell-lint \
  "$ROOT_DIR/src/kernels/dex/settlement_add_liquidity_apply_witness_v1.yaml" \
  --adapter src.kernels.python.settlement_add_liquidity_apply_witness_v1_native_adapter:make_adapter \
  | tee "$VERIFY_ROOT/settlement_add_liquidity_apply_witness_v1/shell_lint.json"

"$PY" -m ESSO shell-lint \
  "$ROOT_DIR/src/kernels/dex/settlement_remove_liquidity_apply_witness_v1.yaml" \
  --adapter src.kernels.python.settlement_remove_liquidity_apply_witness_v1_native_adapter:make_adapter \
  | tee "$VERIFY_ROOT/settlement_remove_liquidity_apply_witness_v1/shell_lint.json"

"$PY" -m ESSO shell-lint \
  "$ROOT_DIR/src/kernels/dex/settlement_swap_apply_witness_v1.yaml" \
  --adapter src.kernels.python.settlement_swap_apply_witness_v1_native_adapter:make_adapter \
  | tee "$VERIFY_ROOT/settlement_swap_apply_witness_v1/shell_lint.json"

"$PY" -m ESSO shell-lint \
  "$ROOT_DIR/src/kernels/dex/settlement_swap_exact_out_apply_witness_v1.yaml" \
  --adapter src.kernels.python.settlement_swap_exact_out_apply_witness_v1_native_adapter:make_adapter \
  | tee "$VERIFY_ROOT/settlement_swap_exact_out_apply_witness_v1/shell_lint.json"

"$PY" -m ESSO verify-shell \
  "$ROOT_DIR/src/kernels/dex/settlement_create_pool_apply_witness_v1.yaml" \
  --adapter src.kernels.python.settlement_create_pool_apply_witness_v1_native_adapter:make_adapter \
  --output "$VERIFY_ROOT/settlement_create_pool_apply_witness_v1/verify_shell.json" \
  >/dev/null

check_verify_shell_report \
  "$VERIFY_ROOT/settlement_create_pool_apply_witness_v1/verify_shell.json" \
  "$ROOT_DIR/src/kernels/dex/settlement_create_pool_apply_witness_v1.yaml" \
  "src.kernels.python.settlement_create_pool_apply_witness_v1_native_adapter:make_adapter"

"$PY" -m ESSO verify-shell \
  "$ROOT_DIR/src/kernels/dex/settlement_add_liquidity_ratio_witness_v1.yaml" \
  --adapter src.kernels.python.settlement_add_liquidity_ratio_witness_v1_native_adapter:make_adapter \
  --output "$VERIFY_ROOT/settlement_add_liquidity_ratio_witness_v1/verify_shell.json" \
  >/dev/null

check_verify_shell_report \
  "$VERIFY_ROOT/settlement_add_liquidity_ratio_witness_v1/verify_shell.json" \
  "$ROOT_DIR/src/kernels/dex/settlement_add_liquidity_ratio_witness_v1.yaml" \
  "src.kernels.python.settlement_add_liquidity_ratio_witness_v1_native_adapter:make_adapter"

"$PY" -m ESSO verify-shell \
  "$ROOT_DIR/src/kernels/dex/settlement_add_liquidity_apply_witness_v1.yaml" \
  --adapter src.kernels.python.settlement_add_liquidity_apply_witness_v1_native_adapter:make_adapter \
  --output "$VERIFY_ROOT/settlement_add_liquidity_apply_witness_v1/verify_shell.json" \
  >/dev/null

check_verify_shell_report \
  "$VERIFY_ROOT/settlement_add_liquidity_apply_witness_v1/verify_shell.json" \
  "$ROOT_DIR/src/kernels/dex/settlement_add_liquidity_apply_witness_v1.yaml" \
  "src.kernels.python.settlement_add_liquidity_apply_witness_v1_native_adapter:make_adapter"

"$PY" -m ESSO verify-shell \
  "$ROOT_DIR/src/kernels/dex/settlement_remove_liquidity_apply_witness_v1.yaml" \
  --adapter src.kernels.python.settlement_remove_liquidity_apply_witness_v1_native_adapter:make_adapter \
  --output "$VERIFY_ROOT/settlement_remove_liquidity_apply_witness_v1/verify_shell.json" \
  >/dev/null

check_verify_shell_report \
  "$VERIFY_ROOT/settlement_remove_liquidity_apply_witness_v1/verify_shell.json" \
  "$ROOT_DIR/src/kernels/dex/settlement_remove_liquidity_apply_witness_v1.yaml" \
  "src.kernels.python.settlement_remove_liquidity_apply_witness_v1_native_adapter:make_adapter"

"$PY" -m ESSO verify-shell \
  "$ROOT_DIR/src/kernels/dex/settlement_swap_apply_witness_v1.yaml" \
  --adapter src.kernels.python.settlement_swap_apply_witness_v1_native_adapter:make_adapter \
  --output "$VERIFY_ROOT/settlement_swap_apply_witness_v1/verify_shell.json" \
  >/dev/null

check_verify_shell_report \
  "$VERIFY_ROOT/settlement_swap_apply_witness_v1/verify_shell.json" \
  "$ROOT_DIR/src/kernels/dex/settlement_swap_apply_witness_v1.yaml" \
  "src.kernels.python.settlement_swap_apply_witness_v1_native_adapter:make_adapter"

"$PY" -m ESSO verify-shell \
  "$ROOT_DIR/src/kernels/dex/settlement_swap_exact_out_apply_witness_v1.yaml" \
  --adapter src.kernels.python.settlement_swap_exact_out_apply_witness_v1_native_adapter:make_adapter \
  --output "$VERIFY_ROOT/settlement_swap_exact_out_apply_witness_v1/verify_shell.json" \
  >/dev/null

check_verify_shell_report \
  "$VERIFY_ROOT/settlement_swap_exact_out_apply_witness_v1/verify_shell.json" \
  "$ROOT_DIR/src/kernels/dex/settlement_swap_exact_out_apply_witness_v1.yaml" \
  "src.kernels.python.settlement_swap_exact_out_apply_witness_v1_native_adapter:make_adapter"

echo "== spot-proof: adapter regression net =="
"$PY" -m pytest -q \
  tests/kernels/test_settlement_create_pool_apply_witness_v1_native_adapter.py \
  tests/kernels/test_settlement_add_liquidity_ratio_witness_v1_native_adapter.py \
  tests/kernels/test_settlement_add_liquidity_apply_witness_v1_native_adapter.py \
  tests/kernels/test_settlement_remove_liquidity_apply_witness_v1_native_adapter.py \
  tests/kernels/test_settlement_witness_native_adapter_edges.py \
  tests/kernels/test_settlement_swap_apply_witness_v1_ml_bva_cases.py \
  tests/kernels/test_settlement_swap_exact_out_apply_witness_v1_ml_bva_cases.py

echo "== spot-proof: manifest check =="
"$PY" "$ROOT_DIR/tools/check_spot_proof_assurance_manifest.py"

echo "ok"

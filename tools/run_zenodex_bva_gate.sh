#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

PY="${PYTHON:-python3}"
if [[ -x "$ROOT_DIR/.venv/bin/python" ]]; then
  PY="$ROOT_DIR/.venv/bin/python"
fi

MODE="${1:-critical}"
COMMON=(
  --matrix "$ROOT_DIR/docs/assurance/zenodex_bva_matrix_v1.json"
  --repo-root "$ROOT_DIR"
  --verify-files
)

case "$MODE" in
  critical)
    "$PY" "$ROOT_DIR/tools/check_zenodex_bva_matrix.py" "${COMMON[@]}"
    "$PY" -m pytest -q \
      "$ROOT_DIR/tests/tools/test_check_zenodex_bva_matrix.py" \
      "$ROOT_DIR/tests/kernels/test_perp_epoch_isolated_v3_ml_bva_cases.py::test_v3_native_settlement_rejects_unusable_oracle_boundaries" \
      "$ROOT_DIR/tests/core/test_perp_v4_parity.py::test_v4_settlement_oracle_boundaries_match_generated_reference"
    ;;
  promotion)
    "$PY" "$ROOT_DIR/tools/check_zenodex_bva_matrix.py" \
      "${COMMON[@]}" \
      --promotion \
      --require-executed-evidence
    ;;
  *)
    echo "usage: $0 {critical|promotion}" >&2
    exit 2
    ;;
esac

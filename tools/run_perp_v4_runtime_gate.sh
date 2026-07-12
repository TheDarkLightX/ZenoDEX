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

if ! command -v lake >/dev/null 2>&1; then
  echo "error: missing required command 'lake'" >&2
  exit 2
fi

echo "== perps-v4: authored-source lint =="
"$PY" -m ruff check \
  src/core/perp_epoch.py \
  src/core/perp_v4 \
  src/kernels/python/perp_epoch_isolated_v4_adapter.py \
  tests/core/test_perp_v4_parity.py \
  tools/build_perp_epoch_isolated_v4.py

echo "== perps-v4: model/runtime/reference and migration evidence =="
"$PY" -m pytest -q \
  tests/core/test_perp_v4_parity.py \
  tests/formal/test_lean_perp_margin_rounding_safety.py

echo "ok"

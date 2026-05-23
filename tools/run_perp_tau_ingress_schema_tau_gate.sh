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

TAU_BIN="${TAU_BIN:-}"
if [[ -z "${TAU_BIN}" ]]; then
  TAU_BIN="$("$PY" - <<'PY'
from src.integration.tau_runner import find_tau_bin
print(find_tau_bin() or "")
PY
)"
fi

if [[ -z "${TAU_BIN}" || ! -x "${TAU_BIN}" ]]; then
  echo "error: tau binary not found or not executable" >&2
  echo "hint: build external/tau-lang or set TAU_BIN=/path/to/tau" >&2
  exit 2
fi

export TAU_BIN

echo "== perp-tau-ingress-schema: trace test =="
"$PY" -m pytest -q tests/tau/test_perps_tau_specs.py::test_perp_tau_ingress_schema_guard_v1_trace

echo "== perp-tau-ingress-schema: manifest check =="
"$PY" "$ROOT_DIR/tools/check_perp_tau_ingress_schema_tau_manifest.py"

echo "ok"

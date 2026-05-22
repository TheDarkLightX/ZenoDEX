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

require_py_module "jsonschema" "jsonschema"
require_py_module "yaml" "PyYAML"
require_py_module "pytest" "pytest"

echo "== fire: formal assurance claims =="
"$PY" "$ROOT_DIR/tools/check_fire_formal_assurance_claims.py"

echo "== fire: release assurance =="
"$PY" "$ROOT_DIR/tools/check_fire_release_assurance.py"

echo "== fire: assurance regression tests =="
"$PY" -m pytest -q \
  tests/kernels/test_fire_formal_assurance_claims.py \
  tests/kernels/test_fire_release_assurance.py \
  tests/kernels/test_fire_acceptance_receipt_v1.py \
  tests/kernels/test_fire_verifier_rules_spec.py \
  tests/kernels/test_cal_fire_logic_package_receipt_binding.py

echo "ok"

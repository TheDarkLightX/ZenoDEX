#!/usr/bin/env bash
# Quality gate for the /api/dex/* dispatch shell.
# Locks in the committed dispatch-shell refactor:
#   - mypy --strict on the dispatch modules
#   - focused branch coverage over helper, metrics, and registry modules
#   - cyclomatic-complexity regression guard on the dispatch modules
#   - focused regression suite for helpers, registry, and dispatch behavior
# Excluded by design: mutmut (slow ~60s; run nightly, not per-PR).
#
# Why a separate gate: the broader run_critical_quality_gate.sh covers
# many surfaces; this one fences the imperative-shell refactor so future
# additions to dispatch handler modules can't silently regress
# complexity, types, or coverage.

set -euo pipefail

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

if [[ -n "${PYTHON:-}" ]]; then
  PY="$PYTHON"
else
  # Prefer the python that has all the required tooling installed.
  # The .venv path may exist but lack dev tooling (radon, coverage); only
  # use it if it can import all four required modules.
  PY="python3"
  if [[ -x "$ROOT_DIR/.venv/bin/python" ]]; then
    if "$ROOT_DIR/.venv/bin/python" -c "import pytest, coverage, mypy, radon" >/dev/null 2>&1; then
      PY="$ROOT_DIR/.venv/bin/python"
    fi
  fi
fi

require_module() {
  local module="$1"
  local package_hint="$2"
  if ! "$PY" -c "import importlib.util as u, sys; sys.exit(0 if u.find_spec('$module') else 1)"; then
    echo "error: missing python module '$module' (install: $package_hint)" >&2
    exit 2
  fi
}

require_module "pytest" "pytest"
require_module "coverage" "coverage"
require_module "mypy" "mypy"
require_module "radon" "radon"

DISPATCH_MODULES=(
  "src/integration/_dex_api_helpers.py"
  "src/integration/api_server_dex_metrics.py"
  "src/integration/api_server_dex_dispatch.py"
  "src/integration/dex_dispatch_exact_in_route_handlers.py"
  "src/integration/dex_dispatch_exact_out_contract_handlers.py"
  "src/integration/dex_dispatch_exact_out_guarded_handlers.py"
  "src/integration/dex_dispatch_exact_out_packet_common.py"
  "src/integration/dex_dispatch_exact_out_packet_handlers.py"
  "src/integration/dex_dispatch_exact_out_verify_handlers.py"
  "src/integration/dex_dispatch_proof_mining_handlers.py"
  "src/integration/dex_dispatch_proof_mining_reward.py"
  "src/integration/dex_dispatch_proof_mining_snapshots.py"
  "src/integration/dex_dispatch_proof_mining_templates.py"
  "src/integration/dex_dispatch_receipt_handlers.py"
  "src/integration/dex_dispatch_settlement_audit_handlers.py"
  "src/integration/dex_dispatch_slippage_handlers.py"
  "src/integration/dex_dispatch_handlers.py"
)

DISPATCH_TESTS=(
  "tests/integration/test_dex_api_helpers.py"
  "tests/integration/test_api_server_dex_dispatch.py"
)

echo "== dex-dispatch: mypy --strict =="
"$PY" -m mypy --strict "${DISPATCH_MODULES[@]}"

echo "== dex-dispatch: pytest + branch coverage =="
# Use the coverage tool directly (pytest-cov isn't on the default
# requirements lock; coverage 7.x is). Write the data file to a known
# location and report only on helper, metrics, and registry modules (pyproject.toml's
# global [tool.coverage] config has broader source paths we don't want).
COVERAGE_DATA="$ROOT_DIR/.coverage.dex_dispatch_gate"
COVERAGE_INCLUDE="src/integration/_dex_api_helpers.py,src/integration/api_server_dex_metrics.py,src/integration/api_server_dex_dispatch.py,src/integration/dex_dispatch_exact_in_route_handlers.py,src/integration/dex_dispatch_exact_out_contract_handlers.py,src/integration/dex_dispatch_exact_out_guarded_handlers.py,src/integration/dex_dispatch_exact_out_packet_common.py,src/integration/dex_dispatch_exact_out_packet_handlers.py,src/integration/dex_dispatch_exact_out_verify_handlers.py,src/integration/dex_dispatch_proof_mining_handlers.py,src/integration/dex_dispatch_proof_mining_reward.py,src/integration/dex_dispatch_proof_mining_snapshots.py,src/integration/dex_dispatch_proof_mining_templates.py,src/integration/dex_dispatch_receipt_handlers.py,src/integration/dex_dispatch_settlement_audit_handlers.py,src/integration/dex_dispatch_slippage_handlers.py,src/integration/dex_dispatch_handlers.py"
COVERAGE_FILE="$COVERAGE_DATA" "$PY" -m coverage erase --rcfile=/dev/null
COVERAGE_FILE="$COVERAGE_DATA" "$PY" -m coverage run --rcfile=/dev/null --branch \
  --include="$COVERAGE_INCLUDE" \
  -m pytest -q --no-header "${DISPATCH_TESTS[@]}"
COVERAGE_FILE="$COVERAGE_DATA" "$PY" -m coverage report --rcfile=/dev/null \
  --fail-under=90 \
  "src/integration/_dex_api_helpers.py" \
  "src/integration/api_server_dex_metrics.py" \
  "src/integration/api_server_dex_dispatch.py"
# Handler-module line coverage is intentionally not claimed here. The focused
# dispatch tests exercise the HTTP-visible registry behavior, while strict
# typing and the complexity ratchets below fence the split adapter modules.
COVERAGE_FILE="$COVERAGE_DATA" "$PY" -m coverage erase --rcfile=/dev/null

echo "== dex-dispatch: radon cyclomatic complexity (no F-grade allowed) =="
# Any F-grade function in the dispatch modules is a regression of the
# refactor work. Grade A-E pass; F (radon score >50) fails.
F_COUNT="$("$PY" -m radon cc "${DISPATCH_MODULES[@]}" -n F -s 2>&1 | grep -c ' - F (' || true)"
if [[ "$F_COUNT" -gt 0 ]]; then
  echo "error: F-grade cyclomatic complexity in dispatch modules:" >&2
  "$PY" -m radon cc "${DISPATCH_MODULES[@]}" -n F -s >&2
  exit 1
fi

echo "== dex-dispatch: radon maintainability index ratchet =="
# The dispatch shell is now split by route family; every included module should
# remain A-grade on radon maintainability.
for module in "${DISPATCH_MODULES[@]}"; do
  MI_GRADE="$("$PY" -m radon mi "$module" -s | grep -oE '\b[A-F]\b' | head -1)"
  if [[ "$MI_GRADE" != "A" ]]; then
    echo "error: $module maintainability index is $MI_GRADE (expected A)" >&2
    exit 1
  fi
done

echo "ok"

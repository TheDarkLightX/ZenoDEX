#!/bin/bash
# Formal-core candidate battery (research tooling; grants no authority).
#
# Runs the THV1-pinned suites of the O-008 formal-cycle campaign from the repository root:
# the python list in one pytest run, the three ESSO gates with the ESSO environment, then the
# two Lean gates STRICTLY serially. Every Lean-bearing step takes the shared lock so concurrent
# campaign worktrees never compile against the shared mathlib oleans at once.
#
# usage: bash tools/formal_core_battery_v1.sh <output-log>   (stored non-executable: the packet pins sources as mode 100644)
# env:   FORMAL_CORE_PY (default: .venv/bin/python), FORMAL_CORE_ESSO_PYTHONPATH, FORMAL_CORE_ESSO_PYTHON,
#        FORMAL_CORE_LEAN_LOCK (default: /tmp/zenodex-lean.lock)
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT" || exit 1
PY="${FORMAL_CORE_PY:-$ROOT/.venv/bin/python}"
LOCK="${FORMAL_CORE_LEAN_LOCK:-/tmp/zenodex-lean.lock}"
ESSO_PP="${FORMAL_CORE_ESSO_PYTHONPATH:-$ROOT/external/ESSO}"
ESSO_PY="${FORMAL_CORE_ESSO_PYTHON:-/usr/bin/python3}"
export PYTHONDONTWRITEBYTECODE=1 CARGO_INCREMENTAL=0
OUT="$1"
{
echo "battery start $(date -u +%FT%TZ) head=$(git rev-parse --short HEAD)"
flock -w 7200 "$LOCK" "$PY" -m pytest -q -p no:cacheprovider -rf \
  tests/core/test_asset_transfer_receipt_admission_v1.py \
  tests/core/test_economic_initial_state_atom_coverage_v1.py \
  tests/core/test_global_accounting_allocation_certificate_v1_golden.py \
  tests/core/test_global_accounting_lane_producers_v1.py \
  tests/core/test_global_claimant_backing_guard_v1_golden.py \
  tests/core/test_global_economic_state_effect_refinement_v1.py \
  tests/core/test_global_settlement_abi_v1.py \
  tests/core/test_global_settlement_abi_v1_resource_bounds.py \
  tests/core/test_global_settlement_canonical_admission_v1.py \
  tests/core/test_transition_resource_bound_totality_v1.py \
  tests/core/test_asset_transfer_refinement_v1.py \
  tests/core/test_global_settlement_fcis_exact_ownership_v1.py \
  tests/formal/test_lean_asset_transfer_refinement_v1.py \
  tests/formal/test_o008_transition_resource_bound_rust_replay.py \
  tests/test_accounting_source_classification_contract_v1.py \
  tests/test_check_global_settlement_canonical_manifest_v1.py \
  tests/test_check_o008_formal_cycle_v1.py \
  tests/test_check_test_hygiene_v1.py \
  tests/test_global_settlement_v1_rust_wire_bounds.py \
  tests/test_o008_v1_projection_runtime_gate.py
echo "python exit $?"
PYTHONPATH="$ESSO_PP" ZENO_ESSO_PYTHON="$ESSO_PY" "$PY" -m pytest -q -p no:cacheprovider -rf \
  tests/formal/test_esso_global_accounting_allocation_certificate_v1.py \
  tests/formal/test_esso_global_claimant_custody_certificate_v1.py \
  tests/formal/test_esso_global_settlement_core_v1.py
echo "esso exit $?"
flock -w 7200 "$LOCK" "$PY" -m pytest -q -p no:cacheprovider tests/formal/test_lean_global_claimant_custody_relation_v1.py; echo "lean1 exit $?"
flock -w 7200 "$LOCK" "$PY" -m pytest -q -p no:cacheprovider tests/formal/test_lean_global_accounting_allocation_certificate_v1.py; echo "lean2 exit $?"
echo "battery done $(date -u +%FT%TZ)"
} > "$OUT" 2>&1

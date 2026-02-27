#!/usr/bin/env bash
set -euo pipefail

# Build a current perps mechanism-design spec from short Morph probes.
#
# Notes:
# - Reward-subsidy and LP domains intentionally reuse sustained historical artifacts
#   in the builder defaults (higher-seed confidence).
# - This script refreshes faster-moving exploratory domains.

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
PY_BIN="${PYTHON:-}"
if [[ -z "$PY_BIN" ]]; then
  if [[ -x "$ROOT_DIR/.venv/bin/python" ]]; then
    PY_BIN="$ROOT_DIR/.venv/bin/python"
  else
    PY_BIN="python3"
  fi
fi

CODEX_HOME="${CODEX_HOME:-$HOME/.codex}"
SUMMARIZER="$CODEX_HOME/skills/morph-perps-mechanical-scientist/scripts/summarize_scientist_runs.py"
if [[ ! -f "$SUMMARIZER" ]]; then
  echo "error: summarizer not found at $SUMMARIZER (set CODEX_HOME or install the skill)" >&2
  exit 1
fi

export PYTHONPATH="$ROOT_DIR/external/Morph${PYTHONPATH:+:$PYTHONPATH}"

run_probe() {
  local domain="$1"
  local seed="$2"
  local out_dir="$ROOT_DIR/runs/mech_sci_iter/spec_design_probe/$domain"
  mkdir -p "$out_dir"
  "$PY_BIN" -m morph --json scientist ab-sweep \
    --domain "$domain" \
    --out "$out_dir" \
    --seed "$seed" \
    --seeds 3 \
    --train-instances 10 \
    --holdout-instances 16 \
    --max-rounds 1 \
    --patience-rounds 1 \
    --max-wall-seconds 8 \
    --max-eval-instances 1200 \
    --max-generated-per-round 6 \
    --fast-refuter-instances 2 \
    --tryaccept-nodes 20 \
    > "$out_dir/ab_sweep.json"

  "$PY_BIN" "$SUMMARIZER" \
    --ab-sweep "$out_dir/ab_sweep.json" \
    --out "$out_dir/summary.json"
}

echo "== perps mechanism spec campaign: short probes =="
run_probe "perp_funding_rate_gaming" 23200
run_probe "perp_settlement_bounty_farming" 23300
run_probe "perp_collateral_depeg" 23100

echo "== perps mechanism spec campaign: synthesize spec =="
"$PY_BIN" "$ROOT_DIR/tools/perps_mechanism_spec_builder.py"

echo "ok: docs/derivatives/PERP_MECHANISM_SCIENTIST_SPEC_V1.md"
echo "ok: runs/mech_sci_iter/spec_design/perp_mechanism_scientist_spec_v1.json"

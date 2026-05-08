#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

STAMP="$(date +%Y%m%d_%H%M%S)"
CAMPAIGN_ID="${CAMPAIGN_ID:-${STAMP}_compute_max}"
CAMPAIGN_ROOT="${MACOS_SCOUT_CAMPAIGN_ROOT:-internal/macos_scout_campaigns/${CAMPAIGN_ID}}"
mkdir -p "$CAMPAIGN_ROOT"

export OPENBLAS_NUM_THREADS="${OPENBLAS_NUM_THREADS:-1}"
export VECLIB_MAXIMUM_THREADS="${VECLIB_MAXIMUM_THREADS:-1}"
export OMP_NUM_THREADS="${OMP_NUM_THREADS:-1}"
export JULIA_NUM_THREADS="${JULIA_NUM_THREADS:-auto}"
export JULIA_EXCLUSIVE="${JULIA_EXCLUSIVE:-1}"

SCOUT_SEEDS="${SCOUT_SEEDS-20260508 20260509 20260510 20260511}"
DEEP_SEEDS="${DEEP_SEEDS-20260520 20260521}"
RUN_SMOKE="${RUN_SMOKE:-1}"
RUN_SOAK="${RUN_SOAK:-0}"
SOAK_SEED="${SOAK_SEED:-20260530}"

RUN_DIRS=()

run_one() {
  local mode="$1"
  local seed="$2"
  local label="$3"
  local outdir="$CAMPAIGN_ROOT/${label}_${mode}_seed${seed}"
  local logfile="$CAMPAIGN_ROOT/${label}_${mode}_seed${seed}.log"

  RUN_DIRS+=("$outdir")
  echo "== macos compute campaign: mode=$mode seed=$seed out=$outdir =="
  MACOS_SCOUT_OUTDIR="$outdir" SEED="$seed" bash tools/macos_scout/run_macos_scout.sh "$mode" 2>&1 | tee "$logfile"
}

{
  echo "date=$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
  echo "campaign_id=$CAMPAIGN_ID"
  echo "campaign_root=$CAMPAIGN_ROOT"
  echo "scout_seeds=$SCOUT_SEEDS"
  echo "deep_seeds=$DEEP_SEEDS"
  echo "run_smoke=$RUN_SMOKE"
  echo "run_soak=$RUN_SOAK"
  echo "soak_seed=$SOAK_SEED"
  echo "JULIA_NUM_THREADS=$JULIA_NUM_THREADS"
  echo "OPENBLAS_NUM_THREADS=$OPENBLAS_NUM_THREADS"
  echo "VECLIB_MAXIMUM_THREADS=$VECLIB_MAXIMUM_THREADS"
  echo "OMP_NUM_THREADS=$OMP_NUM_THREADS"
  echo "RUN_METAL_PREFILTER=${RUN_METAL_PREFILTER:-0}"
  echo "METAL_PREFILTER_N=${METAL_PREFILTER_N:-unset}"
} > "$CAMPAIGN_ROOT/campaign_env.txt"

if [[ "$RUN_SMOKE" == "1" ]]; then
  run_one smoke "${SMOKE_SEED:-20260508}" smoke
fi

for seed in $SCOUT_SEEDS; do
  run_one scout "$seed" scout
done

for seed in $DEEP_SEEDS; do
  run_one deep "$seed" deep
done

if [[ "$RUN_SOAK" == "1" ]]; then
  run_one soak "$SOAK_SEED" soak
fi

WITNESS_ARGS=()
for run_dir in "${RUN_DIRS[@]}"; do
  if [[ -f "$run_dir/summary.json" ]]; then
    WITNESS_ARGS+=(--run-dir "$run_dir")
  fi
done

if (( ${#WITNESS_ARGS[@]} > 0 )); then
  python3 tools/macos_scout/build_witness_space_receipt.py \
    "${WITNESS_ARGS[@]}" \
    --output "$CAMPAIGN_ROOT/witness_space_receipt.json" \
    --format text | tee "$CAMPAIGN_ROOT/witness_space_receipt.txt"
fi

python3 tools/macos_scout/summarize_compute_campaign.py "$CAMPAIGN_ROOT"

echo "campaign done: $CAMPAIGN_ROOT"

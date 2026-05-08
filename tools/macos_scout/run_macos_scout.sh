#!/usr/bin/env bash
set -euo pipefail

MODE="${1:-smoke}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

if ! command -v julia >/dev/null 2>&1; then
  echo "julia is required. Install Julia for macOS first." >&2
  exit 1
fi

export OPENBLAS_NUM_THREADS="${OPENBLAS_NUM_THREADS:-1}"
export VECLIB_MAXIMUM_THREADS="${VECLIB_MAXIMUM_THREADS:-1}"
export OMP_NUM_THREADS="${OMP_NUM_THREADS:-1}"
export JULIA_EXCLUSIVE="${JULIA_EXCLUSIVE:-1}"

STAMP="$(date +%Y%m%d_%H%M%S)"
OUTDIR="internal/macos_scout_runs/${STAMP}_${MODE}"
mkdir -p "$OUTDIR"

{
  echo "date=$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
  echo "mode=$MODE"
  echo "repo_root=$REPO_ROOT"
  echo "julia=$(julia --version)"
  echo "uname=$(uname -a)"
  echo "OPENBLAS_NUM_THREADS=$OPENBLAS_NUM_THREADS"
  echo "VECLIB_MAXIMUM_THREADS=$VECLIB_MAXIMUM_THREADS"
  echo "OMP_NUM_THREADS=$OMP_NUM_THREADS"
  echo "JULIA_EXCLUSIVE=$JULIA_EXCLUSIVE"
  if command -v sysctl >/dev/null 2>&1; then
    echo "hw.ncpu=$(sysctl -n hw.ncpu 2>/dev/null || true)"
    echo "hw.memsize=$(sysctl -n hw.memsize 2>/dev/null || true)"
  fi
  if command -v system_profiler >/dev/null 2>&1; then
    system_profiler SPHardwareDataType 2>/dev/null || true
    system_profiler SPDisplaysDataType 2>/dev/null || true
  fi
} > "$OUTDIR/host_info.txt"

case "$MODE" in
  smoke)
    CANDIDATES=256
    PATHS=12
    STEPS=32
    TOP=20
    RERANK_TOP=5
    RERANK_PATHS=24
    RERANK_STEPS=48
    FRONT_LIMIT=256
    ;;
  scout)
    CANDIDATES="${CANDIDATES:-50000}"
    PATHS="${PATHS:-64}"
    STEPS="${STEPS:-96}"
    TOP="${TOP:-100}"
    RERANK_TOP="${RERANK_TOP:-100}"
    RERANK_PATHS="${RERANK_PATHS:-256}"
    RERANK_STEPS="${RERANK_STEPS:-192}"
    FRONT_LIMIT="${FRONT_LIMIT:-10000}"
    ;;
  deep)
    CANDIDATES="${CANDIDATES:-250000}"
    PATHS="${PATHS:-96}"
    STEPS="${STEPS:-128}"
    TOP="${TOP:-200}"
    RERANK_TOP="${RERANK_TOP:-250}"
    RERANK_PATHS="${RERANK_PATHS:-512}"
    RERANK_STEPS="${RERANK_STEPS:-256}"
    FRONT_LIMIT="${FRONT_LIMIT:-50000}"
    ;;
  soak)
    CANDIDATES="${CANDIDATES:-1000000}"
    PATHS="${PATHS:-96}"
    STEPS="${STEPS:-128}"
    TOP="${TOP:-500}"
    RERANK_TOP="${RERANK_TOP:-500}"
    RERANK_PATHS="${RERANK_PATHS:-768}"
    RERANK_STEPS="${RERANK_STEPS:-256}"
    FRONT_LIMIT="${FRONT_LIMIT:-100000}"
    ;;
  *)
    echo "unknown mode: $MODE" >&2
    echo "usage: bash tools/macos_scout/run_macos_scout.sh [smoke|scout|deep|soak]" >&2
    exit 2
    ;;
esac

SEED="${SEED:-20260508}"
THREADS="${JULIA_NUM_THREADS:-auto}"

echo "writing run to $OUTDIR"
echo "mode=$MODE candidates=$CANDIDATES paths=$PATHS steps=$STEPS seed=$SEED threads=$THREADS"
echo "rerank_top=$RERANK_TOP rerank_paths=$RERANK_PATHS rerank_steps=$RERANK_STEPS"

if [[ "${RUN_METAL_PREFILTER:-0}" == "1" ]]; then
  METAL_OUT="$OUTDIR/metal_prefilter"
  METAL_N="${METAL_PREFILTER_N:-1000000}"
  echo "running optional Metal prefilter n=$METAL_N out=$METAL_OUT"
  if ! julia --project=tools/macos_scout tools/macos_scout/metal_prefilter.jl --n "$METAL_N" --out "$METAL_OUT"; then
    echo "Metal prefilter failed; continuing with CPU authoritative run" >&2
  fi
fi

JULIA_NUM_THREADS="$THREADS" julia --project=tools/macos_scout \
  tools/macos_scout/derivatives_scout.jl \
  --out "$OUTDIR" \
  --candidates "$CANDIDATES" \
  --paths "$PATHS" \
  --steps "$STEPS" \
  --seed "$SEED" \
  --top "$TOP" \
  --front-limit "$FRONT_LIMIT" \
  --rerank-top "$RERANK_TOP" \
  --rerank-paths "$RERANK_PATHS" \
  --rerank-steps "$RERANK_STEPS"

python3 tools/macos_scout/summarize_scout_outputs.py "$OUTDIR"
python3 tools/macos_scout/check_scout_regression_gate.py \
  --run-dir "$OUTDIR" \
  --output "$OUTDIR/regression_gate.json"
python3 tools/macos_scout/build_witness_space_receipt.py \
  --run-dir "$OUTDIR" \
  --output "$OUTDIR/witness_space_receipt.json"

echo "done: $OUTDIR"

#!/usr/bin/env bash
set -euo pipefail

MODE="${1:-smoke}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

if ! command -v julia >/dev/null 2>&1; then
  echo "julia is required. Install Julia for macOS first." >&2
  exit 1
fi

STAMP="$(date +%Y%m%d_%H%M%S)"
OUTDIR="internal/macos_scout_runs/${STAMP}_${MODE}"
mkdir -p "$OUTDIR"

{
  echo "date=$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
  echo "mode=$MODE"
  echo "repo_root=$REPO_ROOT"
  echo "julia=$(julia --version)"
  echo "uname=$(uname -a)"
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
    ;;
  scout)
    CANDIDATES="${CANDIDATES:-20000}"
    PATHS="${PATHS:-64}"
    STEPS="${STEPS:-96}"
    TOP="${TOP:-100}"
    ;;
  deep)
    CANDIDATES="${CANDIDATES:-120000}"
    PATHS="${PATHS:-96}"
    STEPS="${STEPS:-128}"
    TOP="${TOP:-200}"
    ;;
  *)
    echo "unknown mode: $MODE" >&2
    echo "usage: bash tools/macos_scout/run_macos_scout.sh [smoke|scout|deep]" >&2
    exit 2
    ;;
esac

SEED="${SEED:-20260508}"
THREADS="${JULIA_NUM_THREADS:-auto}"

echo "writing run to $OUTDIR"
echo "mode=$MODE candidates=$CANDIDATES paths=$PATHS steps=$STEPS seed=$SEED threads=$THREADS"

JULIA_NUM_THREADS="$THREADS" julia --project=tools/macos_scout \
  tools/macos_scout/derivatives_scout.jl \
  --out "$OUTDIR" \
  --candidates "$CANDIDATES" \
  --paths "$PATHS" \
  --steps "$STEPS" \
  --seed "$SEED" \
  --top "$TOP"

python3 tools/macos_scout/summarize_scout_outputs.py "$OUTDIR"

echo "done: $OUTDIR"

#!/bin/bash
# Run MLX hint generator from Terminal (requires GUI context for Metal access)
# Usage: ./tools/run_mlx_hints.sh <hole_yaml> <synth_json> [output_hints.json] [validate]

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
VENV_PYTHON="$PROJECT_DIR/external/ESSO/.venv/bin/python"

if [ $# -lt 2 ]; then
    echo "Usage: $0 <hole_yaml> <synth_json> [output_hints.json] [validate]"
    echo ""
    echo "Example:"
    echo "  $0 src/kernels/dex/fee_accumulator_simple_hole.yaml \\"
    echo "     src/kernels/dex/fee_accumulator_simple_hole.synth.json"
    exit 1
fi

HOLE_YAML="$1"
SYNTH_JSON="$2"
OUTPUT="${3:-runs/mlx_hints_$(basename "$HOLE_YAML" .yaml).json}"
VALIDATE="${4:-none}"

echo "=== MLX Hint Generator ==="
echo "Model: Qwen3-Next-80B-A3B-Instruct (49GB)"
echo "Hole:  $HOLE_YAML"
echo "Synth: $SYNTH_JSON"
echo "Output: $OUTPUT"
echo ""

cd "$PROJECT_DIR"

$VENV_PYTHON tools/esso_mlx_hints.py hints-only "$HOLE_YAML" "$SYNTH_JSON" --hints-out "$OUTPUT" --validate "$VALIDATE"

echo ""
echo "=== Done ==="
echo "Hints saved to: $OUTPUT"

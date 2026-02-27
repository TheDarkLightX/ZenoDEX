#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

if [[ -n "${PYTHON:-}" ]]; then
  PY="$PYTHON"
elif command -v python3.11 >/dev/null 2>&1; then
  PY="python3.11"
elif [[ -x "$ROOT_DIR/.venv/bin/python" ]]; then
  PY="$ROOT_DIR/.venv/bin/python"
else
  PY="python3"
fi

if [[ -x "$ROOT_DIR/tools/esso/.venv/bin/python" ]]; then
  ESSO_PY="$ROOT_DIR/tools/esso/.venv/bin/python"
else
  ESSO_PY="$PY"
fi

CONFIG_PATH="${PERPS_LIFTOFF_CONFIG:-$ROOT_DIR/docs/derivatives/mechanical_scientist_perps_config_m3max.yaml}"
MODEL_PATH="${PERPS_LIFTOFF_MODEL:-src/kernels/dex/perp_epoch_isolated_v3.yaml}"
GPU_BATCH_HAZARD="${GPU_BATCH_HAZARD:-262144}"
GPU_ITERS_HAZARD="${GPU_ITERS_HAZARD:-20}"
GPU_BATCH_CE="${GPU_BATCH_CE:-262144}"
GPU_STEPS_CE="${GPU_STEPS_CE:-2000}"
ML_BVA_CASES_PER_ACTION="${ML_BVA_CASES_PER_ACTION:-12}"
ML_BVA_ITERS_PER_ACTION="${ML_BVA_ITERS_PER_ACTION:-220}"
ML_BVA_MAX_CANDIDATES="${ML_BVA_MAX_CANDIDATES:-400}"
ML_BVA_MAX_STATES="${ML_BVA_MAX_STATES:-128}"
ML_BVA_ALPHA="${ML_BVA_ALPHA:-1.25}"

STAMP="$(date -u +%Y%m%d_%H%M%S)"
RUN_ROOT="$ROOT_DIR/runs/morph/mechanical_scientist_perps/m3max_liftoff_$STAMP"
CAMPAIGN_DIR="$RUN_ROOT/campaign"
mkdir -p "$RUN_ROOT"

echo "== liftoff run root =="
echo "$RUN_ROOT"
echo

echo "== torch backend check =="
"$ESSO_PY" - <<'PY'
import json
import torch
out = {
    "torch_version": torch.__version__,
    "mps_built": bool(getattr(torch.backends, "mps", None) and torch.backends.mps.is_built()),
    "mps_available": bool(getattr(torch.backends, "mps", None) and torch.backends.mps.is_available()),
    "cuda_available": bool(getattr(torch, "cuda", None) and torch.cuda.is_available()),
}
print(json.dumps(out, sort_keys=True, indent=2))
if not out["mps_available"] and not out["cuda_available"]:
    raise SystemExit("no GPU backend available (need mps/cuda)")
PY
echo

echo "== GPU math hazard mining (funding) =="
"$ESSO_PY" "$ROOT_DIR/tools/mine_perp_math_hazards_gpu.py" \
  --prefer-gpu \
  --require-gpu \
  --kind funding \
  --batch "$GPU_BATCH_HAZARD" \
  --iters "$GPU_ITERS_HAZARD" \
  --json | tee "$RUN_ROOT/hazard_funding.json"
echo

echo "== GPU math hazard mining (pnl) =="
"$ESSO_PY" "$ROOT_DIR/tools/mine_perp_math_hazards_gpu.py" \
  --prefer-gpu \
  --require-gpu \
  --kind pnl \
  --batch "$GPU_BATCH_HAZARD" \
  --iters "$GPU_ITERS_HAZARD" \
  --json | tee "$RUN_ROOT/hazard_pnl.json"
echo

echo "== GPU CE mining =="
"$ESSO_PY" "$ROOT_DIR/tools/mine_perps_ce_gpu.py" \
  --prefer-gpu \
  --require-gpu \
  --model "$MODEL_PATH" \
  --steps "$GPU_STEPS_CE" \
  --batch "$GPU_BATCH_CE" \
  --json | tee "$RUN_ROOT/perps_ce_mining.json"
echo

echo "== ML-driven boundary test generation =="
"$PY" "$ROOT_DIR/tools/ml_boundary_bva.py" \
  --model "$MODEL_PATH" \
  --out-json "$RUN_ROOT/ml_bva_cases.json" \
  --cases-per-action "$ML_BVA_CASES_PER_ACTION" \
  --iterations-per-action "$ML_BVA_ITERS_PER_ACTION" \
  --max-candidates-per-action "$ML_BVA_MAX_CANDIDATES" \
  --max-states "$ML_BVA_MAX_STATES" \
  --alpha "$ML_BVA_ALPHA" \
  --pretty | tee "$RUN_ROOT/ml_bva_summary.json"
echo

echo "== mechanical scientist campaign =="
"$PY" "$ROOT_DIR/tools/mechanical_scientist_perps.py" \
  campaign \
  --config "$CONFIG_PATH" \
  --out "$CAMPAIGN_DIR" | tee "$RUN_ROOT/campaign.stdout.json"
echo

echo "== strict replay =="
"$PY" "$ROOT_DIR/tools/mechanical_scientist_perps.py" \
  replay \
  --campaign-dir "$CAMPAIGN_DIR" \
  --python "$PY" | tee "$RUN_ROOT/replay.stdout.json"
echo

echo "== throughput summary =="
"$PY" - <<PY
import json
from pathlib import Path

run_root = Path("$RUN_ROOT")
campaign_summary = json.loads((run_root / "campaign" / "campaign_summary.json").read_text(encoding="utf-8"))
promotions_path = run_root / "campaign" / "promotions.jsonl"

promotions = 0
coverage = 0
if promotions_path.exists():
    for line in promotions_path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        promotions += 1
        obj = json.loads(line)
        if str(obj.get("promotion_reason", "")) == "coverage_frontier":
            coverage += 1

out = {
    "campaign_dir": str((run_root / "campaign").resolve()),
    "elapsed_seconds": float(campaign_summary.get("elapsed_seconds", 0.0)),
    "evaluations_per_minute": float(campaign_summary.get("evaluations_per_minute", 0.0)),
    "visited_per_second": float(campaign_summary.get("visited_per_second", 0.0)),
    "strict_ok_rate": float(campaign_summary.get("strict_ok_rate", 0.0)),
    "total_evaluations": int(campaign_summary.get("total_evaluations", 0)),
    "total_unique_hypotheses_evaluated": int(campaign_summary.get("total_unique_hypotheses_evaluated", 0)),
    "total_promotions": promotions,
    "coverage_frontier_promotions": coverage,
}
print(json.dumps(out, sort_keys=True, indent=2))
PY

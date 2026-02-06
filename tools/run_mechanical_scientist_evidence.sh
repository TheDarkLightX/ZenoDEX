#!/usr/bin/env bash
set -euo pipefail

# Evidence runner for the perps mechanical-scientist campaign.
#
# This is intentionally fail-closed:
# - runs a quick deterministic campaign smoke
# - replays strict doctor checks over all produced bundles

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

if [[ ! -d "$ROOT_DIR/external/Morph" ]]; then
  echo "error: missing Morph checkout at $ROOT_DIR/external/Morph" >&2
  exit 2
fi

"$PY" - <<'PY'
import sys
if sys.version_info < (3, 10):
    raise SystemExit("error: mechanical scientist evidence requires Python >= 3.10")
PY

echo "== mechanical scientist: claims registry format check =="
"$PY" "$ROOT_DIR/tools/check_claims_registry.py"

echo "== mechanical scientist: stress scenario parity regression =="
"$PY" -m pytest -q "$ROOT_DIR/tests/core/test_perp_parity_stress_scenarios.py"

STAMP="$(date -u +%Y%m%d_%H%M%S)"
OUT_DIR="$ROOT_DIR/runs/morph/mechanical_scientist_perps/evidence_smoke/$STAMP"

echo "== mechanical scientist: campaign quick smoke =="
"$PY" "$ROOT_DIR/tools/mechanical_scientist_perps.py" \
  campaign \
  --config "$ROOT_DIR/docs/derivatives/mechanical_scientist_perps_config.yaml" \
  --out "$OUT_DIR" \
  --quick

echo "== mechanical scientist: replay strict doctor =="
"$PY" "$ROOT_DIR/tools/mechanical_scientist_perps.py" \
  replay \
  --campaign-dir "$OUT_DIR" \
  --python "$PY"

echo "ok"

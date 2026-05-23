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

require_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "error: missing required command '$cmd'" >&2
    exit 2
  fi
}

ensure_esso() {
  if [[ -d "$ROOT_DIR/external/ESSO" ]]; then
    export PYTHONPATH="$ROOT_DIR/external/ESSO${PYTHONPATH:+:$PYTHONPATH}"
    return
  fi
  if ! "$PY" -c "import importlib.util as u; raise SystemExit(0 if u.find_spec('ESSO') else 1)"; then
    echo "error: missing ESSO toolchain (expected either $ROOT_DIR/external/ESSO or an importable ESSO module)" >&2
    exit 2
  fi
}

require_file() {
  local label="$1"
  local path="$2"
  if [[ ! -f "$path" ]]; then
    echo "error: missing required file for $label: $path" >&2
    exit 2
  fi
}

require_cmd "git"
ensure_esso

BASE_CONTRACT="$ROOT_DIR/tools/batch_auction_ifql_sources/batch_auction_compass_contract_v7.json"
INTENT_LATTICE="$ROOT_DIR/tools/intent_lattices/batch_auction_v7_observation_intent.json"
REF_MODEL="$ROOT_DIR/tools/batch_auction_ifql_sources/batch_settler_v5_model.yaml"
CAND_MODEL="$ROOT_DIR/tools/batch_auction_ifql_sources/batch_settler_v7_model.yaml"
VERIFY_ROOT="$ROOT_DIR/internal/esso_verify/batch_auction_ifql_vmo"
CONTRACT_PATH="$VERIFY_ROOT/contract_ifql.json"

require_file "batch-auction v7 contract" "$BASE_CONTRACT"
require_file "batch-auction IFQL intent lattice" "$INTENT_LATTICE"
require_file "batch-auction v5 compiled model" "$REF_MODEL"
require_file "batch-auction v7 compiled model" "$CAND_MODEL"

mkdir -p "$VERIFY_ROOT"

echo "== batch-auction-ifql: contract wrapper =="
"$PY" - "$BASE_CONTRACT" "$CONTRACT_PATH" <<'PY'
from __future__ import annotations

import json
import sys
from pathlib import Path

base_contract = Path(sys.argv[1]).resolve()
out_path = Path(sys.argv[2]).resolve()
root = out_path.parent
contract = json.loads(base_contract.read_text(encoding="utf-8"))
intent_path = (Path("../../../tools/intent_lattices/batch_auction_v7_observation_intent.json")).as_posix()
contract["intent"] = intent_path
out_path.write_text(json.dumps(contract, sort_keys=True, indent=2) + "\n", encoding="utf-8")
PY

echo "== batch-auction-ifql: intent lint =="
"$PY" -m ESSO compass intent lint \
  --contract "$CONTRACT_PATH" \
  >"$VERIFY_ROOT/intent_lint.json"

echo "== batch-auction-ifql: derive reference fiber =="
"$PY" -m ESSO ifql derive \
  --contract "$CONTRACT_PATH" \
  --model "$REF_MODEL" \
  --out "$VERIFY_ROOT/ifql_reference.json" \
  >/dev/null

echo "== batch-auction-ifql: derive candidate fiber =="
"$PY" -m ESSO ifql derive \
  --contract "$CONTRACT_PATH" \
  --model "$CAND_MODEL" \
  --out "$VERIFY_ROOT/ifql_candidate.json" \
  >/dev/null

echo "== batch-auction-ifql: VMO full =="
"$PY" -m ESSO ifql vmo \
  "$CAND_MODEL" \
  --reference "$REF_MODEL" \
  --contract "$CONTRACT_PATH" \
  --intent-id I_observations_batch_settler_public \
  --mode full \
  --timeout-ms 4000 \
  --out "$VERIFY_ROOT/ifql_vmo_full.json" \
  >/dev/null

echo "== batch-auction-ifql: VMO no_extra =="
"$PY" -m ESSO ifql vmo \
  "$CAND_MODEL" \
  --reference "$REF_MODEL" \
  --contract "$CONTRACT_PATH" \
  --intent-id I_observations_batch_settler_public \
  --mode no_extra \
  --timeout-ms 4000 \
  --out "$VERIFY_ROOT/ifql_vmo_no_extra.json" \
  >/dev/null

echo "== batch-auction-ifql: manifest check =="
"$PY" "$ROOT_DIR/tools/check_batch_auction_ifql_vmo_manifest.py"

echo "ok"

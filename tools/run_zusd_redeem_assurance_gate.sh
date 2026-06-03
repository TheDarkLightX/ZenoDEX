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

echo "== pinned-assurance-manifest: zusd_redeem_assurance_manifest.json =="
"$PY" "$ROOT_DIR/tools/check_zusd_repay_assurance_manifest.py" --manifest "$ROOT_DIR/tools/zusd_redeem_assurance_manifest.json"

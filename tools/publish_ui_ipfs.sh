#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
UI_DIR="$ROOT/tools/dex-ui"
OUT_DIR="${OUT_DIR:-$ROOT/generated/ipfs_ui}"
PIN_LOCAL="${PIN_LOCAL:-1}"
API_BASE="${VITE_API_BASE:-}"
BASE_PATH="${VITE_BASE_PATH:-./}"

mkdir -p "$OUT_DIR"

cd "$UI_DIR"

if [[ ! -d node_modules ]]; then
  npm ci
fi

VITE_BASE_PATH="$BASE_PATH" \
VITE_API_BASE="$API_BASE" \
npm run build

rm -rf "$OUT_DIR/dist"
mkdir -p "$OUT_DIR"
cp -R dist "$OUT_DIR/dist"

(
  cd "$OUT_DIR/dist"
  find . -type f -print0 | sort -z | xargs -0 sha256sum > "$OUT_DIR/sha256sums.txt"
)

if [[ "$PIN_LOCAL" == "1" ]] && command -v ipfs >/dev/null 2>&1; then
  CID="$(ipfs add -Qr "$OUT_DIR/dist")"
  printf '{\n  "cid": "%s",\n  "api_base": "%s",\n  "base_path": "%s"\n}\n' \
    "$CID" "$API_BASE" "$BASE_PATH" > "$OUT_DIR/ipfs_publish.json"
  echo "Pinned UI to local IPFS node: $CID"
else
  CID=""
  echo "Built IPFS-ready UI at $OUT_DIR/dist"
  echo "Local ipfs CLI not found or PIN_LOCAL=0; skipping pin step"
fi

manifest_args=(
  --dist-dir "$OUT_DIR/dist"
  --out "$OUT_DIR/release_manifest.json"
  --api-base "$API_BASE"
  --base-path "$BASE_PATH"
)
if [[ -n "${CID:-}" ]]; then
  manifest_args+=(--cid "$CID")
fi
python3 "$ROOT/tools/permissionless_release_manifest.py" "${manifest_args[@]}"

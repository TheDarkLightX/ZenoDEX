#!/usr/bin/env bash
set -euo pipefail

# Production readiness gate for ZenoDEX.
#
# Runs:
# - python tests
# - container hardening artifact checks
# - private-toolchain kernel assurance (cpmm_swap + liquidity_pool)
# - npm audit for UI
# - docker build of production image
# - trivy scan of the built artifact
#
# Usage:
#   bash tools/prod_gate.sh
#   bash tools/prod_gate.sh --skip-docker
#   bash tools/prod_gate.sh --skip-ui
#
# Exit codes:
#   0  pass
#   1  fail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUNTIME_LOCK="$ROOT/requirements-core.lock.txt"
AGENTS_LOCK="$ROOT/requirements-agents.lock.txt"
DEV_LOCK="$ROOT/requirements-dev.lock.txt"

SKIP_DOCKER=0
SKIP_UI=0
IMAGE_TAG="${IMAGE_TAG:-zenodex:local}"
KERNEL_JSON=""
UI_AUDIT_JSON=""
UI_AUDIT_LOG=""
TRIVY_JSON=""

cleanup() {
  rm -f "$KERNEL_JSON" "$UI_AUDIT_JSON" "$UI_AUDIT_LOG" "$TRIVY_JSON"
}
trap cleanup EXIT

while [[ $# -gt 0 ]]; do
  case "$1" in
    --skip-docker) SKIP_DOCKER=1; shift ;;
    --skip-ui) SKIP_UI=1; shift ;;
    --image-tag) IMAGE_TAG="$2"; shift 2 ;;
    *)
      echo "Unknown arg: $1" >&2
      exit 1
      ;;
  esac
done

cd "$ROOT"

echo "[gate] repo: $ROOT"
echo "[gate] image: $IMAGE_TAG"

if [[ ! -f "$RUNTIME_LOCK" ]]; then
  echo "[gate] missing runtime lock file: $RUNTIME_LOCK" >&2
  exit 2
fi
if [[ ! -f "$AGENTS_LOCK" ]]; then
  echo "[gate] missing agents lock file: $AGENTS_LOCK" >&2
  exit 2
fi
if [[ ! -f "$DEV_LOCK" ]]; then
  echo "[gate] missing dev lock file: $DEV_LOCK" >&2
  exit 2
fi

if [[ ! -d .venv ]]; then
  echo "[gate] creating venv .venv"
  python3 -m venv .venv
fi

echo "[gate] installing locked dev requirements"
. .venv/bin/activate
python -m pip install --quiet --require-hashes -r "$DEV_LOCK"

echo "[gate] checking container hardening artifacts"
python tools/check_container_hardening.py

KERNEL_JSON="$(mktemp)"
echo "[gate] running kernel assurance (manifest-backed)"
python tools/dex_kernel_assurance.py --pretty >"$KERNEL_JSON"
python - "$KERNEL_JSON" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as f:
    data = json.load(f)
assert data.get("ok") is True, data
print("[gate] kernel assurance OK")
PY

echo "[gate] running pytest"
pytest -q

if [[ "$SKIP_UI" -eq 0 ]]; then
  if [[ -d tools/dex-ui ]]; then
    UI_AUDIT_JSON="$(mktemp)"
    UI_AUDIT_LOG="$(mktemp)"
    echo "[gate] running npm audit (UI)"
    (
      cd tools/dex-ui
      npm audit --json >"$UI_AUDIT_JSON" 2>"$UI_AUDIT_LOG" || true
      node - "$UI_AUDIT_JSON" "$UI_AUDIT_LOG" <<'NODE'
const fs = require('fs');

const jsonPath = process.argv[2];
const logPath = process.argv[3];
const raw = fs.readFileSync(jsonPath, 'utf8').trim();
const stderr = fs.readFileSync(logPath, 'utf8').trim();

function fail(message) {
  console.error(message);
  process.exit(1);
}

if (!raw) {
  fail(`[gate] npm audit produced no JSON output${stderr ? `\n${stderr}` : ''}`);
}

let data;
try {
  data = JSON.parse(raw);
} catch (err) {
  fail(`[gate] npm audit emitted invalid JSON: ${err.message}${stderr ? `\n${stderr}` : ''}`);
}

if (data.error) {
  fail(`[gate] npm audit failed: ${JSON.stringify(data.error, null, 2)}`);
}

const meta = (data.metadata && data.metadata.vulnerabilities) || {};
const bad = Number(meta.high || 0) + Number(meta.critical || 0);
if (bad > 0) {
  fail(JSON.stringify(data, null, 2));
}

console.log('[gate] npm audit OK');
NODE
    )
  else
    echo "[gate] tools/dex-ui not present; skipping UI audit"
  fi
else
  echo "[gate] skipping UI audit (--skip-ui)"
fi

if [[ "$SKIP_DOCKER" -eq 0 ]]; then
  echo "[gate] building production image (docker build --network=host)"
  docker build --network=host -t "$IMAGE_TAG" -f Dockerfile .

  TRIVY_DIR="tools/_secbin"
  TRIVY_BIN="$TRIVY_DIR/trivy"
  TRIVY_VERSION="0.69.3"
  TRIVY_SHA256="1816b632dfe529869c740c0913e36bd1629cb7688bd5634f4a858c1d57c88b75"
  TRIVY_TARBALL="$TRIVY_DIR/trivy.tar.gz"
  mkdir -p "$TRIVY_DIR"

  NEED_TRIVY_DOWNLOAD=1
  if [[ -x "$TRIVY_BIN" ]]; then
    CURRENT_TRIVY_VERSION="$("$TRIVY_BIN" --version 2>/dev/null | awk '/^Version:/ {print $2; exit}')"
    if [[ "$CURRENT_TRIVY_VERSION" == "$TRIVY_VERSION" ]]; then
      NEED_TRIVY_DOWNLOAD=0
    else
      echo "[gate] refreshing trivy: have ${CURRENT_TRIVY_VERSION:-unknown}, need $TRIVY_VERSION"
      rm -f "$TRIVY_BIN"
    fi
  fi

  if [[ "$NEED_TRIVY_DOWNLOAD" -eq 1 ]]; then
    echo "[gate] trivy not found at pinned version; downloading"
    curl -fsSL -o "$TRIVY_TARBALL" "https://github.com/aquasecurity/trivy/releases/download/v${TRIVY_VERSION}/trivy_${TRIVY_VERSION}_Linux-64bit.tar.gz"
    ACTUAL_SHA256="$(sha256sum "$TRIVY_TARBALL" | awk '{print $1}')"
    if [[ "$ACTUAL_SHA256" != "$TRIVY_SHA256" ]]; then
      echo "[gate] trivy checksum mismatch: expected $TRIVY_SHA256, got $ACTUAL_SHA256" >&2
      exit 1
    fi
    tar -xzf "$TRIVY_TARBALL" -C "$TRIVY_DIR" trivy
    rm -f "$TRIVY_TARBALL"
    INSTALLED_TRIVY_VERSION="$("$TRIVY_BIN" --version 2>/dev/null | awk '/^Version:/ {print $2; exit}')"
    if [[ "$INSTALLED_TRIVY_VERSION" != "$TRIVY_VERSION" ]]; then
      echo "[gate] trivy version mismatch after download: expected $TRIVY_VERSION, got ${INSTALLED_TRIVY_VERSION:-unknown}" >&2
      exit 1
    fi
  fi

  TRIVY_JSON="$(mktemp)"
  echo "[gate] scanning built artifact (HIGH/CRITICAL w/ fixes)"
  "$TRIVY_BIN" clean --all >/dev/null 2>&1 || true
  "$TRIVY_BIN" image --quiet --format json --severity CRITICAL,HIGH --ignore-unfixed --timeout 20m "$IMAGE_TAG" > "$TRIVY_JSON"
  python - "$TRIVY_JSON" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as f:
    d = json.load(f)
bad=[]
for r in d.get('Results') or []:
  for v in r.get('Vulnerabilities') or []:
    if v.get('Severity') in ('CRITICAL','HIGH'):
      bad.append((v.get('VulnerabilityID'), v.get('PkgName'), v.get('InstalledVersion'), v.get('FixedVersion')))
if bad:
  raise SystemExit(f"trivy HIGH/CRIT fixable vulns found: {bad[:20]}")
print("[gate] trivy OK (0 HIGH/CRIT fixable)")
PY
else
  echo "[gate] skipping docker build + trivy (--skip-docker)"
fi

echo "[gate] PASS"

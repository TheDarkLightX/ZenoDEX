#!/usr/bin/env bash
set -euo pipefail

# Production readiness gate for ZenoDEX.
#
# Runs:
# - python tests
# - ESSO kernel assurance (cpmm_swap + liquidity_pool)
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

SKIP_DOCKER=0
SKIP_UI=0
IMAGE_TAG="${IMAGE_TAG:-zenodex:local}"

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

if [[ ! -d .venv ]]; then
  echo "[gate] creating venv .venv"
  python3 -m venv .venv
fi

echo "[gate] installing python requirements"
. .venv/bin/activate
python -m pip install --upgrade --quiet pip
pip install --quiet -r requirements.txt

echo "[gate] running pytest"
pytest -q

echo "[gate] running kernel assurance (manifest-backed)"
python tools/dex_kernel_assurance.py --pretty >/tmp/zenodex_kernel_assurance.json
python -c "import json; d=json.load(open('/tmp/zenodex_kernel_assurance.json')); assert d.get('ok') is True, d"
echo "[gate] kernel assurance OK"

if [[ "$SKIP_UI" -eq 0 ]]; then
  if [[ -d tools/dex-ui ]]; then
    echo "[gate] running npm audit (UI)"
    (cd tools/dex-ui && npm audit --json | node -e "let d='';process.stdin.on('data',c=>d+=c);process.stdin.on('end',()=>{const j=JSON.parse(d);const m=j.metadata?.vulnerabilities||{};const bad=(m.high||0)+(m.critical||0); if(bad>0){console.error(j); process.exit(1);} console.log('[gate] npm audit OK');});")
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
  mkdir -p "$TRIVY_DIR"

  if [[ ! -x "$TRIVY_BIN" ]]; then
    echo "[gate] trivy not found; downloading"
    # Pin to a known-good release for determinism.
    TRIVY_VERSION="0.68.2"
    curl -fsSL -o "$TRIVY_DIR/trivy.tar.gz" "https://github.com/aquasecurity/trivy/releases/download/v${TRIVY_VERSION}/trivy_${TRIVY_VERSION}_Linux-64bit.tar.gz"
    tar -xzf "$TRIVY_DIR/trivy.tar.gz" -C "$TRIVY_DIR" trivy
    rm -f "$TRIVY_DIR/trivy.tar.gz"
  fi

  echo "[gate] scanning built artifact (HIGH/CRITICAL w/ fixes)"
  "$TRIVY_BIN" clean --all >/dev/null 2>&1 || true
  "$TRIVY_BIN" image --quiet --format json --severity CRITICAL,HIGH --ignore-unfixed --timeout 20m "$IMAGE_TAG" > /tmp/zenodex_trivy.json
  python - <<'PY'
import json
d=json.load(open('/tmp/zenodex_trivy.json'))
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


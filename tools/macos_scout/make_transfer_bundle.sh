#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

STAMP="$(date +%Y%m%d_%H%M%S)"
OUTDIR="internal/macos_scout_transfer"
BUNDLE="${OUTDIR}/zenodex_macos_scout_${STAMP}.tar.gz"
mkdir -p "$OUTDIR"

tar -czf "$BUNDLE" \
  docs/macos_scout \
  tools/macos_scout

sha256sum "$BUNDLE" > "${BUNDLE}.sha256" 2>/dev/null || shasum -a 256 "$BUNDLE" > "${BUNDLE}.sha256"

echo "$BUNDLE"
echo "${BUNDLE}.sha256"

#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
DEST_DIR="${ROOT_DIR}/external/tla-tools"
DEST_JAR="${DEST_DIR}/tla2tools.jar"
URL="${TLA_TOOLS_URL:-https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar}"

mkdir -p "${DEST_DIR}"
echo "downloading TLC from ${URL}"
curl -fL "${URL}" -o "${DEST_JAR}"
echo "installed ${DEST_JAR}"

if command -v java >/dev/null 2>&1; then
  HELP_OUT="$(mktemp)"
  if java -XX:+UseParallelGC -cp "${DEST_JAR}" tlc2.TLC -help >"${HELP_OUT}" 2>&1; then
    echo "verified TLC jar"
  elif grep -q "TLC - provides model checking" "${HELP_OUT}"; then
    echo "verified TLC jar"
  else
    cat "${HELP_OUT}" >&2
    rm -f "${HELP_OUT}"
    exit 1
  fi
  rm -f "${HELP_OUT}"
else
  echo "warning: java not found on PATH; TLC jar downloaded but not verified" >&2
fi

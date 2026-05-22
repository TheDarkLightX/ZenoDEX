#!/usr/bin/env bash
# Sync packages/zeno-proof-client/src and test/ from tools/dex-ui/src/sdk/.
#
# The dex-ui SDK directory is the authoritative source. The package is the
# publishable npm artifact. This script copies dex-ui → package and patches
# the test files' import paths.
#
# Run before publishing the SDK package.
# CI invokes this in --check mode to detect drift.
set -euo pipefail

cd "$(dirname "$0")/.."

DEX_UI_SDK="tools/dex-ui/src/sdk"
PKG_SRC="packages/zeno-proof-client/src"
PKG_TEST="packages/zeno-proof-client/test"

CHECK_MODE=0
if [[ "${1-}" == "--check" ]]; then
  CHECK_MODE=1
fi

copy_or_check() {
  local src="$1"
  local dst="$2"
  if [[ "${CHECK_MODE}" -eq 1 ]]; then
    if ! diff -q "${src}" "${dst}" > /dev/null 2>&1; then
      echo "DRIFT: ${dst} differs from ${src}" >&2
      return 1
    fi
  else
    cp "${src}" "${dst}"
  fi
}

copy_or_check "${DEX_UI_SDK}/zenoProofClient.js" "${PKG_SRC}/zenoProofClient.js"
copy_or_check "${DEX_UI_SDK}/zenoBlsVerifier.js" "${PKG_SRC}/zenoBlsVerifier.js"

# Tests need their import paths patched. Compute the patched versions and
# write/check them.
sync_test() {
  local name="$1"
  local src="${DEX_UI_SDK}/${name}"
  local dst="${PKG_TEST}/${name}"
  local tmp
  tmp="$(mktemp)"
  sed \
    -e "s|from './zenoProofClient.js'|from '../src/zenoProofClient.js'|g" \
    -e "s|from './zenoBlsVerifier.js'|from '../src/zenoBlsVerifier.js'|g" \
    -e "s|resolve(_here, '../../../..')|resolve(_here, '../../..')|g" \
    "${src}" > "${tmp}"
  if [[ "${CHECK_MODE}" -eq 1 ]]; then
    if ! diff -q "${tmp}" "${dst}" > /dev/null 2>&1; then
      echo "DRIFT: ${dst} differs from patched ${src}" >&2
      rm -f "${tmp}"
      return 1
    fi
    rm -f "${tmp}"
  else
    mv "${tmp}" "${dst}"
  fi
}

sync_test "zenoProofClient.test.mjs"
sync_test "zenoBlsVerifier.test.mjs"

if [[ "${CHECK_MODE}" -eq 1 ]]; then
  echo "ok: packages/zeno-proof-client/ is in sync with tools/dex-ui/src/sdk/"
else
  echo "ok: synced tools/dex-ui/src/sdk/ → packages/zeno-proof-client/"
fi

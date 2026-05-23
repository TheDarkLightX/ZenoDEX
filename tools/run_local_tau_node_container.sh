#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ ! -f "$ROOT/external/tau-testnet/server.py" ]]; then
  echo "error: missing external/tau-testnet/server.py" >&2
  echo "hint: clone Tau Testnet into external/tau-testnet before enabling the local-node profile" >&2
  exit 2
fi

PYTHON="${PYTHON:-python3}"
VENV_DIR="${TAU_NODE_VENV_DIR:-/opt/zenodex-tau-venv}"

if [[ ! -d "$VENV_DIR" ]]; then
  "$PYTHON" -m venv "$VENV_DIR"
fi

# shellcheck disable=SC1090
source "$VENV_DIR/bin/activate"

python -m pip install --require-hashes -r "$ROOT/requirements-dev.lock.txt"
python -m pip install -r "$ROOT/external/tau-testnet/requirements.txt"

ARGS=(
  tools/tau_testnet_local_e2e.py
  --no-smoke
  --reuse-db
  --host 0.0.0.0
  --port "${TAU_PORT:-65432}"
  --chain-id "${TAU_DEX_CHAIN_ID:-tau-local}"
)

if [[ "${TAU_FORCE_TEST:-1}" == "1" ]]; then
  ARGS+=(--force-test)
fi

if [[ "${TAU_ENABLE_FAUCET:-0}" == "1" ]]; then
  ARGS+=(--enable-faucet)
fi

exec python "${ARGS[@]}"

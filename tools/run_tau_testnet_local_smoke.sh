#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$ROOT"

if [[ ! -f "$ROOT/requirements.txt" ]]; then
  echo "error: run from repo checkout (missing requirements.txt)" >&2
  exit 2
fi

if [[ ! -f "$ROOT/external/tau-testnet/server.py" ]]; then
  echo "error: missing external/tau-testnet/server.py" >&2
  echo "hint: ensure Tau Testnet is cloned at external/tau-testnet" >&2
  exit 2
fi

if command -v git >/dev/null 2>&1 && git -C "$ROOT/external/tau-testnet" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  tau_testnet_head="$(git -C "$ROOT/external/tau-testnet" rev-parse --short HEAD 2>/dev/null || true)"
  tau_testnet_status="$(git -C "$ROOT/external/tau-testnet" status --porcelain=v1 2>/dev/null || true)"
  echo "[tau-testnet] HEAD=${tau_testnet_head:-unknown}"
  if [[ -n "$tau_testnet_status" ]]; then
    echo "[tau-testnet] local changes detected (OK for local dev)"
  fi

  if [[ "${TAU_TESTNET_UPDATE:-0}" == "1" ]]; then
    stashed="0"
    if [[ -n "$tau_testnet_status" ]]; then
      if [[ "${TAU_TESTNET_STASH:-0}" != "1" ]]; then
        echo "[tau-testnet] refusing to auto-update (working tree not clean)."
        echo "[tau-testnet] re-run with TAU_TESTNET_STASH=1 to auto-stash local changes."
        exit 2
      fi
      echo "[tau-testnet] stashing local changes (including untracked)..."
      git -C "$ROOT/external/tau-testnet" stash push -u -m "zenodex: local app-bridge patch"
      stashed="1"
    fi
    echo "[tau-testnet] updating (git pull --ff-only)..."
    git -C "$ROOT/external/tau-testnet" pull --ff-only
    if [[ "$stashed" == "1" ]]; then
      echo "[tau-testnet] re-applying local changes (git stash pop)..."
      git -C "$ROOT/external/tau-testnet" stash pop
    fi
  fi
fi

PYTHON="${PYTHON:-python3}"
VENV_DIR="${VENV_DIR:-$ROOT/.venv}"

if [[ ! -d "$VENV_DIR" ]]; then
  echo "[venv] creating $VENV_DIR"
  "$PYTHON" -m venv "$VENV_DIR"
fi

if [[ ! -f "$VENV_DIR/bin/activate" ]]; then
  echo "error: expected venv activate at $VENV_DIR/bin/activate" >&2
  exit 2
fi

# shellcheck disable=SC1090
source "$VENV_DIR/bin/activate"

echo "[python] $(python -V)"
echo "[pip] upgrading pip/setuptools/wheel"
python -m pip install --upgrade pip setuptools wheel

echo "[deps] installing repo requirements"
python -m pip install -r "$ROOT/requirements.txt"

echo "[deps] installing tau-testnet requirements"
python -m pip install -r "$ROOT/external/tau-testnet/requirements.txt"

if [[ "${RUN_PYTEST:-1}" == "1" ]]; then
  echo "[pytest] running integration tests"
  pytest -q tests/integration/test_tau_testnet_dex_plugin.py tests/integration/test_tau_net_signing_optional.py
fi

HOST="${TAU_HOST:-127.0.0.1}"
PORT="${TAU_PORT:-65432}"
CHAIN_ID="${TAU_DEX_CHAIN_ID:-tau-local}"
DEX_PRIVKEY="${TAU_DEX_PRIVKEY:-}"

if [[ -z "${TAU_DB_PATH:-}" ]]; then
  export TAU_DB_PATH="${TMPDIR:-/tmp}/tau-testnet-dex-smoke.db"
fi
if [[ "${TAU_DB_RESET:-1}" == "1" ]]; then
  rm -f "$TAU_DB_PATH"
fi
echo "[tau-testnet] db_path=$TAU_DB_PATH"

echo "[e2e] starting local node and running smoke test"

args=(
  tools/tau_testnet_local_e2e.py
  --force-test
  --enable-faucet
  --host "$HOST"
  --port "$PORT"
  --chain-id "$CHAIN_ID"
)
if [[ -n "$DEX_PRIVKEY" ]]; then
  args+=(--privkey "$DEX_PRIVKEY")
fi
if [[ "${TAU_STATE_PROOF_DEBUG:-0}" == "1" ]]; then
  args+=(--enable-state-proof-debug)
fi
if [[ "${TAU_STATE_PROOF_RISC0:-0}" == "1" ]]; then
  export RISC0_FORCE_BUILD="${RISC0_FORCE_BUILD:-1}"
  export TAU_STATE_PROOF_SUBPROCESS_TIMEOUT_S="${TAU_STATE_PROOF_SUBPROCESS_TIMEOUT_S:-300}"
  export TAU_STATE_PROOF_MAX_STDOUT_BYTES="${TAU_STATE_PROOF_MAX_STDOUT_BYTES:-6000000}"

  echo "[risc0] building state proof CLI"
  if ! (cd "$ROOT/zk/state_proof_risc0" && cargo build --release --offline -q -p tau-state-proof-risc0-cli); then
    echo "[risc0] offline cargo build failed; retrying without --offline"
    (cd "$ROOT/zk/state_proof_risc0" && cargo build --release -q -p tau-state-proof-risc0-cli)
  fi
  risc0_bin="$ROOT/zk/state_proof_risc0/target/release/tau-state-proof-risc0-cli"
  if [[ ! -x "$risc0_bin" ]]; then
    echo "error: expected risc0 state proof binary at $risc0_bin" >&2
    exit 2
  fi

  export TAU_STATE_PROOF_GENERATE_REQUIRE=1
  export TAU_STATE_PROOF_GENERATE_CMD="$risc0_bin"
  export TAU_STATE_PROOF_VERIFY_CMD="$risc0_bin"
  export TAU_EXPECT_STATE_PROOF=1
  export TAU_STATE_PROOF_VERIFY_LOCAL=1

  args+=(--enable-state-proof-risc0)
fi

python "${args[@]}"

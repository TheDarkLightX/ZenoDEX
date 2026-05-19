#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PY="${PYTHON:-python3}"

usage() {
  cat <<'USAGE'
usage: tools/install_python_hash_locked_deps.sh [core|agents|dev]

Install Python dependencies from committed pip-compile lockfiles with
pip --require-hashes.

Profiles:
  core    production/runtime integration dependencies
  agents  agent and OpenAI SDK dependencies
  dev     full development/test dependency closure
USAGE
}

profile="${1:-dev}"
case "$profile" in
  core)
    lock_file="requirements-core.lock.txt"
    ;;
  agents)
    lock_file="requirements-agents.lock.txt"
    ;;
  dev)
    lock_file="requirements-dev.lock.txt"
    ;;
  -h|--help|help)
    usage
    exit 0
    ;;
  *)
    usage >&2
    echo "error: unknown profile '$profile'" >&2
    exit 2
    ;;
esac

exec "$PY" -m pip install --require-hashes -r "$ROOT_DIR/$lock_file"

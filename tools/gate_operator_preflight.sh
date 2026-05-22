#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ENGINE="${ENGINE:-auto}"
STRICT_DIGEST=0
SKIP_ENGINE=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --engine) ENGINE="$2"; shift 2 ;;
    --strict-digest) STRICT_DIGEST=1; shift ;;
    --skip-engine) SKIP_ENGINE=1; shift ;;
    *)
      echo "Unknown arg: $1" >&2
      exit 2
      ;;
  esac
done

cd "$ROOT"

if [[ "$ENGINE" == "auto" ]]; then
  if command -v docker >/dev/null 2>&1; then
    ENGINE=docker
  elif command -v podman >/dev/null 2>&1; then
    ENGINE=podman
  else
    ENGINE=missing
  fi
fi

echo "[operator-preflight] repo: $ROOT"
echo "[operator-preflight] docker hash-locked install"
if [[ "$STRICT_DIGEST" -eq 1 ]]; then
  python3 tools/check_docker_hashlocked_install.py --strict-digest
  python3 tools/check_docker_hashlocked_install.py --dockerfile Dockerfile.production-hashlocked --strict-digest
  python3 tools/check_docker_hashlocked_install.py --dockerfile Dockerfile.operator-tools --strict-digest
else
  python3 tools/check_docker_hashlocked_install.py
  python3 tools/check_docker_hashlocked_install.py --dockerfile Dockerfile.production-hashlocked
  python3 tools/check_docker_hashlocked_install.py --dockerfile Dockerfile.operator-tools
fi

echo "[operator-preflight] deployment profiles"
python3 tools/check_deployment_profiles.py

echo "[operator-preflight] proof profiles"
python3 tools/check_zeno_ledger_proof_profiles.py

echo "[operator-preflight] UPBA policy profiles"
python3 tools/check_upba_policy_profiles.py

echo "[operator-preflight] Python hash locks"
python3 tools/check_python_hash_locks.py

echo "[operator-preflight] container hardening"
python3 tools/check_container_hardening.py

echo "[operator-preflight] minimal ops status"
python3 tools/zeno_ops_status.py --ledger-height 0 --peer-count 1 >/dev/null

if [[ "$SKIP_ENGINE" -eq 1 ]]; then
  echo "[operator-preflight] skipping container engine presence check"
elif [[ "$ENGINE" == "missing" ]]; then
  echo "[operator-preflight] no docker or podman executable found" >&2
  exit 1
else
  echo "[operator-preflight] permissionless deployment files and engine"
  python3 tools/permissionless_operator_preflight.py --engine "$ENGINE"
fi

echo "[operator-preflight] PASS"

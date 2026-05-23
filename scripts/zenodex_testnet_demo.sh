#!/usr/bin/env bash
# Start a local-only ZenoDEX testnet demo stack.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ACTION="up"
ENGINE="auto"
UI_PORT="${UI_PORT:-3000}"
API_TOKEN="${DEMO_API_TOKEN:-zenodex-local-demo-token}"
WITH_TAU=0
DRY_RUN=0

usage() {
    cat <<'USAGE'
usage: scripts/zenodex_testnet_demo.sh [up|down|logs|status|smoke] [options]

Actions:
  up              Build and start the local UI/API demo stack.
  down            Stop the local UI/API demo stack.
  logs            Follow local UI/API demo logs.
  status          Show container status and local URLs.
  smoke           Run the containerized two-node ZenoLedger smoke test.

Options:
  --engine auto|docker|podman   Container engine. Default: auto.
  --ui-port PORT                Host UI port. Default: 3000.
  --api-token TOKEN             Local demo bearer token injected into runtime UI config.
  --with-tau                    Also start the optional local Tau node profile.
  --dry-run                     Print commands without running them.
  -h, --help                    Show this help.

This demo is local-only. It exposes the UI on 127.0.0.1 via the host port and
keeps the Python API bound to 127.0.0.1 inside the container behind nginx.
USAGE
}

if [[ $# -gt 0 && "${1}" != -* ]]; then
    ACTION="$1"
    shift
fi

while [[ $# -gt 0 ]]; do
    case "$1" in
        --engine)
            ENGINE="${2:?missing value for --engine}"
            shift 2
            ;;
        --ui-port)
            UI_PORT="${2:?missing value for --ui-port}"
            shift 2
            ;;
        --api-token)
            API_TOKEN="${2:?missing value for --api-token}"
            shift 2
            ;;
        --with-tau)
            WITH_TAU=1
            shift
            ;;
        --dry-run)
            DRY_RUN=1
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "unknown argument: $1" >&2
            usage >&2
            exit 2
            ;;
    esac
done

if [[ ! "$UI_PORT" =~ ^[0-9]+$ ]] || (( UI_PORT < 1 || UI_PORT > 65535 )); then
    echo "invalid --ui-port: $UI_PORT" >&2
    exit 2
fi

resolve_engine() {
    if [[ "$ENGINE" == "auto" ]]; then
        if command -v docker >/dev/null 2>&1; then
            ENGINE="docker"
        elif command -v podman >/dev/null 2>&1; then
            ENGINE="podman"
        elif [[ "$DRY_RUN" == "1" ]]; then
            ENGINE="docker"
        else
            echo "container engine not found: install Docker or Podman" >&2
            exit 1
        fi
    elif [[ "$DRY_RUN" != "1" ]] && ! command -v "$ENGINE" >/dev/null 2>&1; then
        echo "container engine not found: $ENGINE" >&2
        exit 1
    fi
}

run_cmd() {
    if [[ "$DRY_RUN" == "1" ]]; then
        printf '+'
        printf ' %q' "$@"
        printf '\n'
        return 0
    fi
    "$@"
}

compose() {
    if [[ "$DRY_RUN" == "1" ]]; then
        run_cmd env UI_PORT="$UI_PORT" DEMO_API_TOKEN="<redacted>" "$ENGINE" compose "$@"
        return 0
    fi
    env UI_PORT="$UI_PORT" DEMO_API_TOKEN="$API_TOKEN" "$ENGINE" compose "$@"
}

cd "$ROOT"
resolve_engine

case "$ACTION" in
    up)
        demo_args=(-f docker-compose.yml -f docker-compose.testnet-demo.yml)
        compose "${demo_args[@]}" up -d --build zenodex
        if [[ "$WITH_TAU" == "1" ]]; then
            tau_args=(-f docker-compose.yml -f docker-compose.permissionless.yml --profile local-node)
            compose "${tau_args[@]}" up -d tau-local
        fi
        cat <<EOF
ZenoDEX local testnet demo is starting.

UI:       http://127.0.0.1:${UI_PORT}
API:      proxied through the UI at /api/*
Token:    injected into the local runtime UI config
Stop:     scripts/zenodex_testnet_demo.sh down --ui-port ${UI_PORT}
Node test: scripts/zenodex_testnet_demo.sh smoke
EOF
        ;;
    down)
        demo_args=(-f docker-compose.yml -f docker-compose.testnet-demo.yml)
        compose "${demo_args[@]}" down
        if [[ "$WITH_TAU" == "1" ]]; then
            tau_args=(-f docker-compose.yml -f docker-compose.permissionless.yml --profile local-node)
            compose "${tau_args[@]}" down
        fi
        ;;
    logs)
        demo_args=(-f docker-compose.yml -f docker-compose.testnet-demo.yml)
        compose "${demo_args[@]}" logs -f zenodex
        ;;
    status)
        demo_args=(-f docker-compose.yml -f docker-compose.testnet-demo.yml)
        compose "${demo_args[@]}" ps
        echo "UI: http://127.0.0.1:${UI_PORT}"
        ;;
    smoke)
        run_cmd python3 tools/zenoctl.py testnet up --profile docker-two-node --engine "$ENGINE"
        ;;
    *)
        echo "unknown action: $ACTION" >&2
        usage >&2
        exit 2
        ;;
esac

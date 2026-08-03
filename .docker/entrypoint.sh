#!/bin/bash
# ZenoDEX entrypoint.
# Starts nginx + the minimal Python API with local-first defaults.

set -euo pipefail

# Optional remote RPC. Core hosting should not depend on a managed provider.
TAU_NET_RPC="${TAU_NET_RPC:-}"
if [[ -n "$TAU_NET_RPC" ]] && [[ ! "$TAU_NET_RPC" =~ ^https?:// ]]; then
    echo "ERROR: TAU_NET_RPC must be a valid URL when set (got: $TAU_NET_RPC)" >&2
    exit 1
fi

if [[ -n "$TAU_NET_RPC" ]]; then
    echo "Using explicit Tau RPC: $TAU_NET_RPC"
else
    echo "TAU_NET_RPC is unset. Running in local-first mode; configure a local Tau node or set an explicit remote RPC if needed."
fi

if [[ "${ZENODEX_TESTNET_DEMO:-0}" == "1" ]]; then
    export ZENODEX_ENV="${ZENODEX_ENV:-local}"
    export ALLOW_DEMO_TOKEN_AUTH="${ALLOW_DEMO_TOKEN_AUTH:-1}"
    if [[ -z "${DEMO_API_TOKEN+x}" || -z "$DEMO_API_TOKEN" ]]; then
        echo "ERROR: DEMO_API_TOKEN must be supplied through the testnet secret environment" >&2
        exit 1
    fi
    export DEX_API_ENABLED="${DEX_API_ENABLED:-true}"
    export PERPS_API_ENABLED="${PERPS_API_ENABLED:-true}"
    export ZUSD_API_ENABLED="${ZUSD_API_ENABLED:-true}"
    export CONFIDENTIAL_ATTESTATION_API_ENABLED="${CONFIDENTIAL_ATTESTATION_API_ENABLED:-true}"
    export RATE_LIMIT_RPM="${RATE_LIMIT_RPM:-1200}"
    echo "ZenoDEX local testnet demo mode enabled. UI/API are intended for localhost testing only."
fi

# Nginx temp dirs (required when using read-only rootfs + tmpfs)
mkdir -p /tmp/nginx/client_body /tmp/nginx/proxy /tmp/nginx/fastcgi /tmp/nginx/uwsgi /tmp/nginx/scgi

if [[ -f /var/www/zenodex/zenodex-config.json ]]; then
    cp /var/www/zenodex/zenodex-config.json /tmp/zenodex-config.json
fi

if [[ "${ZENODEX_TESTNET_DEMO:-0}" == "1" ]]; then
    python - <<'PY'
import json
import os
from pathlib import Path

path = Path("/tmp/zenodex-config.json")
config = {
    "apiBase": "",
    "apiToken": os.environ.get("DEMO_API_TOKEN", ""),
    "demoMode": False,
    "perpsPreviewWrites": True,
    "zenoOracleApiBase": os.environ.get("VITE_ZENO_ORACLE_API_URL", ""),
}
path.write_text(json.dumps(config, indent=2, sort_keys=True) + "\n", encoding="utf-8")
PY
fi

# Start Python API server (internal)
python -m src.integration.api_server &
API_PID=$!

# Start nginx in background (serves UI, proxies /api/ to 127.0.0.1:8000)
nginx -g "daemon off;" &
NGINX_PID=$!

# Trap signals for graceful shutdown
trap "echo 'Shutting down...'; kill $NGINX_PID $API_PID 2>/dev/null; exit 0" SIGTERM SIGINT

echo "ZenoDEX started"
echo "UI:  http://localhost:8080"
echo "API: http://localhost:8000 (internal)"

# Wait for any process to exit
wait -n

# Exit with the status of the first process that exits
exit $?

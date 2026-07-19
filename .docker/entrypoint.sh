#!/bin/bash
# ZenoDEX entrypoint.
# Starts nginx + the minimal Python API with production-safe defaults.

set -euo pipefail

ZENODEX_ENV="${ZENODEX_ENV:-production}"
if [[ "$ZENODEX_ENV" != "production" ]]; then
    echo "ERROR: the production image requires ZENODEX_ENV=production" >&2
    exit 1
fi
if [[ -z "${TAU_DEX_CHAIN_ID:-}" ]]; then
    echo "ERROR: TAU_DEX_CHAIN_ID is required in production" >&2
    exit 1
fi
if ! python /validate_production_ui_config.py \
    /var/www/zenodex/zenodex-config.json \
    --expected-chain-id "$TAU_DEX_CHAIN_ID"; then
    echo "ERROR: production UI config failed the release capability contract" >&2
    exit 1
fi

# Optional remote RPC. Core hosting should not depend on a managed provider.
TAU_NET_RPC="${TAU_NET_RPC:-}"
if [[ -n "$TAU_NET_RPC" ]] && [[ ! "$TAU_NET_RPC" =~ ^https?:// ]]; then
    echo "ERROR: TAU_NET_RPC must be a valid URL when set (got: $TAU_NET_RPC)" >&2
    exit 1
fi

if [[ -n "$TAU_NET_RPC" ]]; then
    echo "Using explicit Tau RPC: $TAU_NET_RPC"
else
    echo "TAU_NET_RPC is unset. Configure an in-network Tau node or set an explicit remote RPC if needed."
fi

# Nginx temp dirs (required when using read-only rootfs + tmpfs)
mkdir -p /tmp/nginx/client_body /tmp/nginx/proxy /tmp/nginx/fastcgi /tmp/nginx/uwsgi /tmp/nginx/scgi

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

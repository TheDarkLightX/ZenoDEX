#!/bin/bash
# ZenoDEX Entrypoint Script
# Validates configuration and starts services (nginx + minimal python API)

set -euo pipefail

# =============================================================================
# Configuration Validation (Poka-yoke)
# =============================================================================

echo "🔍 Validating configuration..."

# Check required environment variables
if [ -z "$TAU_NET_RPC" ]; then
    echo "⚠️  TAU_NET_RPC not set, using default: https://alpha-rpc.tau.net"
    export TAU_NET_RPC="https://alpha-rpc.tau.net"
fi

# Validate RPC URL format
if [[ ! "$TAU_NET_RPC" =~ ^https?:// ]]; then
    echo "❌ ERROR: TAU_NET_RPC must be a valid URL (got: $TAU_NET_RPC)"
    exit 1
fi

# Warn if using testnet (safe default)
if [[ "$TAU_NET_RPC" == *"alpha"* ]]; then
    echo "ℹ️  Using Tau Net Alpha (testnet) - safe for testing"
fi

echo "✅ Configuration valid"

# =============================================================================
# Start Services
# =============================================================================

echo "🚀 Starting ZenoDEX..."

# Nginx temp dirs (required when using read-only rootfs + tmpfs)
mkdir -p /tmp/nginx/client_body /tmp/nginx/proxy /tmp/nginx/fastcgi /tmp/nginx/uwsgi /tmp/nginx/scgi

# Start Python API server (internal)
python -m src.integration.api_server &
API_PID=$!

# Start nginx in background (serves UI, proxies /api/ to 127.0.0.1:8000)
nginx -g "daemon off;" &
NGINX_PID=$!

# Trap signals for graceful shutdown
trap "echo '👋 Shutting down...'; kill $NGINX_PID $API_PID 2>/dev/null; exit 0" SIGTERM SIGINT

echo "✅ ZenoDEX started successfully!"
echo "   📊 UI:  http://localhost:8080"
echo "   🔌 API: http://localhost:8000 (internal)"

# Wait for any process to exit
wait -n

# Exit with the status of the first process that exits
exit $?

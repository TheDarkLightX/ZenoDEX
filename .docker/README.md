# ZenoDEX Docker Deployment

## Quick Start (Plug-and-Play)

```bash
# One-command startup
docker compose up -d

# View logs
docker compose logs -f

# Stop
docker compose down
```

The UI will be available at **http://localhost:3000** (nginx listens on **8080 inside the container**).

## Configuration

1. Copy the example environment file:
   ```bash
   cp .env.example .env
   ```

2. Edit `.env` to customize:
   - `TAU_NET_RPC` - Tau Network RPC endpoint (defaults to testnet)
   - `UI_PORT` - UI port (default: 3000)
   - `API_PORT` - API port (default: 8000)
   - `CORS_ORIGINS` - comma-separated allowed origins (default: empty/deny)

## Poka-yoke Safety Features

- **Safe Defaults**: Configuration defaults to Tau Net Alpha (testnet)
- **Startup Validation**: Entrypoint validates all config before starting
- **Health Checks**: Automatic container health monitoring
- **Graceful Shutdown**: Proper signal handling for clean exits

## Development Mode

For hot-reload development:

```bash
# Uncomment the dev service in docker-compose.yml, then:
docker compose up zenodex-ui-dev
```

## Production Deployment

1. Set production environment:
   ```bash
   TAU_NET_RPC=https://mainnet-rpc.tau.net
   CORS_ORIGINS=https://yourdomain.com
   LOG_LEVEL=warning
   ```

2. Add a reverse proxy (nginx/traefik) with TLS termination

3. Enable metrics for monitoring:
   ```bash
   METRICS_ENABLED=true
   ```

## Architecture

```
┌─────────────────────────────────────────┐
│              Docker Container           │
│  ┌─────────┐         ┌────────────────┐ │
│  │  nginx  │────────▶│ Python API     │ │
│  │  :8080  │  /api/* │ :8000 (local)  │ │
│  └────┬────┘         └────────────────┘ │
│       │                                 │
│  React UI                               │
│  (static)                               │
└─────────────────────────────────────────┘
```

# ZenoDEX - Multi-stage Dockerfile
# Provides plug-and-play deployment for the DEX UI and Python integration layer

# =============================================================================
# Stage 1: Build React UI
# =============================================================================
FROM node:20.19.2-alpine3.21@sha256:be56e91681a8ec1bba91e3006039bd228dc797fd984794a3efedab325b36e679 AS ui-builder

WORKDIR /app

# Copy the local UI dependency before npm resolves the monorepo-relative
# file: reference. Only its publishable runtime surface enters this stage.
COPY packages/zeno-proof-client/package.json ./packages/zeno-proof-client/package.json
COPY packages/zeno-proof-client/src/ ./packages/zeno-proof-client/src/

# Copy package files first for better caching.
COPY tools/dex-ui/package*.json ./tools/dex-ui/
WORKDIR /app/tools/dex-ui

# Install dependencies
RUN npm ci --silent

# Copy source and build
COPY tools/dex-ui/ ./
RUN npm run test:contract && npm run build

# =============================================================================
# Stage 2: Python Integration Layer
# =============================================================================
FROM python:3.11-slim-bookworm@sha256:a2c44ea455da75ce149a1aacb0e48d859277be1e206cfafaba58ef81374d1af1 AS python-base

WORKDIR /app

# Copy Python runtime requirements
COPY requirements-core.lock.txt ./
# Install app deps only from the hash-locked runtime lockfile.
RUN python -m pip install --no-cache-dir --require-hashes -r requirements-core.lock.txt

# Copy source code
COPY src/ ./src/

# Curate the runtime tree in a throw-away build stage. Deleting these files
# after copying them into the final stage would leave their bytes recoverable
# from a lower OCI image layer.
RUN rm -rf ./src/nonproduction
RUN rm -f \
    ./src/integration/autotrader_live.py \
    ./src/integration/autotrader_live_api.py \
    ./src/integration/confidential_attestation_api.py \
    ./src/integration/tau_net_client.py \
    ./src/integration/tau_testnet_dex_plugin.py \
    ./src/integration/zeno_ledger_tokenomics.py \
    ./src/integration/zenodex_local_signer.py
COPY .docker/check_production_python_artifact.py /tmp/check_production_python_artifact.py
RUN python /tmp/check_production_python_artifact.py /app/src

# =============================================================================
# Stage 3: Production Image
# =============================================================================
FROM python:3.11-slim-bookworm@sha256:a2c44ea455da75ce149a1aacb0e48d859277be1e206cfafaba58ef81374d1af1 AS production

# Labels for container metadata
LABEL org.opencontainers.image.title="ZenoDEX"
LABEL org.opencontainers.image.description="Deterministic decentralized exchange"
LABEL org.opencontainers.image.vendor="ZenoDEX"

# Install nginx (no curl dependency; healthcheck uses Python stdlib).
# Add retries to reduce flakiness in constrained build environments.
RUN apt-get update -o Acquire::Retries=3 \
    && apt-get install -y --no-install-recommends nginx \
    && rm -rf /var/lib/apt/lists/* \
    && rm -f /etc/nginx/sites-enabled/default

# Create non-root user for security (fixed UID/GID so compose tmpfs can match).
ARG ZENODEX_UID=10001
ARG ZENODEX_GID=10001
RUN groupadd -g "${ZENODEX_GID}" -r zenodex \
    && useradd -u "${ZENODEX_UID}" -g zenodex -r -m -d /home/zenodex -s /usr/sbin/nologin zenodex

WORKDIR /app

# Copy Python dependencies and code from python-base
COPY --from=python-base /usr/local/lib/python3.11/site-packages /usr/local/lib/python3.11/site-packages
COPY --from=python-base /app/src ./src

# Production images should not ship build tooling.
# This also removes setuptools' vendored dependencies (including jaraco.context 5.3.0),
# reducing attack surface and vulnerability scanner noise.
RUN python -m pip uninstall -y setuptools wheel || true

# Copy built UI from ui-builder
COPY --from=ui-builder /app/tools/dex-ui/dist /var/www/zenodex

# Copy nginx configuration
COPY .docker/nginx-main.conf /etc/nginx/nginx.conf
COPY .docker/nginx.conf /etc/nginx/conf.d/zenodex.conf

# Copy startup script
COPY .docker/entrypoint.sh /entrypoint.sh
COPY .docker/validate_production_ui_config.py /validate_production_ui_config.py
RUN chmod +x /entrypoint.sh /validate_production_ui_config.py

# Expose ports (unprivileged nginx port; API is internal by default)
EXPOSE 8080 8000

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD python -c "import urllib.request; urllib.request.urlopen('http://127.0.0.1:8080/health', timeout=2).read()" || exit 1

# Set environment defaults (runtime can override via docker-compose env)
ENV PYTHONUNBUFFERED=1
ENV ZENODEX_ENV=production
ENV TAU_NET_RPC=""
ENV LOG_LEVEL="info"
ENV API_HOST="127.0.0.1"
ENV API_PORT="8000"

# Ensure nginx/UI dirs exist and are writable by non-root user (read-only rootfs friendly when tmpfs-mounted)
RUN mkdir -p /tmp/nginx /var/www/zenodex \
    && chown -R zenodex:zenodex /tmp/nginx /var/www/zenodex

USER zenodex

# Entrypoint
ENTRYPOINT ["/entrypoint.sh"]

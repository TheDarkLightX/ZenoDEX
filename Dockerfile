# ZenoDEX - Multi-stage Dockerfile
# Provides plug-and-play deployment for the DEX UI and Python integration layer

# =============================================================================
# Stage 1: Build React UI
# =============================================================================
FROM node:20.19.2-alpine3.21 AS ui-builder

WORKDIR /app/ui

# Copy package files first for better caching
COPY tools/dex-ui/package*.json ./

# Install dependencies
RUN npm ci --silent

# Copy source and build
COPY tools/dex-ui/ ./
RUN npm run build

# =============================================================================
# Stage 2: Python Integration Layer
# =============================================================================
FROM python:3.11-slim-bookworm AS python-base

WORKDIR /app

# Copy Python requirements
COPY requirements.txt ./
# Install app deps, then force-upgrade a small set of packages with known fixes
# that can appear in base images/tooling stacks (defense-in-depth).
RUN python -m pip install --no-cache-dir --upgrade "pip>=25.3" setuptools wheel \
    && python -m pip install --no-cache-dir -r requirements.txt \
    && python -m pip install --no-cache-dir "jaraco.context>=6.1.0"

# Copy source code
COPY src/ ./src/
COPY tests/ ./tests/

# =============================================================================
# Stage 3: Production Image
# =============================================================================
FROM python:3.11-slim-bookworm AS production

# Labels for container metadata
LABEL org.opencontainers.image.title="ZenoDEX"
LABEL org.opencontainers.image.description="Formally Verified Decentralized Exchange"
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
COPY --from=ui-builder /app/ui/dist /var/www/zenodex

# Copy nginx configuration
COPY .docker/nginx-main.conf /etc/nginx/nginx.conf
COPY .docker/nginx.conf /etc/nginx/conf.d/zenodex.conf

# Copy startup script
COPY .docker/entrypoint.sh /entrypoint.sh
RUN chmod +x /entrypoint.sh

# Expose ports (unprivileged nginx port; API is internal by default)
EXPOSE 8080 8000

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD python -c "import urllib.request; urllib.request.urlopen('http://127.0.0.1:8080/health', timeout=2).read()" || exit 1

# Set environment defaults (runtime can override via docker-compose env)
ENV PYTHONUNBUFFERED=1
ENV TAU_NET_RPC="https://alpha-rpc.tau.net"
ENV LOG_LEVEL="info"
ENV API_HOST="127.0.0.1"
ENV API_PORT="8000"

# Ensure nginx/UI dirs exist and are writable by non-root user (read-only rootfs friendly when tmpfs-mounted)
RUN mkdir -p /tmp/nginx /var/www/zenodex \
    && chown -R zenodex:zenodex /tmp/nginx /var/www/zenodex

USER zenodex

# Entrypoint
ENTRYPOINT ["/entrypoint.sh"]

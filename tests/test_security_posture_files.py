from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_nginx_config_hardens_api_body_limit_and_static_headers() -> None:
    text = (ROOT / ".docker/nginx.conf").read_text(encoding="utf-8")

    assert "client_max_body_size 512k;" in text
    assert "proxy_pass http://127.0.0.1:8000/;" in text
    assert "proxy_read_timeout 60s;" in text
    static_block = text.split("location ~* \\.(js|css|png|jpg|jpeg|gif|ico|svg|woff|woff2)$ {", 1)[1]
    for header in (
        'add_header X-Frame-Options "DENY" always;',
        'add_header X-Content-Type-Options "nosniff" always;',
        'add_header Content-Security-Policy "default-src \'self\';',
    ):
        assert header in static_block


def test_dependency_manifests_split_runtime_from_agent_packages() -> None:
    dockerfile = (ROOT / "Dockerfile").read_text(encoding="utf-8")
    requirements = (ROOT / "requirements.txt").read_text(encoding="utf-8")

    assert "COPY requirements-core.txt ./" in dockerfile
    assert "-r requirements-core.txt" in dockerfile
    assert "-r requirements-core.txt" in requirements
    assert "-r requirements-agents.txt" in requirements


def test_compose_keeps_api_loopback_and_container_hardened_by_default() -> None:
    text = (ROOT / "docker-compose.yml").read_text(encoding="utf-8")

    assert '- "${UI_PORT:-3000}:8080"' in text
    assert ":8000" not in text.split("ports:", 1)[1].split("environment:", 1)[0]
    assert "- API_HOST=${API_HOST:-127.0.0.1}" in text
    assert "- RATE_LIMIT_RPM=${RATE_LIMIT_RPM:-600}" in text
    assert "DEX_API_ENABLED=true" not in text
    assert "PERPS_API_ENABLED=true" not in text
    assert "ZUSD_API_ENABLED=true" not in text
    assert "no-new-privileges:true" in text
    assert "read_only: true" in text
    assert "- /tmp:mode=1777" in text


def test_entrypoint_preserves_internal_api_and_validates_remote_tau_rpc() -> None:
    text = (ROOT / ".docker" / "entrypoint.sh").read_text(encoding="utf-8")

    assert '[[ ! "$TAU_NET_RPC" =~ ^https?:// ]]' in text
    assert "python -m src.integration.api_server &" in text
    assert 'echo "API: http://localhost:8000 (internal)"' in text

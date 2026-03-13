from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_nginx_config_hardens_api_body_limit_and_static_headers() -> None:
    text = (ROOT / ".docker/nginx.conf").read_text(encoding="utf-8")

    assert "client_max_body_size 512k;" in text
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

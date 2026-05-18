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

    assert "COPY requirements-core.lock.txt ./" in dockerfile
    assert "--require-hashes -r requirements-core.lock.txt" in dockerfile
    assert "requirements-agents" not in dockerfile
    assert "-r requirements-core.txt" in requirements
    assert "-r requirements-agents.txt" in requirements


def test_release_gate_runs_risc0_real_proof_archive_checker() -> None:
    release_gate = (ROOT / "tools/run_release_gate.sh").read_text(encoding="utf-8")

    assert "tools/zeno_ledger_risc0_proof_metadata.py" in release_gate
    assert "tools/zeno_ledger_risc0_real_proof_smoke.py" in release_gate
    assert "tools/check_zeno_ledger_risc0_real_proof_smoke_report.py" in release_gate
    assert "tests/integration/test_zeno_ledger_risc0_proof_metadata.py" in release_gate
    assert "tests/test_check_zeno_ledger_risc0_real_proof_smoke_report.py" in release_gate

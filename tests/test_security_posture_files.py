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


def test_release_gate_runs_risc0_real_proof_archive_checker() -> None:
    release_gate = (ROOT / "tools/run_release_gate.sh").read_text(encoding="utf-8")

    assert "tools/zeno_ledger_risc0_proof_metadata.py" in release_gate
    assert "tools/zeno_ledger_risc0_real_proof_smoke.py" in release_gate
    assert "tools/check_zeno_ledger_risc0_real_proof_smoke_report.py" in release_gate
    assert "tools/check_zeno_ledger_proof_coverage_matrix.py" in release_gate
    assert "tests/integration/test_zeno_ledger_risc0_proof_metadata.py" in release_gate
    assert "tests/test_check_zeno_ledger_risc0_real_proof_smoke_report.py" in release_gate
    assert "tests/test_check_zeno_ledger_proof_coverage_matrix.py" in release_gate


def test_release_gate_runs_zeno_ledger_validator_schedule_peer_check() -> None:
    release_gate = (ROOT / "tools/run_release_gate.sh").read_text(encoding="utf-8")

    assert "src/integration/zeno_ledger_live_quorum_v0.py" in release_gate
    assert "src/integration/zeno_ledger_block_gossip_v0.py" in release_gate
    assert "src/integration/zeno_ledger_bonded_slashing_v0.py" in release_gate
    assert "src/integration/zeno_ledger_dynamic_peers_v0.py" in release_gate
    assert "src/integration/zeno_ledger_peer_discovery_v0.py" in release_gate
    assert "src/integration/zeno_ledger_validator_schedule_v0.py" in release_gate
    assert "tools/check_zeno_ledger_block_gossip.py" in release_gate
    assert "tools/check_zeno_ledger_bonded_slashing.py" in release_gate
    assert "tools/check_zeno_ledger_dynamic_peers.py" in release_gate
    assert "tools/check_zeno_ledger_peer_discovery.py" in release_gate
    assert "tools/zeno_ledger_machine_b_acceptance.py" in release_gate
    assert "tools/zeno_ledger_node.py" in release_gate
    assert "tests/integration/test_zeno_ledger_block_gossip_v0.py" in release_gate
    assert "tests/integration/test_zeno_ledger_bonded_slashing_v0.py" in release_gate
    assert "tests/integration/test_zeno_ledger_dynamic_peer_exchange_v0.py" in release_gate
    assert "tests/integration/test_zeno_ledger_live_quorum_v0.py" in release_gate
    assert "tests/integration/test_zeno_ledger_node_transport_auth.py" in release_gate
    assert "tests/integration/test_zeno_ledger_peer_discovery_v0.py" in release_gate
    assert "tests/integration/test_zeno_ledger_public_network_config_quorum.py" in release_gate
    assert "tests/integration/test_zeno_ledger_validator_schedule_v0.py" in release_gate
    assert "tests/integration/test_zeno_ledger_node_fork_choice.py" in release_gate


def test_release_gate_runs_production_key_management_checks() -> None:
    release_gate = (ROOT / "tools/run_release_gate.sh").read_text(encoding="utf-8")
    public_testnet_gate = (ROOT / "tools/run_public_testnet_candidate_gate.sh").read_text(encoding="utf-8")

    assert "src/integration/production_key_management_v0.py" in release_gate
    assert "tools/check_production_key_management_spec.py" in release_gate
    assert "tools/check_production_key_management_config.py" in release_gate
    assert "tests/integration/test_production_key_management_v0.py" in release_gate
    assert "tests/test_check_production_key_management_config.py" in release_gate
    assert "tools/check_production_key_management_spec.py" in public_testnet_gate

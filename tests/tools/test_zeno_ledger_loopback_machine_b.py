from __future__ import annotations

from pathlib import Path

from tools.zeno_ledger_loopback_machine_b import (
    DEFAULT_HOST_ALIAS,
    _container_script,
    _display_command,
    _docker_command,
)


def test_display_command_redacts_writer_token() -> None:
    command = ["docker", "run", "-e", "ZENO_LEDGER_WRITER_TOKEN=secret-token", "line1\nline2"]

    display = _display_command(command)

    assert "secret-token" not in display
    assert "ZENO_LEDGER_WRITER_TOKEN=<redacted>" in display
    assert "line1" not in display
    assert "<inline-script>" in display


def test_docker_command_mounts_repo_and_output_with_host_gateway(tmp_path: Path) -> None:
    command = _docker_command(
        image="python:3.12-slim",
        host_alias=DEFAULT_HOST_ALIAS,
        add_host_gateway=True,
        out_dir=tmp_path,
        container_script="echo ok",
    )

    assert command[:3] == ["docker", "run", "--rm"]
    assert "--user" in command
    assert "--add-host" in command
    assert f"{DEFAULT_HOST_ALIAS}:host-gateway" in command
    assert "python:3.12-slim" in command
    assert f"{tmp_path.resolve()}:/out" in command
    assert "ZENO_LEDGER_WRITER_TOKEN" in command
    assert all("secret-token" not in item for item in command)


def test_container_script_exposes_testnet_faucet_for_local_loopback_only() -> None:
    script = _container_script(
        config_url="http://host.docker.internal:1000/public_network_config.json",
        peer_url="http://host.docker.internal:2000",
        commit_sha="a" * 40,
    )

    assert "--enable-testnet-faucet" in script
    assert "--expose-testnet-faucet-http" in script
    assert "--write-auth-token-env ZENO_LEDGER_WRITER_TOKEN" in script
    assert 'import os' in script
    assert '"Authorization": "Bearer " + os.environ["ZENO_LEDGER_WRITER_TOKEN"]' in script
    assert '"local_fixture_mode": True' in script

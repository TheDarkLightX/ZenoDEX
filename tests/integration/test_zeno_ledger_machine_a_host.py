from pathlib import Path

import pytest

from tools.zeno_ledger_machine_a_host import (
    build_machine_a_ready_report_v0,
    build_machine_b_acceptance_command_v0,
    validate_testnet_write_binding_v0,
)


def test_machine_b_acceptance_command_binds_config_hash_and_token() -> None:
    command = build_machine_b_acceptance_command_v0(
        config_url="http://192.0.2.10:8000/public_network_config.json",
        network_config_hash="0x" + "11" * 32,
        token_symbol="tZENO",
    )

    assert command[:2] == ["python3", "tools/zeno_ledger_machine_b_acceptance.py"]
    assert command[command.index("--config-url") + 1] == "http://192.0.2.10:8000/public_network_config.json"
    assert command[command.index("--expected-network-config-hash") + 1] == "0x" + "11" * 32
    assert command[command.index("--token-symbol") + 1] == "tZENO"
    assert "--peer-auth-token-file" not in command


def test_machine_b_acceptance_command_can_include_peer_auth_token_file() -> None:
    command = build_machine_b_acceptance_command_v0(
        config_url="http://192.0.2.10:8000/public_network_config.json",
        network_config_hash="0x" + "11" * 32,
        token_symbol="tZENO",
        peer_auth_token_file="/tmp/peer.token",
    )

    assert command[command.index("--peer-auth-token-file") + 1] == "/tmp/peer.token"


def test_machine_a_ready_report_contains_join_urls_and_command() -> None:
    report = build_machine_a_ready_report_v0(
        out_dir=Path("/tmp/zeno-ledger-public-testnet"),
        data_dir=Path("/tmp/zeno-ledger-node-a"),
        public_host="192.0.2.10",
        mirror_port=8000,
        writer_port=8787,
        recommended_node_port=8788,
        poll_seconds=5,
        network_config_path=Path("/tmp/zeno-ledger-public-testnet/public_network_config.json"),
        build_report={"ok": True, "covered_feature_count": 10},
        node_report={"ok": True, "latest_height": 5},
        network_config={
            "network_id": "zeno-ledger-devnet-0",
            "chain_id": "zeno-ledger-devnet-0",
            "network_config_hash": "0x" + "22" * 32,
        },
        machine_b_token_symbol="tKIWI",
    )

    assert report["ok"] is True
    assert report["config_url"] == "http://192.0.2.10:8000/public_network_config.json"
    assert report["writer_url"] == "http://192.0.2.10:8787"
    assert report["network_config_hash"] == "0x" + "22" * 32
    assert report["build_report_ok"] is True
    assert report["node_report_ok"] is True
    assert report["testnet_writes_enabled"] is False
    assert "tx" not in report["endpoints"]
    assert "faucet" not in report["endpoints"]
    assert report["write_auth_required"] is False
    token_index = report["machine_b_acceptance_command"].index("--token-symbol")
    assert report["machine_b_acceptance_command"][token_index + 1] == "tKIWI"


def test_machine_a_ready_report_includes_auth_note_for_public_writes() -> None:
    report = build_machine_a_ready_report_v0(
        out_dir=Path("/tmp/zeno-ledger-public-testnet"),
        data_dir=Path("/tmp/zeno-ledger-node-a"),
        public_host="192.0.2.10",
        mirror_port=8000,
        writer_port=8787,
        recommended_node_port=8788,
        poll_seconds=5,
        network_config_path=Path("/tmp/zeno-ledger-public-testnet/public_network_config.json"),
        build_report={"ok": True, "covered_feature_count": 10},
        node_report={"ok": True, "latest_height": 5},
        network_config={
            "network_id": "zeno-ledger-devnet-0",
            "chain_id": "zeno-ledger-devnet-0",
            "network_config_hash": "0x" + "22" * 32,
        },
        machine_b_token_symbol="tZENO",
        enable_testnet_writes=True,
        write_auth_token_configured=True,
        machine_b_peer_auth_token_file="/tmp/peer.token",
    )

    assert report["testnet_writes_enabled"] is True
    assert report["write_auth_required"] is True
    assert "faucet" in report["endpoints"]
    assert report["machine_b_acceptance_command"][-2:] == ["--peer-auth-token-file", "/tmp/peer.token"]


def test_testnet_writes_disabled_by_default_on_public_binding() -> None:
    assert (
        validate_testnet_write_binding_v0(bind_host="0.0.0.0", enable_testnet_writes=False)
        is False
    )


def test_testnet_writes_reject_unauthenticated_public_binding_even_when_requested() -> None:
    with pytest.raises(ValueError, match="bearer-token auth"):
        validate_testnet_write_binding_v0(bind_host="0.0.0.0", enable_testnet_writes=True)


def test_testnet_writes_can_be_enabled_on_public_binding_with_auth() -> None:
    assert (
        validate_testnet_write_binding_v0(
            bind_host="0.0.0.0",
            enable_testnet_writes=True,
            write_auth_token="secret",
        )
        is True
    )


def test_testnet_writes_can_be_enabled_on_loopback_only() -> None:
    assert (
        validate_testnet_write_binding_v0(bind_host="127.0.0.1", enable_testnet_writes=True)
        is True
    )

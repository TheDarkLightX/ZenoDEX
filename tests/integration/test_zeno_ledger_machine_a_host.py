from pathlib import Path

from tools.zeno_ledger_machine_a_host import (
    build_machine_a_ready_report_v0,
    build_machine_b_acceptance_command_v0,
)


def test_machine_b_acceptance_command_binds_config_hash_and_token() -> None:
    command = build_machine_b_acceptance_command_v0(
        config_url="http://192.0.2.10:8000/public_network_config.json",
        network_config_hash="0x" + "11" * 32,
        token_symbol="tMANGO",
    )

    assert command[:2] == ["python3", "tools/zeno_ledger_machine_b_acceptance.py"]
    assert command[command.index("--config-url") + 1] == "http://192.0.2.10:8000/public_network_config.json"
    assert command[command.index("--expected-network-config-hash") + 1] == "0x" + "11" * 32
    assert command[command.index("--token-symbol") + 1] == "tMANGO"


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
    assert report["machine_b_acceptance_command"][report["machine_b_acceptance_command"].index("--token-symbol") + 1] == "tKIWI"

from __future__ import annotations

from tools.zeno_ledger_machine_b_acceptance import (
    MACHINE_B_LATEST_MAIN_SUMMARY_SCHEMA,
    _read_transport_auth_token_file_v0,
    build_machine_b_latest_main_summary_v0,
)


def test_machine_b_latest_main_summary_binds_evidence_fields() -> None:
    report = build_machine_b_latest_main_summary_v0(
        config_url="http://192.0.2.10:8000/public_network_config.json",
        expected_network_config_hash="0x" + "11" * 32,
        commit_sha="0" * 40,
        node_id="operator-b",
        token_symbol="tMANGO",
        token_report={"ok": True},
        doctor_report={
            "ok": True,
            "remote_network": {
                "network_config_hash": "0x" + "11" * 32,
                "feature_suite_hash": "0x" + "22" * 32,
            },
        },
        join_report={"ok": True, "network_config_hash": "0x" + "11" * 32},
        follow_report={"ok": True},
        evidence_report={
            "ok": True,
            "network_id": "zeno-ledger-devnet-0",
            "chain_id": "zeno-ledger-devnet-0",
            "feature_suite_hash": "0x" + "22" * 32,
        },
        verification_report={
            "ok": True,
            "network_id": "zeno-ledger-devnet-0",
            "chain_id": "zeno-ledger-devnet-0",
            "local_tip": {
                "height": 13,
                "header_hash": "0x" + "33" * 32,
                "app_hash": "0x" + "44" * 32,
            },
            "same_height_peer": {
                "common_header_hash": "0x" + "33" * 32,
                "peer_tip": {
                    "height": 13,
                    "header_hash": "0x" + "33" * 32,
                    "app_hash": "0x" + "44" * 32,
                },
            },
        },
    )

    assert report["schema"] == MACHINE_B_LATEST_MAIN_SUMMARY_SCHEMA
    assert report["ok"] is True
    assert report["commit_sha"] == "0" * 40
    assert report["network_config_hash"] == "0x" + "11" * 32
    assert report["feature_suite_hash"] == "0x" + "22" * 32
    assert report["machine_b_tip"]["height"] == 13
    assert report["machine_a_tip"]["height"] == 13
    assert report["common_header_hash"] == "0x" + "33" * 32
    assert report["created_token_symbol"] == "tMANGO"
    assert report["accepted_submission_count"] == 1
    assert report["rejected_submission_count"] == 0


def test_machine_b_latest_main_summary_reports_rejected_submission() -> None:
    report = build_machine_b_latest_main_summary_v0(
        config_url="http://192.0.2.10:8000/public_network_config.json",
        expected_network_config_hash="0x" + "11" * 32,
        commit_sha="0" * 40,
        node_id="operator-b",
        token_symbol="tMANGO",
        token_report={"ok": False},
        doctor_report={"ok": True},
        join_report={"ok": True},
        follow_report={"ok": True},
        evidence_report={"ok": True},
        verification_report={"ok": True},
    )

    assert report["ok"] is False
    assert report["accepted_submission_count"] == 0
    assert report["rejected_submission_count"] == 1


def test_machine_b_peer_auth_token_file_trims_newline(tmp_path) -> None:
    token_path = tmp_path / "peer.token"
    token_path.write_text("secret-token\n", encoding="utf-8")

    assert _read_transport_auth_token_file_v0(token_path) == "secret-token"


def test_machine_b_peer_auth_token_file_rejects_empty_file(tmp_path) -> None:
    token_path = tmp_path / "peer.token"
    token_path.write_text("\n", encoding="utf-8")

    try:
        _read_transport_auth_token_file_v0(token_path)
    except ValueError as exc:
        assert "empty" in str(exc)
    else:
        raise AssertionError("empty peer auth token file was accepted")

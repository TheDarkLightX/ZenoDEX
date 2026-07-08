from __future__ import annotations

import pytest

from src.integration.zeno_ledger_rejections_v0 import (
    BAD_AUTH,
    BAD_JSON,
    DYNAMIC_PEER_CAP_EXCEEDED,
    GOSSIP_ALREADY_SEEN,
    GOSSIP_PREV_HASH_MISMATCH,
    GOSSIP_REPLAY_HEADER_MISMATCH,
    GOSSIP_TX_CAP_EXCEEDED,
    HTTP_POST_TOO_LARGE,
    KNOWN_REJECTION_CODES,
    LIVE_CHECKPOINT_QUORUM_MISSING,
    PEER_CHAIN_MISMATCH,
    PEER_FORK_CHOICE_REJECTED,
    PEER_NETWORK_MISMATCH,
    PUBLIC_CONFIG_QUORUM_MISSING,
    REMOTE_ARTIFACT_TOO_LARGE,
    build_rejection_report_v0,
    validate_rejection_report_v0,
)


def test_all_known_rejection_codes_validate() -> None:
    for code in sorted(KNOWN_REJECTION_CODES):
        report = build_rejection_report_v0(code, "rejected for test", path="/test")
        validate_rejection_report_v0(report)
        assert report["ok"] is False
        assert report["status"] == "rejected"
        assert report["error_code"] == code


def test_known_code_constants_match_registry() -> None:
    assert KNOWN_REJECTION_CODES == {
        BAD_JSON,
        BAD_AUTH,
        HTTP_POST_TOO_LARGE,
        REMOTE_ARTIFACT_TOO_LARGE,
        GOSSIP_ALREADY_SEEN,
        GOSSIP_TX_CAP_EXCEEDED,
        GOSSIP_PREV_HASH_MISMATCH,
        GOSSIP_REPLAY_HEADER_MISMATCH,
        PEER_NETWORK_MISMATCH,
        PEER_CHAIN_MISMATCH,
        PEER_FORK_CHOICE_REJECTED,
        DYNAMIC_PEER_CAP_EXCEEDED,
        PUBLIC_CONFIG_QUORUM_MISSING,
        LIVE_CHECKPOINT_QUORUM_MISSING,
    }


def test_unknown_code_rejects() -> None:
    with pytest.raises(ValueError, match="unknown rejection code"):
        build_rejection_report_v0("NOT_A_REAL_CODE", "bad")


def test_report_hash_mismatch_rejects() -> None:
    report = build_rejection_report_v0(BAD_JSON, "request body must be valid JSON", path="/tx")
    report["detail"] = "tampered"
    with pytest.raises(ValueError, match="hash mismatch"):
        validate_rejection_report_v0(report)


def test_reports_are_deterministic() -> None:
    left = build_rejection_report_v0(
        HTTP_POST_TOO_LARGE,
        "request body too large",
        content_length=123,
        path="/tx",
    )
    right = build_rejection_report_v0(
        HTTP_POST_TOO_LARGE,
        "request body too large",
        path="/tx",
        content_length=123,
    )
    assert left == right


def test_representative_helper_output_shape() -> None:
    report = build_rejection_report_v0(BAD_AUTH, "unauthorized", error="unauthorized", path="/faucet")
    validate_rejection_report_v0(report)
    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["error_code"] == BAD_AUTH
    assert report["detail"] == "unauthorized"
    assert report["error"] == "unauthorized"
    assert report["path"] == "/faucet"


def test_rejection_report_rejects_bad_input_shapes() -> None:
    with pytest.raises(TypeError, match="report must be a mapping"):
        validate_rejection_report_v0([])
    with pytest.raises(ValueError, match="non-empty string"):
        build_rejection_report_v0("", "bad")
    with pytest.raises(TypeError, match="detail must be a string"):
        build_rejection_report_v0(BAD_JSON, 123)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="reserved rejection report field"):
        build_rejection_report_v0(BAD_JSON, "bad", ok=True)

    report = build_rejection_report_v0(BAD_JSON, "bad")
    for key, value, pattern in (
        ("schema", "bad", "schema mismatch"),
        ("ok", True, "ok must be false"),
        ("status", "bad", "status must be rejected"),
        ("rejection_report_hash", "", "hash must be a non-empty string"),
    ):
        tampered = dict(report)
        tampered[key] = value
        with pytest.raises(ValueError, match=pattern):
            validate_rejection_report_v0(tampered)

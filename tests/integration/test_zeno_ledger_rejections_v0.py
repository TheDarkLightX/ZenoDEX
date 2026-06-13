from __future__ import annotations

import pytest

from src.integration.zeno_ledger_rejections_v0 import (
    BAD_AUTH,
    BAD_JSON,
    REJECTION_REPORT_SCHEMA_V0,
    build_rejection_report_v0,
    validate_rejection_report_v0,
)


def test_rejection_report_is_hash_bound_and_tamper_rejected() -> None:
    report = build_rejection_report_v0(BAD_AUTH, "unauthorized", path="/submit_tx")

    assert report["schema"] == REJECTION_REPORT_SCHEMA_V0
    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["error_code"] == BAD_AUTH
    validate_rejection_report_v0(report)

    tampered = dict(report, path="/submit_faucet")
    with pytest.raises(ValueError, match="hash mismatch"):
        validate_rejection_report_v0(tampered)


def test_rejection_report_rejects_unknown_and_reserved_fields() -> None:
    with pytest.raises(ValueError, match="unknown rejection code"):
        build_rejection_report_v0("NOT_A_CODE")

    with pytest.raises(ValueError, match="reserved rejection report field"):
        build_rejection_report_v0(BAD_JSON, "bad json", ok=True)

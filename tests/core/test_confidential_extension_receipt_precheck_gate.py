from __future__ import annotations

import pytest

from src.core.confidential_extension_receipts import (
    PRECHECK_BAD_POLICY_DIGEST,
    PRECHECK_HASH_MISMATCH,
    PRECHECK_OK,
    confidential_extension_receipt_precheck_error,
    evaluate_confidential_extension_receipt_precheck_gate,
)


def _base_args() -> dict[str, int]:
    return {
        "schema_ok": 1,
        "receipt_hash_present": 1,
        "hash_matches": 1,
        "extension_id_ok": 1,
        "provider_id_ok": 1,
        "request_id_ok": 1,
        "policy_version_ok": 1,
        "policy_digest_ok": 1,
        "measurement_format_ok": 1,
        "measurement_approved": 1,
        "host_object_ok": 1,
        "attestation_object_ok": 1,
        "accounting_object_ok": 1,
        "numeric_fields_ok": 1,
        "do_execute_flag_ok": 1,
        "policy_ok_flag_ok": 1,
        "nonce_unused_flag_ok": 1,
        "output_bound_ok_flag_ok": 1,
    }


def test_confidential_extension_receipt_precheck_gate_happy_path() -> None:
    outcome = evaluate_confidential_extension_receipt_precheck_gate(**_base_args())
    assert outcome.precheck_ok is True
    assert outcome.reject_code == PRECHECK_OK
    assert confidential_extension_receipt_precheck_error(outcome) == "ok"


def test_confidential_extension_receipt_precheck_gate_hash_mismatch_precedes_bad_policy_digest() -> None:
    args = _base_args()
    args["hash_matches"] = 0
    args["policy_digest_ok"] = 0
    outcome = evaluate_confidential_extension_receipt_precheck_gate(**args)
    assert outcome.precheck_ok is False
    assert outcome.reject_code == PRECHECK_HASH_MISMATCH
    assert confidential_extension_receipt_precheck_error(outcome) == "hash_mismatch"


def test_confidential_extension_receipt_precheck_gate_bad_policy_digest_after_hash_ok() -> None:
    args = _base_args()
    args["policy_digest_ok"] = 0
    outcome = evaluate_confidential_extension_receipt_precheck_gate(**args)
    assert outcome.precheck_ok is False
    assert outcome.reject_code == PRECHECK_BAD_POLICY_DIGEST
    assert confidential_extension_receipt_precheck_error(outcome) == "bad_policy_digest"


def test_confidential_extension_receipt_precheck_gate_bad_output_bound_flag_is_last_host_flag_failure() -> None:
    args = _base_args()
    args["output_bound_ok_flag_ok"] = 0
    outcome = evaluate_confidential_extension_receipt_precheck_gate(**args)
    assert outcome.precheck_ok is False
    assert confidential_extension_receipt_precheck_error(outcome) == "bad_output_bound_ok"


def test_confidential_extension_receipt_precheck_gate_rejects_non_flag_input() -> None:
    args = _base_args()
    args["schema_ok"] = 2
    with pytest.raises(ValueError):
        evaluate_confidential_extension_receipt_precheck_gate(**args)

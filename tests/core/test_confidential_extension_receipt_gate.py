from __future__ import annotations

import pytest

from src.core.confidential_extension_receipts import evaluate_confidential_extension_receipt_gate


def _base_args() -> dict[str, int]:
    return {
        "do_execute": 1,
        "policy_ok": 1,
        "nonce_unused": 1,
        "output_bound_ok": 1,
        "current_epoch": 10,
        "attestation_epoch": 8,
        "max_attestation_age": 2,
        "fee_charged": 7,
        "receipt_fee": 7,
        "credit_before": 40,
        "credit_after": 33,
        "provider_balance_before": 9,
        "provider_balance_after": 16,
    }


def test_confidential_extension_receipt_gate_happy_path() -> None:
    outcome = evaluate_confidential_extension_receipt_gate(**_base_args())
    assert outcome.fresh_attestation_ok is True
    assert outcome.host_guards_ok is True
    assert outcome.accounting_ok is True
    assert outcome.receipt_admissible is True


def test_confidential_extension_receipt_gate_stale_attestation_blocks_admissibility() -> None:
    args = _base_args()
    args["current_epoch"] = 11
    outcome = evaluate_confidential_extension_receipt_gate(**args)
    assert outcome.fresh_attestation_ok is False
    assert outcome.host_guards_ok is True
    assert outcome.accounting_ok is True
    assert outcome.receipt_admissible is False


def test_confidential_extension_receipt_gate_execute_requires_all_host_guards() -> None:
    args = _base_args()
    args["nonce_unused"] = 0
    outcome = evaluate_confidential_extension_receipt_gate(**args)
    assert outcome.fresh_attestation_ok is True
    assert outcome.host_guards_ok is False
    assert outcome.accounting_ok is True
    assert outcome.receipt_admissible is False


def test_confidential_extension_receipt_gate_no_execute_path_allows_zero_fee_noop() -> None:
    args = _base_args()
    args.update(
        {
            "do_execute": 0,
            "policy_ok": 0,
            "nonce_unused": 0,
            "output_bound_ok": 0,
            "attestation_epoch": 10,
            "fee_charged": 0,
            "receipt_fee": 0,
            "credit_after": 40,
            "provider_balance_after": 9,
        }
    )
    outcome = evaluate_confidential_extension_receipt_gate(**args)
    assert outcome.fresh_attestation_ok is True
    assert outcome.host_guards_ok is True
    assert outcome.accounting_ok is True
    assert outcome.receipt_admissible is True


def test_confidential_extension_receipt_gate_rejects_noncanonical_flag() -> None:
    args = _base_args()
    args["policy_ok"] = 2
    with pytest.raises(ValueError):
        evaluate_confidential_extension_receipt_gate(**args)

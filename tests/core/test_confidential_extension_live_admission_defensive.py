from __future__ import annotations

import pytest

import src.core.confidential_extension_live_admission as live_admission
from src.core.confidential_extension_live_admission import (
    validate_confidential_extension_live_admission,
)
from src.core.confidential_extension_receipts import make_confidential_extension_receipt
from src.state.confidential_requests import ConfidentialRequestTable

NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
POLICY_DIGEST = "0x" + ("d" * 64)
APPROVED = {f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"}


def _receipt() -> dict[str, object]:
    return make_confidential_extension_receipt(
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-1",
        policy_version="tee-policy-v1",
        policy_digest=POLICY_DIGEST,
        measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        attestation_epoch=8,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )


def test_live_admission_bad_expected_policy_digest_rejects() -> None:
    ok, err, updated = validate_confidential_extension_live_admission(
        receipt=_receipt(),
        approved_measurements=APPROVED,
        expected_policy_digest="not-a-digest",
        request_table=ConfidentialRequestTable(),
    )

    assert ok is False
    assert err == "bad_expected_policy_digest"
    assert updated is None


def test_live_admission_policy_digest_helper_bug_propagates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def broken_policy_digest(value: object, *, name: str) -> str:
        raise RuntimeError("policy digest helper bug")

    monkeypatch.setattr(live_admission, "_canonical_policy_digest", broken_policy_digest)
    with pytest.raises(RuntimeError, match="policy digest helper bug"):
        validate_confidential_extension_live_admission(
            receipt=_receipt(),
            approved_measurements=APPROVED,
            expected_policy_digest=POLICY_DIGEST,
            request_table=ConfidentialRequestTable(),
        )

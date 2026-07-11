from __future__ import annotations

from src.core.confidential_extension_live_admission import validate_confidential_extension_live_admission
from src.core.confidential_extension_receipts import make_confidential_extension_receipt
from src.integration.confidential_attestation import (
    VerifiedConfidentialAttestation,
    make_confidential_extension_receipt_from_verified_attestation,
)
from src.state.confidential_requests import ConfidentialRequestKey, ConfidentialRequestTable


NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
POLICY_DIGEST = "0x" + ("d" * 64)
OTHER_POLICY_DIGEST = "0x" + ("e" * 64)
APPROVED = {f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"}


def _raw_receipt(*, do_execute: int = 1) -> dict:
    policy_ok = 1 if do_execute == 1 else 0
    nonce_unused = 1 if do_execute == 1 else 0
    output_bound_ok = 1 if do_execute == 1 else 0
    fee = 7 if do_execute == 1 else 0
    credit_after = 33 if do_execute == 1 else 40
    provider_after = 16 if do_execute == 1 else 9
    return make_confidential_extension_receipt(
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-1",
        policy_version="tee-policy-v1",
        policy_digest=POLICY_DIGEST,
        measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
        do_execute=do_execute,
        policy_ok=policy_ok,
        nonce_unused=nonce_unused,
        output_bound_ok=output_bound_ok,
        current_epoch=10,
        attestation_epoch=8,
        max_attestation_age=2,
        fee_charged=fee,
        receipt_fee=fee,
        credit_before=40,
        credit_after=credit_after,
        provider_balance_before=9,
        provider_balance_after=provider_after,
    )


def _receipt(*, do_execute: int = 1) -> dict:
    raw = _raw_receipt(do_execute=do_execute)
    body = raw["body"]
    return make_confidential_extension_receipt_from_verified_attestation(
        verified_attestation=VerifiedConfidentialAttestation(
            measurement=body["measurement"],
            policy_digest=body["policy_digest"],
            attestation_epoch=body["attestation"]["attestation_epoch"],
        ),
        extension_id=body["extension_id"],
        provider_id=body["provider_id"],
        request_id=body["request_id"],
        policy_version=body["policy_version"],
        do_execute=body["host"]["do_execute"],
        policy_ok=body["host"]["policy_ok"],
        nonce_unused=body["host"]["nonce_unused"],
        output_bound_ok=body["host"]["output_bound_ok"],
        current_epoch=body["attestation"]["current_epoch"],
        max_attestation_age=body["attestation"]["max_attestation_age"],
        fee_charged=body["accounting"]["fee_charged"],
        receipt_fee=body["accounting"]["receipt_fee"],
        credit_before=body["accounting"]["credit_before"],
        credit_after=body["accounting"]["credit_after"],
        provider_balance_before=body["accounting"]["provider_balance_before"],
        provider_balance_after=body["accounting"]["provider_balance_after"],
    )


def test_confidential_extension_live_admission_rejects_self_hashed_receipt_without_verified_attestation() -> None:
    ok, err, updated = validate_confidential_extension_live_admission(
        receipt=_raw_receipt(),
        approved_measurements=APPROVED,
        expected_policy_digest=POLICY_DIGEST,
        request_table=ConfidentialRequestTable(),
    )
    assert ok is False
    assert err == "receipt_not_authenticated"
    assert updated is None


def test_confidential_extension_live_admission_accepts_verified_fresh_unused_request() -> None:
    ok, err, updated = validate_confidential_extension_live_admission(
        receipt=_receipt(),
        approved_measurements=APPROVED,
        expected_policy_digest=POLICY_DIGEST,
        request_table=ConfidentialRequestTable(),
    )
    assert ok is True
    assert err is None
    assert updated is not None
    assert updated.is_used(
        ConfidentialRequestKey(
            extension_id="route-premium-v1",
            provider_id="provider-1",
            request_id="req-1",
        )
    )


def test_confidential_extension_live_admission_rejects_policy_digest_mismatch() -> None:
    ok, err, updated = validate_confidential_extension_live_admission(
        receipt=_receipt(),
        approved_measurements=APPROVED,
        expected_policy_digest=OTHER_POLICY_DIGEST,
        request_table=ConfidentialRequestTable(),
    )
    assert ok is False
    assert err == "policy_digest_mismatch"
    assert updated is None


def test_confidential_extension_live_admission_rejects_request_replay() -> None:
    request_table = ConfidentialRequestTable()
    request_table.mark_used(
        ConfidentialRequestKey(
            extension_id="route-premium-v1",
            provider_id="provider-1",
            request_id="req-1",
        )
    )
    ok, err, updated = validate_confidential_extension_live_admission(
        receipt=_receipt(),
        approved_measurements=APPROVED,
        expected_policy_digest=POLICY_DIGEST,
        request_table=request_table,
    )
    assert ok is False
    assert err == "request_replay"
    assert updated is None


def test_confidential_extension_live_admission_rejects_non_executing_receipt() -> None:
    ok, err, updated = validate_confidential_extension_live_admission(
        receipt=_receipt(do_execute=0),
        approved_measurements=APPROVED,
        expected_policy_digest=POLICY_DIGEST,
        request_table=ConfidentialRequestTable(),
    )
    assert ok is False
    assert err == "not_executed"
    assert updated is None


def test_confidential_extension_live_admission_accepts_receipt_from_verified_attestation() -> None:
    receipt = make_confidential_extension_receipt_from_verified_attestation(
        verified_attestation=VerifiedConfidentialAttestation(
            measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
            policy_digest=POLICY_DIGEST,
            attestation_epoch=8,
        ),
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-verified",
        policy_version="tee-policy-v1",
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )
    ok, err, updated = validate_confidential_extension_live_admission(
        receipt=receipt,
        approved_measurements=APPROVED,
        expected_policy_digest=POLICY_DIGEST,
        request_table=ConfidentialRequestTable(),
    )
    assert ok is True
    assert err is None
    assert updated is not None


def test_confidential_extension_live_admission_rejects_verified_attestation_policy_snapshot_mismatch() -> None:
    receipt = make_confidential_extension_receipt_from_verified_attestation(
        verified_attestation=VerifiedConfidentialAttestation(
            measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
            policy_digest=POLICY_DIGEST,
            attestation_epoch=8,
        ),
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-policy-drift",
        policy_version="tee-policy-v1",
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )
    ok, err, updated = validate_confidential_extension_live_admission(
        receipt=receipt,
        approved_measurements=APPROVED,
        expected_policy_digest=OTHER_POLICY_DIGEST,
        request_table=ConfidentialRequestTable(),
    )
    assert ok is False
    assert err == "policy_digest_mismatch"
    assert updated is None


def test_confidential_extension_live_admission_rejects_verified_attestation_request_replay() -> None:
    receipt = make_confidential_extension_receipt_from_verified_attestation(
        verified_attestation=VerifiedConfidentialAttestation(
            measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
            policy_digest=POLICY_DIGEST,
            attestation_epoch=8,
        ),
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-attested-replay",
        policy_version="tee-policy-v1",
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )
    request_table = ConfidentialRequestTable()
    request_table.mark_used(
        ConfidentialRequestKey(
            extension_id="route-premium-v1",
            provider_id="provider-1",
            request_id="req-attested-replay",
        )
    )
    ok, err, updated = validate_confidential_extension_live_admission(
        receipt=receipt,
        approved_measurements=APPROVED,
        expected_policy_digest=POLICY_DIGEST,
        request_table=request_table,
    )
    assert ok is False
    assert err == "request_replay"
    assert updated is None


def test_confidential_extension_live_admission_rejects_verified_attestation_request_projection_drift() -> None:
    receipt = make_confidential_extension_receipt_from_verified_attestation(
        verified_attestation=VerifiedConfidentialAttestation(
            measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
            policy_digest=POLICY_DIGEST,
            attestation_epoch=8,
        ),
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-producer",
        policy_version="tee-policy-v1",
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )
    receipt["body"] = dict(receipt["body"], request_id="req-consumer")

    ok, err, updated = validate_confidential_extension_live_admission(
        receipt=receipt,
        approved_measurements=APPROVED,
        expected_policy_digest=POLICY_DIGEST,
        request_table=ConfidentialRequestTable(),
    )
    assert ok is False
    assert err == "hash_mismatch"
    assert updated is None


def test_confidential_extension_live_admission_rejects_verified_attestation_missing_measurement_allowlist() -> None:
    receipt = make_confidential_extension_receipt_from_verified_attestation(
        verified_attestation=VerifiedConfidentialAttestation(
            measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
            policy_digest=POLICY_DIGEST,
            attestation_epoch=8,
        ),
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-missing-allowlist",
        policy_version="tee-policy-v1",
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )
    ok, err, updated = validate_confidential_extension_live_admission(
        receipt=receipt,
        approved_measurements=set(),
        expected_policy_digest=POLICY_DIGEST,
        request_table=ConfidentialRequestTable(),
    )
    assert ok is False
    assert err == "measurement_not_approved"
    assert updated is None

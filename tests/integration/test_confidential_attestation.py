from __future__ import annotations

import pytest

from src.core.confidential_extension_receipts import verify_confidential_extension_receipt
from src.integration.confidential_attestation import (
    VerifiedConfidentialAttestation,
    attestation_epoch_from_unix_time,
    azure_hostdata_measurement_from_claims,
    make_confidential_extension_receipt_from_azure,
    make_confidential_extension_receipt_from_nitro,
    make_confidential_extension_receipt_from_verified_attestation,
    nitro_measurement_from_summary,
)


NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
AZURE_HOSTDATA = "c" * 64
POLICY_DIGEST = "0x" + ("d" * 64)


def test_nitro_measurement_from_summary_binds_pcr0_and_pcr8() -> None:
    summary = {"pcrs": {"0": NITRO_PCR0.upper(), "8": NITRO_PCR8.upper()}}
    assert nitro_measurement_from_summary(summary) == f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"


@pytest.mark.parametrize("issued_at_s,epoch_length_s,expected", [(0, 60, 0), (59, 60, 0), (60, 60, 1), (121, 60, 2)])
def test_attestation_epoch_from_unix_time_bva(issued_at_s: int, epoch_length_s: int, expected: int) -> None:
    assert attestation_epoch_from_unix_time(issued_at_s=issued_at_s, epoch_length_s=epoch_length_s) == expected


def test_make_confidential_extension_receipt_from_nitro_roundtrip() -> None:
    receipt = make_confidential_extension_receipt_from_nitro(
        summary={"pcrs": {"0": NITRO_PCR0, "8": NITRO_PCR8}},
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-1",
        policy_version="tee-policy-v1",
        policy_digest=POLICY_DIGEST,
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        attestation_epoch=9,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )
    ok, err = verify_confidential_extension_receipt(
        receipt,
        approved_measurements={f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"},
    )
    assert ok, err


def test_azure_hostdata_measurement_from_claims_requires_sevsnp_and_non_debug() -> None:
    claims = {
        "x-ms-attestation-type": "sevsnpvm",
        "x-ms-sevsnpvm-is-debuggable": False,
        "x-ms-sevsnpvm-hostdata": AZURE_HOSTDATA.upper(),
    }
    assert azure_hostdata_measurement_from_claims(claims) == f"azure-sevsnp:hostdata:{AZURE_HOSTDATA}"


def test_make_confidential_extension_receipt_from_azure_roundtrip() -> None:
    receipt = make_confidential_extension_receipt_from_azure(
        claims={
            "x-ms-attestation-type": "sevsnpvm",
            "x-ms-sevsnpvm-is-debuggable": False,
            "x-ms-sevsnpvm-hostdata": AZURE_HOSTDATA,
        },
        extension_id="risk-sidecar-v1",
        provider_id="provider-azure",
        request_id="req-2",
        policy_version="tee-policy-v1",
        policy_digest=POLICY_DIGEST,
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        attestation_epoch=10,
        max_attestation_age=1,
        fee_charged=3,
        receipt_fee=3,
        credit_before=20,
        credit_after=17,
        provider_balance_before=5,
        provider_balance_after=8,
    )
    ok, err = verify_confidential_extension_receipt(
        receipt,
        approved_measurements={f"azure-sevsnp:hostdata:{AZURE_HOSTDATA}"},
    )
    assert ok, err


def test_make_confidential_extension_receipt_from_verified_attestation_roundtrip() -> None:
    verified = VerifiedConfidentialAttestation(
        measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
        policy_digest="0x" + ("D" * 64),
        attestation_epoch=9,
    )
    receipt = make_confidential_extension_receipt_from_verified_attestation(
        verified_attestation=verified,
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
    ok, err = verify_confidential_extension_receipt(
        receipt,
        approved_measurements={f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"},
    )
    assert ok, err
    assert receipt["body"]["policy_digest"] == POLICY_DIGEST


def test_azure_hostdata_measurement_rejects_debuggable_claim() -> None:
    with pytest.raises(ValueError, match="must not be debuggable"):
        azure_hostdata_measurement_from_claims(
            {
                "x-ms-attestation-type": "sevsnpvm",
                "x-ms-sevsnpvm-is-debuggable": True,
                "x-ms-sevsnpvm-hostdata": AZURE_HOSTDATA,
            }
        )


def test_confidential_attestation_helpers_fail_closed_on_bad_shapes() -> None:
    from src.integration import confidential_attestation as mod

    with pytest.raises(ValueError, match="summary must be a mapping"):
        mod._require_mapping([], name="summary")

    with pytest.raises(ValueError, match="provider_id must be a non-empty string"):
        mod._require_nonempty_str("", name="provider_id")

    with pytest.raises(ValueError, match="measurement must be hex"):
        mod._normalize_hex("0xZZ", name="measurement")


def test_attestation_epoch_from_unix_time_roundtrip_with_real_current_time() -> None:
    issued_at_s = 1_773_522_180
    current_epoch = attestation_epoch_from_unix_time(issued_at_s=issued_at_s, epoch_length_s=60)
    attested_epoch = attestation_epoch_from_unix_time(issued_at_s=issued_at_s - 30, epoch_length_s=60)
    receipt = make_confidential_extension_receipt_from_nitro(
        summary={"pcrs": {"0": NITRO_PCR0, "8": NITRO_PCR8}},
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-current",
        policy_version="tee-policy-v1",
        policy_digest=POLICY_DIGEST,
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=current_epoch,
        attestation_epoch=attested_epoch,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )
    ok, err = verify_confidential_extension_receipt(
        receipt,
        approved_measurements={f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"},
    )
    assert ok, err


def test_azure_hostdata_measurement_rejects_wrong_attestation_type() -> None:
    with pytest.raises(ValueError, match="x-ms-attestation-type must be sevsnpvm"):
        azure_hostdata_measurement_from_claims(
            {
                "x-ms-attestation-type": "sgx",
                "x-ms-sevsnpvm-is-debuggable": False,
                "x-ms-sevsnpvm-hostdata": AZURE_HOSTDATA,
            }
        )


@pytest.mark.parametrize(
    ("issued_at_s", "epoch_length_s", "message"),
    [
        (-1, 60, "issued_at_s must be a non-negative int"),
        (10, 0, "epoch_length_s must be a positive int"),
    ],
)
def test_attestation_epoch_from_unix_time_rejects_invalid_bounds(
    issued_at_s: int, epoch_length_s: int, message: str
) -> None:
    with pytest.raises(ValueError, match=message):
        attestation_epoch_from_unix_time(issued_at_s=issued_at_s, epoch_length_s=epoch_length_s)

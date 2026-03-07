from __future__ import annotations

import pytest

from src.core.confidential_extension_receipts import verify_confidential_extension_receipt
from src.integration.confidential_attestation import (
    attestation_epoch_from_unix_time,
    azure_hostdata_measurement_from_claims,
    make_confidential_extension_receipt_from_azure,
    make_confidential_extension_receipt_from_nitro,
    nitro_measurement_from_summary,
)


def test_nitro_measurement_from_summary_binds_pcr0_and_pcr8() -> None:
    summary = {"pcrs": {"0": "AA", "8": "bb"}}
    assert nitro_measurement_from_summary(summary) == "nitro:pcr0:aa:pcr8:bb"


@pytest.mark.parametrize("issued_at_s,epoch_length_s,expected", [(0, 60, 0), (59, 60, 0), (60, 60, 1), (121, 60, 2)])
def test_attestation_epoch_from_unix_time_bva(issued_at_s: int, epoch_length_s: int, expected: int) -> None:
    assert attestation_epoch_from_unix_time(issued_at_s=issued_at_s, epoch_length_s=epoch_length_s) == expected


def test_make_confidential_extension_receipt_from_nitro_roundtrip() -> None:
    receipt = make_confidential_extension_receipt_from_nitro(
        summary={"pcrs": {"0": "aa", "8": "bb"}},
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-1",
        policy_version="tee-policy-v1",
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
        approved_measurements={"nitro:pcr0:aa:pcr8:bb"},
    )
    assert ok, err


def test_azure_hostdata_measurement_from_claims_requires_sevsnp_and_non_debug() -> None:
    claims = {
        "x-ms-attestation-type": "sevsnpvm",
        "x-ms-sevsnpvm-is-debuggable": False,
        "x-ms-sevsnpvm-hostdata": "ABCD",
    }
    assert azure_hostdata_measurement_from_claims(claims) == "azure-sevsnp:hostdata:abcd"


def test_make_confidential_extension_receipt_from_azure_roundtrip() -> None:
    receipt = make_confidential_extension_receipt_from_azure(
        claims={
            "x-ms-attestation-type": "sevsnpvm",
            "x-ms-sevsnpvm-is-debuggable": False,
            "x-ms-sevsnpvm-hostdata": "abcd",
        },
        extension_id="risk-sidecar-v1",
        provider_id="provider-azure",
        request_id="req-2",
        policy_version="tee-policy-v1",
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
        approved_measurements={"azure-sevsnp:hostdata:abcd"},
    )
    assert ok, err


def test_azure_hostdata_measurement_rejects_debuggable_claim() -> None:
    with pytest.raises(ValueError, match="must not be debuggable"):
        azure_hostdata_measurement_from_claims(
            {
                "x-ms-attestation-type": "sevsnpvm",
                "x-ms-sevsnpvm-is-debuggable": True,
                "x-ms-sevsnpvm-hostdata": "abcd",
            }
        )

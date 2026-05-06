from __future__ import annotations

import pytest

from src.integration.confidential_attestation import (
    VerifiedConfidentialAttestation,
    attestation_epoch_from_unix_time,
    azure_hostdata_measurement_from_claims,
    nitro_measurement_from_summary,
)


NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
AZURE_HOSTDATA = "c" * 64


def test_nitro_measurement_rejects_bad_summary_shapes() -> None:
    assert nitro_measurement_from_summary({"pcrs": {"0": f"0x{NITRO_PCR0}", "8": f"0x{NITRO_PCR8}"}}) == f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"

    with pytest.raises(ValueError, match="summary must be a mapping"):
        nitro_measurement_from_summary("bad")  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="pcrs must be a mapping"):
        nitro_measurement_from_summary({"pcrs": "bad"})
    with pytest.raises(ValueError, match="pcr0 must be hex"):
        nitro_measurement_from_summary({"pcrs": {"0": "zz", "8": "bb"}})
    with pytest.raises(ValueError, match="pcr8 must be a non-empty string"):
        nitro_measurement_from_summary({"pcrs": {"0": NITRO_PCR0, "8": ""}})
    with pytest.raises(ValueError, match="pcr0 must be 96-char hex"):
        nitro_measurement_from_summary({"pcrs": {"0": "aa", "8": NITRO_PCR8}})


def test_azure_measurement_and_epoch_helpers_reject_invalid_inputs() -> None:
    with pytest.raises(ValueError, match="x-ms-attestation-type must be sevsnpvm"):
        azure_hostdata_measurement_from_claims(
            {
                "x-ms-attestation-type": "tdx",
                "x-ms-sevsnpvm-is-debuggable": False,
                "x-ms-sevsnpvm-hostdata": AZURE_HOSTDATA,
            }
        )

    with pytest.raises(ValueError, match="x-ms-sevsnpvm-hostdata must be hex"):
        azure_hostdata_measurement_from_claims(
            {
                "x-ms-attestation-type": "sevsnpvm",
                "x-ms-sevsnpvm-is-debuggable": False,
                "x-ms-sevsnpvm-hostdata": "xyz",
            }
        )
    with pytest.raises(ValueError, match="x-ms-sevsnpvm-hostdata must be 64-char hex"):
        azure_hostdata_measurement_from_claims(
            {
                "x-ms-attestation-type": "sevsnpvm",
                "x-ms-sevsnpvm-is-debuggable": False,
                "x-ms-sevsnpvm-hostdata": "ab",
            }
        )

    with pytest.raises(ValueError, match="issued_at_s must be a non-negative int"):
        attestation_epoch_from_unix_time(issued_at_s=True, epoch_length_s=60)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="epoch_length_s must be a positive int"):
        attestation_epoch_from_unix_time(issued_at_s=0, epoch_length_s=False)  # type: ignore[arg-type]


def test_verified_confidential_attestation_rejects_invalid_fields() -> None:
    with pytest.raises(ValueError, match="measurement must be canonical"):
        VerifiedConfidentialAttestation(
            measurement=f"nitro:pcr0:{NITRO_PCR0.upper()}:pcr8:{NITRO_PCR8}",
            policy_digest="0x" + ("d" * 64),
            attestation_epoch=1,
        )
    with pytest.raises(ValueError, match="attestation_epoch must be a bounded int"):
        VerifiedConfidentialAttestation(
            measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
            policy_digest="0x" + ("d" * 64),
            attestation_epoch=-1,
        )

from __future__ import annotations

import pytest

from src.integration.confidential_attestation import (
    attestation_epoch_from_unix_time,
    azure_hostdata_measurement_from_claims,
    nitro_measurement_from_summary,
)


def test_nitro_measurement_rejects_bad_summary_shapes() -> None:
    assert nitro_measurement_from_summary({"pcrs": {"0": "0xAA", "8": "0xBB"}}) == "nitro:pcr0:aa:pcr8:bb"

    with pytest.raises(ValueError, match="summary must be a mapping"):
        nitro_measurement_from_summary("bad")  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="pcrs must be a mapping"):
        nitro_measurement_from_summary({"pcrs": "bad"})
    with pytest.raises(ValueError, match="pcr0 must be hex"):
        nitro_measurement_from_summary({"pcrs": {"0": "zz", "8": "bb"}})
    with pytest.raises(ValueError, match="pcr8 must be a non-empty string"):
        nitro_measurement_from_summary({"pcrs": {"0": "aa", "8": ""}})


def test_azure_measurement_and_epoch_helpers_reject_invalid_inputs() -> None:
    with pytest.raises(ValueError, match="x-ms-attestation-type must be sevsnpvm"):
        azure_hostdata_measurement_from_claims(
            {
                "x-ms-attestation-type": "tdx",
                "x-ms-sevsnpvm-is-debuggable": False,
                "x-ms-sevsnpvm-hostdata": "abcd",
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

    with pytest.raises(ValueError, match="issued_at_s must be a non-negative int"):
        attestation_epoch_from_unix_time(issued_at_s=True, epoch_length_s=60)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="epoch_length_s must be a positive int"):
        attestation_epoch_from_unix_time(issued_at_s=0, epoch_length_s=False)  # type: ignore[arg-type]

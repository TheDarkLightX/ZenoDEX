from __future__ import annotations

import sys

import pytest

from src.integration.confidential_attestation_verifier import (
    SubprocessConfidentialAttestationVerifier,
)


def test_confidential_attestation_verifier_rejects_bool_resource_fields() -> None:
    kwargs = {
        "cmd": [sys.executable, "-c", "print('unused')"],
        "timeout_s": 1.0,
        "max_bytes": 1024,
        "max_stdout_bytes": 1024,
        "max_stderr_bytes": 1024,
    }

    with pytest.raises(ValueError, match="timeout_s must be positive"):
        SubprocessConfidentialAttestationVerifier(**{**kwargs, "timeout_s": True})
    with pytest.raises(ValueError, match="max_bytes must be positive"):
        SubprocessConfidentialAttestationVerifier(**{**kwargs, "max_bytes": True})
    with pytest.raises(ValueError, match="max_stdout_bytes must be positive"):
        SubprocessConfidentialAttestationVerifier(**{**kwargs, "max_stdout_bytes": True})
    with pytest.raises(ValueError, match="max_stderr_bytes must be positive"):
        SubprocessConfidentialAttestationVerifier(**{**kwargs, "max_stderr_bytes": False})

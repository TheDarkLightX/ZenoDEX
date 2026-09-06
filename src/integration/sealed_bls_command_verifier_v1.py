"""Execute acquired immutable BLS verifier bytes in a sealed Linux memfd.

The existing receipt adapter's bounded pipe exchange is reused as transport;
no receipt verification, image identity or receipt authority is involved. The
new BLS protocol independently validates every response. Interpreter, OS,
dynamic loader and system libraries remain trusted. Construction grants no
release capability or publication authority, and does not qualify arbitrary ELF
bytes as a correct verifier. Historical BLS releases are unchanged.
"""

from __future__ import annotations

import fcntl
import hashlib
import os
from contextlib import contextmanager
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Iterator

from ..core.bls_command_verifier_protocol_v1 import (
    decode_bls_command_response_v1,
    encode_bls_command_request_v1,
)
from ..core.economic_command_signature_verifier_deployment_v1 import (
    MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1,
)
from .economic_command_signature_verifier_deployment_v1 import _read_regular_artifact_bytes_v1
from .global_receipt_verifier_v1 import GlobalReceiptVerifierErrorV1, _invoke_v1


class SealedBlsCommandVerifierRejectV1(str, Enum):
    EXECUTABLE_UNAVAILABLE = "EXECUTABLE_UNAVAILABLE"
    EXECUTABLE_BINDING = "EXECUTABLE_BINDING"
    PROCESS_UNAVAILABLE = "PROCESS_UNAVAILABLE"
    PROCESS_TIMEOUT = "PROCESS_TIMEOUT"
    OUTPUT_LIMIT = "OUTPUT_LIMIT"
    PROCESS_REJECTED = "PROCESS_REJECTED"
    RESPONSE_BINDING = "RESPONSE_BINDING"


class SealedBlsCommandVerifierErrorV1(RuntimeError):
    def __init__(self, reason: SealedBlsCommandVerifierRejectV1) -> None:
        self.reason = reason
        super().__init__(f"sealed BLS command verifier rejected: {reason.value}")


@contextmanager
def _sealed_bls_bytes_v1(artifact: bytes) -> Iterator[int]:
    descriptor = None
    try:
        descriptor = os.memfd_create("zenodex-bls-verifier-v1", os.MFD_ALLOW_SEALING)
        pending = memoryview(artifact)
        while pending:
            count = os.write(descriptor, pending)
            if count <= 0:
                raise OSError("verifier snapshot write failed")
            pending = pending[count:]
        os.lseek(descriptor, 0, os.SEEK_SET)
        os.fchmod(descriptor, 0o500)
        fcntl.fcntl(descriptor, fcntl.F_ADD_SEALS,
                    fcntl.F_SEAL_SEAL | fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SHRINK)
        yield descriptor
    except OSError:
        raise SealedBlsCommandVerifierErrorV1(
            SealedBlsCommandVerifierRejectV1.PROCESS_UNAVAILABLE,
        ) from None
    finally:
        if descriptor is not None:
            os.close(descriptor)


@dataclass(frozen=True, slots=True)
class SealedBlsCommandVerifierV1:
    executable_bytes: bytes = field(repr=False)
    executable_sha256: str
    timeout_ms: int

    def __post_init__(self) -> None:
        artifact = self.executable_bytes
        if (type(artifact) is not bytes
            or not 1 <= len(artifact) <= MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1
            or not artifact.startswith(b"\x7fELF")
            or type(self.executable_sha256) is not str
            or hashlib.sha256(artifact).hexdigest() != self.executable_sha256):
            raise SealedBlsCommandVerifierErrorV1(SealedBlsCommandVerifierRejectV1.EXECUTABLE_BINDING)
        if type(self.timeout_ms) is not int or not 1 <= self.timeout_ms <= 60_000:
            raise ValueError("BLS command verifier timeout must be 1 through 60000 ms")

    def verify_command_signature(
        self, *, signature_algorithm: str, signer_public_key: str,
        message_bytes: bytes, signature_bytes: bytes,
    ) -> bool:
        try:
            request = encode_bls_command_request_v1(
                signature_algorithm=signature_algorithm, signer_public_key=signer_public_key,
                message_bytes=message_bytes, signature_bytes=signature_bytes,
            )
        except ValueError:
            return False
        try:
            with _sealed_bls_bytes_v1(self.executable_bytes) as descriptor:
                stdout, stderr, returncode = _invoke_v1(descriptor, request, self.timeout_ms)
        except GlobalReceiptVerifierErrorV1 as error:
            # The shared exchange emits only these transport reasons.
            reasons = {
                "PROCESS_UNAVAILABLE": SealedBlsCommandVerifierRejectV1.PROCESS_UNAVAILABLE,
                "PROCESS_TIMEOUT": SealedBlsCommandVerifierRejectV1.PROCESS_TIMEOUT,
                "OUTPUT_LIMIT": SealedBlsCommandVerifierRejectV1.OUTPUT_LIMIT,
            }
            raise SealedBlsCommandVerifierErrorV1(
                reasons.get(error.reason.value, SealedBlsCommandVerifierRejectV1.PROCESS_REJECTED),
            ) from None
        if returncode != 0 or stderr:
            raise SealedBlsCommandVerifierErrorV1(SealedBlsCommandVerifierRejectV1.PROCESS_REJECTED)
        try:
            return decode_bls_command_response_v1(request, stdout)
        except ValueError:
            raise SealedBlsCommandVerifierErrorV1(SealedBlsCommandVerifierRejectV1.RESPONSE_BINDING) from None


def load_sealed_bls_command_verifier_v1(
    artifact_path: Path, *, expected_sha256: str, timeout_ms: int,
) -> SealedBlsCommandVerifierV1:
    """Acquire once; each subsequent execution uses the same owned bytes."""

    try:
        artifact = _read_regular_artifact_bytes_v1(artifact_path)
    except (OSError, ValueError):
        raise SealedBlsCommandVerifierErrorV1(
            SealedBlsCommandVerifierRejectV1.EXECUTABLE_UNAVAILABLE,
        ) from None
    return SealedBlsCommandVerifierV1(artifact, expected_sha256, timeout_ms)

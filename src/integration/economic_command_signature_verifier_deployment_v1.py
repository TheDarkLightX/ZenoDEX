"""Imperative-shell artifact measurement for command-signature verifiers.

This loader measures one regular non-symlink artifact through a stable file
descriptor, then delegates all release, manifest, and scope decisions to the
deterministic core.  The caller still owns the external premise that the
injected backend executes the measured artifact.
"""

from __future__ import annotations

import os
import stat
from pathlib import Path

from src.core.economic_command_signature_verifier_deployment_v1 import (
    MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1,
    BoundEconomicCommandSignatureVerifierV1,
    EconomicCommandSignatureVerifierBackendV1,
    EconomicCommandSignatureVerifierEvidenceManifestV1,
    bind_economic_command_signature_verifier_deployment_v1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierReleaseV1,
)


def bind_deployed_economic_command_signature_verifier_v1(
    *,
    artifact_path: Path,
    release: EconomicCommandSignatureVerifierReleaseV1,
    evidence_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    deployment_root: str,
    profile_root: str,
    backend: EconomicCommandSignatureVerifierBackendV1,
) -> BoundEconomicCommandSignatureVerifierV1:
    """Measure one artifact and construct its process-local bound capability."""

    artifact_bytes = _read_regular_artifact_bytes_v1(artifact_path)
    return bind_economic_command_signature_verifier_deployment_v1(
        release=release,
        evidence_manifest=evidence_manifest,
        measured_artifact_bytes=artifact_bytes,
        deployment_root=deployment_root,
        profile_root=profile_root,
        backend=backend,
    )


def _read_regular_artifact_bytes_v1(artifact_path: Path) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NONBLOCK", 0)
    no_follow = getattr(os, "O_NOFOLLOW", 0)
    if no_follow == 0:
        raise ValueError(
            "command signature verifier artifact loading requires O_NOFOLLOW"
        )
    try:
        descriptor = os.open(artifact_path, flags | no_follow)
    except OSError as exc:
        raise ValueError(
            "command signature verifier artifact must be a regular non-symlink file"
        ) from exc
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise ValueError(
                "command signature verifier artifact must be a regular non-symlink file"
            )
        if not 1 <= before.st_size <= MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1:
            raise ValueError("command signature verifier artifact byte length is out of bounds")
        artifact_bytes = _read_exact_artifact_bytes_v1(descriptor, before.st_size)
        after = os.fstat(descriptor)
        stable_coordinates = (
            before.st_dev,
            before.st_ino,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        if stable_coordinates != (
            after.st_dev,
            after.st_ino,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ):
            raise ValueError("command signature verifier artifact changed during measurement")
        return artifact_bytes
    finally:
        os.close(descriptor)


def _read_exact_artifact_bytes_v1(descriptor: int, expected_size: int) -> bytes:
    chunks: list[bytes] = []
    remaining = expected_size
    while remaining:
        chunk = os.read(descriptor, min(remaining, 1024 * 1024))
        if not chunk:
            raise ValueError("command signature verifier artifact changed during measurement")
        chunks.append(chunk)
        remaining -= len(chunk)
    if os.read(descriptor, 1):
        raise ValueError("command signature verifier artifact changed during measurement")
    return b"".join(chunks)


__all__ = ["bind_deployed_economic_command_signature_verifier_v1"]

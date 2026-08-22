from __future__ import annotations

import os

import pytest

from src.core.economic_command_signature_verifier_deployment_v1 import (
    MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1,
    CommandSignatureVerifierEvidenceArtifactV1,
    EconomicCommandSignatureVerifierEvidenceManifestV1,
    command_signature_verifier_backend_protocol_root_v1,
    command_signature_verifier_implementation_root_v1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    CommandSignatureVerifierEvidenceStatusV1,
    EconomicCommandSignatureVerifierReleaseV1,
)
from src.core.global_settlement_types_v1 import ReleaseStatusV1
from src.integration.economic_command_signature_verifier_deployment_v1 import (
    bind_deployed_economic_command_signature_verifier_v1,
)

_ALGORITHM = "BLS12_381_G2_BASIC_V1"


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _manifest(artifact_bytes: bytes) -> EconomicCommandSignatureVerifierEvidenceManifestV1:
    rows = tuple(
        CommandSignatureVerifierEvidenceArtifactV1(status, _root(600 + index))
        for index, status in enumerate(
            sorted(CommandSignatureVerifierEvidenceStatusV1, key=lambda item: item.value)
        )
    )
    return EconomicCommandSignatureVerifierEvidenceManifestV1(
        signature_algorithm=_ALGORITHM,
        implementation_root=command_signature_verifier_implementation_root_v1(artifact_bytes),
        public_key_schema_root=_root(611),
        signature_schema_root=_root(612),
        message_schema_root=_root(613),
        specification_root=_root(614),
        source_root=_root(615),
        toolchain_root=_root(616),
        backend_protocol_root=command_signature_verifier_backend_protocol_root_v1(),
        max_public_key_bytes=160,
        max_signature_bytes=4_096,
        evidence_artifacts=rows,
    )


def _release(
    manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
) -> EconomicCommandSignatureVerifierReleaseV1:
    return EconomicCommandSignatureVerifierReleaseV1.build(
        semantic_version="1.0.0-shell-test",
        signature_algorithm=manifest.signature_algorithm,
        implementation_root=manifest.implementation_root,
        public_key_schema_root=manifest.public_key_schema_root,
        signature_schema_root=manifest.signature_schema_root,
        message_schema_root=manifest.message_schema_root,
        specification_root=manifest.specification_root,
        source_root=manifest.source_root,
        toolchain_root=manifest.toolchain_root,
        evidence_manifest_root=manifest.manifest_root,
        max_public_key_bytes=manifest.max_public_key_bytes,
        max_signature_bytes=manifest.max_signature_bytes,
        status=ReleaseStatusV1.ACTIVE_NEW,
        accepts_new_authentications=True,
        evidence_statuses=tuple(row.status for row in manifest.evidence_artifacts),
    )


class _BackendV1:
    def verify_command_signature(
        self,
        *,
        signature_algorithm: str,
        signer_public_key: str,
        message_bytes: bytes,
        signature_bytes: bytes,
    ) -> bool:
        return bool(
            signature_algorithm
            and signer_public_key
            and message_bytes
            and signature_bytes
        )


def test_given_exact_regular_artifact_when_loaded_then_release_is_bound(tmp_path) -> None:
    artifact_bytes = b"deployed-command-signature-verifier-v1"
    artifact_path = tmp_path / "signature-verifier.bin"
    artifact_path.write_bytes(artifact_bytes)
    manifest = _manifest(artifact_bytes)

    bound = bind_deployed_economic_command_signature_verifier_v1(
        artifact_path=artifact_path,
        release=_release(manifest),
        evidence_manifest=manifest,
        deployment_root=_root(701),
        profile_root=_root(702),
        backend=_BackendV1(),
    )

    assert bound.release_id == _release(manifest).release_id
    assert bound.deployment_root == _root(701)
    assert bound.profile_root == _root(702)


def test_given_symlink_artifact_when_loaded_then_measurement_rejects(tmp_path) -> None:
    artifact_bytes = b"deployed-command-signature-verifier-v1"
    target_path = tmp_path / "target.bin"
    target_path.write_bytes(artifact_bytes)
    link_path = tmp_path / "verifier-link.bin"
    link_path.symlink_to(target_path)
    manifest = _manifest(artifact_bytes)

    with pytest.raises(ValueError, match="regular non-symlink"):
        bind_deployed_economic_command_signature_verifier_v1(
            artifact_path=link_path,
            release=_release(manifest),
            evidence_manifest=manifest,
            deployment_root=_root(701),
            profile_root=_root(702),
            backend=_BackendV1(),
        )


def test_given_oversized_sparse_artifact_when_loaded_then_rejects_before_read(tmp_path) -> None:
    artifact_path = tmp_path / "oversized.bin"
    with artifact_path.open("wb") as handle:
        handle.truncate(MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1 + 1)
    manifest = _manifest(b"placeholder")

    with pytest.raises(ValueError, match="artifact byte length"):
        bind_deployed_economic_command_signature_verifier_v1(
            artifact_path=artifact_path,
            release=_release(manifest),
            evidence_manifest=manifest,
            deployment_root=_root(701),
            profile_root=_root(702),
            backend=_BackendV1(),
        )


def test_given_empty_artifact_when_loaded_then_rejects_before_read(tmp_path) -> None:
    artifact_path = tmp_path / "empty.bin"
    artifact_path.write_bytes(b"")
    manifest = _manifest(b"placeholder")

    with pytest.raises(ValueError, match="artifact byte length"):
        bind_deployed_economic_command_signature_verifier_v1(
            artifact_path=artifact_path,
            release=_release(manifest),
            evidence_manifest=manifest,
            deployment_root=_root(701),
            profile_root=_root(702),
            backend=_BackendV1(),
        )


@pytest.mark.skipif(not hasattr(os, "mkfifo"), reason="platform lacks FIFO support")
def test_given_fifo_artifact_when_loaded_then_regular_file_check_rejects(tmp_path) -> None:
    artifact_path = tmp_path / "verifier.fifo"
    os.mkfifo(artifact_path)
    manifest = _manifest(b"placeholder")

    with pytest.raises(ValueError, match="regular non-symlink"):
        bind_deployed_economic_command_signature_verifier_v1(
            artifact_path=artifact_path,
            release=_release(manifest),
            evidence_manifest=manifest,
            deployment_root=_root(701),
            profile_root=_root(702),
            backend=_BackendV1(),
        )


def test_given_replaced_artifact_after_manifest_when_loaded_then_rejects(tmp_path) -> None:
    original = b"original-command-signature-verifier-v1"
    artifact_path = tmp_path / "signature-verifier.bin"
    artifact_path.write_bytes(original)
    manifest = _manifest(original)
    artifact_path.write_bytes(b"replacement-command-signature-verifier-v1")

    with pytest.raises(ValueError, match="implementation root"):
        bind_deployed_economic_command_signature_verifier_v1(
            artifact_path=artifact_path,
            release=_release(manifest),
            evidence_manifest=manifest,
            deployment_root=_root(701),
            profile_root=_root(702),
            backend=_BackendV1(),
        )


def test_given_artifact_mutation_during_read_when_loaded_then_rejects(tmp_path, monkeypatch) -> None:
    original = b"a" * (2 * 1024 * 1024)
    artifact_path = tmp_path / "signature-verifier.bin"
    artifact_path.write_bytes(original)
    manifest = _manifest(original)
    real_read = os.read
    mutated = False

    def mutate_after_first_read(descriptor: int, count: int) -> bytes:
        nonlocal mutated
        chunk = real_read(descriptor, count)
        if not mutated:
            mutated = True
            artifact_path.write_bytes(b"b" * len(original))
        return chunk

    monkeypatch.setattr(os, "read", mutate_after_first_read)

    with pytest.raises(ValueError, match="changed during measurement"):
        bind_deployed_economic_command_signature_verifier_v1(
            artifact_path=artifact_path,
            release=_release(manifest),
            evidence_manifest=manifest,
            deployment_root=_root(701),
            profile_root=_root(702),
            backend=_BackendV1(),
        )


@pytest.mark.skipif(not hasattr(os, "O_NOFOLLOW"), reason="platform lacks O_NOFOLLOW")
def test_loader_uses_no_follow_file_descriptor_semantics() -> None:
    assert os.O_NOFOLLOW > 0


def test_loader_fails_closed_when_no_follow_is_unavailable(tmp_path, monkeypatch) -> None:
    artifact_bytes = b"deployed-command-signature-verifier-v1"
    artifact_path = tmp_path / "signature-verifier.bin"
    artifact_path.write_bytes(artifact_bytes)
    manifest = _manifest(artifact_bytes)
    monkeypatch.delattr(os, "O_NOFOLLOW")

    with pytest.raises(ValueError, match="requires O_NOFOLLOW"):
        bind_deployed_economic_command_signature_verifier_v1(
            artifact_path=artifact_path,
            release=_release(manifest),
            evidence_manifest=manifest,
            deployment_root=_root(701),
            profile_root=_root(702),
            backend=_BackendV1(),
        )

"""Measured BLS binding; synthetic roots here are not release evidence."""

from __future__ import annotations

import hashlib
import inspect
import os
from pathlib import Path

import pytest

from src.core.bls_command_verifier_protocol_v1 import (
    BLS_COMMAND_ALGORITHM_V1,
    bls_command_verifier_protocol_root_v1,
)
from src.core.economic_command_signature_verifier_deployment_v1 import (
    BLS_COMMAND_PUBLIC_KEY_TOKEN_BYTES_V1,
    BLS_COMMAND_SIGNATURE_BYTES_V1,
    CommandSignatureVerifierEvidenceArtifactV1,
    EconomicCommandSignatureVerifierEvidenceManifestV1,
    command_signature_verifier_implementation_root_v1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    REQUIRED_ISOLATED_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1,
    EconomicCommandSignatureVerifierReleaseV1,
    EconomicCommandSignatureVerifierSelectionPurposeV1,
)
from src.core.global_settlement_types_v1 import ReleaseStatusV1
from src.integration import sealed_bls_command_verifier_deployment_v1 as deployment

_DEPLOYMENT_ROOT = "0x" + "51" * 32
_PROFILE_ROOT = "0x" + "52" * 32


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _isolated_test_manifest(
    artifact_bytes: bytes,
) -> EconomicCommandSignatureVerifierEvidenceManifestV1:
    artifacts = tuple(
        CommandSignatureVerifierEvidenceArtifactV1(status, _root(700 + index))
        for index, status in enumerate(
            sorted(
                REQUIRED_ISOLATED_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1,
                key=lambda item: item.value,
            )
        )
    )
    return EconomicCommandSignatureVerifierEvidenceManifestV1(
        signature_algorithm=BLS_COMMAND_ALGORITHM_V1,
        implementation_root=command_signature_verifier_implementation_root_v1(
            artifact_bytes
        ),
        public_key_schema_root=_root(611),
        signature_schema_root=_root(612),
        message_schema_root=_root(613),
        specification_root=_root(614),
        source_root=_root(615),
        toolchain_root=_root(616),
        backend_protocol_root=bls_command_verifier_protocol_root_v1(),
        max_public_key_bytes=BLS_COMMAND_PUBLIC_KEY_TOKEN_BYTES_V1,
        max_signature_bytes=BLS_COMMAND_SIGNATURE_BYTES_V1,
        evidence_artifacts=artifacts,
    )


def _isolated_test_release(
    manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
) -> EconomicCommandSignatureVerifierReleaseV1:
    return EconomicCommandSignatureVerifierReleaseV1.build(
        semantic_version="1.0.0-isolated-native-bls-test",
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
        status=ReleaseStatusV1.SHADOW,
        accepts_new_authentications=False,
        evidence_statuses=tuple(row.status for row in manifest.evidence_artifacts),
    )


def test_public_shell_factory_has_no_backend_injection_and_acquires_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifact = b"\x7fELFowned-exact-byte-snapshot"
    reads: list[Path] = []
    constructions: list[object] = []
    sentinel = object()

    def read_once(path: Path) -> bytes:
        reads.append(path)
        return artifact

    class CapturingSealedBackendV1:
        def __init__(
            self,
            *,
            executable_bytes: bytes,
            executable_sha256: str,
            timeout_ms: int,
        ) -> None:
            assert executable_bytes is artifact
            assert executable_sha256 == hashlib.sha256(artifact).hexdigest()
            assert timeout_ms == 4321
            self.executable_bytes = executable_bytes
            constructions.append(self)

    def bind_core(**values: object) -> object:
        assert values["measured_artifact_bytes"] is artifact
        assert values["backend"] is constructions[0]
        assert constructions[0].executable_bytes is artifact  # type: ignore[attr-defined]
        return sentinel

    monkeypatch.setattr(deployment, "_read_regular_artifact_bytes_v1", read_once)
    monkeypatch.setattr(deployment, "SealedBlsCommandVerifierV1", CapturingSealedBackendV1)
    monkeypatch.setattr(
        deployment,
        "bind_bls_command_signature_verifier_deployment_v1",
        bind_core,
    )

    signature = inspect.signature(
        deployment.bind_deployed_sealed_bls_command_verifier_v1
    )
    assert "backend" not in signature.parameters
    path = Path("/unused/test/verifier")
    manifest = _isolated_test_manifest(artifact)
    result = deployment.bind_deployed_sealed_bls_command_verifier_v1(
        artifact_path=path,
        release=_isolated_test_release(manifest),
        evidence_manifest=manifest,
        deployment_root=_DEPLOYMENT_ROOT,
        profile_root=_PROFILE_ROOT,
        timeout_ms=4321,
        selection_purpose=(
            EconomicCommandSignatureVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION
        ),
    )

    assert result is sentinel
    assert reads == [path]
    assert len(constructions) == 1


def test_fresh_isolated_binding_executes_real_independent_g2basic_signature() -> None:
    configured = os.environ.get("ZENODEX_BLS_VERIFIER_TEST_BINARY")
    if not configured:
        pytest.skip("explicit offline-built BLS verifier required for real execution evidence")
    assert configured is not None
    from py_ecc.bls import G2Basic

    path = Path(configured)
    artifact_bytes = path.read_bytes()
    manifest = _isolated_test_manifest(artifact_bytes)
    release = _isolated_test_release(manifest)
    bound = deployment.bind_deployed_sealed_bls_command_verifier_v1(
        artifact_path=path,
        release=release,
        evidence_manifest=manifest,
        deployment_root=_DEPLOYMENT_ROOT,
        profile_root=_PROFILE_ROOT,
        timeout_ms=5000,
        selection_purpose=(
            EconomicCommandSignatureVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION
        ),
    )

    secret = 42  # Public test scalar; never a wallet or funded identity.
    message = b"fresh release-bound native BLS endpoint"
    public_key = "0x" + G2Basic.SkToPk(secret).hex()
    signature = G2Basic.Sign(secret, message)
    assert bound.verify_command_signature(
        signature_algorithm=BLS_COMMAND_ALGORITHM_V1,
        signer_public_key=public_key,
        message_bytes=message,
        signature_bytes=signature,
    ) is True
    assert bound.verify_command_signature(
        signature_algorithm=BLS_COMMAND_ALGORITHM_V1,
        signer_public_key=public_key,
        message_bytes=message + b" changed",
        signature_bytes=signature,
    ) is False

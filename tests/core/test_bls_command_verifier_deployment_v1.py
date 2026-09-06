"""Successor binder checks with synthetic, non-published release fixtures."""

from __future__ import annotations

from dataclasses import replace

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
    bind_bls_command_signature_verifier_deployment_v1,
    bind_economic_command_signature_verifier_deployment_v1,
    command_signature_verifier_backend_protocol_root_v1,
    command_signature_verifier_implementation_root_v1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    REQUIRED_ACTIVE_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1,
    REQUIRED_ISOLATED_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1,
    CommandSignatureVerifierEvidenceStatusV1,
    EconomicCommandSignatureVerifierReleaseV1,
    EconomicCommandSignatureVerifierSelectionPurposeV1,
)
from src.core.global_settlement_types_v1 import ReleaseStatusV1

_ARTIFACT_BYTES = b"measured-native-bls-command-verifier-v1"
_DEPLOYMENT_ROOT = "0x" + "41" * 32
_PROFILE_ROOT = "0x" + "42" * 32


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _evidence_artifacts(
    statuses: frozenset[CommandSignatureVerifierEvidenceStatusV1],
) -> tuple[CommandSignatureVerifierEvidenceArtifactV1, ...]:
    return tuple(
        CommandSignatureVerifierEvidenceArtifactV1(status, _root(500 + index))
        for index, status in enumerate(sorted(statuses, key=lambda item: item.value))
    )


def _manifest(
    *,
    backend_protocol_root: str | None = None,
    signature_algorithm: str = BLS_COMMAND_ALGORITHM_V1,
    max_public_key_bytes: int = BLS_COMMAND_PUBLIC_KEY_TOKEN_BYTES_V1,
    max_signature_bytes: int = BLS_COMMAND_SIGNATURE_BYTES_V1,
    production: bool = False,
) -> EconomicCommandSignatureVerifierEvidenceManifestV1:
    statuses = (
        REQUIRED_ACTIVE_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1
        if production
        else REQUIRED_ISOLATED_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1
    )
    return EconomicCommandSignatureVerifierEvidenceManifestV1(
        signature_algorithm=signature_algorithm,
        implementation_root=command_signature_verifier_implementation_root_v1(_ARTIFACT_BYTES),
        public_key_schema_root=_root(311),
        signature_schema_root=_root(312),
        message_schema_root=_root(313),
        specification_root=_root(314),
        source_root=_root(315),
        toolchain_root=_root(316),
        backend_protocol_root=(
            backend_protocol_root or bls_command_verifier_protocol_root_v1()
        ),
        max_public_key_bytes=max_public_key_bytes,
        max_signature_bytes=max_signature_bytes,
        evidence_artifacts=_evidence_artifacts(statuses),
    )


def _release(
    manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    *,
    production: bool = False,
) -> EconomicCommandSignatureVerifierReleaseV1:
    return EconomicCommandSignatureVerifierReleaseV1.build(
        semantic_version="1.0.0-bls-deployment-test",
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
        status=ReleaseStatusV1.ACTIVE_NEW if production else ReleaseStatusV1.SHADOW,
        accepts_new_authentications=production,
        evidence_statuses=tuple(row.status for row in manifest.evidence_artifacts),
    )


class _RecordingBackendV1:
    def __init__(self, result: bool = True) -> None:
        self.result = result
        self.calls: list[tuple[str, str, bytes, bytes]] = []

    def verify_command_signature(
        self,
        *,
        signature_algorithm: str,
        signer_public_key: str,
        message_bytes: bytes,
        signature_bytes: bytes,
    ) -> bool:
        self.calls.append(
            (signature_algorithm, signer_public_key, message_bytes, signature_bytes)
        )
        return self.result


def _bind(
    manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    *,
    backend: _RecordingBackendV1 | None = None,
    measured_artifact_bytes: bytes = _ARTIFACT_BYTES,
    deployment_root: str = _DEPLOYMENT_ROOT,
    profile_root: str = _PROFILE_ROOT,
    production: bool = False,
):
    return bind_bls_command_signature_verifier_deployment_v1(
        release=_release(manifest, production=production),
        evidence_manifest=manifest,
        measured_artifact_bytes=measured_artifact_bytes,
        deployment_root=deployment_root,
        profile_root=profile_root,
        backend=backend or _RecordingBackendV1(),
        selection_purpose=(
            EconomicCommandSignatureVerifierSelectionPurposeV1.PRODUCTION_NEW
            if production
            else EconomicCommandSignatureVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION
        ),
    )


def test_successor_protocol_root_is_fixed_and_distinct_from_legacy() -> None:
    assert bls_command_verifier_protocol_root_v1() == (
        "0xf5a1d92017eca916feccff07b5da8204f389ee15fbf3547b3ff9b72107f7d9dd"
    )
    assert (
        bls_command_verifier_protocol_root_v1()
        != command_signature_verifier_backend_protocol_root_v1()
    )


def test_successor_binding_mints_only_the_requested_scoped_capability() -> None:
    manifest = _manifest()
    backend = _RecordingBackendV1()
    bound = _bind(manifest, backend=backend)

    assert bound.release_id == _release(manifest).release_id
    assert bound.deployment_root == _DEPLOYMENT_ROOT
    assert bound.profile_root == _PROFILE_ROOT
    assert bound.binding_root == (
        "0x1f77876303982338b7cd4e094ff2a45749666f80e1b9653473b06a6233252cda"
    )
    assert (
        bound.selection_purpose
        is EconomicCommandSignatureVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION
    )
    bound.require_binding(
        release_id=bound.release_id,
        deployment_root=_DEPLOYMENT_ROOT,
        profile_root=_PROFILE_ROOT,
        selection_purpose=(
            EconomicCommandSignatureVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION
        ),
    )
    assert bound.verify_command_signature(
        signature_algorithm=BLS_COMMAND_ALGORITHM_V1,
        signer_public_key="0x" + "01" * 48,
        message_bytes=b"bound message",
        signature_bytes=b"\x02" * 96,
    ) is True
    assert len(backend.calls) == 1


def test_old_and_new_protocol_binders_reject_each_others_manifests() -> None:
    bls_manifest = _manifest(production=True)
    with pytest.raises(ValueError, match="backend protocol root mismatch"):
        bind_economic_command_signature_verifier_deployment_v1(
            release=_release(bls_manifest, production=True),
            evidence_manifest=bls_manifest,
            measured_artifact_bytes=_ARTIFACT_BYTES,
            deployment_root=_DEPLOYMENT_ROOT,
            profile_root=_PROFILE_ROOT,
            backend=_RecordingBackendV1(),
        )

    legacy_manifest = _manifest(
        backend_protocol_root=command_signature_verifier_backend_protocol_root_v1()
    )
    with pytest.raises(ValueError, match="backend protocol root mismatch"):
        _bind(legacy_manifest)


@pytest.mark.parametrize(
    ("manifest", "error"),
    (
        (_manifest(signature_algorithm="BLS12_381_G2_POP_V1"), "algorithm mismatch"),
        (_manifest(max_public_key_bytes=97), "public-key ceiling mismatch"),
        (_manifest(max_public_key_bytes=99), "public-key ceiling mismatch"),
        (_manifest(max_signature_bytes=95), "signature ceiling mismatch"),
        (_manifest(max_signature_bytes=97), "signature ceiling mismatch"),
    ),
)
def test_successor_binder_requires_exact_bls_algorithm_and_ceilings(
    manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    error: str,
) -> None:
    with pytest.raises(ValueError, match=error):
        _bind(manifest)


def test_successor_binder_rejects_artifact_manifest_and_scope_mismatches() -> None:
    manifest = _manifest()
    release = _release(manifest)
    backend = _RecordingBackendV1()

    with pytest.raises(ValueError, match="measured implementation root mismatch"):
        _bind(manifest, backend=backend, measured_artifact_bytes=b"other bytes")

    with pytest.raises(ValueError, match="evidence manifest root mismatch"):
        bind_bls_command_signature_verifier_deployment_v1(
            release=release,
            evidence_manifest=replace(manifest, source_root=_root(999)),
            measured_artifact_bytes=_ARTIFACT_BYTES,
            deployment_root=_DEPLOYMENT_ROOT,
            profile_root=_PROFILE_ROOT,
            backend=backend,
            selection_purpose=(
                EconomicCommandSignatureVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION
            ),
        )

    for deployment_root, profile_root in (
        ("0x" + "00" * 32, _PROFILE_ROOT),
        (_DEPLOYMENT_ROOT, "0x" + "00" * 32),
    ):
        with pytest.raises(ValueError, match="root"):
            _bind(
                manifest,
                backend=backend,
                deployment_root=deployment_root,
                profile_root=profile_root,
            )
    assert backend.calls == []


def test_successor_binder_enforces_production_and_isolated_purposes() -> None:
    shadow_manifest = _manifest()
    with pytest.raises(ValueError, match="production.*active verifier release"):
        bind_bls_command_signature_verifier_deployment_v1(
            release=_release(shadow_manifest),
            evidence_manifest=shadow_manifest,
            measured_artifact_bytes=_ARTIFACT_BYTES,
            deployment_root=_DEPLOYMENT_ROOT,
            profile_root=_PROFILE_ROOT,
            backend=_RecordingBackendV1(),
            selection_purpose=(
                EconomicCommandSignatureVerifierSelectionPurposeV1.PRODUCTION_NEW
            ),
        )

    production_manifest = _manifest(production=True)
    with pytest.raises(ValueError, match="isolated.*shadow verifier release"):
        bind_bls_command_signature_verifier_deployment_v1(
            release=_release(production_manifest, production=True),
            evidence_manifest=production_manifest,
            measured_artifact_bytes=_ARTIFACT_BYTES,
            deployment_root=_DEPLOYMENT_ROOT,
            profile_root=_PROFILE_ROOT,
            backend=_RecordingBackendV1(),
            selection_purpose=(
                EconomicCommandSignatureVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION
            ),
        )

    incomplete_manifest = replace(
        shadow_manifest,
        evidence_artifacts=(shadow_manifest.evidence_artifacts[0],),
    )
    with pytest.raises(ValueError, match="isolated.*lacks baseline evidence"):
        _bind(incomplete_manifest)

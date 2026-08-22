from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.economic_command_signature_verifier_deployment_v1 import (
    MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1,
    BoundEconomicCommandSignatureVerifierV1,
    CommandSignatureVerifierEvidenceArtifactV1,
    EconomicCommandSignatureVerifierEvidenceManifestV1,
    bind_economic_command_signature_verifier_deployment_v1,
    command_signature_verifier_backend_protocol_root_v1,
    command_signature_verifier_implementation_root_v1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    CommandSignatureVerifierEvidenceStatusV1,
    EconomicCommandSignatureVerifierReleaseV1,
)
from src.core.global_settlement_types_v1 import ReleaseStatusV1

_ALGORITHM = "BLS12_381_G2_BASIC_V1"
_ARTIFACT_BYTES = b"zenodex-command-signature-verifier-test-artifact-v1"


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _evidence_artifacts() -> tuple[CommandSignatureVerifierEvidenceArtifactV1, ...]:
    return tuple(
        CommandSignatureVerifierEvidenceArtifactV1(status, _root(500 + index))
        for index, status in enumerate(
            sorted(CommandSignatureVerifierEvidenceStatusV1, key=lambda item: item.value)
        )
    )


def _manifest(
    *,
    implementation_root: str | None = None,
) -> EconomicCommandSignatureVerifierEvidenceManifestV1:
    return EconomicCommandSignatureVerifierEvidenceManifestV1(
        signature_algorithm=_ALGORITHM,
        implementation_root=(
            implementation_root
            or command_signature_verifier_implementation_root_v1(_ARTIFACT_BYTES)
        ),
        public_key_schema_root=_root(311),
        signature_schema_root=_root(312),
        message_schema_root=_root(313),
        specification_root=_root(314),
        source_root=_root(315),
        toolchain_root=_root(316),
        backend_protocol_root=command_signature_verifier_backend_protocol_root_v1(),
        max_public_key_bytes=160,
        max_signature_bytes=4_096,
        evidence_artifacts=_evidence_artifacts(),
    )


def _release(
    manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
) -> EconomicCommandSignatureVerifierReleaseV1:
    return EconomicCommandSignatureVerifierReleaseV1.build(
        semantic_version="1.0.0-deployment-test",
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


class _RecordingBackendV1:
    def __init__(self, result: object = True) -> None:
        self.result = result
        self.calls: list[tuple[str, str, bytes, bytes]] = []

    @property
    def verifier_release_id(self) -> str:
        raise AssertionError("backend release self-report must never be read")

    def verify_command_signature(
        self,
        *,
        signature_algorithm: str,
        signer_public_key: str,
        message_bytes: bytes,
        signature_bytes: bytes,
    ) -> bool:
        self.calls.append((signature_algorithm, signer_public_key, message_bytes, signature_bytes))
        return self.result  # type: ignore[return-value]


def _bind(
    *,
    artifact_bytes: bytes = _ARTIFACT_BYTES,
    manifest: EconomicCommandSignatureVerifierEvidenceManifestV1 | None = None,
    deployment_root: str = _root(401),
    profile_root: str = _root(402),
    backend: _RecordingBackendV1 | None = None,
) -> BoundEconomicCommandSignatureVerifierV1:
    selected_manifest = manifest or _manifest()
    return bind_economic_command_signature_verifier_deployment_v1(
        release=_release(selected_manifest),
        evidence_manifest=selected_manifest,
        measured_artifact_bytes=artifact_bytes,
        deployment_root=deployment_root,
        profile_root=profile_root,
        backend=backend or _RecordingBackendV1(),
    )


def test_exact_manifest_measurement_and_scope_construct_opaque_binding() -> None:
    bound = _bind()

    assert type(bound) is BoundEconomicCommandSignatureVerifierV1
    assert bound.release_id == _release(_manifest()).release_id
    assert bound.deployment_root == _root(401)
    assert bound.profile_root == _root(402)
    assert bound.binding_root.startswith("0x")


def test_backend_release_self_report_is_removed_from_the_trusted_path() -> None:
    backend = _RecordingBackendV1()
    bound = _bind(backend=backend)

    assert bound.verify_command_signature(
        signature_algorithm=_ALGORITHM,
        signer_public_key="test-public-key",
        message_bytes=b"message",
        signature_bytes=b"signature",
    ) is True
    assert backend.calls == [
        (_ALGORITHM, "test-public-key", b"message", b"signature")
    ]


def test_bound_capability_has_no_writable_authority_slot() -> None:
    bound = _bind()
    baseline = bound.binding_root

    for field_name in (
        "_BoundEconomicCommandSignatureVerifierV1__fields",
        "_fields",
        "deployment_root",
    ):
        with pytest.raises((AttributeError, TypeError)):
            object.__setattr__(bound, field_name, object())

    assert bound.binding_root == baseline


def test_wrong_artifact_bytes_reject_before_backend_use() -> None:
    backend = _RecordingBackendV1()

    with pytest.raises(ValueError, match="implementation root"):
        _bind(artifact_bytes=b"different-artifact", backend=backend)

    assert backend.calls == []


@pytest.mark.parametrize(
    "mutation",
    (
        {"signature_algorithm": "OTHER_ALGORITHM_V1"},
        {"implementation_root": _root(900)},
        {"public_key_schema_root": _root(901)},
        {"signature_schema_root": _root(902)},
        {"message_schema_root": _root(903)},
        {"specification_root": _root(904)},
        {"source_root": _root(905)},
        {"toolchain_root": _root(906)},
        {"backend_protocol_root": _root(907)},
        {"max_public_key_bytes": 159},
        {"max_signature_bytes": 4_095},
    ),
)
def test_each_manifest_coordinate_is_committed_by_its_root(
    mutation: dict[str, object],
) -> None:
    manifest = _manifest()
    release = _release(manifest)
    mutated = replace(manifest, **mutation)

    with pytest.raises(ValueError, match="evidence manifest root"):
        bind_economic_command_signature_verifier_deployment_v1(
            release=release,
            evidence_manifest=mutated,
            measured_artifact_bytes=_ARTIFACT_BYTES,
            deployment_root=_root(401),
            profile_root=_root(402),
            backend=_RecordingBackendV1(),
        )


def test_evidence_artifacts_are_sorted_unique_and_exactly_typed() -> None:
    manifest = _manifest()
    with pytest.raises(ValueError, match="sorted and unique"):
        replace(manifest, evidence_artifacts=())
    with pytest.raises(ValueError, match="sorted and unique"):
        replace(manifest, evidence_artifacts=manifest.evidence_artifacts[::-1])
    with pytest.raises(ValueError, match="sorted and unique"):
        replace(
            manifest,
            evidence_artifacts=manifest.evidence_artifacts
            + (manifest.evidence_artifacts[-1],),
        )
    with pytest.raises(TypeError, match="evidence artifact"):
        replace(manifest, evidence_artifacts=(object(),))

    object.__setattr__(manifest.evidence_artifacts[0], "artifact_root", object())
    with pytest.raises(TypeError, match="artifact root must be exact str"):
        manifest.validate_current()


def test_unsupported_backend_protocol_rejects_even_when_release_commits_manifest() -> None:
    manifest = replace(_manifest(), backend_protocol_root=_root(999))

    with pytest.raises(ValueError, match="backend protocol root"):
        bind_economic_command_signature_verifier_deployment_v1(
            release=_release(manifest),
            evidence_manifest=manifest,
            measured_artifact_bytes=_ARTIFACT_BYTES,
            deployment_root=_root(401),
            profile_root=_root(402),
            backend=_RecordingBackendV1(),
        )


@pytest.mark.parametrize(
    ("artifact_length", "accepted"),
    (
        (0, False),
        (1, True),
        (MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1, True),
        (MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1 + 1, False),
    ),
)
def test_measured_artifact_bytes_use_zero_one_maximum_neighbor_bva(
    artifact_length: int,
    accepted: bool,
) -> None:
    artifact_bytes = b"a" * artifact_length
    if accepted:
        assert command_signature_verifier_implementation_root_v1(artifact_bytes).startswith("0x")
    else:
        with pytest.raises(ValueError, match="artifact byte length"):
            command_signature_verifier_implementation_root_v1(artifact_bytes)


def test_binding_roots_match_cross_language_golden() -> None:
    manifest = _manifest()
    bound = _bind(manifest=manifest)

    assert command_signature_verifier_implementation_root_v1(_ARTIFACT_BYTES) == (
        "0xd6b4fd058a7714e0fe9695a2aab134985cb10c3f471ce41fcca35feb6753cc93"
    )
    assert manifest.manifest_root == (
        "0x4ab6a095bdded66a5a2809734f097ff271daf80a397944e8ffa994305fb64983"
    )
    assert bound.binding_root == (
        "0x4ad7612be045c5b6d7ea52f458dc9814075030ee866ff825b215da92b93d68bd"
    )

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.economic_command_signature_verifier_registry_v1 import (
    ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
    CommandSignatureVerifierEvidenceStatusV1,
    EconomicCommandSignatureVerifierRegistryV1,
    EconomicCommandSignatureVerifierReleaseV1,
    select_profile_governed_command_signature_verifier_release_v1,
)
from src.core.global_settlement_types_v1 import (
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    ReleaseStatusV1,
)

_ALGORITHM = "BLS12_381_G2_BASIC_V1"
_COMMAND = "asset_transfer"


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _active_evidence() -> tuple[CommandSignatureVerifierEvidenceStatusV1, ...]:
    return tuple(
        sorted(
            CommandSignatureVerifierEvidenceStatusV1,
            key=lambda status: status.value,
        )
    )


def _release(
    *,
    signature_algorithm: str = _ALGORITHM,
    implementation_root: str = _root(1),
    status: ReleaseStatusV1 = ReleaseStatusV1.ACTIVE_NEW,
    accepts_new_authentications: bool = True,
    max_public_key_bytes: int = 32,
    max_signature_bytes: int = 16,
) -> EconomicCommandSignatureVerifierReleaseV1:
    return EconomicCommandSignatureVerifierReleaseV1.build(
        semantic_version="1.0.0-test",
        signature_algorithm=signature_algorithm,
        implementation_root=implementation_root,
        public_key_schema_root=_root(2),
        signature_schema_root=_root(3),
        message_schema_root=_root(4),
        specification_root=_root(5),
        source_root=_root(6),
        toolchain_root=_root(7),
        evidence_manifest_root=_root(8),
        max_public_key_bytes=max_public_key_bytes,
        max_signature_bytes=max_signature_bytes,
        status=status,
        accepts_new_authentications=accepts_new_authentications,
        evidence_statuses=_active_evidence() if accepts_new_authentications else (),
    )


def _policy(registry: EconomicCommandSignatureVerifierRegistryV1) -> EconomicPolicyRegistryV1:
    return EconomicPolicyRegistryV1(
        (
            EconomicPolicyBindingV1(
                ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
                _COMMAND,
                registry.registry_root,
            ),
        )
    )


def _select(
    registry: EconomicCommandSignatureVerifierRegistryV1,
    signature_bytes: bytes,
    *,
    signer_public_key: str = "test-public-key",
) -> EconomicCommandSignatureVerifierReleaseV1:
    return select_profile_governed_command_signature_verifier_release_v1(
        policy_registry=_policy(registry),
        verifier_registry=registry,
        command_kind=_COMMAND,
        signature_algorithm=_ALGORITHM,
        signer_public_key=signer_public_key,
        signature_bytes=signature_bytes,
    )


def test_release_and_registry_roots_match_cross_language_golden() -> None:
    release = _release()
    registry = EconomicCommandSignatureVerifierRegistryV1((release,))

    assert (
        release.release_id == "0x01368bcd29677a41ffe2248a74ea2fce6ab490d898d72866c772fc9b2d8f440e"
    )
    assert (
        registry.registry_root
        == "0x101888ac655b02e227e77b9fdf020f6f968b1a9a55793f139e11964731277051"
    )


@pytest.mark.parametrize("field_name", ("signature_algorithm", "implementation_root"))
def test_release_rejects_hostile_string_subclasses(field_name: str) -> None:
    class AlwaysEqual(str):
        def __eq__(self, other: object) -> bool:
            return True

    with pytest.raises(TypeError, match="release strings must be exact strings"):
        replace(_release(), **{field_name: AlwaysEqual("mallory")})


@pytest.mark.parametrize(
    ("signature_length", "accepted"),
    ((15, True), (16, True), (17, False)),
)
def test_release_signature_ceiling_uses_closed_boundary_bva(
    signature_length: int,
    accepted: bool,
) -> None:
    registry = EconomicCommandSignatureVerifierRegistryV1((_release(),))
    if accepted:
        assert _select(registry, b"s" * signature_length) == registry.releases[0]
    else:
        with pytest.raises(ValueError, match="exceeds release ceiling"):
            _select(registry, b"s" * signature_length)


@pytest.mark.parametrize(
    ("public_key_length", "accepted"),
    ((31, True), (32, True), (33, False)),
)
def test_release_public_key_ceiling_uses_utf8_byte_boundary_bva(
    public_key_length: int,
    accepted: bool,
) -> None:
    registry = EconomicCommandSignatureVerifierRegistryV1((_release(),))
    public_key = "k" * public_key_length
    if accepted:
        assert _select(registry, b"signature", signer_public_key=public_key)
    else:
        with pytest.raises(ValueError, match="public key exceeds release ceiling"):
            _select(registry, b"signature", signer_public_key=public_key)

    if public_key_length == 32:
        for utf8_key, utf8_bytes, utf8_accepted in (
            ("é" * 15 + "a", 31, True),
            ("é" * 16, 32, True),
            ("é" * 16 + "a", 33, False),
        ):
            assert len(utf8_key.encode("utf-8")) == utf8_bytes
            if utf8_accepted:
                assert _select(registry, b"signature", signer_public_key=utf8_key)
            else:
                with pytest.raises(ValueError, match="public key exceeds release ceiling"):
                    _select(registry, b"signature", signer_public_key=utf8_key)


@pytest.mark.parametrize(
    ("release_count", "accepted"),
    ((0, False), (1, True), (31, True), (32, True), (33, False)),
)
def test_registry_release_count_uses_closed_boundary_bva(
    release_count: int,
    accepted: bool,
) -> None:
    releases = tuple(
        sorted(
            (
                _release(
                    signature_algorithm=f"TEST_SIGNATURE_ALGORITHM_{index:02d}_V1",
                    implementation_root=_root(100 + index),
                )
                for index in range(release_count)
            ),
            key=lambda release: release.key,
        )
    )
    if accepted:
        assert EconomicCommandSignatureVerifierRegistryV1(releases).registry_root.startswith("0x")
    else:
        with pytest.raises(ValueError, match="registry size"):
            EconomicCommandSignatureVerifierRegistryV1(releases)


def test_wrong_policy_root_rejects_before_release_selection() -> None:
    registry = EconomicCommandSignatureVerifierRegistryV1((_release(),))
    wrong_policy = EconomicPolicyRegistryV1(
        (
            EconomicPolicyBindingV1(
                ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
                _COMMAND,
                _root(999),
            ),
        )
    )

    with pytest.raises(ValueError, match="not profile governed"):
        select_profile_governed_command_signature_verifier_release_v1(
            policy_registry=wrong_policy,
            verifier_registry=registry,
            command_kind=_COMMAND,
            signature_algorithm=_ALGORITHM,
            signer_public_key="test-public-key",
            signature_bytes=b"signature",
        )


def test_rotation_allows_one_verify_only_and_one_active_release() -> None:
    old = _release(
        implementation_root=_root(8),
        status=ReleaseStatusV1.VERIFY_ONLY,
        accepts_new_authentications=False,
    )
    active = _release()
    registry = EconomicCommandSignatureVerifierRegistryV1(
        tuple(sorted((old, active), key=lambda release: release.key))
    )

    assert _select(registry, b"signature") == active


def test_zero_active_releases_for_algorithm_fail_closed() -> None:
    verify_only = _release(
        status=ReleaseStatusV1.VERIFY_ONLY,
        accepts_new_authentications=False,
    )
    registry = EconomicCommandSignatureVerifierRegistryV1((verify_only,))

    with pytest.raises(ValueError, match="one active verifier release"):
        _select(registry, b"signature")


def test_two_active_releases_for_one_algorithm_fail_closed() -> None:
    left = _release()
    right = _release(implementation_root=_root(8))
    registry = EconomicCommandSignatureVerifierRegistryV1(
        tuple(sorted((left, right), key=lambda release: release.key))
    )

    with pytest.raises(ValueError, match="one active verifier release"):
        _select(registry, b"signature")


def test_release_status_and_content_id_mutations_reject() -> None:
    release = _release()
    with pytest.raises(ValueError, match="active status"):
        replace(release, accepts_new_authentications=False)
    with pytest.raises(ValueError, match="content-derived"):
        replace(release, implementation_root=_root(9))
    with pytest.raises(ValueError, match="content-derived"):
        replace(release, evidence_manifest_root=_root(9))
    with pytest.raises(ValueError, match="lacks release evidence"):
        replace(release, evidence_statuses=())
    with pytest.raises(ValueError, match="sorted and unique"):
        replace(release, evidence_statuses=release.evidence_statuses[::-1])
    with pytest.raises(ValueError, match="sorted and unique"):
        replace(
            release,
            evidence_statuses=release.evidence_statuses + (release.evidence_statuses[-1],),
        )
    with pytest.raises(TypeError, match="not closed"):
        replace(release, evidence_statuses=(object(),))


@pytest.mark.parametrize(
    ("ceiling_name", "ceiling_value", "accepted"),
    (
        ("public_key", 0, False),
        ("public_key", 1, True),
        ("public_key", 160, True),
        ("public_key", 161, False),
        ("signature", 0, False),
        ("signature", 1, True),
        ("signature", 4_096, True),
        ("signature", 4_097, False),
    ),
)
def test_release_configured_ceilings_use_zero_one_maximum_neighbor_bva(
    ceiling_name: str,
    ceiling_value: int,
    accepted: bool,
) -> None:
    arguments = (
        {"max_public_key_bytes": ceiling_value}
        if ceiling_name == "public_key"
        else {"max_signature_bytes": ceiling_value}
    )
    if accepted:
        assert _release(**arguments).release_id.startswith("0x")
    else:
        with pytest.raises(ValueError):
            _release(**arguments)

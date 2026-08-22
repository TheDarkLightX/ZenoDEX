from __future__ import annotations

from dataclasses import dataclass, replace

import pytest

from src.core.asset_transfer_types_v1 import (
    ASSET_TRANSFER_COMMAND_KIND_V1,
    AssetTransferCommandV1,
)
from src.core.economic_command_authentication_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    AuthenticatedEconomicCommandIntentV1,
    AuthenticatedEconomicCommandV1,
    EconomicCommandAuthenticationCandidateV1,
    EconomicCommandAuthenticationEnvelopeV1,
    EconomicCommandAuthorizationRegistryV1,
    EconomicCommandAuthorizationV1,
    EconomicCommandIntentV1,
    authenticate_economic_command_intent_v1,
    bind_authenticated_intent_to_occurrence_v1,
    economic_command_authentication_message_bytes_v1,
)
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1
from src.core.global_settlement_types_v1 import (
    MAX_U64_V1,
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    ProfileStatusV1,
    canonical_economic_command_body_bytes_v1,
    hash_economic_command_body_bytes_v1,
)
from tests.core.test_lane_module_release_route_binding_v1 import _profile, _root


@dataclass(frozen=True, slots=True)
class _FixtureV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    authorization_registry: EconomicCommandAuthorizationRegistryV1
    authorization: EconomicCommandAuthorizationV1
    intent: EconomicCommandIntentV1
    occurrence: EconomicCommandOccurrenceV1
    envelope: EconomicCommandAuthenticationEnvelopeV1

    @property
    def candidate(self) -> EconomicCommandAuthenticationCandidateV1:
        return EconomicCommandAuthenticationCandidateV1(
            self.profile,
            self.policy_registry,
            self.authorization_registry,
            self.intent,
            self.envelope,
        )


class _RecordingVerifierV1:
    def __init__(self, result: object = True) -> None:
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
        return self.result  # type: ignore[return-value]


def _rebuild_profile(
    profile: EconomicProfileSnapshotV1,
    policy_registry_root: str,
) -> EconomicProfileSnapshotV1:
    return EconomicProfileSnapshotV1.build(
        authority_epoch=profile.authority_epoch,
        lane_registry=profile.lane_registry,
        lane_coordinator_registry=profile.lane_coordinator_registry,
        route_registry=profile.route_registry,
        proof_shape_root=profile.proof_shape_root,
        root_image_id=profile.root_image_id,
        verifier_registry_root=profile.verifier_registry_root,
        migration_registry_root=profile.migration_registry_root,
        policy_registry_root=policy_registry_root,
        terminal_registry_root=profile.terminal_registry_root,
        status=ProfileStatusV1.ACTIVE,
    )


def _fixture(
    *,
    height: int = 11,
    nonce: int = 9,
    intent_from: int = 10,
    intent_through: int = 12,
    authorization_from: int = 10,
    authorization_through: int = 12,
    min_nonce: int = 8,
    max_nonce: int = 10,
    enabled: bool = True,
) -> _FixtureV1:
    base_profile, routes = _profile()
    route = routes[ASSET_TRANSFER_COMMAND_KIND_V1]
    command = AssetTransferCommandV1(
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "USD",
        "alice",
        "bob",
        30,
        2,
    )
    authorization = EconomicCommandAuthorizationV1(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V1,
        subject_id="alice",
        grant_root=_root(7),
        route_release_id=route.route_release_id,
        signer_key_id="alice-key-1",
        signer_public_key="bls12-381-g2:alice-public-key",
        signature_algorithm="BLS12_381_G2_BASIC_V1",
        valid_from_height=authorization_from,
        valid_through_height=authorization_through,
        min_nonce=min_nonce,
        max_nonce=max_nonce,
        enabled=enabled,
    )
    authorization_registry = EconomicCommandAuthorizationRegistryV1((authorization,))
    policy_registry = EconomicPolicyRegistryV1(
        (
            EconomicPolicyBindingV1(
                ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
                ASSET_TRANSFER_COMMAND_KIND_V1,
                authorization_registry.registry_root,
            ),
        )
    )
    profile = _rebuild_profile(base_profile, policy_registry.registry_root)
    intent = EconomicCommandIntentV1(
        chain_id="zeno-command-auth-test",
        deployment_root=_root(1),
        profile_root=profile.profile_id,
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V1,
        command_body_hash=command.command_body_hash,
        route_release_id=route.route_release_id,
        subject_id="alice",
        grant_root=_root(7),
        nonce=nonce,
        consumed_object_ids=(),
        valid_from_height=intent_from,
        valid_through_height=intent_through,
    )
    occurrence = EconomicCommandOccurrenceV1(
        chain_id=intent.chain_id,
        deployment_root=intent.deployment_root,
        height=height,
        tx_index=2,
        op_index=3,
        command_kind=intent.command_kind,
        command_body_hash=intent.command_body_hash,
        route_release_id=intent.route_release_id,
        subject_id=intent.subject_id,
        grant_root=intent.grant_root,
        nonce=intent.nonce,
        profile_root=intent.profile_root,
        pre_state_root=_root(2),
        consumed_object_ids=intent.consumed_object_ids,
    )
    envelope = EconomicCommandAuthenticationEnvelopeV1(
        canonical_economic_command_body_bytes_v1(intent.command_kind, command),
        authorization.signer_key_id,
        authorization.signer_public_key,
        authorization.signature_algorithm,
        b"test-signature-v1",
    )
    return _FixtureV1(
        profile,
        policy_registry,
        authorization_registry,
        authorization,
        intent,
        occurrence,
        envelope,
    )


def _authenticate_intent(
    fixture: _FixtureV1,
    verifier: _RecordingVerifierV1,
) -> AuthenticatedEconomicCommandIntentV1:
    return authenticate_economic_command_intent_v1(fixture.candidate, verifier)


def _authenticate_command(
    fixture: _FixtureV1,
    verifier: _RecordingVerifierV1,
) -> AuthenticatedEconomicCommandV1:
    return bind_authenticated_intent_to_occurrence_v1(
        _authenticate_intent(fixture, verifier),
        fixture.occurrence,
    )


def test_presequencing_intent_authenticates_then_binds_exact_occurrence() -> None:
    fixture = _fixture()
    verifier = _RecordingVerifierV1()
    authenticated_intent = _authenticate_intent(fixture, verifier)
    authenticated = bind_authenticated_intent_to_occurrence_v1(
        authenticated_intent,
        fixture.occurrence,
    )
    expected_message = economic_command_authentication_message_bytes_v1(
        fixture.candidate,
        fixture.authorization,
    )
    assert verifier.calls == [
        (
            fixture.envelope.signature_algorithm,
            fixture.envelope.signer_public_key,
            expected_message,
            fixture.envelope.signature_bytes,
        )
    ]
    assert authenticated_intent.intent == fixture.intent
    assert authenticated.occurrence == fixture.occurrence
    assert authenticated.occurrence is not fixture.occurrence


def test_sequencer_fields_do_not_require_a_second_signature() -> None:
    fixture = _fixture()
    verifier = _RecordingVerifierV1()
    authenticated_intent = _authenticate_intent(fixture, verifier)
    for occurrence in (
        fixture.occurrence,
        replace(fixture.occurrence, tx_index=99, op_index=17, pre_state_root=_root(99)),
    ):
        bound = bind_authenticated_intent_to_occurrence_v1(
            authenticated_intent,
            occurrence,
        )
        assert bound.occurrence == occurrence
    assert len(verifier.calls) == 1


@pytest.mark.parametrize(
    "field",
    (
        "chain_id",
        "deployment_root",
        "profile_root",
        "command_kind",
        "command_body_hash",
        "route_release_id",
        "subject_id",
        "grant_root",
        "nonce",
        "consumed_object_ids",
    ),
)
def test_each_signed_intent_field_rejects_occurrence_substitution(field: str) -> None:
    fixture = _fixture()
    authenticated_intent = _authenticate_intent(fixture, _RecordingVerifierV1())
    replacement: object = _root(999)
    if field in {"chain_id", "command_kind", "subject_id"}:
        replacement = "mallory"
    elif field == "nonce":
        replacement = fixture.occurrence.nonce + 1
    elif field == "consumed_object_ids":
        replacement = ("object-1",)
    with pytest.raises(ValueError, match="mismatch"):
        bind_authenticated_intent_to_occurrence_v1(
            authenticated_intent,
            replace(fixture.occurrence, **{field: replacement}),
        )


@pytest.mark.parametrize(
    ("height", "accepted"),
    ((9, False), (10, True), (12, True), (13, False)),
)
def test_occurrence_height_uses_signed_intent_interval_bva(
    height: int,
    accepted: bool,
) -> None:
    fixture = _fixture(height=height)
    authenticated_intent = _authenticate_intent(fixture, _RecordingVerifierV1())
    if accepted:
        bind_authenticated_intent_to_occurrence_v1(
            authenticated_intent,
            fixture.occurrence,
        )
    else:
        with pytest.raises(ValueError, match="outside validity"):
            bind_authenticated_intent_to_occurrence_v1(
                authenticated_intent,
                fixture.occurrence,
            )


@pytest.mark.parametrize(
    ("nonce", "accepted"),
    ((7, False), (8, True), (10, True), (11, False)),
)
def test_authorization_nonce_interval_bva(nonce: int, accepted: bool) -> None:
    fixture = _fixture(nonce=nonce)
    verifier = _RecordingVerifierV1()
    if accepted:
        _authenticate_intent(fixture, verifier)
    else:
        with pytest.raises(ValueError, match="nonce"):
            _authenticate_intent(fixture, verifier)
        assert verifier.calls == []


def test_intent_validity_must_be_contained_by_authorization() -> None:
    for intent_from, intent_through in ((9, 12), (10, 13)):
        fixture = _fixture(intent_from=intent_from, intent_through=intent_through)
        verifier = _RecordingVerifierV1()
        with pytest.raises(ValueError, match="exceeds"):
            _authenticate_intent(fixture, verifier)
        assert verifier.calls == []


def test_body_substitution_rejects_before_signature_verification() -> None:
    fixture = _fixture()
    substituted = replace(fixture.envelope, command_body_bytes=b"{}")
    verifier = _RecordingVerifierV1()
    with pytest.raises(ValueError, match="body hash"):
        _authenticate_intent(replace(fixture, envelope=substituted), verifier)
    assert verifier.calls == []


@pytest.mark.parametrize("result", (False, 0, 1, "true", object()))
def test_only_exact_true_signature_result_is_accepted(result: object) -> None:
    verifier = _RecordingVerifierV1(result)
    with pytest.raises(ValueError, match="signature rejected"):
        _authenticate_intent(_fixture(), verifier)
    assert len(verifier.calls) == 1


def test_disabled_wrong_signer_and_shadow_profile_fail_closed() -> None:
    disabled = _fixture(enabled=False)
    verifier = _RecordingVerifierV1()
    with pytest.raises(ValueError, match="disabled"):
        _authenticate_intent(disabled, verifier)
    assert verifier.calls == []

    fixture = _fixture()
    wrong_key = replace(fixture.envelope, signer_public_key="mallory-public-key")
    with pytest.raises(ValueError, match="public key"):
        _authenticate_intent(replace(fixture, envelope=wrong_key), verifier)
    shadow = replace(fixture.profile, status=ProfileStatusV1.SHADOW)
    with pytest.raises(ValueError, match="ACTIVE profile"):
        _authenticate_intent(replace(fixture, profile=shadow), verifier)
    assert verifier.calls == []


def test_canonical_body_hash_and_u64_endpoint_remain_exact() -> None:
    fixture = _fixture(
        height=MAX_U64_V1,
        nonce=MAX_U64_V1,
        intent_from=MAX_U64_V1,
        intent_through=MAX_U64_V1,
        authorization_from=MAX_U64_V1,
        authorization_through=MAX_U64_V1,
        min_nonce=MAX_U64_V1,
        max_nonce=MAX_U64_V1,
    )
    assert hash_economic_command_body_bytes_v1(
        fixture.envelope.command_body_bytes
    ) == fixture.intent.command_body_hash
    _authenticate_command(fixture, _RecordingVerifierV1())


@pytest.mark.parametrize("target", ("authorization", "envelope", "policy", "intent"))
def test_hostile_string_subclasses_reject_before_verification(target: str) -> None:
    class AlwaysEqual(str):
        def __eq__(self, other: object) -> bool:
            return True

        __hash__ = str.__hash__

    fixture = _fixture()
    if target == "authorization":
        object.__setattr__(
            fixture.authorization,
            "signer_public_key",
            AlwaysEqual("mallory"),
        )
    elif target == "envelope":
        object.__setattr__(fixture.envelope, "signer_public_key", AlwaysEqual("mallory"))
    elif target == "policy":
        object.__setattr__(
            fixture.policy_registry.bindings[0],
            "policy_root",
            AlwaysEqual(_root(999)),
        )
    else:
        object.__setattr__(fixture.intent, "subject_id", AlwaysEqual("mallory"))
    verifier = _RecordingVerifierV1()
    with pytest.raises(TypeError, match="exact string"):
        _authenticate_intent(fixture, verifier)
    assert verifier.calls == []


def test_opaque_witnesses_reject_public_construction_and_mutation() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        AuthenticatedEconomicCommandIntentV1(object(), object())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="binder-constructed"):
        AuthenticatedEconomicCommandV1(object(), object())  # type: ignore[arg-type]
    authenticated = _authenticate_command(_fixture(), _RecordingVerifierV1())
    object.__setattr__(authenticated._fields.occurrence, "nonce", 10)  # noqa: SLF001
    with pytest.raises(ValueError, match="occurrence was mutated"):
        _ = authenticated.occurrence

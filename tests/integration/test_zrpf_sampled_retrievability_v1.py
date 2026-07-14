from __future__ import annotations

import copy
import hashlib
import json
import pickle
from collections.abc import Callable
from dataclasses import replace

import pytest

from src.integration.zeno_ledger_signature import (
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_v0 import canonical_json_bytes_v0, hash_v0
from src.integration.zrpf_sampled_retrievability_v1 import (
    SAMPLED_RETRIEVABILITY_RESPONSE_PAYLOAD_KIND_V1,
    BeaconCommitmentV1,
    FullBlobRetrievabilityTargetV1,
    ProviderKeyLifecycleV1,
    SampledRetrievabilityPolicyV1,
    SampledRetrievabilityRejectV1,
    SignedProviderResponseV1,
    build_exact_evidence_bytes_v1,
    build_provider_response_bytes_v1,
    derive_challenge_indices_v1,
    derive_exact_full_blob_target_v1,
    response_payload_hash_v1,
    verify_exact_evidence_v1,
)
from src.integration.zrpf_sampled_retrievability_v1.hashing import (
    map_digest_to_unbiased_chunk_index_v1,
)

CHECKED_EPOCH = 52
PRIVATE_KEYS = tuple("0x" + value.to_bytes(32, "big").hex() for value in (1, 2, 3))
EXACT_BLOB = b"a" * 65_536 + b"b" * 65_536 + b"tail"


def _root(label: str) -> str:
    return "0x" + hashlib.sha256(label.encode("ascii")).hexdigest()


def _provider(
    index: int,
    *,
    activation_epoch: int = 40,
    revocation_epoch: int | None = None,
) -> ProviderKeyLifecycleV1:
    private_key = "0x" + (index + 1).to_bytes(32, "big").hex()
    return ProviderKeyLifecycleV1(
        provider_id=f"provider-{index}",
        key_id=f"provider-key-{index}",
        public_key=bls_public_key_hex_from_private_key_v0(private_key),
        activation_epoch=activation_epoch,
        revocation_epoch=revocation_epoch,
    )


def _policy(
    *,
    providers: tuple[ProviderKeyLifecycleV1, ...] | None = None,
    minimum_provider_responses: int = 2,
    storage_policy_hash: str | None = None,
) -> SampledRetrievabilityPolicyV1:
    return SampledRetrievabilityPolicyV1.validated(
        application_id=_root("application"),
        chain_or_domain_id=_root("domain"),
        policy_revision=7,
        activation_epoch=40,
        revocation_epoch=None,
        storage_policy_hash=storage_policy_hash or _root("storage-policy"),
        beacon_source_id=_root("beacon-source"),
        beacon_policy_hash=_root("beacon-policy"),
        minimum_retention_epochs=20,
        minimum_remaining_epochs=4,
        challenge_count=2,
        response_window_epochs=2,
        minimum_provider_responses=minimum_provider_responses,
        providers=providers or (_provider(0), _provider(1), _provider(2)),
    )


def _target(
    *, storage_policy_hash: str | None = None
) -> FullBlobRetrievabilityTargetV1:
    return derive_exact_full_blob_target_v1(
        application_id=_root("application"),
        chain_or_domain_id=_root("domain"),
        epoch_id=40,
        data_schema_id=_root("data-schema"),
        exact_blob_bytes=EXACT_BLOB,
        retention_through_epoch=70,
        storage_policy_hash=storage_policy_hash or _root("storage-policy"),
    )


def _beacon(*, commitment: str | None = None) -> BeaconCommitmentV1:
    return BeaconCommitmentV1.validated(
        source_id=_root("beacon-source"),
        policy_hash=_root("beacon-policy"),
        beacon_epoch=CHECKED_EPOCH,
        commitment=commitment or _root("beacon-52"),
    )


def _signed_response(
    *,
    policy: SampledRetrievabilityPolicyV1,
    target: FullBlobRetrievabilityTargetV1,
    beacon: BeaconCommitmentV1,
    provider_index: int,
    response_epoch: int = CHECKED_EPOCH + 1,
    mutate: Callable[[dict[str, object]], None] | None = None,
    signing_key: str | None = None,
) -> SignedProviderResponseV1:
    provider = policy.providers[provider_index]
    response_bytes = build_provider_response_bytes_v1(
        policy=policy,
        target=target,
        beacon=beacon,
        checked_epoch=CHECKED_EPOCH,
        response_epoch=response_epoch,
        provider_id=provider.provider_id,
        key_id=provider.key_id,
        exact_blob_bytes=EXACT_BLOB,
    )
    if mutate is not None:
        document = json.loads(response_bytes)
        mutate(document)
        response_bytes = canonical_json_bytes_v0(document)
    envelope = build_bls_signed_artifact_envelope_v0(
        payload_kind=SAMPLED_RETRIEVABILITY_RESPONSE_PAYLOAD_KIND_V1,
        payload_hash=response_payload_hash_v1(response_bytes),
        signer_id=provider.provider_id,
        key_id=provider.key_id,
        private_key_hex=signing_key or PRIVATE_KEYS[provider_index],
    )
    return SignedProviderResponseV1(response_bytes, envelope)


def _valid_material():
    policy = _policy()
    target = _target()
    beacon = _beacon()
    responses = tuple(
        _signed_response(
            policy=policy,
            target=target,
            beacon=beacon,
            provider_index=index,
        )
        for index in (0, 1)
    )
    evidence = build_exact_evidence_bytes_v1(
        policy=policy,
        target=target,
        beacon=beacon,
        checked_epoch=CHECKED_EPOCH,
        exact_blob_bytes=EXACT_BLOB,
        signed_responses=responses,
    )
    return policy, target, beacon, responses, evidence


def _verify(
    evidence: bytes,
    *,
    policy: SampledRetrievabilityPolicyV1 | None = None,
    target: FullBlobRetrievabilityTargetV1 | None = None,
    beacon: BeaconCommitmentV1 | None = None,
):
    return verify_exact_evidence_v1(
        evidence,
        expected_policy=policy or _policy(),
        expected_target=target or _target(),
        expected_beacon=beacon or _beacon(),
        checked_epoch=CHECKED_EPOCH,
    )


def _replace_responses(
    evidence: bytes,
    responses: tuple[SignedProviderResponseV1, ...],
) -> bytes:
    document = json.loads(evidence)
    document["responses"] = [
        {
            "response_bytes_hex": response.response_bytes.hex(),
            "signature_envelope": response.signature_envelope,
        }
        for response in responses
    ]
    return canonical_json_bytes_v0(document)


def _mutate_evidence(
    evidence: bytes,
    mutate: Callable[[dict[str, object]], None],
) -> bytes:
    document = json.loads(evidence)
    mutate(document)
    return canonical_json_bytes_v0(document)


def _assert_reject(code: str, call: Callable[[], object]) -> None:
    with pytest.raises(SampledRetrievabilityRejectV1) as captured:
        call()
    assert captured.value.code == code


def _reverse_assigned_indices(body: dict[str, object]) -> None:
    indices = body["assigned_chunk_indices"]
    assert isinstance(indices, list)
    indices.reverse()


def _duplicate_assigned_index(body: dict[str, object]) -> None:
    indices = body["assigned_chunk_indices"]
    assert isinstance(indices, list)
    assert len(indices) >= 2
    indices[1] = indices[0]


def _drop_assigned_index(body: dict[str, object]) -> None:
    indices = body["assigned_chunk_indices"]
    assert isinstance(indices, list)
    indices.pop()


def _replace_first_opening_bytes(body: dict[str, object]) -> None:
    openings = body["openings"]
    assert isinstance(openings, list)
    first = openings[0]
    assert isinstance(first, dict)
    first["chunk_bytes_hex"] = "00"


def _replace_integer_opening_index_with_bool(body: dict[str, object]) -> None:
    openings = body["openings"]
    assert isinstance(openings, list)
    for opening in openings:
        assert isinstance(opening, dict)
        observed = opening["chunk_index"]
        if type(observed) is int and observed in (0, 1):
            opening["chunk_index"] = bool(observed)
            return
    raise AssertionError("test response has no Boolean-aliasable opening index")


def _replace_nested_field(
    document: dict[str, object],
    section: str,
    field: str,
    value: object,
) -> None:
    nested = document[section]
    assert isinstance(nested, dict)
    nested[field] = value


def test_valid_exact_evidence_authenticates_bounded_sample_only() -> None:
    policy, target, beacon, _, evidence = _valid_material()

    result = _verify(evidence, policy=policy, target=target, beacon=beacon)

    assert result.authenticated_sampled_response_scoped_to_checked_epoch is True
    assert result.checked_epoch == CHECKED_EPOCH
    assert result.accepted_provider_ids == ("provider-0", "provider-1")
    assert result.policy_root == policy.policy_root
    assert result.certificate_root == target.certificate_root
    assert result.beacon_commitment == beacon.commitment
    assert result.exact_evidence_bytes == evidence
    assert result.evidence_sha256 == hashlib.sha256(evidence).hexdigest()
    assert result.governed_policy_provenance_verified is False
    assert result.governed_beacon_provenance_verified is False
    assert result.beacon_unpredictability_verified is False
    assert result.response_timing_provenance_verified is False
    assert result.provider_independence_verified is False
    assert result.continuous_availability_verified is False
    assert result.public_future_availability_verified is False
    assert result.release_authority is False
    assert result.settlement_authority is False
    assert result.production_authority is False


def test_authenticated_result_cannot_be_mutated_copied_or_serialized() -> None:
    policy, target, beacon, _, evidence = _valid_material()
    result = _verify(evidence, policy=policy, target=target, beacon=beacon)

    with pytest.raises(TypeError, match="cannot be mutated"):
        result.checked_epoch = CHECKED_EPOCH + 1
    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(result)
    with pytest.raises(TypeError, match="cannot be deep-copied"):
        copy.deepcopy(result)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(result)


def test_challenge_indices_are_deterministic_distinct_bounded_and_provider_bound() -> None:
    policy = _policy()
    target = _target()
    beacon = _beacon()

    first = derive_challenge_indices_v1(policy, target, beacon, "provider-0")
    second = derive_challenge_indices_v1(policy, target, beacon, "provider-0")
    other = derive_challenge_indices_v1(policy, target, beacon, "provider-1")

    assert first == (2, 1)
    assert first == second
    assert len(first) == policy.challenge_count
    assert len(set(first)) == len(first)
    assert all(0 <= index < target.chunk_count for index in first)
    assert first != other


def test_challenge_candidate_mapping_rejects_exact_biased_tail() -> None:
    universe_size = 1 << 256
    acceptance_limit = universe_size - (universe_size % 3)

    assert map_digest_to_unbiased_chunk_index_v1(
        (acceptance_limit - 1).to_bytes(32, "big"),
        3,
    ) == (acceptance_limit - 1) % 3
    assert (
        map_digest_to_unbiased_chunk_index_v1(
            acceptance_limit.to_bytes(32, "big"),
            3,
        )
        is None
    )
    assert map_digest_to_unbiased_chunk_index_v1(b"\xff" * 32, 2) == 1


def test_duplicate_provider_response_rejects() -> None:
    policy, target, beacon, responses, evidence = _valid_material()
    duplicate = _replace_responses(evidence, (responses[0], responses[0]))

    _assert_reject(
        "DUPLICATE_PROVIDER",
        lambda: _verify(duplicate, policy=policy, target=target, beacon=beacon),
    )


@pytest.mark.parametrize(
    ("code", "mutate"),
    [
        (
            "CHALLENGE_INDICES_MISMATCH",
            _reverse_assigned_indices,
        ),
        (
            "CHALLENGE_INDICES_MISMATCH",
            _duplicate_assigned_index,
        ),
        (
            "CHALLENGE_INDICES_MISMATCH",
            _drop_assigned_index,
        ),
        (
            "CHUNK_OPENING_MISMATCH",
            _replace_first_opening_bytes,
        ),
        (
            "CHUNK_OPENING_MISMATCH",
            _replace_integer_opening_index_with_bool,
        ),
    ],
)
def test_wrong_index_or_chunk_rejects_after_valid_provider_signature(
    code: str,
    mutate: Callable[[dict[str, object]], None],
) -> None:
    policy, target, beacon, responses, evidence = _valid_material()
    changed = _signed_response(
        policy=policy,
        target=target,
        beacon=beacon,
        provider_index=0,
        mutate=mutate,
    )
    evidence = _replace_responses(evidence, (changed, responses[1]))

    _assert_reject(
        code,
        lambda: _verify(evidence, policy=policy, target=target, beacon=beacon),
    )


def test_wrong_chunk_hash_vector_root_rejects() -> None:
    policy, target, beacon, _, evidence = _valid_material()

    def mutate(document: dict[str, object]) -> None:
        hashes = document["ordered_chunk_hashes"]
        assert isinstance(hashes, list)
        hashes[0] = _root("wrong-chunk")

    changed = _mutate_evidence(evidence, mutate)
    _assert_reject(
        "CHUNK_ROOT_MISMATCH",
        lambda: _verify(changed, policy=policy, target=target, beacon=beacon),
    )


def test_wrong_beacon_rejects() -> None:
    policy, target, beacon, _, evidence = _valid_material()
    changed = _mutate_evidence(
        evidence,
        lambda document: _replace_nested_field(
            document,
            "beacon",
            "commitment",
            _root("other-beacon"),
        ),
    )
    _assert_reject(
        "BEACON_BINDING_MISMATCH",
        lambda: _verify(changed, policy=policy, target=target, beacon=beacon),
    )


def test_wrong_deadline_rejects_after_valid_provider_signature() -> None:
    policy, target, beacon, responses, evidence = _valid_material()
    changed = _signed_response(
        policy=policy,
        target=target,
        beacon=beacon,
        provider_index=0,
        mutate=lambda body: body.__setitem__("response_deadline_epoch", CHECKED_EPOCH + 3),
    )
    evidence = _replace_responses(evidence, (changed, responses[1]))
    _assert_reject(
        "RESPONSE_BINDING_MISMATCH",
        lambda: _verify(evidence, policy=policy, target=target, beacon=beacon),
    )


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("application_id", _root("wrong-application")),
        ("chain_or_domain_id", _root("wrong-domain")),
        ("epoch_id", 41),
        ("data_root", _root("wrong-data-root")),
        ("chunk_root", _root("wrong-chunk-root")),
        ("policy_root", _root("wrong-policy-root")),
        ("retention_through_epoch", 71),
    ],
)
def test_signed_response_binds_scope_roots_policy_and_retention(
    field: str,
    value: object,
) -> None:
    policy, target, beacon, responses, evidence = _valid_material()
    changed = _signed_response(
        policy=policy,
        target=target,
        beacon=beacon,
        provider_index=0,
        mutate=lambda body: body.__setitem__(field, value),
    )
    evidence = _replace_responses(evidence, (changed, responses[1]))
    _assert_reject(
        "RESPONSE_BINDING_MISMATCH",
        lambda: _verify(evidence, policy=policy, target=target, beacon=beacon),
    )


def test_late_response_rejects() -> None:
    policy, target, beacon, responses, evidence = _valid_material()
    late = _signed_response(
        policy=policy,
        target=target,
        beacon=beacon,
        provider_index=0,
        response_epoch=CHECKED_EPOCH + 3,
    )
    evidence = _replace_responses(evidence, (late, responses[1]))
    _assert_reject(
        "RESPONSE_DEADLINE_EXCEEDED",
        lambda: _verify(evidence, policy=policy, target=target, beacon=beacon),
    )


def test_invalid_signature_rejects() -> None:
    policy, target, beacon, responses, evidence = _valid_material()
    forged = _signed_response(
        policy=policy,
        target=target,
        beacon=beacon,
        provider_index=0,
        signing_key=PRIVATE_KEYS[2],
    )
    evidence = _replace_responses(evidence, (forged, responses[1]))
    _assert_reject(
        "SIGNATURE_INVALID",
        lambda: _verify(evidence, policy=policy, target=target, beacon=beacon),
    )


def test_signed_artifact_payload_kind_allowlist_remains_closed() -> None:
    with pytest.raises(ValueError, match="payload_kind is not supported"):
        build_bls_signed_artifact_envelope_v0(
            payload_kind="zrpf_unknown_retrievability_response",
            payload_hash=_root("unknown-payload"),
            signer_id="provider-0",
            key_id="provider-key-0",
            private_key_hex=PRIVATE_KEYS[0],
        )


def test_quorum_threshold_rejects() -> None:
    policy, target, beacon, responses, evidence = _valid_material()
    evidence = _replace_responses(evidence, (responses[0],))
    _assert_reject(
        "PROVIDER_QUORUM_NOT_MET",
        lambda: _verify(evidence, policy=policy, target=target, beacon=beacon),
    )


def test_policy_substitution_rejects() -> None:
    policy, target, beacon, _, evidence = _valid_material()
    other_policy = _policy(storage_policy_hash=_root("other-storage-policy"))
    _assert_reject(
        "POLICY_BINDING_MISMATCH",
        lambda: _verify(evidence, policy=other_policy, target=target, beacon=beacon),
    )
    assert policy.policy_root != other_policy.policy_root


@pytest.mark.parametrize(
    "provider",
    [
        _provider(1, activation_epoch=CHECKED_EPOCH + 1),
        _provider(1, revocation_epoch=CHECKED_EPOCH),
        _provider(1, revocation_epoch=CHECKED_EPOCH + 1),
    ],
)
def test_provider_must_be_active_at_checked_epoch(provider: ProviderKeyLifecycleV1) -> None:
    providers = (_provider(0), provider, _provider(2))
    policy = _policy(providers=providers)
    target = _target()
    beacon = _beacon()
    responses = tuple(
        _signed_response(
            policy=policy,
            target=target,
            beacon=beacon,
            provider_index=index,
        )
        for index in (0, 1)
    )
    evidence = build_exact_evidence_bytes_v1(
        policy=policy,
        target=target,
        beacon=beacon,
        checked_epoch=CHECKED_EPOCH,
        exact_blob_bytes=EXACT_BLOB,
        signed_responses=responses,
    )
    _assert_reject(
        "PROVIDER_NOT_ACTIVE",
        lambda: _verify(evidence, policy=policy, target=target, beacon=beacon),
    )


def test_policy_rejects_overlapping_keys_for_one_provider_and_duplicate_pubkeys() -> None:
    overlapping = ProviderKeyLifecycleV1(
        provider_id="provider-0",
        key_id="rotated-key",
        public_key=bls_public_key_hex_from_private_key_v0(PRIVATE_KEYS[2]),
        activation_epoch=45,
        revocation_epoch=None,
    )
    with pytest.raises(ValueError, match="overlapping provider key lifecycles"):
        _policy(providers=(_provider(0), overlapping, _provider(1)))

    duplicate_key = ProviderKeyLifecycleV1(
        provider_id="provider-9",
        key_id="provider-key-9",
        public_key=_provider(0).public_key,
        activation_epoch=40,
        revocation_epoch=None,
    )
    with pytest.raises(ValueError, match="duplicate provider public key"):
        _policy(providers=(_provider(0), _provider(1), duplicate_key))

    with pytest.raises(ValueError, match="provider count exceeds"):
        _policy(
            providers=tuple(_provider(index) for index in range(9)),
            minimum_provider_responses=1,
        )


def test_policy_and_retention_lifecycle_rejects() -> None:
    policy, target, beacon, _, evidence = _valid_material()
    revoked = SampledRetrievabilityPolicyV1.validated(
        **{
            **policy.constructor_fields(),
            "revocation_epoch": CHECKED_EPOCH,
        }
    )
    _assert_reject(
        "POLICY_NOT_ACTIVE",
        lambda: _verify(evidence, policy=revoked, target=target, beacon=beacon),
    )

    revoked_during_response = SampledRetrievabilityPolicyV1.validated(
        **{
            **policy.constructor_fields(),
            "revocation_epoch": CHECKED_EPOCH + 1,
        }
    )
    response = _signed_response(
        policy=revoked_during_response,
        target=target,
        beacon=beacon,
        provider_index=0,
    )
    second = _signed_response(
        policy=revoked_during_response,
        target=target,
        beacon=beacon,
        provider_index=1,
    )
    revoked_response_evidence = build_exact_evidence_bytes_v1(
        policy=revoked_during_response,
        target=target,
        beacon=beacon,
        checked_epoch=CHECKED_EPOCH,
        exact_blob_bytes=EXACT_BLOB,
        signed_responses=(response, second),
    )
    _assert_reject(
        "POLICY_NOT_ACTIVE",
        lambda: _verify(
            revoked_response_evidence,
            policy=revoked_during_response,
            target=target,
            beacon=beacon,
        ),
    )

    short_target = derive_exact_full_blob_target_v1(
        application_id=_root("application"),
        chain_or_domain_id=_root("domain"),
        epoch_id=40,
        data_schema_id=_root("data-schema"),
        exact_blob_bytes=EXACT_BLOB,
        retention_through_epoch=CHECKED_EPOCH + 1,
        storage_policy_hash=_root("storage-policy"),
    )
    _assert_reject(
        "RETENTION_INSUFFICIENT",
        lambda: _verify(evidence, policy=policy, target=short_target, beacon=beacon),
    )


def test_evidence_requires_exact_canonical_bytes_and_false_broad_claims() -> None:
    policy, target, beacon, _, evidence = _valid_material()
    _assert_reject(
        "NONCANONICAL_EVIDENCE",
        lambda: _verify(evidence + b"\n", policy=policy, target=target, beacon=beacon),
    )
    expanded = _mutate_evidence(
        evidence,
        lambda document: _replace_nested_field(
            document,
            "authority",
            "production_authority",
            True,
        ),
    )
    _assert_reject(
        "AUTHORITY_CLAIM_MISMATCH",
        lambda: _verify(expanded, policy=policy, target=target, beacon=beacon),
    )
    integer_false = _mutate_evidence(
        evidence,
        lambda document: _replace_nested_field(
            document,
            "authority",
            "production_authority",
            0,
        ),
    )
    _assert_reject(
        "AUTHORITY_CLAIM_MISMATCH",
        lambda: _verify(integer_false, policy=policy, target=target, beacon=beacon),
    )


def test_evidence_codec_rejects_duplicate_unknown_and_float_fields() -> None:
    policy, target, beacon, _, evidence = _valid_material()
    duplicate = b'{"schema":"shadow",' + evidence[1:]
    unknown = _mutate_evidence(
        evidence,
        lambda document: document.__setitem__("unknown_field", False),
    )
    floating = evidence.replace(b'"checked_epoch":52', b'"checked_epoch":52.0', 1)

    for malformed in (duplicate, unknown, floating):
        def verify_malformed(value: bytes = malformed) -> object:
            return _verify(
                value,
                policy=policy,
                target=target,
                beacon=beacon,
            )

        _assert_reject(
            "NONCANONICAL_EVIDENCE",
            verify_malformed,
        )


def test_signed_unknown_response_field_rejects_before_authority() -> None:
    policy, target, beacon, responses, evidence = _valid_material()
    response_bytes = build_provider_response_bytes_v1(
        policy=policy,
        target=target,
        beacon=beacon,
        checked_epoch=CHECKED_EPOCH,
        response_epoch=CHECKED_EPOCH + 1,
        provider_id=policy.providers[0].provider_id,
        key_id=policy.providers[0].key_id,
        exact_blob_bytes=EXACT_BLOB,
    )
    response_document = json.loads(response_bytes)
    response_document["unknown_field"] = False
    response_bytes = canonical_json_bytes_v0(response_document)
    envelope = build_bls_signed_artifact_envelope_v0(
        payload_kind=SAMPLED_RETRIEVABILITY_RESPONSE_PAYLOAD_KIND_V1,
        payload_hash=hash_v0(
            "zrpf_sampled_retrievability_response_payload_v1",
            response_bytes,
        ),
        signer_id=policy.providers[0].provider_id,
        key_id=policy.providers[0].key_id,
        private_key_hex=PRIVATE_KEYS[0],
    )
    changed = SignedProviderResponseV1(response_bytes, envelope)
    evidence = _replace_responses(evidence, (changed, responses[1]))

    _assert_reject(
        "NONCANONICAL_RESPONSE",
        lambda: _verify(evidence, policy=policy, target=target, beacon=beacon),
    )


def test_exact_full_blob_target_matches_existing_hash_domains() -> None:
    target = _target()

    assert target.chunk_count == 3
    assert target.chunk_size == 65_536
    assert target.blob_length == len(EXACT_BLOB)
    assert target.data_root != target.chunk_root
    assert target.certificate_root not in {
        target.data_root,
        target.chunk_root,
        target.storage_policy_hash,
    }

    retained = derive_exact_full_blob_target_v1(
        application_id="0x" + "01" * 32,
        chain_or_domain_id="0x" + "02" * 32,
        epoch_id=7,
        data_schema_id="0x" + "03" * 32,
        exact_blob_bytes=b"locally present governed replay blob",
        retention_through_epoch=30,
        storage_policy_hash="0x" + "04" * 32,
    )
    assert retained.data_root == (
        "0x43f126a24dde3f2d200094c9c8805005f40eafe5b10f575c044be27a11f8468d"
    )
    assert retained.chunk_root == (
        "0xa2cca633f2ade5c3350416c3ad0ff3c62a94702f2ec3ff960d90f0de82f580e5"
    )
    assert retained.certificate_root == (
        "0x6eda12e380d4c9a72b0f85e35bf1542622356ecccd6c273679b65b63db2594d3"
    )

    with pytest.raises(ValueError, match="certificate version 1"):
        replace(target, certificate_version=True)
    with pytest.raises(ValueError, match="chunk_size must be 65536"):
        replace(target, chunk_size=65_536.0)

"""CBC tests for governed Spot V7 operational policy V3 provenance."""

from __future__ import annotations

import copy
import hashlib
import json
import pickle
from dataclasses import replace

import pytest

from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedOperationalPolicyMaterialV2,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    BeaconPolicyV1,
    _GovernedOperationalPolicyMaterialV3,
    _GovernedSpotV7OperationalPolicyV3,
    derive_zeno_ledger_checkpoint_beacon_source_id_v1,
)
from src.integration._zrpf_spot_v7_zeno_ledger_finality_contract import (
    derive_zeno_ledger_finality_network_id_v1,
    derive_zeno_ledger_finality_protocol_id_v2,
    derive_zeno_ledger_finality_protocol_id_v3,
)
from src.integration.zeno_ledger_signature import (
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zrpf_sampled_retrievability_v1.model import (
    ProviderKeyLifecycleV1,
    SampledRetrievabilityPolicyV1,
)
from src.integration.zrpf_spot_v7_operational_policy_provenance_v2 import (
    _AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V2,
    SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V2,
    SpotV7OperationalPolicyProvenanceErrorV2,
    SpotV7OperationalPolicyReleasePinsV2,
    _AuthenticatedSpotV7OperationalPolicyReleasePinsV2,
    load_governed_spot_v7_operational_policy_v3,
    spot_v7_operational_policy_manifest_bytes_v2,
    spot_v7_operational_policy_manifest_payload_hash_v2,
)

CHAIN_ID = "zeno-ledger-main-v1"
POLICY_REVISION = 8
POLICY_ACTIVATION_EPOCH = 20
REGISTRY_ID = "zrpf-spot-v7-operational-policy-v2-signers"
REGISTRY_REVISION = 4
PRIVATE_KEY = "0x" + (11).to_bytes(32, "big").hex()


def _root(label: str) -> str:
    return "0x" + hashlib.sha256(label.encode("ascii")).hexdigest()


def _base_material() -> _GovernedOperationalPolicyMaterialV2:
    return _GovernedOperationalPolicyMaterialV2(
        application_id=_root("application"),
        chain_or_domain_id=_root("domain"),
        data_schema_id=_root("data-schema"),
        storage_policy_hash=_root("storage-policy"),
        minimum_retention_epochs=10,
        minimum_remaining_epochs=2,
        maximum_blob_bytes=1_048_576,
        finality_network_id=derive_zeno_ledger_finality_network_id_v1(CHAIN_ID),
        finality_protocol_id=derive_zeno_ledger_finality_protocol_id_v3(),
        external_finality_policy_hash=_root("external-finality-policy"),
        finality_verifier_set_root=_root("finality-verifier-set"),
        genesis_application_checkpoint_sequence=0,
        genesis_application_checkpoint_hash=_root("genesis-checkpoint"),
    )


def _beacon_policy(
    *,
    source_epoch_lag: int = 1,
    activation_epoch: int = POLICY_ACTIVATION_EPOCH,
) -> BeaconPolicyV1:
    base = _base_material()
    return BeaconPolicyV1(
        policy_revision=1,
        activation_epoch=activation_epoch,
        revocation_epoch=None,
        source_id=derive_zeno_ledger_checkpoint_beacon_source_id_v1(CHAIN_ID),
        source_network_id=base.finality_network_id,
        source_protocol_id=derive_zeno_ledger_finality_protocol_id_v2(),
        source_epoch_lag=source_epoch_lag,
    )


def _providers() -> tuple[ProviderKeyLifecycleV1, ...]:
    return (
        ProviderKeyLifecycleV1(
            provider_id="provider-a",
            key_id="key-a",
            public_key=bls_public_key_hex_from_private_key_v0(
                "0x" + (21).to_bytes(32, "big").hex()
            ),
            activation_epoch=10,
            revocation_epoch=None,
        ),
        ProviderKeyLifecycleV1(
            provider_id="provider-b",
            key_id="key-b",
            public_key=bls_public_key_hex_from_private_key_v0(
                "0x" + (22).to_bytes(32, "big").hex()
            ),
            activation_epoch=10,
            revocation_epoch=None,
        ),
    )


def _sampled_policy(
    *,
    beacon: BeaconPolicyV1 | None = None,
    providers: tuple[ProviderKeyLifecycleV1, ...] | None = None,
) -> SampledRetrievabilityPolicyV1:
    base = _base_material()
    selected_beacon = beacon or _beacon_policy()
    return SampledRetrievabilityPolicyV1.validated(
        application_id=base.application_id,
        chain_or_domain_id=base.chain_or_domain_id,
        policy_revision=1,
        activation_epoch=POLICY_ACTIVATION_EPOCH,
        revocation_epoch=None,
        storage_policy_hash=base.storage_policy_hash,
        beacon_source_id=selected_beacon.source_id,
        beacon_policy_hash=selected_beacon.policy_root,
        minimum_retention_epochs=base.minimum_retention_epochs,
        minimum_remaining_epochs=base.minimum_remaining_epochs,
        challenge_count=2,
        response_window_epochs=2,
        minimum_provider_responses=2,
        providers=providers or _providers(),
    )


def _material(
    *,
    base: _GovernedOperationalPolicyMaterialV2 | None = None,
    beacon: BeaconPolicyV1 | None = None,
    sampled: SampledRetrievabilityPolicyV1 | None = None,
) -> _GovernedOperationalPolicyMaterialV3:
    selected_beacon = beacon or _beacon_policy()
    return _GovernedOperationalPolicyMaterialV3(
        base_material=base or _base_material(),
        zeno_ledger_chain_id=CHAIN_ID,
        sampled_retrievability_policy=(sampled or _sampled_policy(beacon=selected_beacon)),
        beacon_policy=selected_beacon,
    )


def _registry() -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id=REGISTRY_ID,
        payload_kind=SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V2,
        threshold=1,
        signers=[
            {
                "signer_id": "release-signer-0",
                "key_id": "release-key-0",
                "public_key": bls_public_key_hex_from_private_key_v0(PRIVATE_KEY),
                "weight": 1,
                "status": "active",
            }
        ],
    )


def _manifest(
    registry: dict[str, object],
    *,
    material: _GovernedOperationalPolicyMaterialV3 | None = None,
) -> bytes:
    return spot_v7_operational_policy_manifest_bytes_v2(
        material or _material(),
        policy_revision=POLICY_REVISION,
        policy_activation_epoch=POLICY_ACTIVATION_EPOCH,
        policy_revocation_epoch=None,
        signer_registry_id=REGISTRY_ID,
        signer_registry_hash=str(registry["registry_hash"]),
        signer_registry_revision=REGISTRY_REVISION,
        signer_registry_activation_epoch=10,
        signer_registry_revocation_epoch=None,
    )


def _envelopes(raw: bytes) -> tuple[dict[str, object], ...]:
    return (
        build_bls_signed_artifact_envelope_v0(
            payload_kind=SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V2,
            payload_hash=spot_v7_operational_policy_manifest_payload_hash_v2(raw),
            signer_id="release-signer-0",
            key_id="release-key-0",
            private_key_hex=PRIVATE_KEY,
        ),
    )


def _load(
    raw: bytes,
    registry: dict[str, object],
    *,
    expected_manifest_sha256: str | None = None,
    pin_material: _GovernedOperationalPolicyMaterialV3 | None = None,
) -> _GovernedSpotV7OperationalPolicyV3:
    material = pin_material or _material()
    pins = SpotV7OperationalPolicyReleasePinsV2(
        manifest_sha256=(expected_manifest_sha256 or hashlib.sha256(raw).hexdigest()),
        application_id=material.base_material.application_id,
        chain_or_domain_id=material.base_material.chain_or_domain_id,
        zeno_ledger_chain_id=CHAIN_ID,
        policy_revision=POLICY_REVISION,
        sampled_policy_root=material.sampled_retrievability_policy.policy_root,
        beacon_policy_root=material.beacon_policy.policy_root,
        signer_registry_id=REGISTRY_ID,
        signer_registry_hash=str(registry["registry_hash"]),
        signer_registry_revision=REGISTRY_REVISION,
    )
    authenticated = _AuthenticatedSpotV7OperationalPolicyReleasePinsV2(
        pins,
        trusted_evaluation_epoch=POLICY_ACTIVATION_EPOCH,
        seal=_AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V2,
    )
    return load_governed_spot_v7_operational_policy_v3(
        raw,
        authenticated_release=authenticated,
        signer_registry=registry,
        signature_envelopes=_envelopes(raw),
    )


def test_v3_manifest_mints_governed_sampled_policy_with_exact_chain_binding() -> None:
    registry = _registry()
    raw = _manifest(registry)

    policy = _load(raw, registry)

    assert type(policy) is _GovernedSpotV7OperationalPolicyV3
    projection = policy._projection_for_governed_da_v2()
    assert projection.application_id == _root("application")
    assert projection.chain_or_domain_id == _root("domain")
    assert projection.zeno_ledger_chain_id == CHAIN_ID
    assert projection.sampled_policy_root == _sampled_policy().policy_root
    assert projection.beacon_policy_root == _beacon_policy().policy_root
    assert policy.sampled_policy_governance_provenance_verified is True
    assert policy.current_operational_policy_release_head_verified is False
    assert policy.beacon_unpredictability_verified is False
    assert policy.provider_independence_verified is False
    assert policy.continuous_availability_verified is False
    assert policy.public_future_availability_verified is False
    assert policy.release_authority is False
    assert policy.settlement_authority is False
    assert policy.production_authority is False


def test_signed_policy_separates_settlement_v3_from_lagged_beacon_source_v2() -> None:
    registry = _registry()
    policy = _load(_manifest(registry), registry)

    settlement_policy = policy._base_store_policy_for_governed_beacon_v1()
    beacon_policy = policy._beacon_policy_for_governed_da_v2()
    assert settlement_policy.finality_protocol_id == (
        derive_zeno_ledger_finality_protocol_id_v3()
    )
    assert beacon_policy.source_protocol_id == (
        derive_zeno_ledger_finality_protocol_id_v2()
    )
    assert settlement_policy.finality_protocol_id != beacon_policy.source_protocol_id


def test_v3_material_rejects_v2_settlement_finality_protocol() -> None:
    legacy_settlement_policy = replace(
        _base_material(),
        finality_protocol_id=derive_zeno_ledger_finality_protocol_id_v2(),
    )

    with pytest.raises(ValueError, match="settlement finality protocol mismatch"):
        _material(base=legacy_settlement_policy)


def test_v3_manifest_is_canonical_and_hash_stable() -> None:
    registry = _registry()
    raw = _manifest(registry)

    assert json.dumps(json.loads(raw), sort_keys=True, separators=(",", ":")).encode() == raw
    assert len(raw) < 32 * 1024
    assert spot_v7_operational_policy_manifest_payload_hash_v2(raw).startswith("0x")
    assert len(spot_v7_operational_policy_manifest_payload_hash_v2(raw)) == 66


@pytest.mark.parametrize(
    ("path", "value"),
    (
        (("policy_context", "policy_revision"), True),
        (("policy_context", "policy_revision"), 1.5),
        (("policy_context", "policy_revision"), -1),
        (("policy_context", "policy_revision"), 1 << 64),
        (("policy_material", "zeno_ledger_chain_id"), ""),
        (("policy_material", "beacon_policy", "source_epoch_lag"), 0),
        (("policy_material", "sampled_retrievability_policy", "challenge_count"), True),
    ),
)
def test_v3_parser_rejects_wrong_types_and_bounds(
    path: tuple[str, ...],
    value: object,
) -> None:
    registry = _registry()
    document = json.loads(_manifest(registry))
    cursor = document
    for key in path[:-1]:
        cursor = cursor[key]
    cursor[path[-1]] = value
    raw = json.dumps(document, sort_keys=True, separators=(",", ":")).encode()

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV2):
        spot_v7_operational_policy_manifest_payload_hash_v2(raw)


def test_v3_parser_rejects_unknown_duplicate_and_noncanonical_json() -> None:
    registry = _registry()
    raw = _manifest(registry)
    document = json.loads(raw)
    document["unknown"] = 1
    unknown = json.dumps(document, sort_keys=True, separators=(",", ":")).encode()
    duplicate = raw[:-1] + b',"schema":"duplicate"}'
    noncanonical = json.dumps(json.loads(raw), indent=2).encode()

    for rejected in (unknown, duplicate, noncanonical):
        with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV2):
            spot_v7_operational_policy_manifest_payload_hash_v2(rejected)


def test_coherently_resigned_nested_policy_mutation_rejects_trusted_digest() -> None:
    registry = _registry()
    trusted = _manifest(registry)
    mutated_beacon = replace(_beacon_policy(), source_epoch_lag=2)
    changed = _manifest(registry, material=_material(beacon=mutated_beacon))

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV2) as captured:
        _load(
            changed,
            registry,
            expected_manifest_sha256=hashlib.sha256(trusted).hexdigest(),
        )

    assert captured.value.code == "MANIFEST_SHA256_MISMATCH"


@pytest.mark.parametrize(
    "mutation",
    (
        "application",
        "domain",
        "storage",
        "network",
        "protocol",
        "source",
        "sampled_beacon_root",
        "provider_key",
    ),
)
def test_v3_material_rejects_cross_binding_mutations(mutation: str) -> None:
    base = _base_material()
    beacon = _beacon_policy()
    sampled = _sampled_policy(beacon=beacon)
    chain_id = CHAIN_ID
    if mutation == "application":
        sampled = replace(sampled, application_id=_root("other-app"))
    elif mutation == "domain":
        sampled = replace(sampled, chain_or_domain_id=_root("other-domain"))
    elif mutation == "storage":
        sampled = replace(sampled, storage_policy_hash=_root("other-storage"))
    elif mutation == "network":
        beacon = replace(beacon, source_network_id=_root("other-network"))
    elif mutation == "protocol":
        beacon = replace(beacon, source_protocol_id=_root("other-protocol"))
    elif mutation == "source":
        beacon = replace(beacon, source_id=_root("other-source"))
    elif mutation == "sampled_beacon_root":
        sampled = replace(sampled, beacon_policy_hash=_root("other-beacon-policy"))
    elif mutation == "provider_key":
        duplicate = replace(_providers()[1], public_key=_providers()[0].public_key)
        with pytest.raises(ValueError, match="duplicate provider public key"):
            _sampled_policy(providers=(_providers()[0], duplicate))
        return

    with pytest.raises(ValueError):
        _GovernedOperationalPolicyMaterialV3(
            base_material=base,
            zeno_ledger_chain_id=chain_id,
            sampled_retrievability_policy=sampled,
            beacon_policy=beacon,
        )


def test_v3_policy_capability_is_nontransferable_and_rechecks_provenance() -> None:
    registry = _registry()
    policy = _load(_manifest(registry), registry)

    with pytest.raises(TypeError):
        copy.copy(policy)
    with pytest.raises(TypeError):
        copy.deepcopy(policy)
    with pytest.raises(TypeError):
        pickle.dumps(policy)
    with pytest.raises(TypeError):
        policy._seal = object()  # type: ignore[assignment]

    object.__setattr__(policy._provenance, "exact_evidence_bytes", b"forged")
    with pytest.raises(ValueError, match="provenance drift"):
        policy._projection_for_governed_da_v2()


def test_v3_loader_rejects_inactive_nested_policy_and_provider_lifecycles() -> None:
    registry = _registry()
    future_beacon = _beacon_policy(activation_epoch=POLICY_ACTIVATION_EPOCH + 1)
    future_provider = replace(_providers()[0], activation_epoch=POLICY_ACTIVATION_EPOCH + 1)

    with pytest.raises(ValueError):
        _material(beacon=future_beacon)

    sampled = _sampled_policy(providers=(future_provider, _providers()[1]))
    material = _material(sampled=sampled)
    raw = _manifest(registry, material=material)
    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV2) as captured:
        _load(raw, registry, pin_material=material)
    assert captured.value.code == "NESTED_POLICY_INACTIVE"

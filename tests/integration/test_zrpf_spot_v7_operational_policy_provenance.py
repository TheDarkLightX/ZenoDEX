from __future__ import annotations

import hashlib
import json
from typing import Callable, cast

import pytest

from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedOperationalPolicyMaterialV2,
    _GovernedSpotV7OperationalPolicyV2,
)
from src.integration.zeno_ledger_signature import (
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zrpf_spot_v7_operational_policy_provenance import (
    _AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V1,
    SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V1,
    SpotV7OperationalPolicyProvenanceErrorV1,
    SpotV7OperationalPolicyReleasePinsV1,
    _AuthenticatedSpotV7OperationalPolicyReleasePinsV1,
    load_governed_spot_v7_operational_policy_v2,
    spot_v7_operational_policy_manifest_bytes_v1,
    spot_v7_operational_policy_manifest_payload_hash_v1,
)

POLICY_REVISION = 7
POLICY_ACTIVATION_EPOCH = 20
REGISTRY_ID = "zrpf-spot-v7-operational-policy-signers"
REGISTRY_REVISION = 3
REGISTRY_ACTIVATION_EPOCH = 10
PRIVATE_KEY = "0x" + (1).to_bytes(32, "big").hex()
ATTACKER_PRIVATE_KEY = "0x" + (2).to_bytes(32, "big").hex()


def _root(label: str) -> str:
    return "0x" + hashlib.sha256(label.encode("ascii")).hexdigest()


def _material(*, storage_policy_hash: str | None = None) -> _GovernedOperationalPolicyMaterialV2:
    return _GovernedOperationalPolicyMaterialV2(
        application_id=_root("application"),
        chain_or_domain_id=_root("domain"),
        data_schema_id=_root("data-schema"),
        storage_policy_hash=storage_policy_hash or _root("storage-policy"),
        minimum_retention_epochs=10,
        minimum_remaining_epochs=2,
        maximum_blob_bytes=1_048_576,
        finality_network_id=_root("finality-network"),
        finality_protocol_id=_root("finality-protocol"),
        external_finality_policy_hash=_root("external-finality-policy"),
        finality_verifier_set_root=_root("finality-verifier-set"),
        genesis_application_checkpoint_sequence=0,
        genesis_application_checkpoint_hash=_root("genesis-checkpoint"),
    )


def _registry(*, private_key: str = PRIVATE_KEY) -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id=REGISTRY_ID,
        payload_kind=SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V1,
        threshold=1,
        signers=[
            {
                "signer_id": "release-signer-0",
                "key_id": "release-key-0",
                "public_key": bls_public_key_hex_from_private_key_v0(private_key),
                "weight": 1,
                "status": "active",
            }
        ],
    )


def _manifest(
    registry: dict[str, object],
    *,
    material: _GovernedOperationalPolicyMaterialV2 | None = None,
    policy_activation_epoch: int = POLICY_ACTIVATION_EPOCH,
    policy_revocation_epoch: int | None = None,
    registry_activation_epoch: int = REGISTRY_ACTIVATION_EPOCH,
    registry_revocation_epoch: int | None = None,
) -> bytes:
    return spot_v7_operational_policy_manifest_bytes_v1(
        material or _material(),
        policy_revision=POLICY_REVISION,
        policy_activation_epoch=policy_activation_epoch,
        policy_revocation_epoch=policy_revocation_epoch,
        signer_registry_id=REGISTRY_ID,
        signer_registry_hash=str(registry["registry_hash"]),
        signer_registry_revision=REGISTRY_REVISION,
        signer_registry_activation_epoch=registry_activation_epoch,
        signer_registry_revocation_epoch=registry_revocation_epoch,
    )


def _envelopes(raw: bytes, *, private_key: str = PRIVATE_KEY) -> tuple[dict[str, object], ...]:
    return (
        build_bls_signed_artifact_envelope_v0(
            payload_kind=SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V1,
            payload_hash=spot_v7_operational_policy_manifest_payload_hash_v1(raw),
            signer_id="release-signer-0",
            key_id="release-key-0",
            private_key_hex=private_key,
        ),
    )


def _load(
    raw: bytes,
    registry: dict[str, object],
    envelopes: tuple[dict[str, object], ...],
    *,
    expected_manifest_sha256: str | None = None,
    expected_registry_hash: str | None = None,
    expected_policy_revision: int = POLICY_REVISION,
    expected_registry_revision: int = REGISTRY_REVISION,
    evaluation_epoch: int = POLICY_ACTIVATION_EPOCH,
) -> _GovernedSpotV7OperationalPolicyV2:
    # This test-only construction exercises the post-bootstrap verifier. The
    # architecture ratchet rejects these private names from every production
    # module, and this tranche intentionally provides no production mint.
    pins = SpotV7OperationalPolicyReleasePinsV1(
        manifest_sha256=(expected_manifest_sha256 or hashlib.sha256(raw).hexdigest()),
        application_id=_root("application"),
        chain_or_domain_id=_root("domain"),
        policy_revision=expected_policy_revision,
        signer_registry_id=REGISTRY_ID,
        signer_registry_hash=(expected_registry_hash or str(registry["registry_hash"])),
        signer_registry_revision=expected_registry_revision,
    )
    return load_governed_spot_v7_operational_policy_v2(
        raw,
        authenticated_release=_AuthenticatedSpotV7OperationalPolicyReleasePinsV1(
            pins,
            trusted_evaluation_epoch=evaluation_epoch,
            seal=_AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V1,
        ),
        signer_registry=registry,
        signature_envelopes=envelopes,
    )


def test_loader_mints_exact_governed_policy_after_pinned_bls_quorum() -> None:
    registry = _registry()
    raw = _manifest(registry)

    policy = _load(raw, registry, _envelopes(raw))

    assert type(policy) is _GovernedSpotV7OperationalPolicyV2
    assert policy._policy_for_atomic_store() == _material()._to_authority_false_store_policy()
    provenance = policy._policy_provenance_for_atomic_store()
    evidence = json.loads(provenance.exact_evidence_bytes)
    assert provenance.evidence_root == "0x" + hashlib.sha256(
        provenance.exact_evidence_bytes
    ).hexdigest()
    assert provenance.manifest_sha256 == hashlib.sha256(raw).hexdigest()
    assert provenance.signer_registry_hash == registry["registry_hash"]
    assert evidence["manifest_bytes_hex"] == raw.hex()
    assert evidence["signature_quorum_report"]["quorum_report_hash"] == (
        provenance.signature_quorum_report_hash
    )
    assert policy.settlement_authority is False
    assert policy.production_authority is False


def test_loader_canonicalizes_signature_set_order_in_retained_provenance() -> None:
    registry = build_signer_registry_v0(
        registry_id=REGISTRY_ID,
        payload_kind=SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V1,
        threshold=2,
        signers=[
            {
                "signer_id": "release-signer-0",
                "key_id": "release-key-0",
                "public_key": bls_public_key_hex_from_private_key_v0(PRIVATE_KEY),
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "release-signer-1",
                "key_id": "release-key-1",
                "public_key": bls_public_key_hex_from_private_key_v0(ATTACKER_PRIVATE_KEY),
                "weight": 1,
                "status": "active",
            },
        ],
    )
    raw = _manifest(registry)
    payload_hash = spot_v7_operational_policy_manifest_payload_hash_v1(raw)
    envelopes = (
        build_bls_signed_artifact_envelope_v0(
            payload_kind=SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V1,
            payload_hash=payload_hash,
            signer_id="release-signer-0",
            key_id="release-key-0",
            private_key_hex=PRIVATE_KEY,
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V1,
            payload_hash=payload_hash,
            signer_id="release-signer-1",
            key_id="release-key-1",
            private_key_hex=ATTACKER_PRIVATE_KEY,
        ),
    )

    forward = _load(raw, registry, envelopes)
    reverse = _load(raw, registry, tuple(reversed(envelopes)))

    assert (
        forward._policy_provenance_for_atomic_store().evidence_root
        == reverse._policy_provenance_for_atomic_store().evidence_root
    )


def test_policy_rechecks_retained_provenance_before_atomic_handoff() -> None:
    registry = _registry()
    raw = _manifest(registry)
    policy = _load(raw, registry, _envelopes(raw))
    provenance = policy._policy_provenance_for_atomic_store()
    object.__setattr__(provenance, "exact_evidence_bytes", b"forged")

    with pytest.raises(ValueError, match="provenance drift"):
        policy._policy_provenance_for_atomic_store()


def test_manifest_builder_is_canonical_and_payload_hash_is_deterministic() -> None:
    registry = _registry()
    raw = _manifest(registry)

    assert (
        json.dumps(
            json.loads(raw),
            sort_keys=True,
            separators=(",", ":"),
        ).encode("ascii")
        == raw
    )
    assert hashlib.sha256(raw).hexdigest() == (
        "4b7e9d910b324c59110bbf2fd4fc09bca8158f157823ec5b333edab84418c61a"
    )
    assert spot_v7_operational_policy_manifest_payload_hash_v1(raw) == (
        "0x6cd27a5b71bbf5892a0937223525bdea269ae109f1b0445b00a15572fe4471ff"
    )


def test_loader_rejects_coherently_resigned_policy_edit_against_trusted_digest() -> None:
    registry = _registry()
    trusted_raw = _manifest(registry)
    changed_raw = _manifest(
        registry,
        material=_material(storage_policy_hash=_root("attacker-storage-policy")),
    )

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV1) as captured:
        _load(
            changed_raw,
            registry,
            _envelopes(changed_raw),
            expected_manifest_sha256=hashlib.sha256(trusted_raw).hexdigest(),
        )

    assert captured.value.code == "MANIFEST_SHA256_MISMATCH"


def test_loader_rejects_coherent_registry_substitution_against_trusted_pin() -> None:
    trusted_registry = _registry()
    attacker_registry = _registry(private_key=ATTACKER_PRIVATE_KEY)
    attacker_raw = _manifest(attacker_registry)

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV1) as captured:
        _load(
            attacker_raw,
            attacker_registry,
            _envelopes(attacker_raw, private_key=ATTACKER_PRIVATE_KEY),
            expected_registry_hash=str(trusted_registry["registry_hash"]),
        )

    assert captured.value.code == "REGISTRY_HASH_MISMATCH"


@pytest.mark.parametrize(
    ("expected_policy_revision", "expected_registry_revision", "code"),
    (
        (POLICY_REVISION + 1, REGISTRY_REVISION, "POLICY_REVISION_MISMATCH"),
        (POLICY_REVISION, REGISTRY_REVISION + 1, "REGISTRY_REVISION_MISMATCH"),
    ),
)
def test_loader_rejects_revision_rollback_or_drift(
    expected_policy_revision: int,
    expected_registry_revision: int,
    code: str,
) -> None:
    registry = _registry()
    raw = _manifest(registry)

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV1) as captured:
        _load(
            raw,
            registry,
            _envelopes(raw),
            expected_policy_revision=expected_policy_revision,
            expected_registry_revision=expected_registry_revision,
        )

    assert captured.value.code == code


@pytest.mark.parametrize(
    ("raw", "evaluation_epoch", "code"),
    (
        pytest.param(
            lambda registry: _manifest(registry, policy_activation_epoch=21),
            20,
            "POLICY_NOT_ACTIVE",
            id="policy-not-active",
        ),
        pytest.param(
            lambda registry: _manifest(registry, policy_revocation_epoch=20),
            20,
            "POLICY_REVOKED",
            id="policy-revoked",
        ),
        pytest.param(
            lambda registry: _manifest(registry, registry_activation_epoch=21),
            20,
            "REGISTRY_NOT_ACTIVE",
            id="registry-not-active",
        ),
        pytest.param(
            lambda registry: _manifest(registry, registry_revocation_epoch=20),
            20,
            "REGISTRY_REVOKED",
            id="registry-revoked",
        ),
    ),
)
def test_loader_enforces_policy_and_registry_lifecycle(
    raw: Callable[[dict[str, object]], bytes],
    evaluation_epoch: int,
    code: str,
) -> None:
    registry = _registry()
    manifest = raw(registry)

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV1) as captured:
        _load(
            manifest,
            registry,
            _envelopes(manifest),
            evaluation_epoch=evaluation_epoch,
        )

    assert captured.value.code == code


def test_loader_rejects_noncanonical_duplicate_or_float_manifest() -> None:
    registry = _registry()
    raw = _manifest(registry)
    noncanonical = raw.replace(b'"policy_revision":7', b'"policy_revision":7.0')

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV1) as float_error:
        _load(noncanonical, registry, ())
    assert float_error.value.code == "FLOAT_FORBIDDEN"

    duplicate = raw.replace(
        b'"schema":"zenodex.zrpf.spot_v7.operational_policy_manifest.v1"',
        b'"schema":"zenodex.zrpf.spot_v7.operational_policy_manifest.v1",'
        b'"schema":"zenodex.zrpf.spot_v7.operational_policy_manifest.v1"',
    )
    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV1) as duplicate_error:
        _load(duplicate, registry, ())
    assert duplicate_error.value.code == "DUPLICATE_JSON_KEY"


def test_loader_rejects_manifest_authority_boolean_even_when_canonical() -> None:
    registry = _registry()
    document = json.loads(_manifest(registry))
    document["production_authority"] = False
    raw = json.dumps(document, sort_keys=True, separators=(",", ":")).encode("ascii")

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV1) as captured:
        _load(raw, registry, ())

    assert captured.value.code == "FIELD_SET_MISMATCH"


def test_loader_rejects_envelope_from_revoked_registry_signer() -> None:
    registry = build_signer_registry_v0(
        registry_id=REGISTRY_ID,
        payload_kind=SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V1,
        threshold=1,
        signers=[
            {
                "signer_id": "release-signer-0",
                "key_id": "release-key-0",
                "public_key": bls_public_key_hex_from_private_key_v0(PRIVATE_KEY),
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "revoked-signer",
                "key_id": "revoked-key",
                "public_key": bls_public_key_hex_from_private_key_v0(ATTACKER_PRIVATE_KEY),
                "weight": 1,
                "status": "revoked",
            },
        ],
    )
    raw = _manifest(registry)
    revoked_envelope = build_bls_signed_artifact_envelope_v0(
        payload_kind=SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V1,
        payload_hash=spot_v7_operational_policy_manifest_payload_hash_v1(raw),
        signer_id="revoked-signer",
        key_id="revoked-key",
        private_key_hex=ATTACKER_PRIVATE_KEY,
    )

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV1) as captured:
        _load(raw, registry, (revoked_envelope,))

    assert captured.value.code == "SIGNATURE_QUORUM_INVALID"


def test_loader_has_no_caller_boolean_authority_override_channel() -> None:
    registry = _registry()
    raw = _manifest(registry)
    unchecked_call = cast(Callable[..., object], load_governed_spot_v7_operational_policy_v2)

    with pytest.raises(TypeError, match="unexpected keyword argument"):
        unchecked_call(
            raw,
            authenticated_release=_AuthenticatedSpotV7OperationalPolicyReleasePinsV1(
                SpotV7OperationalPolicyReleasePinsV1(
                    manifest_sha256=hashlib.sha256(raw).hexdigest(),
                    application_id=_root("application"),
                    chain_or_domain_id=_root("domain"),
                    policy_revision=POLICY_REVISION,
                    signer_registry_id=REGISTRY_ID,
                    signer_registry_hash=str(registry["registry_hash"]),
                    signer_registry_revision=REGISTRY_REVISION,
                ),
                trusted_evaluation_epoch=POLICY_ACTIVATION_EPOCH,
                seal=_AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V1,
            ),
            signer_registry=registry,
            signature_envelopes=_envelopes(raw),
            production_authority=True,
        )


def test_loader_rejects_public_caller_constructed_release_pins() -> None:
    registry = _registry()
    raw = _manifest(registry)
    public_pins = SpotV7OperationalPolicyReleasePinsV1(
        manifest_sha256=hashlib.sha256(raw).hexdigest(),
        application_id=_root("application"),
        chain_or_domain_id=_root("domain"),
        policy_revision=POLICY_REVISION,
        signer_registry_id=REGISTRY_ID,
        signer_registry_hash=str(registry["registry_hash"]),
        signer_registry_revision=REGISTRY_REVISION,
    )
    unchecked_call = cast(Callable[..., object], load_governed_spot_v7_operational_policy_v2)

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV1) as captured:
        unchecked_call(
            raw,
            authenticated_release=public_pins,
            signer_registry=registry,
            signature_envelopes=_envelopes(raw),
        )

    assert captured.value.code == "AUTHENTICATED_RELEASE_PINS_REQUIRED"


def test_loader_rejects_nominal_authenticated_release_without_private_seal() -> None:
    registry = _registry()
    raw = _manifest(registry)
    forged = object.__new__(_AuthenticatedSpotV7OperationalPolicyReleasePinsV1)

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV1) as captured:
        load_governed_spot_v7_operational_policy_v2(
            raw,
            authenticated_release=forged,
            signer_registry=registry,
            signature_envelopes=_envelopes(raw),
        )

    assert captured.value.code == "AUTHENTICATED_RELEASE_PINS_REQUIRED"


def test_loader_rejects_signature_or_quorum_failure_without_partial_policy() -> None:
    registry = _registry()
    raw = _manifest(registry)
    policies: list[_GovernedSpotV7OperationalPolicyV2] = []

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV1) as captured:
        policies.append(_load(raw, registry, ()))

    assert captured.value.code == "SIGNATURE_QUORUM_INVALID"
    assert policies == []


@pytest.mark.parametrize("surface", ("registry", "envelope"))
def test_loader_rejects_oversized_plain_signature_data_before_quorum(surface: str) -> None:
    registry = _registry()
    raw = _manifest(registry)
    envelopes = list(_envelopes(raw))
    oversized = "x" * (256 * 1024 + 1)
    if surface == "registry":
        registry["untrusted_padding"] = oversized
    else:
        envelopes[0]["untrusted_padding"] = oversized

    with pytest.raises(SpotV7OperationalPolicyProvenanceErrorV1) as captured:
        _load(raw, registry, tuple(envelopes))

    assert captured.value.code == "PLAIN_DATA_REQUIRED"

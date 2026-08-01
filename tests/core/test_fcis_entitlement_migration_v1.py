"""C03 state/manifest codec and fail-closed admission tests."""
from __future__ import annotations

import json

import pytest

from src.core.fcis_entitlement_key_v1 import EntitlementKeyV1
from src.core.fcis_entitlement_migration_codec_v1 import (
    C03CodecCodeV1,
    C03CodecRejectV1,
    canonical_entitlement_state_root_v1,
    canonical_sha256_migration_manifest_v1,
    decode_entitlement_state_v1,
    decode_representation_migration_manifest_v1,
    encode_entitlement_state_v1,
    encode_representation_migration_manifest_v1,
)
from src.core.fcis_entitlement_migration_values_v1 import (
    EntitlementStateEntryV1,
    EntitlementStateV1,
    RepresentationMigrationManifestV1,
)
from src.core.fcis_m6_profile_ids import (
    AGQE_REPRESENTATION_PROFILE_ID_V1,
    FIXED_ROLE_ORDER_ID_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
    SRGD_REPRESENTATION_PROFILE_ID_V1,
)


def _key(asset: str = "USDC") -> EntitlementKeyV1:
    return EntitlementKeyV1(
        "protocol-fees",
        asset,
        SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
        FIXED_ROLE_ORDER_ID_V1,
    )


def _state(
    representation_id: str,
    *,
    asset: str = "USDC",
    entry_coordinates: tuple[int, int, int] = (3, -1, -2),
) -> EntitlementStateV1:
    return EntitlementStateV1(
        _key(asset),
        representation_id,
        (EntitlementStateEntryV1("entry-0", entry_coordinates),),
    )


def _manifest(
    old_state: EntitlementStateV1,
    new_state: EntitlementStateV1,
) -> RepresentationMigrationManifestV1:
    return RepresentationMigrationManifestV1(
        old_state,
        new_state,
        "migration-map-v1",
        "0x" + "11" * 32,
        7,
    )


def test_state_root_is_recomputed_from_complete_entries() -> None:
    state = _state(SRGD_REPRESENTATION_PROFILE_ID_V1)
    assert encode_entitlement_state_v1(state).startswith(b"{")
    assert state.state_root.startswith("0x")
    assert state.state_root == canonical_entitlement_state_root_v1(state)
    changed = _state(
        SRGD_REPRESENTATION_PROFILE_ID_V1,
        entry_coordinates=(4, -1, -3),
    )
    assert encode_entitlement_state_v1(state) != encode_entitlement_state_v1(changed)
    assert state.state_root != changed.state_root


def test_manifest_exposes_computed_roots_and_exact_fields() -> None:
    old_state = _state(SRGD_REPRESENTATION_PROFILE_ID_V1)
    new_state = _state(AGQE_REPRESENTATION_PROFILE_ID_V1)
    manifest = _manifest(old_state, new_state)
    assert manifest.old_semantic_key == old_state.key
    assert manifest.new_semantic_key == new_state.key
    assert manifest.old_representation_id == SRGD_REPRESENTATION_PROFILE_ID_V1
    assert manifest.new_representation_id == AGQE_REPRESENTATION_PROFILE_ID_V1
    assert manifest.old_state_root == old_state.state_root
    assert manifest.new_state_root == new_state.state_root
    with pytest.raises(TypeError):
        RepresentationMigrationManifestV1(  # type: ignore[call-arg]
            old_state,
            new_state,
            "migration-map-v1",
            "0x" + "11" * 32,
            7,
            new_state_root="0x" + "22" * 32,
        )


def test_manifest_codec_contains_computed_new_root_only() -> None:
    manifest = _manifest(
        _state(SRGD_REPRESENTATION_PROFILE_ID_V1),
        _state(AGQE_REPRESENTATION_PROFILE_ID_V1),
    )
    decoded = json.loads(encode_representation_migration_manifest_v1(manifest))
    assert set(decoded["value"]) == {
        "old_semantic_key",
        "new_semantic_key",
        "old_representation_id",
        "new_representation_id",
        "old_state_root",
        "new_state_root",
        "migration_map_id",
        "authority_epoch_root",
        "activation_sequence",
    }
    assert decoded["value"]["new_state_root"] == manifest.new_state_root


def test_manifest_round_trip_requires_verified_states() -> None:
    old_state = _state(SRGD_REPRESENTATION_PROFILE_ID_V1)
    new_state = _state(AGQE_REPRESENTATION_PROFILE_ID_V1)
    manifest = _manifest(old_state, new_state)
    payload = encode_representation_migration_manifest_v1(manifest)
    accepted = decode_representation_migration_manifest_v1(
        payload,
        expected_old_state=old_state,
        expected_new_state=new_state,
    )
    assert accepted == manifest
    missing = decode_representation_migration_manifest_v1(
        payload,
        expected_old_state=old_state,
        expected_new_state=None,
    )
    assert missing == C03CodecRejectV1(
        C03CodecCodeV1.VERIFIED_STATE_REQUIRED,
        ("expected_new_state",),
    )


def test_manifest_rejects_caller_changed_new_root() -> None:
    old_state = _state(SRGD_REPRESENTATION_PROFILE_ID_V1)
    new_state = _state(AGQE_REPRESENTATION_PROFILE_ID_V1)
    manifest = _manifest(old_state, new_state)
    raw = json.loads(encode_representation_migration_manifest_v1(manifest))
    raw["value"]["new_state_root"] = "0x" + "22" * 32
    payload = json.dumps(raw, separators=(",", ":"), sort_keys=True).encode()
    rejected = decode_representation_migration_manifest_v1(
        payload,
        expected_old_state=old_state,
        expected_new_state=new_state,
    )
    assert rejected == C03CodecRejectV1(
        C03CodecCodeV1.STATE_ROOT_MISMATCH,
        ("value", "state_root"),
    )


@pytest.mark.parametrize(  # type: ignore[untyped-decorator]
    "mutant",
    [
        "unknown_schema",
        "unknown_envelope_field",
        "unknown_state_field",
        "unknown_manifest_field",
        "caller_new_state_root",
    ],
)
def test_unknown_schema_fields_and_caller_root_mutants_reject(mutant: str) -> None:
    old_state = _state(SRGD_REPRESENTATION_PROFILE_ID_V1)
    result: object = None
    new_state = _state(AGQE_REPRESENTATION_PROFILE_ID_V1)
    manifest = _manifest(old_state, new_state)
    if mutant == "unknown_schema":
        payload = encode_entitlement_state_v1(old_state).replace(
            b"entitlement/state/v1",
            b"entitlement/state/v9",
        )
        result = decode_entitlement_state_v1(payload)
    elif mutant == "unknown_envelope_field":
        raw = json.loads(encode_entitlement_state_v1(old_state))
        raw["extra"] = 1
        payload = json.dumps(raw, separators=(",", ":"), sort_keys=True).encode()
        result = decode_entitlement_state_v1(payload)
    elif mutant == "unknown_state_field":
        raw = json.loads(encode_entitlement_state_v1(old_state))
        raw["value"]["extra"] = 1
        payload = json.dumps(raw, separators=(",", ":"), sort_keys=True).encode()
        result = decode_entitlement_state_v1(payload)
    elif mutant == "unknown_manifest_field":
        raw = json.loads(encode_representation_migration_manifest_v1(manifest))
        raw["value"]["extra"] = 1
        payload = json.dumps(raw, separators=(",", ":"), sort_keys=True).encode()
        result = decode_representation_migration_manifest_v1(
            payload,
            expected_old_state=old_state,
            expected_new_state=new_state,
        )
    else:
        raw = json.loads(encode_representation_migration_manifest_v1(manifest))
        raw["value"]["new_state_root"] = "0x" + "22" * 32
        payload = json.dumps(raw, separators=(",", ":"), sort_keys=True).encode()
        result = decode_representation_migration_manifest_v1(
            payload,
            expected_old_state=old_state,
            expected_new_state=new_state,
        )
    assert type(result) is C03CodecRejectV1


def test_state_rejects_duplicate_and_out_of_order_entries() -> None:
    key = _key()
    duplicate = (
        EntitlementStateEntryV1("entry-0", (1, -1, 0)),
        EntitlementStateEntryV1("entry-0", (2, -1, -1)),
    )
    with pytest.raises(ValueError, match="strictly ordered"):
        EntitlementStateV1(key, SRGD_REPRESENTATION_PROFILE_ID_V1, duplicate)
    out_of_order = (
        EntitlementStateEntryV1("entry-1", (1, -1, 0)),
        EntitlementStateEntryV1("entry-0", (2, -1, -1)),
    )
    with pytest.raises(ValueError, match="strictly ordered"):
        EntitlementStateV1(key, SRGD_REPRESENTATION_PROFILE_ID_V1, out_of_order)


def test_state_decode_round_trip_and_noncanonical_rejection() -> None:
    state = _state(SRGD_REPRESENTATION_PROFILE_ID_V1)
    payload = encode_entitlement_state_v1(state)
    accepted = decode_entitlement_state_v1(payload)
    assert accepted == state
    with_space = payload.replace(b"{", b"{ ", 1)
    rejected = decode_entitlement_state_v1(with_space)
    assert rejected == C03CodecRejectV1(
        C03CodecCodeV1.NONCANONICAL_ENCODING,
        (),
    )


def test_migration_requires_distinct_supported_representations() -> None:
    state = _state(SRGD_REPRESENTATION_PROFILE_ID_V1)
    with pytest.raises(ValueError, match="change representation"):
        _manifest(state, state)


def test_manifest_digest_is_stable() -> None:
    manifest = _manifest(
        _state(SRGD_REPRESENTATION_PROFILE_ID_V1),
        _state(AGQE_REPRESENTATION_PROFILE_ID_V1),
    )
    assert canonical_sha256_migration_manifest_v1(manifest) == (
        canonical_sha256_migration_manifest_v1(manifest)
    )

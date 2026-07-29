"""Acceptance scenarios for the unmounted FCIS B1B-1 carrier boundary."""

from __future__ import annotations

import json
from dataclasses import fields

import pytest

from src.core.fcis_b1b_authority_admission import (
    admit_fcis_b1b_authority_source_v2,
    decode_fcis_b1b_authority_v2,
)
from src.core.fcis_b1b_authority_codec import encode_fcis_b1b_authority_v2
from src.core.fcis_b1b_authority_schema import (
    DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_FIELDS_V2,
    FCIS_AUTHORITY_HEADER_FIELDS_V2,
    FCIS_B1B_AUTHORITY_FIELDS_BY_SCHEMA_V2,
    FCIS_B1B_AUTHORITY_REGISTERED_SCHEMA_IDS_V2,
    V1_TO_V2_MIGRATION_MANIFEST_FIELDS_V2,
)
from src.core.fcis_b1b_authority_values import (
    DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2,
    FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2,
    MAX_B1B_TEXT_CHARACTERS_V2,
    MAX_U256_V2,
    V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
    B1BAuthorityAdmissionCodeV2,
    B1BAuthorityAdmissionRejectV2,
    DeploymentBootstrapAnchorClaimSourceV2,
    DeploymentBootstrapAnchorClaimV2,
    FCISAuthorityHeaderSourceV2,
    FCISAuthorityHeaderV2,
    V1ToV2MigrationManifestSourceV2,
    V1ToV2MigrationManifestV2,
)

ZERO = "0x" + ("0" * 64)
ONE = "0x" + ("0" * 63) + "1"


def _canonical(value: dict[str, object]) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")


def _header_document(**overrides: object) -> dict[str, object]:
    value: dict[str, object] = {
        "chain_deployment_id": "zenodex:testnet:α",
        "sequence": 0,
        "fee_distribution_configuration_root": ONE,
    }
    value.update(overrides)
    return {"schema": FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2, "value": value}


def _reject(payload: bytes) -> B1BAuthorityAdmissionRejectV2:
    result = decode_fcis_b1b_authority_v2(payload)
    assert type(result) is B1BAuthorityAdmissionRejectV2
    return result


def test_schema_registry_is_closed_and_field_exact() -> None:
    assert FCIS_B1B_AUTHORITY_REGISTERED_SCHEMA_IDS_V2 == (
        FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2,
        DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2,
        V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
    )
    assert FCIS_B1B_AUTHORITY_FIELDS_BY_SCHEMA_V2 == {
        FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2: FCIS_AUTHORITY_HEADER_FIELDS_V2,
        DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2: (
            DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_FIELDS_V2
        ),
        V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2: (
            V1_TO_V2_MIGRATION_MANIFEST_FIELDS_V2
        ),
    }
    with pytest.raises(TypeError):
        FCIS_B1B_AUTHORITY_FIELDS_BY_SCHEMA_V2["unknown"] = ()  # type: ignore[index]


def test_stored_dataclass_fields_equal_the_canonical_projection_fields() -> None:
    expected_by_type = {
        FCISAuthorityHeaderSourceV2: FCIS_AUTHORITY_HEADER_FIELDS_V2,
        FCISAuthorityHeaderV2: FCIS_AUTHORITY_HEADER_FIELDS_V2,
        DeploymentBootstrapAnchorClaimSourceV2: (
            DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_FIELDS_V2
        ),
        DeploymentBootstrapAnchorClaimV2: (
            DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_FIELDS_V2
        ),
        V1ToV2MigrationManifestSourceV2: V1_TO_V2_MIGRATION_MANIFEST_FIELDS_V2,
        V1ToV2MigrationManifestV2: V1_TO_V2_MIGRATION_MANIFEST_FIELDS_V2,
    }
    for carrier_type, expected_fields in expected_by_type.items():
        assert tuple(field.name for field in fields(carrier_type)) == expected_fields


def test_schema_unknown_missing_duplicate_and_trailing_bytes_reject() -> None:
    unknown = _header_document(extra=1)
    reject = _reject(_canonical(unknown))
    assert reject.code is B1BAuthorityAdmissionCodeV2.UNKNOWN_FIELD
    assert reject.path == ("value", "extra")

    missing = _header_document()
    del missing["value"]["sequence"]  # type: ignore[index]
    reject = _reject(_canonical(missing))
    assert reject.code is B1BAuthorityAdmissionCodeV2.MISSING_FIELD
    assert reject.path == ("value", "sequence")

    duplicate = (
        b'{"schema":"'
        + FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2.encode("ascii")
        + b'","value":{"chain_deployment_id":"deployment",'
        + b'"chain_deployment_id":"mallory",'
        + b'"fee_distribution_configuration_root":"'
        + ONE.encode("ascii")
        + b'","sequence":0}}'
    )
    reject = _reject(duplicate)
    assert reject.code is B1BAuthorityAdmissionCodeV2.DUPLICATE_FIELD
    assert reject.path == ("value", "chain_deployment_id")

    canonical = _canonical(_header_document())
    assert _reject(canonical + b"\n").code is (
        B1BAuthorityAdmissionCodeV2.NONCANONICAL_ENCODING
    )


def test_identifiers_accept_exact_unicode_scalar_and_utf8_boundaries() -> None:
    maximum = "🧪" * MAX_B1B_TEXT_CHARACTERS_V2
    assert len(maximum) == MAX_B1B_TEXT_CHARACTERS_V2
    assert len(maximum.encode("utf-8")) == 16_384

    header = FCISAuthorityHeaderV2(maximum, MAX_U256_V2, ONE)
    payload = encode_fcis_b1b_authority_v2(
        FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2,
        header,
    )
    assert decode_fcis_b1b_authority_v2(payload) == header


@pytest.mark.parametrize(
    "identifier",
    (
        "",
        "a" * (MAX_B1B_TEXT_CHARACTERS_V2 + 1),
        "bad\ud800",
    ),
)
def test_identifiers_reject_empty_over_bound_and_surrogate_values(
    identifier: str,
) -> None:
    with pytest.raises((TypeError, ValueError)):
        FCISAuthorityHeaderV2(identifier, 0, ONE)


@pytest.mark.parametrize(
    "digest",
    (
        "0X" + ("0" * 64),
        "0x" + ("A" * 64),
        "0x" + ("g" * 64),
        "0x" + ("0" * 63),
        "0x" + ("0" * 65),
    ),
)
def test_identifiers_reject_noncanonical_digest_spellings(digest: str) -> None:
    with pytest.raises(TypeError):
        FCISAuthorityHeaderV2("deployment", 0, digest)


def test_carrier_only_wrong_migration_constants_never_promote_authority() -> None:
    source = V1ToV2MigrationManifestSourceV2(
        "zenodex:testnet:α",
        ZERO,
        "protocol-fees:α",
        ONE,
        9,
        7,
        4,
        3,
        6,
    )
    admitted = admit_fcis_b1b_authority_source_v2(
        V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
        source,
    )
    assert type(admitted) is V1ToV2MigrationManifestV2
    assert admitted.source_snapshot_version == 3
    assert admitted.target_snapshot_version == 6

    import src.core.fcis_b1b_authority_values as values

    authority_symbols = (
        "PinnedDeploymentBootstrapVerifierV2",
        "VerifiedV1ToV2MigrationAuthorityV2",
        "V1ToV2MigrationCandidateV2",
        "FCISCommittedStateV2",
        "StateBoundFeeDistributionConfigurationV2",
        "TransitionCauseV2",
    )
    assert all(not hasattr(values, symbol) for symbol in authority_symbols)


def test_carrier_only_source_requires_the_exact_source_type() -> None:
    wrong_source = FCISAuthorityHeaderSourceV2("deployment", 0, ONE)
    result = admit_fcis_b1b_authority_source_v2(
        V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
        wrong_source,
    )
    assert type(result) is B1BAuthorityAdmissionRejectV2
    assert result.code is B1BAuthorityAdmissionCodeV2.WRONG_EXACT_TYPE


def test_canonical_carrier_encoding_is_injective_over_boundary_samples() -> None:
    headers = (
        FCISAuthorityHeaderV2("deployment:a", 0, ZERO),
        FCISAuthorityHeaderV2("deployment:a", 1, ZERO),
        FCISAuthorityHeaderV2("deployment:b", 1, ONE),
    )
    anchors = (
        DeploymentBootstrapAnchorClaimV2("deployment:a", ZERO),
        DeploymentBootstrapAnchorClaimV2("deployment:a", ONE),
        DeploymentBootstrapAnchorClaimV2("deployment:b", ONE),
    )
    manifests = (
        V1ToV2MigrationManifestV2(
            "deployment:a", ZERO, "domain:a", ONE, 0, 1, 0, 4, 5
        ),
        V1ToV2MigrationManifestV2(
            "deployment:a", ZERO, "domain:a", ONE, 1, 2, 1, 4, 5
        ),
        V1ToV2MigrationManifestV2(
            "deployment:b", ONE, "domain:b", ZERO, MAX_U256_V2, 1, 0, 4, 5
        ),
    )
    groups = (
        (FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2, headers),
        (DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2, anchors),
        (V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2, manifests),
    )
    for schema_id, values in groups:
        for left in values:
            for right in values:
                left_bytes = encode_fcis_b1b_authority_v2(schema_id, left)
                right_bytes = encode_fcis_b1b_authority_v2(schema_id, right)
                if left_bytes == right_bytes:
                    assert left == right

from __future__ import annotations

import json

import pytest

from src.core.fcis_b1b_authority_admission import (
    admit_fcis_b1b_authority_source_v2,
    decode_fcis_b1b_authority_v2,
)
from src.core.fcis_b1b_authority_codec import (
    canonical_bootstrap_anchor_claim_root_v2,
    canonical_v1_to_v2_migration_manifest_root_v2,
    encode_fcis_b1b_authority_v2,
)
from src.core.fcis_b1b_authority_values import (
    DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2,
    FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2,
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
TWO = "0x" + ("0" * 63) + "2"


def _header(*, sequence: int = 0) -> FCISAuthorityHeaderV2:
    return FCISAuthorityHeaderV2("zenodex:testnet:α", sequence, ONE)


def _anchor() -> DeploymentBootstrapAnchorClaimV2:
    return DeploymentBootstrapAnchorClaimV2("zenodex:testnet:α", TWO)


def _manifest(**overrides: object) -> V1ToV2MigrationManifestV2:
    values: dict[str, object] = {
        "chain_deployment_id": "zenodex:testnet:α",
        "expected_v1_pre_root": ZERO,
        "fee_distribution_domain_id": "protocol-fees:α",
        "expected_initial_configuration_root": ONE,
        "initial_sequence": 0,
        "initial_configuration_version": 1,
        "initial_activation_sequence": 0,
        "source_snapshot_version": 4,
        "target_snapshot_version": 5,
    }
    values.update(overrides)
    return V1ToV2MigrationManifestV2(**values)  # type: ignore[arg-type]


def _reject(result: object) -> B1BAuthorityAdmissionRejectV2:
    assert type(result) is B1BAuthorityAdmissionRejectV2
    return result


def test_exact_carriers_round_trip_through_unique_canonical_bytes() -> None:
    cases = (
        (FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2, _header()),
        (DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2, _anchor()),
        (V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2, _manifest()),
    )

    for schema_id, value in cases:
        payload = encode_fcis_b1b_authority_v2(schema_id, value)
        assert decode_fcis_b1b_authority_v2(payload) == value
        assert payload == json.dumps(
            json.loads(payload),
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode("utf-8")


def test_roots_are_domain_separated_and_content_sensitive() -> None:
    anchor = _anchor()
    manifest = _manifest()

    assert canonical_bootstrap_anchor_claim_root_v2(anchor).startswith("0x")
    assert canonical_v1_to_v2_migration_manifest_root_v2(manifest).startswith("0x")
    assert canonical_bootstrap_anchor_claim_root_v2(anchor) != (
        canonical_v1_to_v2_migration_manifest_root_v2(manifest)
    )
    assert canonical_v1_to_v2_migration_manifest_root_v2(manifest) != (
        canonical_v1_to_v2_migration_manifest_root_v2(
            _manifest(fee_distribution_domain_id="other-domain")
        )
    )


def test_complete_u256_domain_and_unicode_are_structurally_supported() -> None:
    assert _header(sequence=MAX_U256_V2).sequence == MAX_U256_V2
    maximum_manifest = _manifest(
        initial_sequence=MAX_U256_V2,
        initial_configuration_version=MAX_U256_V2,
        initial_activation_sequence=MAX_U256_V2,
        source_snapshot_version=MAX_U256_V2,
        target_snapshot_version=MAX_U256_V2,
    )
    assert maximum_manifest.initial_configuration_version == MAX_U256_V2
    assert "α" in encode_fcis_b1b_authority_v2(
        V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
        maximum_manifest,
    ).decode("utf-8")


@pytest.mark.parametrize("bad", [True, False, -1, MAX_U256_V2 + 1, "0"])
def test_u256_fields_reject_boolean_aliases_and_out_of_range_values(bad: object) -> None:
    with pytest.raises((TypeError, ValueError)):
        FCISAuthorityHeaderV2("deployment", bad, ONE)  # type: ignore[arg-type]


@pytest.mark.parametrize(
    "digest",
    (
        "",
        "0x0",
        "0X" + ("0" * 64),
        "0x" + ("A" * 64),
        "0x" + ("g" * 64),
        "0x" + ("0" * 62),
    ),
)
def test_digest_spelling_is_unique(digest: str) -> None:
    with pytest.raises(TypeError):
        FCISAuthorityHeaderV2("deployment", 0, digest)


def test_source_admission_is_exact_and_remains_non_authoritative() -> None:
    admitted = admit_fcis_b1b_authority_source_v2(
        FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2,
        FCISAuthorityHeaderSourceV2("deployment", 0, ONE),
    )
    assert type(admitted) is FCISAuthorityHeaderV2

    wrong_source = admit_fcis_b1b_authority_source_v2(
        FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2,
        DeploymentBootstrapAnchorClaimSourceV2("deployment", ONE),
    )
    assert _reject(wrong_source).code is B1BAuthorityAdmissionCodeV2.WRONG_EXACT_TYPE

    import src.core.fcis_b1b_authority_values as values

    forbidden = (
        "PinnedDeploymentBootstrapVerifierV2",
        "VerifiedV1ToV2MigrationAuthorityV2",
        "V1ToV2MigrationCandidateV2",
        "FCISCommittedStateV2",
        "StateBoundFeeDistributionConfigurationV2",
        "TransitionCauseV2",
        "ConfigurationUpdateCommandClaimV2",
    )
    assert all(not hasattr(values, name) for name in forbidden)


def test_manifest_fixed_constants_are_later_semantics_not_carrier_authority() -> None:
    structurally_exact_but_semantically_wrong = V1ToV2MigrationManifestSourceV2(
        "deployment",
        ZERO,
        "domain",
        ONE,
        9,
        7,
        4,
        3,
        6,
    )
    admitted = admit_fcis_b1b_authority_source_v2(
        V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
        structurally_exact_but_semantically_wrong,
    )
    assert type(admitted) is V1ToV2MigrationManifestV2
    assert admitted.source_snapshot_version == 3
    assert admitted.target_snapshot_version == 6


def test_constructor_rejects_surrogates_and_empty_identifiers() -> None:
    with pytest.raises(TypeError):
        FCISAuthorityHeaderV2("", 0, ONE)
    with pytest.raises(ValueError):
        FCISAuthorityHeaderV2("bad\ud800", 0, ONE)

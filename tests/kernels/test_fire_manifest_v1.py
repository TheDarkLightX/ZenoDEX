from __future__ import annotations

from dataclasses import replace

import pytest

from src.fire.registry.object_manifest_v1 import (
    DEFAULT_FIRE_EVIDENCE,
    FireImportedInterfaceRequirement,
    FireInstancePolicy,
    FireObjectManifest,
    FireParameterRequirement,
    FireWitnessRequirement,
    fire_manifest_sha256,
    fire_manifest_file_sha256,
    load_fire_object_manifest,
    verify_fire_object_manifest,
    write_fire_object_manifest,
)


def _sample_manifest() -> FireObjectManifest:
    return FireObjectManifest.build(
        object_name="BurnBoostCall",
        object_version="v1",
        object_family="capped_index_call",
        settlement_asset="zUSD",
        payoff_summary="N * min(max(BurnIndex_T - K, 0), Cap)",
        artifact_lower=0,
        artifact_upper=30,
        holder_collateral_required=0,
        writer_collateral_required=30,
        ir_hash="sha256:" + "1" * 64,
        cert_sha256="sha256:" + "2" * 64,
        parameters=(
            FireParameterRequirement(
                name="n_notional",
                unit="Amount[zUSD]",
                minimum=0,
                maximum=1000,
                description="Settlement notional",
            ),
        ),
        imported_interfaces=(
            FireImportedInterfaceRequirement(
                name="burn_final",
                interface_object_id="burn_index_v1",
                interface_output="burn_final",
                unit="Index",
                lower=0,
                upper=9,
            ),
        ),
        witnesses=(
            FireWitnessRequirement(
                name="BurnCertificate[TDEX]",
                freshness="1 epoch",
                lower=0,
                upper=9,
            ),
        ),
        evidence=DEFAULT_FIRE_EVIDENCE,
        instance_policy=FireInstancePolicy(required_party_roles=("holder", "writer")),
    )


def test_fire_object_manifest_round_trip_and_verify() -> None:
    manifest = _sample_manifest()
    restored = FireObjectManifest.from_dict(manifest.to_dict())

    assert restored == manifest
    assert verify_fire_object_manifest(restored) == (True, None)


def test_fire_instance_policy_from_dict_rejects_non_string_required_party_role() -> None:
    with pytest.raises(TypeError, match=r"required_party_roles\[0\] must be a string"):
        FireInstancePolicy.from_dict(
            {
                "required_party_roles": [1],
                "authorization_mode": "role_binding",
                "nonce_required": True,
                "maturity_required": False,
                "settlement_window_required": False,
            }
        )


def test_fire_object_manifest_detects_hash_tamper() -> None:
    manifest = replace(_sample_manifest(), manifest_hash="sha256:" + "0" * 64)

    assert verify_fire_object_manifest(manifest) == (False, "manifest_hash_mismatch")


def test_fire_object_manifest_detects_collateral_mismatch() -> None:
    manifest = replace(_sample_manifest(), writer_collateral_required=29)

    assert verify_fire_object_manifest(manifest) == (False, "writer_collateral_mismatch")


def test_fire_object_manifest_write_and_load_round_trip(tmp_path) -> None:
    manifest = _sample_manifest()
    manifest_path = tmp_path / "burn_manifest.json"

    written_sha256 = write_fire_object_manifest(manifest_path, manifest)
    loaded_manifest, loaded_sha256 = load_fire_object_manifest(manifest_path)

    assert loaded_manifest == manifest
    assert written_sha256 == loaded_sha256 == fire_manifest_file_sha256(manifest)


def test_fire_object_manifest_accepts_legacy_hash_without_imports() -> None:
    manifest = FireObjectManifest.build(
        object_name="LegacyObject",
        object_version="v1",
        object_family="legacy",
        settlement_asset="zUSD",
        payoff_summary="legacy",
        artifact_lower=0,
        artifact_upper=1,
        holder_collateral_required=0,
        writer_collateral_required=1,
        ir_hash="sha256:" + "3" * 64,
        cert_sha256="sha256:" + "4" * 64,
        parameters=(),
        imported_interfaces=(),
        witnesses=(),
        evidence=DEFAULT_FIRE_EVIDENCE,
        instance_policy=FireInstancePolicy(),
    )
    legacy_payload_without_imports = {
        "schema": manifest.schema,
        "object_name": manifest.object_name,
        "object_version": manifest.object_version,
        "object_family": manifest.object_family,
        "settlement_asset": manifest.settlement_asset,
        "payoff_summary": manifest.payoff_summary,
        "artifact_bound": {
            "lower": manifest.artifact_lower,
            "upper": manifest.artifact_upper,
        },
        "collateral_required": {
            "holder": manifest.holder_collateral_required,
            "writer": manifest.writer_collateral_required,
        },
        "ir_hash": manifest.ir_hash,
        "cert_sha256": manifest.cert_sha256,
        "witnesses": [],
        "evidence": manifest.evidence.to_dict(),
    }
    legacy_manifest = replace(
        manifest,
        manifest_hash=fire_manifest_sha256(legacy_payload_without_imports),
    )

    assert verify_fire_object_manifest(legacy_manifest) == (True, None)

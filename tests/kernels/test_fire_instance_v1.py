from __future__ import annotations

from dataclasses import replace

from src.fire.registry.instance_v1 import (
    FireObjectInstanceManifest,
    FireObjectParameterValue,
    FireObjectPartyBinding,
    FireSettlementWindow,
    fire_object_instance_file_sha256,
    load_fire_object_instance,
    verify_fire_object_instance,
    verify_fire_object_instance_against_manifest,
    write_fire_object_instance,
)
from src.fire.registry.object_manifest_v1 import (
    DEFAULT_FIRE_EVIDENCE,
    FireImportedInterfaceRequirement,
    FireInstancePolicy,
    FireObjectManifest,
    FireParameterRequirement,
    FireWitnessRequirement,
)


def _sample_instance() -> FireObjectInstanceManifest:
    return FireObjectInstanceManifest.build(
        object_hash="sha256:" + "1" * 64,
        lock_hash="sha256:" + "2" * 64,
        object_name="BurnBoostCall",
        object_version="v1",
        object_family="capped_index_call",
        parameters=(
            FireObjectParameterValue(name="cap_index", value=3),
            FireObjectParameterValue(name="n_notional", value=10),
            FireObjectParameterValue(name="strike_index", value=4),
            FireObjectParameterValue(name="source_upper", value=9),
        ),
        parties=(
            FireObjectPartyBinding(role="holder", party_id="role:holder"),
            FireObjectPartyBinding(role="writer", party_id="role:writer"),
        ),
        nonce="bundle:BurnBoostCall:v1",
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
        ir_hash="sha256:" + "3" * 64,
        cert_sha256="sha256:" + "4" * 64,
        parameters=(
            FireParameterRequirement(
                name="cap_index",
                unit="Index",
                minimum=0,
                maximum=1000,
                description="Payoff cap",
            ),
            FireParameterRequirement(
                name="n_notional",
                unit="Amount[zUSD]",
                minimum=0,
                maximum=1000,
                description="Settlement notional",
            ),
            FireParameterRequirement(
                name="strike_index",
                unit="Index",
                minimum=0,
                maximum=1000,
                description="Strike index",
            ),
            FireParameterRequirement(
                name="source_upper",
                unit="Index",
                minimum=0,
                maximum=1000,
                description="Certified source upper bound",
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


def _sample_manifest_bound_instance(manifest: FireObjectManifest | None = None) -> FireObjectInstanceManifest:
    if manifest is None:
        manifest = _sample_manifest()
    return FireObjectInstanceManifest.build(
        object_hash=manifest.manifest_hash,
        lock_hash="sha256:" + "2" * 64,
        object_name=manifest.object_name,
        object_version=manifest.object_version,
        object_family=manifest.object_family,
        parameters=_sample_instance().parameters,
        parties=_sample_instance().parties,
        nonce=_sample_instance().nonce,
    )


def test_fire_object_instance_round_trip_and_verify() -> None:
    instance = _sample_instance()

    restored = FireObjectInstanceManifest.from_dict(instance.to_dict())

    assert restored == instance
    assert verify_fire_object_instance(
        restored,
        expected_object_hash="sha256:" + "1" * 64,
        expected_lock_hash="sha256:" + "2" * 64,
    ) == (True, None)


def test_fire_object_instance_detects_hash_tamper() -> None:
    instance = replace(_sample_instance(), instance_hash="sha256:" + "0" * 64)

    assert verify_fire_object_instance(
        instance,
        expected_object_hash="sha256:" + "1" * 64,
        expected_lock_hash="sha256:" + "2" * 64,
    ) == (False, "instance_hash_mismatch")


def test_fire_object_instance_write_and_load_round_trip(tmp_path) -> None:
    instance = _sample_instance()
    instance_path = tmp_path / "instance_manifest.json"

    written_sha256 = write_fire_object_instance(instance_path, instance)
    loaded_instance, loaded_sha256 = load_fire_object_instance(instance_path)

    assert loaded_instance == instance
    assert written_sha256 == loaded_sha256 == fire_object_instance_file_sha256(instance)


def test_fire_object_instance_admissibility_accepts_manifest_bound_instance() -> None:
    manifest = _sample_manifest()
    ok, err, report = verify_fire_object_instance_against_manifest(
        _sample_manifest_bound_instance(manifest),
        object_manifest=manifest,
    )

    assert ok is True
    assert err is None
    assert report.ok is True
    assert report.param_ok is True
    assert report.authorization_ok is True
    assert report.nonce_ok is True
    assert report.maturity_ok is True
    assert report.window_ok is True


def test_fire_object_instance_admissibility_rejects_out_of_range_param() -> None:
    manifest = _sample_manifest()
    bad_instance = replace(
        _sample_manifest_bound_instance(manifest),
        parameters=tuple(
            FireObjectParameterValue(name=item.name, value=(1001 if item.name == "n_notional" else item.value))
            for item in _sample_manifest_bound_instance(manifest).parameters
        ),
        instance_hash="sha256:" + "0" * 64,
    )
    rebuilt = FireObjectInstanceManifest.build(
        object_hash=bad_instance.object_hash,
        lock_hash=bad_instance.lock_hash,
        object_name=bad_instance.object_name,
        object_version=bad_instance.object_version,
        object_family=bad_instance.object_family,
        parameters=bad_instance.parameters,
        parties=bad_instance.parties,
        nonce=bad_instance.nonce,
    )

    ok, err, report = verify_fire_object_instance_against_manifest(
        rebuilt,
        object_manifest=manifest,
    )

    assert ok is False
    assert err == "param_out_of_range:n_notional"
    assert report.param_ok is False


def test_fire_object_instance_admissibility_rejects_party_role_mismatch() -> None:
    manifest = _sample_manifest()
    rebuilt = FireObjectInstanceManifest.build(
        object_hash=manifest.manifest_hash,
        lock_hash="sha256:" + "2" * 64,
        object_name=manifest.object_name,
        object_version=manifest.object_version,
        object_family=manifest.object_family,
        parameters=_sample_instance().parameters,
        parties=(FireObjectPartyBinding(role="holder", party_id="role:holder"),),
        nonce=_sample_instance().nonce,
    )

    ok, err, report = verify_fire_object_instance_against_manifest(
        rebuilt,
        object_manifest=manifest,
    )

    assert ok is False
    assert err == "authorization_role_mismatch"
    assert report.authorization_ok is False


def test_fire_object_instance_round_trip_with_maturity_and_window() -> None:
    instance = FireObjectInstanceManifest.build(
        object_hash="sha256:" + "1" * 64,
        lock_hash="sha256:" + "2" * 64,
        object_name="BurnBoostCall",
        object_version="v1",
        object_family="capped_index_call",
        parameters=_sample_instance().parameters,
        parties=_sample_instance().parties,
        nonce="bundle:BurnBoostCall:v1",
        maturity="2026-07-01T00:00:00Z",
        settlement_window=FireSettlementWindow(
            start="2026-07-01T00:00:00Z",
            end="2026-07-02T00:00:00Z",
        ),
    )

    restored = FireObjectInstanceManifest.from_dict(instance.to_dict())

    assert restored == instance

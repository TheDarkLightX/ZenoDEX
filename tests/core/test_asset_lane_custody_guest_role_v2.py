"""Falsification tests for the isolated custody guest role binding."""

from __future__ import annotations

import json
from dataclasses import fields, replace
from pathlib import Path

import pytest

from src.core.asset_lane_custody_guest_role_v2 import (
    ASSET_LANE_CUSTODY_GUEST_ROLE_BINDING_DOMAIN_V2,
    ASSET_LANE_CUSTODY_GUEST_SPECIFICATION_ROOT_V2,
    ASSET_LANE_CUSTODY_JOURNAL_SCHEMA_ROOT_V2,
    ASSET_LANE_CUSTODY_RECEIPT_SCHEMA_ROOT_V2,
    ASSET_LANE_CUSTODY_STATE_SCHEMA_ROOT_V2,
    AssetLaneCustodyGuestRoleBindingV2,
    require_asset_lane_custody_guest_role_binding_v2,
    snapshot_asset_lane_custody_guest_role_binding_v2,
)
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.economic_receipt_verifier_deployment_v1 import (
    economic_receipt_verifier_backend_protocol_root_v1,
)
from src.core.economic_receipt_verifier_evidence_v1 import (
    EconomicReceiptVerifierEvidenceManifestV1,
)
from src.core.global_settlement_primitives_v2 import hash_global_v2
from tests.core.test_asset_lane_custody_profile_binding_v2 import _binding_inputs
from tests.core.test_economic_receipt_verifier_release_v1 import _manifest


def _case() -> tuple[AssetLaneCustodyGuestRoleBindingV2, object, object, object]:
    profile, context, global_pre = _binding_inputs()
    manifest = replace(
        _manifest(),
        proof_system="risc0-succinct",
        receipt_schema_root=ASSET_LANE_CUSTODY_RECEIPT_SCHEMA_ROOT_V2,
        journal_schema_root=ASSET_LANE_CUSTODY_JOURNAL_SCHEMA_ROOT_V2,
        specification_root=ASSET_LANE_CUSTODY_GUEST_SPECIFICATION_ROOT_V2,
    )
    binding = AssetLaneCustodyGuestRoleBindingV2(
        profile.profile_id,
        profile.authority_epoch,
        ASSET_LANE_CUSTODY_STATE_SCHEMA_ROOT_V2,
        manifest,
    )
    return binding, profile, context, global_pre


def test_valid_role_binding_is_owned_and_preserves_v1_profile_coordinates() -> None:
    binding, profile, context, global_pre = _case()
    before = (profile.to_canonical(), context.to_canonical(), global_pre.to_canonical())

    owned = require_asset_lane_custody_guest_role_binding_v2(
        binding, binding.binding_root, profile, context, global_pre
    )

    assert type(owned) is AssetLaneCustodyGuestRoleBindingV2
    assert owned is not binding
    assert owned.evidence_manifest is not binding.evidence_manifest
    assert (
        profile.to_canonical(),
        context.to_canonical(),
        global_pre.to_canonical(),
    ) == before
    assert profile.root_image_id == before[0]["root_image_id"]


def test_constructor_owns_manifest_and_artifact_rows() -> None:
    binding, _, _, _ = _case()
    source_manifest = replace(
        binding.evidence_manifest,
        evidence_artifacts=binding.evidence_manifest.evidence_artifacts,
    )
    binding = AssetLaneCustodyGuestRoleBindingV2(
        binding.profile_root,
        binding.authority_epoch,
        binding.state_schema_root,
        source_manifest,
    )
    original_root = binding.binding_root
    source_artifact = source_manifest.evidence_artifacts[0]

    object.__setattr__(source_manifest, "source_root", "0x" + "12" * 32)
    object.__setattr__(source_artifact, "artifact_root", "0x" + "13" * 32)

    assert binding.binding_root == original_root
    assert binding.evidence_manifest.source_root != source_manifest.source_root
    assert (
        binding.evidence_manifest.evidence_artifacts[0].artifact_root
        != source_artifact.artifact_root
    )


def test_binding_root_has_fixed_v2_role_and_purpose_coordinates() -> None:
    binding, _, _, _ = _case()
    expected = hash_global_v2(
        ASSET_LANE_CUSTODY_GUEST_ROLE_BINDING_DOMAIN_V2,
        binding.to_canonical(),
    )
    assert binding.binding_root == expected
    assert {field.name for field in fields(binding)} == {
        "profile_root",
        "authority_epoch",
        "state_schema_root",
        "evidence_manifest",
    }
    assert binding.to_canonical()["role"] == "ASSET_LANE_CUSTODY_GLOBAL_V2"
    assert binding.to_canonical()["purpose"] == "ISOLATED_QUALIFICATION"


def test_schema_literals_are_recomputed_from_the_normative_json() -> None:
    specification = json.loads(
        (
            Path(__file__).parents[2] / "docs/specifications/asset-lane-custody-guest-role-v2.json"
        ).read_text(encoding="utf-8")
    )
    assert ASSET_LANE_CUSTODY_STATE_SCHEMA_ROOT_V2 == hash_global_v2(
        "asset-lane-custody-state-schema-v2", specification["state_schema"]
    )
    assert ASSET_LANE_CUSTODY_JOURNAL_SCHEMA_ROOT_V2 == hash_global_v2(
        "asset-lane-custody-global-journal-schema-v2", specification["journal_schema"]
    )
    assert ASSET_LANE_CUSTODY_RECEIPT_SCHEMA_ROOT_V2 == hash_global_v2(
        "asset-lane-custody-receipt-schema-v2", specification["receipt_schema"]
    )
    assert ASSET_LANE_CUSTODY_GUEST_SPECIFICATION_ROOT_V2 == hash_global_v2(
        "asset-lane-custody-guest-role-specification-v2", specification
    )


@pytest.mark.parametrize(
    ("field", "message"),
    (
        ("state_schema_root", "state schema root mismatch"),
        ("proof_system", "proof system mismatch"),
        ("receipt_schema_root", "receipt schema root mismatch"),
        ("journal_schema_root", "journal schema root mismatch"),
        ("specification_root", "specification root mismatch"),
        ("backend_protocol_root", "backend protocol root mismatch"),
    ),
)
def test_forged_role_schema_is_revalidated_by_the_selector(field: str, message: str) -> None:
    binding, profile, context, global_pre = _case()
    expected = binding.binding_root
    if field == "state_schema_root":
        object.__setattr__(binding, "state_schema_root", "0x" + "11" * 32)
    else:
        object.__setattr__(
            binding.evidence_manifest,
            field,
            "foreign-proof" if field == "proof_system" else "0x" + "11" * 32,
        )
    with pytest.raises(ValueError, match=message):
        require_asset_lane_custody_guest_role_binding_v2(
            binding, expected, profile, context, global_pre
        )


def test_backend_protocol_root_is_existing_v1_protocol_coordinate() -> None:
    binding, _, _, _ = _case()
    assert binding.evidence_manifest.backend_protocol_root == (
        economic_receipt_verifier_backend_protocol_root_v1()
    )


def test_missing_required_evidence_rejects() -> None:
    binding, _, _, _ = _case()
    incomplete = replace(
        binding.evidence_manifest,
        evidence_artifacts=binding.evidence_manifest.evidence_artifacts[:1],
    )
    with pytest.raises(ValueError, match="lacks required shadow statuses"):
        replace(binding, evidence_manifest=incomplete)


@pytest.mark.parametrize("field", ("profile_root", "authority_epoch"))
def test_coherent_role_for_another_profile_or_epoch_is_rejected(field: str) -> None:
    binding, profile, context, global_pre = _case()
    value = "0x" + "23" * 32 if field == "profile_root" else binding.authority_epoch + 1
    foreign = replace(binding, **{field: value})
    with pytest.raises(ValueError, match="custody guest (profile root|authority epoch) mismatch"):
        require_asset_lane_custody_guest_role_binding_v2(
            foreign, foreign.binding_root, profile, context, global_pre
        )


@pytest.mark.parametrize("field", ("context_pre", "occurrence_pre", "occurrence_profile"))
def test_actual_predecessor_and_occurrence_must_match_the_selected_role(field: str) -> None:
    binding, profile, context, global_pre = _case()
    foreign = "0x" + "24" * 32
    occurrence = context.occurrence
    if field == "context_pre":
        pre_root = foreign
    else:
        pre_root = context.global_pre_state_root
        occurrence_field = "pre_state_root" if field == "occurrence_pre" else "profile_root"
        occurrence = replace(occurrence, **{occurrence_field: foreign})
    context = AssetLaneContextV2(
        context.writer_epoch, context.module_release_id, pre_root, occurrence
    )
    with pytest.raises(ValueError, match="custody guest .* (state root|profile root) mismatch"):
        require_asset_lane_custody_guest_role_binding_v2(
            binding, binding.binding_root, profile, context, global_pre
        )


def test_external_expected_root_is_independent_and_mismatch_rejects() -> None:
    binding, profile, context, global_pre = _case()
    with pytest.raises(ValueError, match="binding root mismatch"):
        require_asset_lane_custody_guest_role_binding_v2(
            binding, "0x" + "22" * 32, profile, context, global_pre
        )


@pytest.mark.parametrize("epoch", (True, 1 << 64))
def test_bool_and_overflow_epoch_reject_at_construction(epoch: object) -> None:
    binding, _, _, _ = _case()
    with pytest.raises(ValueError):
        replace(binding, authority_epoch=epoch)


def test_subclass_manifest_and_binding_are_rejected() -> None:
    binding, profile, context, global_pre = _case()

    class ManifestChild(EconomicReceiptVerifierEvidenceManifestV1):
        pass

    with pytest.raises(TypeError, match="exactly typed"):
        replace(
            binding,
            evidence_manifest=ManifestChild(
                proof_system=binding.evidence_manifest.proof_system,
                implementation_root=binding.evidence_manifest.implementation_root,
                receipt_schema_root=binding.evidence_manifest.receipt_schema_root,
                journal_schema_root=binding.evidence_manifest.journal_schema_root,
                root_image_id=binding.evidence_manifest.root_image_id,
                specification_root=binding.evidence_manifest.specification_root,
                source_root=binding.evidence_manifest.source_root,
                toolchain_root=binding.evidence_manifest.toolchain_root,
                backend_protocol_root=binding.evidence_manifest.backend_protocol_root,
                max_receipt_bytes=binding.evidence_manifest.max_receipt_bytes,
                max_journal_bytes=binding.evidence_manifest.max_journal_bytes,
                evidence_artifacts=binding.evidence_manifest.evidence_artifacts,
            ),
        )

    class BindingChild(AssetLaneCustodyGuestRoleBindingV2):
        pass

    forged = object.__new__(BindingChild)
    with pytest.raises(TypeError, match="exactly typed"):
        snapshot_asset_lane_custody_guest_role_binding_v2(forged)

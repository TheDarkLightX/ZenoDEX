"""Selected perps-margin role admission over the existing protocol fixture.

The receipt exchange remains a process-protocol fixture.  These tests exercise
the signed command, pure joint transition, and selected role boundaries; they
make no genuine RISC0 proof or publication claim.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace
from pathlib import Path
from typing import cast

import pytest
from py_ecc.bls import G2Basic

from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_transfer_types_v2 import AssetTransferStateV2
from src.core.economic_command_authentication_types_v2 import (
    EconomicCommandAuthenticationCandidateV2,
    EconomicCommandIntentV2,
)
from src.core.economic_command_authentication_v2 import (
    prepare_isolated_economic_command_authentication_v2,
)
from src.core.economic_command_authorization_registry_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    EconomicCommandAuthorizationRegistryV1,
    EconomicCommandAuthorizationV1,
)
from src.core.economic_command_signature_verifier_deployment_v1 import (
    EconomicCommandSignatureVerifierEvidenceManifestV1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
    EconomicCommandSignatureVerifierRegistryV1,
)
from src.core.economic_receipt_verifier_evidence_v1 import (
    EconomicReceiptVerifierEvidenceArtifactV1,
    EconomicReceiptVerifierEvidenceManifestV1,
    economic_receipt_verifier_backend_protocol_root_v1,
    economic_receipt_verifier_implementation_root_v1,
)
from src.core.economic_receipt_verifier_registry_v1 import (
    REQUIRED_SHADOW_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_economic_state_v2 import GlobalEconomicStateV2, LaneStateRootV2
from src.core.global_settlement_primitives_v2 import (
    canonical_economic_command_body_bytes_v2,
    hash_economic_command_body_v2,
    hash_global_v2,
)
from src.core.global_settlement_types_v1 import (
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    LaneCoordinatorRegistryV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteRegistryV1,
    RouteReleaseV1,
)
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    GLOBAL_SETTLEMENT_ABI_V2,
    ZERO_ROOT_V2,
    LaneIdV2,
)
from src.core.perps_margin_global_v2 import (
    PerpsMarginGlobalRejectedV2,
    PerpsMarginOracleV2,
)
from src.core.perps_margin_guest_role_v2 import (
    PERPS_MARGIN_GLOBAL_GUEST_SPECIFICATION_DESCRIPTOR_V2,
    PERPS_MARGIN_GLOBAL_GUEST_SPECIFICATION_ROOT_V2,
    PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_DESCRIPTOR_V2,
    PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_ROOT_V2,
    PERPS_MARGIN_GLOBAL_RECEIPT_SCHEMA_DESCRIPTOR_V2,
    PERPS_MARGIN_GLOBAL_RECEIPT_SCHEMA_ROOT_V2,
    PERPS_MARGIN_GUEST_ROLE_BINDING_DOMAIN_V2,
    PerpsMarginGuestRoleBindingV2,
    require_perps_margin_guest_role_binding_v2,
)
from src.core.perps_margin_receipt_v2 import prepare_perps_margin_statement_v2
from src.core.perps_margin_state_v2 import PerpsMarginStateV2
from src.core.perps_margin_types_v1 import (
    PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
    PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
    PerpsMarginCommandV1,
    PerpsMarginRejectCodeV1,
)
from src.core.perps_margin_wire_v2 import PerpsMarginRequestV2
from src.integration import global_receipt_verifier_v1 as receipt_transport
from src.integration import profiled_perps_margin_receipt_v2 as admission
from src.integration.global_receipt_verifier_v1 import (
    GlobalReceiptVerifierErrorV1,
    GlobalReceiptVerifierRejectV1,
)
from tests.core import test_perps_margin_release_receipt_binding_v1 as perps_support
from tests.core.test_asset_lane_custody_v2 import custody_state
from tests.core.test_perps_margin_module_v1 import _state
from tests.integration.test_authenticated_asset_lane_custody_receipt_v2 import (
    _RECEIPT,
    _receipt_exchange,
)
from tests.integration.test_global_receipt_verifier_v1 import IMAGE, OTHER_IMAGE
from tests.integration.test_isolated_economic_command_authentication_v2 import (
    _ARTIFACT,
    _SECRET,
    _signed_case,
)
from tests.integration.test_isolated_economic_command_authentication_v2 import (
    protocol_case as _protocol_case,
)

globals()["protocol_case"] = _protocol_case


def _root(label: str) -> str:
    return hash_global_v2("perps-margin-guest-role-test-v2", {"label": label})


@dataclass(frozen=True, slots=True)
class PerpsMarginProfileCase:
    """One immutable profile/state bundle reusable by publisher tests."""

    profile: EconomicProfileSnapshotV1
    assets: AssetLaneCustodyStateV2
    margin: PerpsMarginStateV2
    global_pre: GlobalEconomicStateV2
    signature_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1
    receipt_manifest: EconomicReceiptVerifierEvidenceManifestV1
    guest_role_binding: PerpsMarginGuestRoleBindingV2
    policy_registry: EconomicPolicyRegistryV1
    authorization_registry: EconomicCommandAuthorizationRegistryV1
    signature_verifier_registry: EconomicCommandSignatureVerifierRegistryV1
    candidate_template: EconomicCommandAuthenticationCandidateV2


@dataclass(frozen=True, slots=True)
class PerpsMarginSignedCase:
    """A signed request paired with the reusable profile/state bundle."""

    profile: EconomicProfileSnapshotV1
    assets: AssetLaneCustodyStateV2
    margin: PerpsMarginStateV2
    global_pre: GlobalEconomicStateV2
    signature_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1
    receipt_manifest: EconomicReceiptVerifierEvidenceManifestV1
    guest_role_binding: PerpsMarginGuestRoleBindingV2
    candidate: EconomicCommandAuthenticationCandidateV2
    request: PerpsMarginRequestV2


def _receipt_manifest() -> EconomicReceiptVerifierEvidenceManifestV1:
    statuses = tuple(
        sorted(REQUIRED_SHADOW_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1, key=lambda item: item.value)
    )
    return EconomicReceiptVerifierEvidenceManifestV1(
        proof_system="risc0-succinct",
        implementation_root=economic_receipt_verifier_implementation_root_v1(_ARTIFACT),
        receipt_schema_root=PERPS_MARGIN_GLOBAL_RECEIPT_SCHEMA_ROOT_V2,
        journal_schema_root=PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_ROOT_V2,
        root_image_id=IMAGE,
        specification_root=PERPS_MARGIN_GLOBAL_GUEST_SPECIFICATION_ROOT_V2,
        source_root=_root("receipt-source"),
        toolchain_root=_root("receipt-toolchain"),
        backend_protocol_root=economic_receipt_verifier_backend_protocol_root_v1(),
        max_receipt_bytes=16 * 1024 * 1024,
        max_journal_bytes=1024 * 1024,
        evidence_artifacts=tuple(
            EconomicReceiptVerifierEvidenceArtifactV1(status, _root(f"receipt-status:{status.value}"))
            for status in statuses
        ),
    )


def _profile_case() -> PerpsMarginProfileCase:
    base_candidate, _, signature_manifest, _ = _signed_case()
    base_profile = base_candidate.profile
    perps_profile = perps_support._profile()[0]
    old_asset_release = base_profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    asset_release = LaneModuleReleaseV1.build(
        lane_id=old_asset_release.lane_id,
        semantic_version=old_asset_release.semantic_version,
        state_schema_root=old_asset_release.state_schema_root,
        command_variants=tuple(
            sorted(
                (
                    *old_asset_release.command_variants,
                    PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
                    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
                    PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
                )
            )
        ),
        terminal_command_variants=old_asset_release.terminal_command_variants,
        guest_image_id=old_asset_release.guest_image_id,
        specification_root=old_asset_release.specification_root,
        source_root=old_asset_release.source_root,
        toolchain_root=old_asset_release.toolchain_root,
        terminal_coverage_root=old_asset_release.terminal_coverage_root,
        migration_compatibility_root=old_asset_release.migration_compatibility_root,
        max_cycles=old_asset_release.max_cycles,
        max_journal_bytes=old_asset_release.max_journal_bytes,
        status=old_asset_release.status,
        accepts_new_objects=old_asset_release.accepts_new_objects,
        evidence_statuses=old_asset_release.evidence_statuses,
    )
    margin_release = perps_profile.lane_registry.release_for(LaneIdV1.PERPS_MARKET)
    lanes = LaneRegistryV1(
        tuple(
            asset_release
            if row.lane_id is LaneIdV1.ASSET_TRANSFER
            else margin_release
            if row.lane_id is LaneIdV1.PERPS_MARKET
            else row
            for row in base_profile.lane_registry.releases
        )
    )
    margin_coordinator = perps_profile.lane_coordinator_registry.release_for(
        LaneIdV1.PERPS_MARKET
    )
    coordinators = LaneCoordinatorRegistryV1(
        tuple(
            margin_coordinator
            if row.lane_id is LaneIdV1.PERPS_MARKET
            else row
            for row in base_profile.lane_coordinator_registry.releases
        )
    )
    old_asset_route = base_profile.route_registry.route_for_command("asset_transfer")
    asset_route = RouteReleaseV1.build(
        semantic_version=old_asset_route.semantic_version,
        command_kind=old_asset_route.command_kind,
        ordered_lanes=old_asset_route.ordered_lanes,
        module_release_ids=(asset_release.release_id,),
        dependency_roles=old_asset_route.dependency_roles,
        port_schema_roots=old_asset_route.port_schema_roots,
        guest_image_id=old_asset_route.guest_image_id,
        specification_root=old_asset_route.specification_root,
        source_root=old_asset_route.source_root,
        toolchain_root=old_asset_route.toolchain_root,
        oracle_policy_root=old_asset_route.oracle_policy_root,
        issue_burn_policy_root=old_asset_route.issue_burn_policy_root,
        max_cycles=old_asset_route.max_cycles,
        max_journal_bytes=old_asset_route.max_journal_bytes,
        status=old_asset_route.status,
        accepts_new_objects=old_asset_route.accepts_new_objects,
        evidence_statuses=old_asset_route.evidence_statuses,
    )
    margin_routes = tuple(
        RouteReleaseV1.build(
            semantic_version=route.semantic_version,
            command_kind=route.command_kind,
            ordered_lanes=(LaneIdV1.ASSET_TRANSFER, LaneIdV1.PERPS_MARKET),
            module_release_ids=(asset_release.release_id, margin_release.release_id),
            dependency_roles=("ASSET_TRANSFER", "PERPS_MARKET"),
            port_schema_roots=(route.port_schema_roots[0], _root(f"margin-port:{route.command_kind}")),
            guest_image_id=route.guest_image_id,
            specification_root=route.specification_root,
            source_root=route.source_root,
            toolchain_root=route.toolchain_root,
            oracle_policy_root=route.oracle_policy_root,
            issue_burn_policy_root=route.issue_burn_policy_root,
            max_cycles=route.max_cycles,
            max_journal_bytes=route.max_journal_bytes,
            status=ReleaseStatusV1.ACTIVE_NEW,
            accepts_new_objects=True,
            evidence_statuses=route.evidence_statuses,
        )
        for route in perps_profile.route_registry.routes
    )
    routes = RouteRegistryV1(
        tuple(
            sorted(
                    (asset_route, *margin_routes),
                key=lambda route: route.command_kind,
            )
        )
    )
    base_authorization = base_candidate.authorization_registry.authorizations[0]
    authorizations = EconomicCommandAuthorizationRegistryV1(
        tuple(
            sorted(
                (
                    EconomicCommandAuthorizationV1(
                        command_kind=route.command_kind,
                        subject_id="alice",
                        grant_root=base_authorization.grant_root,
                        route_release_id=route.route_release_id,
                        signer_key_id=base_authorization.signer_key_id,
                        signer_public_key=base_authorization.signer_public_key,
                        signature_algorithm=base_authorization.signature_algorithm,
                        valid_from_height=0,
                        valid_through_height=(1 << 64) - 1,
                        min_nonce=0,
                        max_nonce=(1 << 64) - 1,
                        enabled=True,
                    )
                    for route in routes.routes
                ),
                key=lambda authorization: authorization.key,
            )
        )
    )
    policy_registry = EconomicPolicyRegistryV1(
        tuple(
            sorted(
                    tuple(
                        EconomicPolicyBindingV1(
                            ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
                            route.command_kind,
                        authorizations.registry_root,
                    )
                    for route in routes.routes
                )
                + tuple(
                    EconomicPolicyBindingV1(
                        ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
                        route.command_kind,
                        base_candidate.signature_verifier_registry.registry_root,
                    )
                    for route in routes.routes
                ),
                key=lambda binding: (binding.policy_kind, binding.command_kind),
            )
        )
    )
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=base_profile.authority_epoch,
        lane_registry=lanes,
        lane_coordinator_registry=coordinators,
        route_registry=routes,
        proof_shape_root=base_profile.proof_shape_root,
        root_image_id=base_profile.root_image_id,
        verifier_registry_root=base_profile.verifier_registry_root,
        migration_registry_root=base_profile.migration_registry_root,
        policy_registry_root=policy_registry.registry_root,
        terminal_registry_root=base_profile.terminal_registry_root,
        status=ProfileStatusV1.ACTIVE,
    )

    raw_assets = custody_state(accounts=100, custody=0)
    assets = AssetLaneCustodyStateV2(
        AssetTransferStateV2(
            asset_release.release_id,
            raw_assets.transfer_state.policies,
            raw_assets.transfer_state.balances,
            raw_assets.transfer_state.supplies,
        ),
        replace(raw_assets.origin_registry, module_release_id=asset_release.release_id),
        raw_assets.managed_policies,
        raw_assets.custody,
    )
    margin = PerpsMarginStateV2(
        replace(
            _state(),
            module_release_id=margin_release.release_id,
            collateral_asset="USD",
        ),
        (),
    )
    lane_roots = tuple(
        LaneStateRootV2(
            lane_id,
            lanes.release_for(LaneIdV1(lane_id.value)).release_id,
            lane_id in {LaneIdV2.ASSET_TRANSFER, LaneIdV2.PERPS_MARKET},
            assets.state_root
            if lane_id is LaneIdV2.ASSET_TRANSFER
            else margin.state_root
            if lane_id is LaneIdV2.PERPS_MARKET
            else ZERO_ROOT_V2,
        )
        for lane_id in ALL_LANE_IDS_V2
    )
    global_pre = GlobalEconomicStateV2(
        "perps-margin-test",
        _root("deployment"),
        profile.authority_epoch,
        0,
        profile.profile_id,
        lane_roots,
        balances=assets.transfer_state.balances,
        supplies=assets.transfer_state.supplies,
        custody=assets.custody,
    )
    receipt_manifest = _receipt_manifest()
    binding = PerpsMarginGuestRoleBindingV2(
        profile.profile_id,
        profile.authority_epoch,
        receipt_manifest,
    )
    return PerpsMarginProfileCase(
        profile,
        assets,
        margin,
        global_pre,
        signature_manifest,
        receipt_manifest,
        binding,
        policy_registry,
        authorizations,
        base_candidate.signature_verifier_registry,
        replace(
            base_candidate,
            profile=profile,
            policy_registry=policy_registry,
            authorization_registry=authorizations,
        ),
    )


def perps_margin_profile_case() -> PerpsMarginProfileCase:
    """Return the fixed two-lane profile/state bundle for same-store tests."""

    return _profile_case()


def perps_margin_signed_case(
    *,
    command_kind: str = PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
    amount_atoms: int = 10,
    account_id: str = "margin-a",
    owner: str = "alice",
    nonce: int = 1,
    occurrence_nonce: int = 1,
) -> PerpsMarginSignedCase:
    """Return one signed command against the fixed initial profile/state."""

    bundle = perps_margin_profile_case()
    base_candidate = bundle.candidate_template
    route = bundle.profile.route_registry.route_for_command(command_kind)
    command = PerpsMarginCommandV1(
        command_kind,
        account_id,
        "perp-btc-usd",
        owner,
        "USD",
        amount_atoms,
        nonce,
    )
    body_hash = hash_economic_command_body_v2(command_kind, command)
    auth_row = next(row for row in bundle.authorization_registry.authorizations if row.command_kind == command_kind)
    intent = EconomicCommandIntentV2(
        "perps-margin-test",
        bundle.global_pre.deployment_root,
        bundle.profile.profile_id,
        command_kind,
        body_hash,
        route.route_release_id,
        owner,
        auth_row.grant_root,
        occurrence_nonce,
        (),
        0,
        (1 << 64) - 1,
    )
    envelope = replace(
        base_candidate.envelope,
        command_body_bytes=canonical_economic_command_body_bytes_v2(command_kind, command),
        signer_key_id=auth_row.signer_key_id,
        signer_public_key=auth_row.signer_public_key,
        signature_algorithm=auth_row.signature_algorithm,
        signature_bytes=b"\0" * 96,
    )
    candidate = EconomicCommandAuthenticationCandidateV2(
        bundle.profile,
        bundle.policy_registry,
        bundle.authorization_registry,
        bundle.signature_verifier_registry,
        intent,
        envelope,
    )
    _, _, message = prepare_isolated_economic_command_authentication_v2(candidate)
    candidate = replace(
        candidate,
        envelope=replace(candidate.envelope, signature_bytes=G2Basic.Sign(_SECRET, message)),
    )
    occurrence = EconomicCommandOccurrenceV2(
        bundle.global_pre.chain_id,
        bundle.global_pre.deployment_root,
        bundle.global_pre.height + 1,
        0,
        0,
        command_kind,
        body_hash,
        route.route_release_id,
        owner,
        auth_row.grant_root,
        occurrence_nonce,
        bundle.profile.profile_id,
        bundle.global_pre.state_root,
        (),
    )
    request = PerpsMarginRequestV2(command, occurrence)
    return PerpsMarginSignedCase(
        bundle.profile,
        bundle.assets,
        bundle.margin,
        bundle.global_pre,
        bundle.signature_manifest,
        bundle.receipt_manifest,
        bundle.guest_role_binding,
        candidate,
        request,
    )


def _run(
    case: PerpsMarginSignedCase,
    signature_path: Path,
    receipt_path: Path,
    *,
    monkeypatch: pytest.MonkeyPatch,
    receipt_bytes: bytes = _RECEIPT,
    expected_guest_role_binding_root: str | None = None,
) -> bytes | PerpsMarginGlobalRejectedV2:
    return admission.verify_isolated_profiled_perps_margin_receipt_v2(
        case.candidate,
        case.assets,
        case.margin,
        case.global_pre,
        case.request,
        guest_role_binding=case.guest_role_binding,
        expected_guest_role_binding_root=(
            case.guest_role_binding.binding_root
            if expected_guest_role_binding_root is None
            else expected_guest_role_binding_root
        ),
        receipt_executable_path=str(receipt_path),
        receipt_timeout_ms=5_000,
        signature_artifact_path=signature_path,
        signature_evidence_manifest=case.signature_manifest,
        signature_timeout_ms=5_000,
        receipt_bytes=receipt_bytes,
    )


def test_role_schema_roots_use_the_exact_descriptors_and_owned_manifest() -> None:
    case = perps_margin_profile_case()
    assert PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_ROOT_V2 == hash_global_v2(
        "perps-margin-global-journal-schema-v2",
        PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_DESCRIPTOR_V2,
    )
    assert PERPS_MARGIN_GLOBAL_RECEIPT_SCHEMA_ROOT_V2 == hash_global_v2(
        "perps-margin-global-receipt-schema-v2",
        PERPS_MARGIN_GLOBAL_RECEIPT_SCHEMA_DESCRIPTOR_V2,
    )
    assert PERPS_MARGIN_GLOBAL_GUEST_SPECIFICATION_DESCRIPTOR_V2["abi"] == GLOBAL_SETTLEMENT_ABI_V2
    assert PERPS_MARGIN_GLOBAL_GUEST_SPECIFICATION_ROOT_V2 == hash_global_v2(
        "perps-margin-global-guest-specification-v2",
        PERPS_MARGIN_GLOBAL_GUEST_SPECIFICATION_DESCRIPTOR_V2,
    )
    assert case.guest_role_binding.evidence_manifest is not case.receipt_manifest
    assert set(row.status for row in case.receipt_manifest.evidence_artifacts) >= (
        REQUIRED_SHADOW_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1
    )
    assert case.guest_role_binding.binding_root == hash_global_v2(
        PERPS_MARGIN_GUEST_ROLE_BINDING_DOMAIN_V2,
        case.guest_role_binding.to_canonical(),
    )


def test_signed_margin_statement_reaches_selected_receipt_endpoint(protocol_case, tmp_path, monkeypatch):
    _, signature_path, signatures = protocol_case
    case = perps_margin_signed_case()
    endpoint = tmp_path / "perps-receipt-endpoint"
    endpoint.write_bytes(_ARTIFACT)
    expected = prepare_perps_margin_statement_v2(
        case.assets, case.margin, case.global_pre, case.request
    )
    assert type(expected) is bytes
    requests = _receipt_exchange(monkeypatch, expected)
    assert _run(case, signature_path, endpoint, monkeypatch=monkeypatch) == expected
    assert len(signatures) == len(requests) == 1


def test_economic_zero_amount_rejects_without_receipt_io(protocol_case, tmp_path, monkeypatch):
    _, signature_path, signatures = protocol_case
    case = perps_margin_signed_case(amount_atoms=0)
    monkeypatch.setattr(
        admission,
        "_verify_selected_custody_statement_v2",
        lambda *_: pytest.fail("economic rejection reached receipt IO"),
    )
    rejected = _run(case, signature_path, tmp_path / "absent", monkeypatch=monkeypatch, receipt_bytes=b"")
    assert type(rejected) is PerpsMarginGlobalRejectedV2
    rejected_value = cast(PerpsMarginGlobalRejectedV2, rejected)
    assert rejected_value.code is PerpsMarginRejectCodeV1.ZERO_AMOUNT
    assert rejected_value.pre_state_root == rejected_value.post_state_root == case.global_pre.state_root
    assert rejected_value.effects.is_empty
    assert len(signatures) == 1


def test_oracle_candidate_is_rejected_before_signature_io(protocol_case, tmp_path, monkeypatch):
    _, signature_path, signatures = protocol_case
    case = perps_margin_signed_case()
    oracle_request = replace(
        case.request,
        oracle=PerpsMarginOracleV2(_root("oracle-authority"), _root("oracle-occurrence"), 1),
    )
    case = replace(case, request=oracle_request)
    with pytest.raises(ValueError, match="does not accept an oracle"):
        _run(case, signature_path, tmp_path / "absent", monkeypatch=monkeypatch)
    assert signatures == []


def test_foreign_binding_rejects_against_independent_expected_root(
    protocol_case, tmp_path, monkeypatch
):
    _, signature_path, signatures = protocol_case
    case = perps_margin_signed_case()
    foreign_binding = replace(
        case.guest_role_binding,
        profile_root=_root("foreign-guest-role-profile"),
    )
    foreign_case = replace(case, guest_role_binding=foreign_binding)
    with pytest.raises(ValueError, match="binding root mismatch"):
        _run(
            foreign_case,
            signature_path,
            tmp_path / "absent",
            monkeypatch=monkeypatch,
            expected_guest_role_binding_root=case.guest_role_binding.binding_root,
        )
    assert signatures == []


def test_exact_margin_type_guards_precede_hostile_getters(protocol_case, tmp_path, monkeypatch):
    _, signature_path, _ = protocol_case
    accesses: list[str] = []

    class HostileMargin:
        @property
        def economic_state(self):
            accesses.append("economic_state")
            raise AssertionError("economic_state getter was accessed")

        @property
        def active_claims(self):
            accesses.append("active_claims")
            raise AssertionError("active_claims getter was accessed")

    case = perps_margin_signed_case()
    hostile = HostileMargin()
    with pytest.raises(TypeError, match="perps margin guest margin must be exact"):
        require_perps_margin_guest_role_binding_v2(
            case.guest_role_binding,
            case.guest_role_binding.binding_root,
            case.profile,
            case.assets,
            hostile,
            case.global_pre,
            case.request,
        )
    assert accesses == []

    hostile_case = replace(case, margin=HostileMargin())
    with pytest.raises(TypeError, match="profiled perps margin must be exact"):
        _run(
            hostile_case,
            signature_path,
            tmp_path / "absent",
            monkeypatch=monkeypatch,
        )
    assert accesses == []


@pytest.mark.parametrize(
    "mutation,expected",
    (
        ("route", "caller-selected route"),
        ("head", "predecessor context"),
        ("profile", "predecessor context"),
        ("profile_status", "ACTIVE profile"),
    ),
)
def test_role_context_mutations_reject_before_signature_io(
    protocol_case, tmp_path, monkeypatch, mutation, expected
):
    _, signature_path, signatures = protocol_case
    case = perps_margin_signed_case()
    if mutation == "route":
        request = replace(
            case.request,
            occurrence=replace(case.request.occurrence, route_release_id=_root("foreign-route")),
        )
        case = replace(case, request=request)
    elif mutation == "head":
        request = replace(
            case.request,
            occurrence=replace(case.request.occurrence, pre_state_root=_root("stale-head")),
        )
        case = replace(case, request=request)
    elif mutation == "profile":
        request = replace(
            case.request,
            occurrence=replace(case.request.occurrence, profile_root=_root("foreign-profile")),
        )
        case = replace(case, request=request)
    else:
        case = replace(case, candidate=replace(case.candidate, profile=replace(case.profile, status=ProfileStatusV1.REVOKED)))
    with pytest.raises(ValueError, match=expected):
        _run(case, signature_path, tmp_path / "absent", monkeypatch=monkeypatch)
    assert signatures == []


def test_wrong_asset_release_rejects_before_signature_io(protocol_case, tmp_path, monkeypatch):
    _, signature_path, signatures = protocol_case
    case = perps_margin_signed_case()
    drifted = AssetLaneCustodyStateV2(
        AssetTransferStateV2(
            _root("foreign-asset-release"),
            case.assets.transfer_state.policies,
            case.assets.transfer_state.balances,
            case.assets.transfer_state.supplies,
        ),
        replace(case.assets.origin_registry, module_release_id=_root("foreign-asset-release")),
        case.assets.managed_policies,
        case.assets.custody,
    )
    case = replace(case, assets=drifted)
    with pytest.raises(ValueError, match="asset release"):
        _run(case, signature_path, tmp_path / "absent", monkeypatch=monkeypatch)
    assert signatures == []


def test_bad_signature_precedes_economics_and_receipt(protocol_case, tmp_path, monkeypatch):
    _, signature_path, signatures = protocol_case
    case = perps_margin_signed_case()
    _, _, message = prepare_isolated_economic_command_authentication_v2(case.candidate)
    forged = replace(
        case.candidate,
        envelope=replace(
            case.candidate.envelope,
            signature_bytes=G2Basic.Sign(_SECRET + 1, message),
        ),
    )
    case = replace(case, candidate=forged)
    with pytest.raises(ValueError, match="signature rejected"):
        _run(case, signature_path, tmp_path / "absent", monkeypatch=monkeypatch)
    assert len(signatures) == 1


def test_empty_receipt_hits_input_bounds_after_statement_preparation(
    protocol_case, tmp_path, monkeypatch
):
    _, signature_path, signatures = protocol_case
    case = perps_margin_signed_case()
    endpoint = tmp_path / "perps-receipt-endpoint"
    endpoint.write_bytes(_ARTIFACT)
    with pytest.raises(GlobalReceiptVerifierErrorV1) as error:
        _run(case, signature_path, endpoint, monkeypatch=monkeypatch, receipt_bytes=b"")
    assert error.value.reason is GlobalReceiptVerifierRejectV1.INPUT_BOUNDS
    assert len(signatures) == 1


@pytest.mark.parametrize("foreign_response", ("image", "request"))
def test_foreign_receipt_response_never_returns_statement(
    protocol_case, tmp_path, monkeypatch, foreign_response
):
    _, signature_path, signatures = protocol_case
    case = perps_margin_signed_case()
    endpoint = tmp_path / "perps-receipt-endpoint"
    endpoint.write_bytes(_ARTIFACT)
    expected = prepare_perps_margin_statement_v2(
        case.assets, case.margin, case.global_pre, case.request
    )
    assert type(expected) is bytes

    def exchange(_descriptor, request, timeout_ms):
        assert timeout_ms == 5_000
        assert request[:8] == b"ZDXRV1RQ"
        assert request[8:40] == bytes.fromhex(IMAGE[2:])
        foreign_request = request[:-1] + bytes((request[-1] ^ 1,))
        response_hash = hashlib.sha256(
            foreign_request if foreign_response == "request" else request
        ).digest()
        response_image = (
            bytes.fromhex(OTHER_IMAGE[2:])
            if foreign_response == "image"
            else request[8:40]
        )
        return b"ZDXRV1OK" + response_hash + response_image, b"", 0

    monkeypatch.setattr(receipt_transport, "_invoke_v1", exchange)
    with pytest.raises(GlobalReceiptVerifierErrorV1) as error:
        _run(case, signature_path, endpoint, monkeypatch=monkeypatch)
    assert error.value.reason is GlobalReceiptVerifierRejectV1.RESPONSE_BINDING
    assert len(signatures) == 1


def test_owned_inputs_survive_mutation_during_signature_io(protocol_case, tmp_path, monkeypatch):
    _, signature_path, _ = protocol_case
    case = perps_margin_signed_case()
    endpoint = tmp_path / "perps-receipt-endpoint"
    endpoint.write_bytes(_ARTIFACT)
    expected = prepare_perps_margin_statement_v2(
        case.assets, case.margin, case.global_pre, case.request
    )
    assert type(expected) is bytes
    requests = _receipt_exchange(monkeypatch, expected)
    original = admission.verify_isolated_economic_command_occurrence_v2

    def mutate_originals(candidate, occurrence, **kwargs):
        object.__setattr__(case.request.command, "amount_atoms", 99)
        object.__setattr__(case.global_pre, "height", 99)
        object.__setattr__(case.guest_role_binding.evidence_manifest, "root_image_id", OTHER_IMAGE)
        return original(candidate, occurrence, **kwargs)

    monkeypatch.setattr(admission, "verify_isolated_economic_command_occurrence_v2", mutate_originals)
    assert _run(case, signature_path, endpoint, monkeypatch=monkeypatch) == expected
    assert len(requests) == 1


__all__ = [
    "PerpsMarginProfileCase",
    "PerpsMarginSignedCase",
    "perps_margin_profile_case",
    "perps_margin_signed_case",
]

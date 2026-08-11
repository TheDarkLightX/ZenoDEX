from __future__ import annotations

import hashlib
from dataclasses import replace

import pytest

from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1
from src.core.asset_lane_projection_v1 import (
    AssetLaneCompositionAcceptedV1,
    AssetLaneCoordinatorContextV1,
    AssetLaneModuleCompatibilityV1,
)
from src.core.asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
    transition_asset_transfer_lane_module_v1,
)
from src.core.asset_transfer_types_v1 import (
    ASSET_TRANSFER_COMMAND_KIND_V1,
    ASSET_TRANSFER_MODULE_SCHEMA_V1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferStateV1,
)
from src.core.global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    LaneCompositionJournalV1,
    ReceiptKindV1,
    RouteCompositionJournalV1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicProfileSnapshotV1,
    EvidenceStatusV1,
    LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteRegistryV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
)
from src.core.lane_composition_receipt_verification_v1 import (
    LaneCompositionReceiptCandidateV1,
    LaneCompositionReceiptEnvelopeV1,
    VerifiedLaneCompositionV1,
    verify_asset_lane_composition_receipt_v1,
)
from src.core.lane_module_receipt_verification_v1 import (
    AssetTransferLaneModuleReceiptCandidateV1,
    LaneModuleReceiptEnvelopeV1,
    ManagedAssetLifecycleLaneModuleReceiptCandidateV1,
    VerifiedLaneModuleTransitionV1,
    verify_asset_transfer_lane_module_receipt_v1,
    verify_managed_asset_lifecycle_lane_module_receipt_v1,
)
from src.core.lane_module_release_route_binding_v1 import (
    ReleaseRouteBoundLaneTransitionV1,
    bind_asset_transfer_lane_output_to_release_route_v1,
    bind_managed_asset_lifecycle_lane_output_to_release_route_v1,
)
from src.core.managed_asset_lifecycle_lane_module_v1 import (
    ManagedAssetLifecycleLaneModuleAcceptedV1,
    ManagedAssetLifecycleLaneModuleInputV1,
    transition_managed_asset_lifecycle_lane_module_v1,
)
from src.core.managed_asset_lifecycle_types_v1 import (
    MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
    ManagedAssetClassV1,
    ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleStateV1,
)
from src.core.receipt_backed_asset_lane_composition_v1 import (
    LaneCompositionAuthorityLevelV1,
    ReceiptBackedAssetLaneCompositionCandidateV1,
    ReceiptBackedAssetLaneCompositionV1,
    compose_receipt_backed_asset_lane_single_v1,
)
from src.core.route_composition_receipt_verification_v1 import (
    RouteCompositionReceiptCandidateV1,
    RouteCompositionReceiptEnvelopeV1,
    VerifiedRouteCompositionV1,
    verify_route_composition_receipt_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _active_evidence() -> tuple[EvidenceStatusV1, ...]:
    return tuple(
        sorted(
            (
                EvidenceStatusV1.SPECIFIED,
                EvidenceStatusV1.IMPLEMENTED,
                EvidenceStatusV1.PROVED,
                EvidenceStatusV1.MOUNTED,
                EvidenceStatusV1.TESTED,
                EvidenceStatusV1.TERMINAL_COMPLETE,
                EvidenceStatusV1.MIGRATABLE,
                EvidenceStatusV1.NO_BYPASS,
                EvidenceStatusV1.RELEASE_BACKED,
            ),
            key=lambda item: item.value,
        )
    )


def _lane_release(lane_id: LaneIdV1, ordinal: int) -> LaneModuleReleaseV1:
    is_asset_lane = lane_id is LaneIdV1.ASSET_TRANSFER
    command_variants = (
        (
            ASSET_TRANSFER_COMMAND_KIND_V1,
            MANAGED_ASSET_BURN_COMMAND_KIND_V1,
            MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        )
        if is_asset_lane
        else ()
    )
    offset = ordinal * 16
    return LaneModuleReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-test",
        state_schema_root=_root(100 + offset),
        command_variants=command_variants,
        terminal_command_variants=(MANAGED_ASSET_BURN_COMMAND_KIND_V1,)
        if is_asset_lane
        else (),
        guest_image_id=_root(101 + offset),
        specification_root=_root(102 + offset),
        source_root=_root(103 + offset),
        toolchain_root=_root(104 + offset),
        terminal_coverage_root=_root(105 + offset),
        migration_compatibility_root=_root(106 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW if is_asset_lane else ReleaseStatusV1.SHADOW,
        accepts_new_objects=is_asset_lane,
        evidence_statuses=(
            _active_evidence()
            if is_asset_lane
            else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _coordinator_release(lane_id: LaneIdV1, ordinal: int) -> LaneCoordinatorReleaseV1:
    is_asset_lane = lane_id is LaneIdV1.ASSET_TRANSFER
    offset = ordinal * 16
    return LaneCoordinatorReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-test",
        coordinator_schema_root=_root(300 + offset),
        guest_image_id=_root(301 + offset),
        specification_root=_root(302 + offset),
        source_root=_root(303 + offset),
        toolchain_root=_root(304 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW
        if is_asset_lane
        else ReleaseStatusV1.SHADOW,
        accepts_new_objects=is_asset_lane,
        evidence_statuses=(
            _active_evidence()
            if is_asset_lane
            else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _profile() -> tuple[EconomicProfileSnapshotV1, dict[str, RouteReleaseV1]]:
    lane_registry = LaneRegistryV1(
        tuple(
            _lane_release(lane_id, ordinal)
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    lane_coordinator_registry = LaneCoordinatorRegistryV1(
        tuple(
            _coordinator_release(lane_id, ordinal)
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    asset_release = lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    routes = tuple(
        RouteReleaseV1.build(
            semantic_version="1.0.0-test",
            command_kind=command_kind,
            ordered_lanes=(LaneIdV1.ASSET_TRANSFER,),
            module_release_ids=(asset_release.release_id,),
            dependency_roles=("VALUE_OWNER",),
            port_schema_roots=(_root(500 + index),),
            guest_image_id=_root(520 + index),
            specification_root=_root(530 + index),
            source_root=_root(540 + index),
            toolchain_root=_root(550 + index),
            oracle_policy_root=_root(510),
            issue_burn_policy_root=_root(511),
            max_cycles=2_000_000,
            max_journal_bytes=131_072,
            status=ReleaseStatusV1.ACTIVE_NEW,
            accepts_new_objects=True,
            evidence_statuses=_active_evidence(),
        )
        for index, command_kind in enumerate(
            (
                ASSET_TRANSFER_COMMAND_KIND_V1,
                MANAGED_ASSET_BURN_COMMAND_KIND_V1,
                MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
            )
        )
    )
    route_registry = RouteRegistryV1(routes)
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=7,
        lane_registry=lane_registry,
        lane_coordinator_registry=lane_coordinator_registry,
        route_registry=route_registry,
        proof_shape_root=_root(520),
        root_image_id=_root(521),
        verifier_registry_root=_root(522),
        migration_registry_root=_root(523),
        policy_registry_root=_root(524),
        terminal_registry_root=_root(525),
        status=ProfileStatusV1.ACTIVE,
    )
    return profile, {route.command_kind: route for route in routes}


def _occurrence(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    *,
    subject_id: str,
    grant_root: str,
) -> EconomicCommandOccurrenceV1:
    return EconomicCommandOccurrenceV1(
        chain_id="zeno-release-route-test",
        deployment_root=_root(1),
        height=11,
        tx_index=2,
        op_index=3,
        command_kind=route.command_kind,
        route_release_id=route.route_release_id,
        subject_id=subject_id,
        grant_root=grant_root,
        nonce=9,
        profile_root=profile.profile_id,
        pre_state_root=_root(2),
        consumed_object_ids=(),
    )


def _asset_input(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    *,
    module_release_id: str | None = None,
) -> AssetTransferLaneModuleInputV1:
    release_id = (
        profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER).release_id
        if module_release_id is None
        else module_release_id
    )
    return AssetTransferLaneModuleInputV1(
        context=AssetTransferContextV1(
            chain_id=occurrence.chain_id,
            deployment_root=occurrence.deployment_root,
            profile_root=occurrence.profile_root,
            writer_epoch=profile.authority_epoch,
            module_release_id=release_id,
            command_occurrence_id=occurrence.occurrence_id,
            subject_id=occurrence.subject_id,
            grant_root=occurrence.grant_root,
        ),
        pre_state=AssetTransferStateV1(
            module_release_id=release_id,
            policies=(AssetTransferPolicyV1("USD", "treasury", 2, True),),
            balances=(
                EconomicAmountV1("alice", "USD", "accounts", 100),
                EconomicAmountV1("bob", "USD", "accounts", 10),
                EconomicAmountV1("treasury", "USD", "accounts", 5),
            ),
            supplies=(AssetSupplyV1("USD", 115),),
        ),
        command=AssetTransferCommandV1(
            ASSET_TRANSFER_COMMAND_KIND_V1,
            "USD",
            "alice",
            "bob",
            30,
            2,
        ),
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
        custody=(),
    )


def _managed_input(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    command_kind: str,
) -> ManagedAssetLifecycleLaneModuleInputV1:
    release_id = profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER).release_id
    return ManagedAssetLifecycleLaneModuleInputV1(
        context=ManagedAssetLifecycleContextV1(
            chain_id=occurrence.chain_id,
            deployment_root=occurrence.deployment_root,
            profile_root=occurrence.profile_root,
            writer_epoch=profile.authority_epoch,
            module_release_id=release_id,
            command_occurrence_id=occurrence.occurrence_id,
            subject_id=occurrence.subject_id,
            grant_root=occurrence.grant_root,
        ),
        pre_state=ManagedAssetLifecycleStateV1(
            module_release_id=release_id,
            policies=(
                ManagedAssetLifecyclePolicyV1(
                    asset="USD",
                    asset_class=ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN,
                    issue_authority_subject="issuer",
                    issue_policy_root=_root(5),
                    burn_policy_root=_root(6),
                    enabled=True,
                ),
            ),
            balances=(EconomicAmountV1("alice", "USD", "accounts", 10),),
            supplies=(AssetSupplyV1("USD", 10),),
        ),
        command=ManagedAssetLifecycleCommandV1(
            command_kind=command_kind,
            asset="USD",
            account_owner="alice",
            amount_atoms=7 if command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V1 else 4,
        ),
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
        custody=(),
    )


def test_asset_output_gets_opaque_active_profile_release_route_binding() -> None:
    profile, routes = _profile()
    occurrence = _occurrence(profile, routes[ASSET_TRANSFER_COMMAND_KIND_V1], subject_id="alice", grant_root=_root(7))
    module_input = _asset_input(profile, occurrence)
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)

    bound = bind_asset_transfer_lane_output_to_release_route_v1(
        profile,
        occurrence,
        module_input,
        accepted,
    )

    assert bound.profile_id == profile.profile_id
    assert bound.route_release_id == routes[ASSET_TRANSFER_COMMAND_KIND_V1].route_release_id
    assert bound.lane_id is LaneIdV1.ASSET_TRANSFER
    assert bound.module_release_id == accepted.module_journal.module_release_id
    assert bound.command_occurrence_id == occurrence.occurrence_id
    assert bound.module_journal_root == accepted.module_journal.journal_root
    assert bound.statement_root == module_input.statement_root
    assert bound.producer_module_schema == ASSET_TRANSFER_MODULE_SCHEMA_V1
    assert bound.route_lane_index == 0
    assert bound.port_schema_root == routes[ASSET_TRANSFER_COMMAND_KIND_V1].port_schema_roots[0]
    assert bound.binding_root == "0x8c984258df8fd4c7f20ad262ac180e5a91d0ba2da1997831bebf3d8ca7608724"
    with pytest.raises(AttributeError, match="immutable"):
        bound._profile_id = _root(999)


@pytest.mark.parametrize(
    ("command_kind", "subject_id", "grant_root"),
    (
        (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, "issuer", _root(5)),
        (MANAGED_ASSET_BURN_COMMAND_KIND_V1, "alice", _root(6)),
    ),
)
def test_managed_issue_and_burn_bind_to_their_exact_governed_routes(
    command_kind: str,
    subject_id: str,
    grant_root: str,
) -> None:
    profile, routes = _profile()
    occurrence = _occurrence(profile, routes[command_kind], subject_id=subject_id, grant_root=grant_root)
    module_input = _managed_input(profile, occurrence, command_kind)
    accepted = transition_managed_asset_lifecycle_lane_module_v1(module_input)
    assert isinstance(accepted, ManagedAssetLifecycleLaneModuleAcceptedV1)

    bound = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
        profile,
        occurrence,
        module_input,
        accepted,
    )

    assert bound.route_release_id == routes[command_kind].route_release_id
    assert bound.statement_root == module_input.statement_root
    assert bound.producer_module_schema == MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1


def test_caller_selected_route_and_inactive_profile_fail_closed() -> None:
    profile, routes = _profile()
    route = routes[ASSET_TRANSFER_COMMAND_KIND_V1]
    occurrence = _occurrence(profile, route, subject_id="alice", grant_root=_root(7))
    wrong_route_occurrence = replace(occurrence, route_release_id=_root(998))
    module_input = _asset_input(profile, wrong_route_occurrence)
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)

    with pytest.raises(ValueError, match="caller-selected route"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            profile,
            wrong_route_occurrence,
            module_input,
            accepted,
        )

    valid_input = _asset_input(profile, occurrence)
    valid_accepted = transition_asset_transfer_lane_module_v1(valid_input)
    assert isinstance(valid_accepted, AssetTransferLaneModuleAcceptedV1)
    with pytest.raises(ValueError, match="profile is not ACTIVE"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            replace(profile, status=ProfileStatusV1.SHADOW),
            occurrence,
            valid_input,
            valid_accepted,
        )


def test_command_substitution_and_unregistered_module_release_fail_closed() -> None:
    profile, routes = _profile()
    issue_route = routes[MANAGED_ASSET_ISSUE_COMMAND_KIND_V1]
    occurrence = _occurrence(profile, issue_route, subject_id="alice", grant_root=_root(6))
    burn_input = _managed_input(profile, occurrence, MANAGED_ASSET_BURN_COMMAND_KIND_V1)
    burn_accepted = transition_managed_asset_lifecycle_lane_module_v1(burn_input)
    assert isinstance(burn_accepted, ManagedAssetLifecycleLaneModuleAcceptedV1)
    with pytest.raises(ValueError, match="command kind mismatch"):
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            profile,
            occurrence,
            burn_input,
            burn_accepted,
        )

    transfer_occurrence = _occurrence(
        profile,
        routes[ASSET_TRANSFER_COMMAND_KIND_V1],
        subject_id="alice",
        grant_root=_root(7),
    )
    foreign_input = _asset_input(profile, transfer_occurrence, module_release_id=_root(997))
    foreign_accepted = transition_asset_transfer_lane_module_v1(foreign_input)
    assert isinstance(foreign_accepted, AssetTransferLaneModuleAcceptedV1)
    with pytest.raises(ValueError, match="module release mismatch"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            profile,
            transfer_occurrence,
            foreign_input,
            foreign_accepted,
        )


def test_occurrence_subject_and_cross_domain_substitution_fail_closed() -> None:
    profile, routes = _profile()
    route = routes[ASSET_TRANSFER_COMMAND_KIND_V1]
    occurrence = _occurrence(profile, route, subject_id="alice", grant_root=_root(7))
    module_input = _asset_input(profile, occurrence)
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)

    wrong_subject = replace(occurrence, subject_id="mallory")
    with pytest.raises(ValueError, match="subject mismatch"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            profile,
            wrong_subject,
            module_input,
            accepted,
        )
    wrong_chain = replace(occurrence, chain_id="other-chain")
    with pytest.raises(ValueError, match="chain id mismatch"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            profile,
            wrong_chain,
            module_input,
            accepted,
        )


def test_release_route_bound_witness_rejects_public_construction() -> None:
    with pytest.raises(TypeError, match="binder-constructed"):
        ReleaseRouteBoundLaneTransitionV1(
            object(),
            _root(1),
            _root(2),
            LaneIdV1.ASSET_TRANSFER,
            _root(3),
            _root(4),
            _root(5),
            _root(6),
            ASSET_TRANSFER_MODULE_SCHEMA_V1,
            0,
            _root(7),
        )


class _RecordingModuleReceiptVerifier:
    def __init__(self, *, reject: bool = False) -> None:
        self.reject = reject
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        self.calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))
        if self.reject:
            raise ValueError("test verifier rejected module receipt")


def _accepted_transfer_with_binding() -> tuple[
    EconomicProfileSnapshotV1,
    EconomicCommandOccurrenceV1,
    AssetTransferLaneModuleInputV1,
    AssetTransferLaneModuleAcceptedV1,
    ReleaseRouteBoundLaneTransitionV1,
]:
    profile, routes = _profile()
    occurrence = _occurrence(
        profile,
        routes[ASSET_TRANSFER_COMMAND_KIND_V1],
        subject_id="alice",
        grant_root=_root(7),
    )
    module_input = _asset_input(profile, occurrence)
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)
    bound = bind_asset_transfer_lane_output_to_release_route_v1(
        profile,
        occurrence,
        module_input,
        accepted,
    )
    return profile, occurrence, module_input, accepted, bound


def test_module_receipt_verification_uses_release_image_and_exact_journal() -> None:
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()
    receipt_bytes = b"succinct-asset-transfer-module-receipt-v1"
    verifier = _RecordingModuleReceiptVerifier()

    verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1(
            profile,
            occurrence,
            module_input,
            accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, receipt_bytes),
        ),
        verifier,
    )

    release = profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    journal_bytes = canonical_global_bytes_v1(accepted.module_journal)
    assert verifier.calls == [(receipt_bytes, release.guest_image_id, journal_bytes)]
    assert verified.release_route_binding_root == bound.binding_root
    assert verified.expected_image_id == release.guest_image_id
    assert verified.module_journal_root == accepted.module_journal.journal_root
    assert verified.module_journal_digest == "0x" + hashlib.sha256(journal_bytes).hexdigest()
    assert verified.receipt_digest == "0x" + hashlib.sha256(receipt_bytes).hexdigest()
    assert verified.receipt_kind is ReceiptKindV1.SUCCINCT
    assert verified.receipt_digest != accepted.module_journal.receipt_root
    assert verified.binding_root == "0xff9d4232a72f8e1039d6afd78ae92052aaca8f29b5d7bd0dd7cf7b6ec50c844f"
    with pytest.raises(AttributeError, match="immutable"):
        verified._receipt_digest = _root(999)


@pytest.mark.parametrize(
    ("command_kind", "subject_id", "grant_root"),
    (
        (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, "issuer", _root(5)),
        (MANAGED_ASSET_BURN_COMMAND_KIND_V1, "alice", _root(6)),
    ),
)
def test_managed_module_receipts_gain_only_release_image_bound_authority(
    command_kind: str,
    subject_id: str,
    grant_root: str,
) -> None:
    profile, routes = _profile()
    occurrence = _occurrence(
        profile,
        routes[command_kind],
        subject_id=subject_id,
        grant_root=grant_root,
    )
    module_input = _managed_input(profile, occurrence, command_kind)
    accepted = transition_managed_asset_lifecycle_lane_module_v1(module_input)
    assert isinstance(accepted, ManagedAssetLifecycleLaneModuleAcceptedV1)
    bound = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
        profile,
        occurrence,
        module_input,
        accepted,
    )
    verifier = _RecordingModuleReceiptVerifier()

    verified = verify_managed_asset_lifecycle_lane_module_receipt_v1(
        ManagedAssetLifecycleLaneModuleReceiptCandidateV1(
            profile,
            occurrence,
            module_input,
            accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                ("receipt:" + command_kind).encode("ascii"),
            ),
        ),
        verifier,
    )

    assert verified.command_occurrence_id == occurrence.occurrence_id
    assert verified.statement_root == module_input.statement_root
    assert len(verifier.calls) == 1


def test_module_receipt_rejects_empty_nonsuccinct_and_verifier_failure() -> None:
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()

    for receipt_kind, receipt_bytes, message in (
        (ReceiptKindV1.SUCCINCT, b"", "non-empty"),
        (ReceiptKindV1.COMPOSITE, b"composite", "succinct"),
    ):
        verifier = _RecordingModuleReceiptVerifier()
        with pytest.raises(ValueError, match=message):
            verify_asset_transfer_lane_module_receipt_v1(
                AssetTransferLaneModuleReceiptCandidateV1(
                    profile,
                    occurrence,
                    module_input,
                    accepted,
                    bound,
                    LaneModuleReceiptEnvelopeV1(receipt_kind, receipt_bytes),
                ),
                verifier,
            )
        assert verifier.calls == []

    rejecting_verifier = _RecordingModuleReceiptVerifier(reject=True)
    with pytest.raises(ValueError, match="test verifier rejected"):
        verify_asset_transfer_lane_module_receipt_v1(
            AssetTransferLaneModuleReceiptCandidateV1(
                profile,
                occurrence,
                module_input,
                accepted,
                bound,
                LaneModuleReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"cryptographically-invalid",
                ),
            ),
            rejecting_verifier,
        )
    assert len(rejecting_verifier.calls) == 1


def test_structural_binding_cannot_authorize_a_mutated_module_journal() -> None:
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()
    with pytest.raises(ValueError, match="receipt root mismatch"):
        replace(
            accepted,
            module_journal=replace(accepted.module_journal, receipt_root=_root(999)),
        )
    substituted_input = replace(
        module_input,
        command=replace(module_input.command, amount_atoms=29),
    )
    substituted = transition_asset_transfer_lane_module_v1(substituted_input)
    assert isinstance(substituted, AssetTransferLaneModuleAcceptedV1)
    verifier = _RecordingModuleReceiptVerifier()

    with pytest.raises(ValueError, match="structural binding mismatch"):
        verify_asset_transfer_lane_module_receipt_v1(
            AssetTransferLaneModuleReceiptCandidateV1(
                profile,
                occurrence,
                substituted_input,
                substituted,
                bound,
                LaneModuleReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"succinct-module-receipt",
                ),
            ),
            verifier,
        )

    assert verifier.calls == []


def test_verified_module_witness_rejects_public_construction() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedLaneModuleTransitionV1(
            object(),
            object(),
        )


def _verified_transfer_and_coordinator_context() -> tuple[
    EconomicProfileSnapshotV1,
    EconomicCommandOccurrenceV1,
    AssetTransferLaneModuleInputV1,
    AssetTransferLaneModuleAcceptedV1,
    VerifiedLaneModuleTransitionV1,
    AssetLaneCoordinatorContextV1,
]:
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()
    coordinator_release = profile.lane_coordinator_registry.release_for(
        LaneIdV1.ASSET_TRANSFER
    )
    verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1(
            profile,
            occurrence,
            module_input,
            accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"succinct-asset-transfer-module-receipt-v1",
            ),
        ),
        _RecordingModuleReceiptVerifier(),
    )
    coordinator_context = AssetLaneCoordinatorContextV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        coordinator_release_id=coordinator_release.coordinator_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        asset_policy_registry_root=module_input.asset_policy_registry_root,
        fee_policy_registry_root=module_input.fee_policy_registry_root,
        compatible_modules=(
            AssetLaneModuleCompatibilityV1(
                accepted.module_journal.module_release_id,
                accepted.private_port.producer_module_schema,
            ),
        ),
    )
    return profile, occurrence, module_input, accepted, verified, coordinator_context


class _RecordingCompositionReceiptVerifier:
    def __init__(self, *, reject: bool = False) -> None:
        self.reject = reject
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        self.calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))
        if self.reject:
            raise ValueError("test verifier rejected lane composition receipt")


def _structural_asset_lane_composition_fixture() -> tuple[
    EconomicProfileSnapshotV1,
    EconomicCommandOccurrenceV1,
    AssetTransferLaneModuleAcceptedV1,
    VerifiedLaneModuleTransitionV1,
    AssetLaneCoordinatorContextV1,
    LaneCompositionJournalV1,
    ReceiptBackedAssetLaneCompositionV1,
]:
    profile, occurrence, _, accepted, verified, coordinator_context = (
        _verified_transfer_and_coordinator_context()
    )
    result = compose_asset_lane_single_v1(
        coordinator_context,
        accepted.module_journal,
        accepted.private_port,
        accepted.effects,
    )
    assert isinstance(result, AssetLaneCompositionAcceptedV1)
    structural_composition = compose_receipt_backed_asset_lane_single_v1(
        ReceiptBackedAssetLaneCompositionCandidateV1(
            profile,
            occurrence,
            coordinator_context,
            accepted.module_journal,
            accepted.private_port,
            accepted.effects,
            verified,
        )
    )
    return (
        profile,
        occurrence,
        accepted,
        verified,
        coordinator_context,
        result.lane_journal,
        structural_composition,
    )


def test_verified_module_receipt_backs_only_exact_structural_lane_composition() -> None:
    profile, occurrence, _, accepted, verified, coordinator_context = (
        _verified_transfer_and_coordinator_context()
    )

    composition = compose_receipt_backed_asset_lane_single_v1(
        ReceiptBackedAssetLaneCompositionCandidateV1(
            profile,
            occurrence,
            coordinator_context,
            accepted.module_journal,
            accepted.private_port,
            accepted.effects,
            verified,
        )
    )

    assert composition.authority_level is (
        LaneCompositionAuthorityLevelV1.RECEIPT_BACKED_STRUCTURAL_ONLY
    )
    assert composition.profile_id == profile.profile_id
    assert composition.command_occurrence_id == occurrence.occurrence_id
    assert composition.verified_module_binding_root == verified.binding_root
    assert composition.module_receipt_digest == verified.receipt_digest
    assert composition.lane_journal_root != accepted.module_journal.journal_root
    assert composition.binding_root == (
        "0xee2fd20b3a047f1bb86c014decaaeeca38603fd935af8c2fa7c8a0fd3b97d839"
    )


def test_structural_composition_rejects_caller_selected_coordinator_release() -> None:
    profile, occurrence, _, accepted, verified, coordinator_context = (
        _verified_transfer_and_coordinator_context()
    )
    with pytest.raises(ValueError, match="selected coordinator release mismatch"):
        compose_receipt_backed_asset_lane_single_v1(
            ReceiptBackedAssetLaneCompositionCandidateV1(
                profile,
                occurrence,
                replace(coordinator_context, coordinator_release_id=_root(999)),
                accepted.module_journal,
                accepted.private_port,
                accepted.effects,
                verified,
            )
        )


def test_lane_composition_receipt_uses_selected_image_and_exact_journal() -> None:
    (
        profile,
        occurrence,
        _accepted,
        _verified,
        _coordinator_context,
        lane_journal,
        structural_composition,
    ) = _structural_asset_lane_composition_fixture()
    receipt_bytes = b"x"
    verifier = _RecordingCompositionReceiptVerifier()

    verified_composition = verify_asset_lane_composition_receipt_v1(
        LaneCompositionReceiptCandidateV1(
            profile,
            occurrence,
            structural_composition,
            lane_journal,
            LaneCompositionReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, receipt_bytes),
        ),
        verifier,
    )

    coordinator_release = profile.lane_coordinator_registry.release_for(
        LaneIdV1.ASSET_TRANSFER
    )
    lane_journal_bytes = canonical_global_bytes_v1(lane_journal)
    assert verifier.calls == [
        (receipt_bytes, coordinator_release.guest_image_id, lane_journal_bytes)
    ]
    assert verified_composition.profile_id == profile.profile_id
    assert verified_composition.route_release_id == structural_composition.route_release_id
    assert verified_composition.lane_id is LaneIdV1.ASSET_TRANSFER
    assert (
        verified_composition.coordinator_release_id
        == coordinator_release.coordinator_release_id
    )
    assert verified_composition.command_occurrence_id == occurrence.occurrence_id
    assert verified_composition.writer_epoch == profile.authority_epoch
    assert verified_composition.structural_composition_root == structural_composition.binding_root
    assert verified_composition.lane_journal_root == lane_journal.journal_root
    assert verified_composition.lane_journal_digest == (
        "0x" + hashlib.sha256(lane_journal_bytes).hexdigest()
    )
    assert verified_composition.expected_image_id == coordinator_release.guest_image_id
    assert verified_composition.receipt_digest == (
        "0x" + hashlib.sha256(receipt_bytes).hexdigest()
    )
    assert verified_composition.receipt_kind is ReceiptKindV1.SUCCINCT
    assert verified_composition.binding_root == (
        "0x033c60a4fcf6dbf3c6d9b3893106060bcb344ff0662e149322bfb3ffce8037cb"
    )


def test_lane_composition_receipt_rejects_empty_nonsuccinct_and_verifier_failure() -> None:
    profile, occurrence, _, _, _, lane_journal, structural_composition = (
        _structural_asset_lane_composition_fixture()
    )
    for receipt_kind, receipt_bytes, message in (
        (ReceiptKindV1.SUCCINCT, b"", "non-empty"),
        (ReceiptKindV1.COMPOSITE, b"composite", "succinct"),
    ):
        verifier = _RecordingCompositionReceiptVerifier()
        with pytest.raises(ValueError, match=message):
            verify_asset_lane_composition_receipt_v1(
                LaneCompositionReceiptCandidateV1(
                    profile,
                    occurrence,
                    structural_composition,
                    lane_journal,
                    LaneCompositionReceiptEnvelopeV1(receipt_kind, receipt_bytes),
                ),
                verifier,
            )
        assert verifier.calls == []

    rejecting_verifier = _RecordingCompositionReceiptVerifier(reject=True)
    with pytest.raises(ValueError, match="test verifier rejected"):
        verify_asset_lane_composition_receipt_v1(
            LaneCompositionReceiptCandidateV1(
                profile,
                occurrence,
                structural_composition,
                lane_journal,
                LaneCompositionReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"cryptographically-invalid",
                ),
            ),
            rejecting_verifier,
        )
    assert len(rejecting_verifier.calls) == 1


def test_lane_composition_receipt_rejects_wrong_journal_without_verifier_bypass() -> None:
    profile, occurrence, _, _, _, lane_journal, structural_composition = (
        _structural_asset_lane_composition_fixture()
    )
    verifier = _RecordingCompositionReceiptVerifier()

    with pytest.raises(ValueError, match="journal post-lane root mismatch"):
        verify_asset_lane_composition_receipt_v1(
            LaneCompositionReceiptCandidateV1(
                profile,
                occurrence,
                structural_composition,
                replace(lane_journal, post_lane_root=_root(999)),
                LaneCompositionReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"succinct-lane-composition-receipt",
                ),
            ),
            verifier,
        )

    assert verifier.calls == []


def test_verified_lane_composition_rejects_public_construction() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedLaneCompositionV1(
            object(),
            object(),
        )


def test_valid_module_receipt_cannot_back_a_different_lane_journal() -> None:
    profile, occurrence, module_input, accepted, _, coordinator_context = (
        _verified_transfer_and_coordinator_context()
    )
    substituted_input = replace(
        module_input,
        command=replace(module_input.command, amount_atoms=29),
    )
    substituted = transition_asset_transfer_lane_module_v1(substituted_input)
    assert isinstance(substituted, AssetTransferLaneModuleAcceptedV1)
    substituted_bound = bind_asset_transfer_lane_output_to_release_route_v1(
        profile,
        occurrence,
        substituted_input,
        substituted,
    )
    substituted_verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1(
            profile,
            occurrence,
            substituted_input,
            substituted,
            substituted_bound,
            LaneModuleReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"succinct-substituted-module-receipt-v1",
            ),
        ),
        _RecordingModuleReceiptVerifier(),
    )

    with pytest.raises(ValueError, match="verified module journal root mismatch"):
        compose_receipt_backed_asset_lane_single_v1(
            ReceiptBackedAssetLaneCompositionCandidateV1(
                profile,
                occurrence,
                coordinator_context,
                accepted.module_journal,
                accepted.private_port,
                accepted.effects,
                substituted_verified,
            )
        )


def test_receipt_backed_lane_composition_rejects_public_construction() -> None:
    with pytest.raises(TypeError, match="composition-constructed"):
        ReceiptBackedAssetLaneCompositionV1(
            object(),
            object(),  # type: ignore[arg-type]
        )


def _verified_route_composition_fixture() -> tuple[
    EconomicProfileSnapshotV1,
    EconomicCommandOccurrenceV1,
    LaneCompositionJournalV1,
    VerifiedLaneCompositionV1,
    RouteCompositionJournalV1,
]:
    (
        profile,
        occurrence,
        _accepted,
        _verified_module,
        _coordinator_context,
        lane_journal,
        structural_composition,
    ) = _structural_asset_lane_composition_fixture()
    verified_lane = verify_asset_lane_composition_receipt_v1(
        LaneCompositionReceiptCandidateV1(
            profile,
            occurrence,
            structural_composition,
            lane_journal,
            LaneCompositionReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"succinct-lane-composition-receipt-v1",
            ),
        ),
        _RecordingCompositionReceiptVerifier(),
    )
    route_journal = RouteCompositionJournalV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        route_release_id=occurrence.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        ordered_lane_journal_roots=(lane_journal.journal_root,),
        pre_state_root=occurrence.pre_state_root,
        post_state_root=_root(8_001),
        effect_plan_root=lane_journal.effect_plan_root,
        terminal_obligations_root=lane_journal.terminal_obligations_root,
    )
    return profile, occurrence, lane_journal, verified_lane, route_journal


def test_route_composition_receipt_uses_selected_image_and_exact_lane_witness() -> None:
    # Arrange
    profile, occurrence, lane_journal, verified_lane, route_journal = (
        _verified_route_composition_fixture()
    )
    receipt_bytes = b"x"
    verifier = _RecordingCompositionReceiptVerifier()

    # Act
    verified_route = verify_route_composition_receipt_v1(
        RouteCompositionReceiptCandidateV1(
            profile,
            occurrence,
            (lane_journal,),
            (verified_lane,),
            route_journal,
            RouteCompositionReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, receipt_bytes),
        ),
        verifier,
    )

    # Assert
    route = profile.route_registry.route_for_command(occurrence.command_kind)
    route_journal_bytes = canonical_global_bytes_v1(route_journal)
    assert verifier.calls == [(receipt_bytes, route.guest_image_id, route_journal_bytes)]
    assert verified_route.profile_id == profile.profile_id
    assert verified_route.route_release_id == route.route_release_id
    assert verified_route.command_occurrence_id == occurrence.occurrence_id
    assert verified_route.writer_epoch == profile.authority_epoch
    assert verified_route.ordered_lane_ids == route.ordered_lanes
    assert verified_route.ordered_lane_binding_roots == (verified_lane.binding_root,)
    assert verified_route.ordered_lane_journal_roots == (lane_journal.journal_root,)
    assert verified_route.route_journal_root == route_journal.journal_root
    assert verified_route.route_journal_digest == (
        "0x" + hashlib.sha256(route_journal_bytes).hexdigest()
    )
    assert verified_route.expected_image_id == route.guest_image_id
    assert verified_route.receipt_digest == "0x" + hashlib.sha256(receipt_bytes).hexdigest()
    assert verified_route.receipt_kind is ReceiptKindV1.SUCCINCT
    assert verified_route.binding_root == (
        "0xfc0d847ff20c8a00aef5865eb65d51aca7b7b6ff70246c03b070a8a190d1e817"
    )


def test_route_composition_rejects_structural_duplicate_and_journal_substitution() -> None:
    # Arrange
    profile, occurrence, lane_journal, verified_lane, route_journal = (
        _verified_route_composition_fixture()
    )
    receipt = RouteCompositionReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"route-receipt")

    for lane_journals, verified_lanes, selected_journal, message in (
        ((lane_journal,), (), route_journal, "lane witness count"),
        (
            (lane_journal, lane_journal),
            (verified_lane, verified_lane),
            route_journal,
            "lane journal count",
        ),
        (
            (lane_journal,),
            (verified_lane,),
            replace(route_journal, command_occurrence_id=_root(8_002)),
            "journal occurrence",
        ),
        (
            (lane_journal,),
            (verified_lane,),
            replace(route_journal, writer_epoch=profile.authority_epoch - 1),
            "writer epoch",
        ),
        (
            (lane_journal,),
            (verified_lane,),
            replace(route_journal, writer_epoch=profile.authority_epoch + 1),
            "writer epoch",
        ),
    ):
        verifier = _RecordingCompositionReceiptVerifier()

        # Act / Assert
        with pytest.raises(ValueError, match=message):
            verify_route_composition_receipt_v1(
                RouteCompositionReceiptCandidateV1(
                    profile,
                    occurrence,
                    lane_journals,
                    verified_lanes,
                    selected_journal,
                    receipt,
                ),
                verifier,
            )
        assert verifier.calls == []

    with pytest.raises(TypeError, match="verified lane witnesses must be typed"):
        RouteCompositionReceiptCandidateV1(
            profile,
            occurrence,
            (lane_journal,),
            (object(),),
            route_journal,
            receipt,
        )


def test_valid_lane_witness_cannot_back_a_different_route_lane_journal() -> None:
    # Arrange: preserve the route shape while changing the consumed lane statement.
    profile, occurrence, lane_journal, verified_lane, route_journal = (
        _verified_route_composition_fixture()
    )
    substituted_lane_journal = replace(lane_journal, post_lane_root=_root(8_004))
    substituted_route_journal = replace(
        route_journal,
        ordered_lane_journal_roots=(substituted_lane_journal.journal_root,),
    )
    verifier = _RecordingCompositionReceiptVerifier()

    # Act / Assert: the old opaque lane witness cannot authorize the new journal.
    with pytest.raises(ValueError, match="lane witness journal"):
        verify_route_composition_receipt_v1(
            RouteCompositionReceiptCandidateV1(
                profile,
                occurrence,
                (substituted_lane_journal,),
                (verified_lane,),
                substituted_route_journal,
                RouteCompositionReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"route-receipt",
                ),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_route_composition_receipt_rejects_empty_wrong_kind_and_verifier_failure() -> None:
    # Arrange
    profile, occurrence, lane_journal, verified_lane, route_journal = (
        _verified_route_composition_fixture()
    )

    for receipt_kind, receipt_bytes, message in (
        (ReceiptKindV1.SUCCINCT, b"", "non-empty"),
        (ReceiptKindV1.COMPOSITE, b"composite", "succinct"),
    ):
        verifier = _RecordingCompositionReceiptVerifier()

        # Act / Assert
        with pytest.raises(ValueError, match=message):
            verify_route_composition_receipt_v1(
                RouteCompositionReceiptCandidateV1(
                    profile,
                    occurrence,
                    (lane_journal,),
                    (verified_lane,),
                    route_journal,
                    RouteCompositionReceiptEnvelopeV1(receipt_kind, receipt_bytes),
                ),
                verifier,
            )
        assert verifier.calls == []

    rejecting_verifier = _RecordingCompositionReceiptVerifier(reject=True)
    with pytest.raises(ValueError, match="test verifier rejected"):
        verify_route_composition_receipt_v1(
            RouteCompositionReceiptCandidateV1(
                profile,
                occurrence,
                (lane_journal,),
                (verified_lane,),
                route_journal,
                RouteCompositionReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"cryptographically-invalid-route-receipt",
                ),
            ),
            rejecting_verifier,
        )
    assert len(rejecting_verifier.calls) == 1


def test_verified_route_composition_rejects_public_construction() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedRouteCompositionV1(object(), object())


def test_semantically_identical_route_rebuild_preserves_verified_binding_root() -> None:
    # Arrange
    profile, occurrence, lane_journal, verified_lane, route_journal = (
        _verified_route_composition_fixture()
    )
    receipt = RouteCompositionReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"x")

    # Act
    first = verify_route_composition_receipt_v1(
        RouteCompositionReceiptCandidateV1(
            profile,
            occurrence,
            (lane_journal,),
            (verified_lane,),
            route_journal,
            receipt,
        ),
        _RecordingCompositionReceiptVerifier(),
    )
    rebuilt = verify_route_composition_receipt_v1(
        RouteCompositionReceiptCandidateV1(
            profile,
            occurrence,
            (replace(lane_journal),),
            (verified_lane,),
            replace(route_journal),
            receipt,
        ),
        _RecordingCompositionReceiptVerifier(),
    )

    # Assert
    assert rebuilt.binding_root == first.binding_root

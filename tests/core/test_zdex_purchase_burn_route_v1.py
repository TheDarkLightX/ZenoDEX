from __future__ import annotations

import hashlib
from dataclasses import replace

import pytest

from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    REQUIRED_ACTIVE_EVIDENCE_V1,
    AssetConservationRowV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    EvidenceStatusV1,
    GlobalEconomicEffectPlanV1,
    LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    LaneWriteV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteRegistryV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
)
from src.core.zdex_fee_allocation_receipt_verification_v1 import (
    GovernedZDEXFeeAllocationProfileV1,
    VerifiedZDEXFeeAllocationV1,
    ZDEXFeeAllocationReceiptCandidateV1,
    bind_zdex_fee_allocation_shadow_profile_v1,
    verify_zdex_fee_allocation_receipt_v1,
)
from src.core.zdex_fee_allocation_types_v1 import (
    FEE_ALLOCATION_OUTPUT_ROLE_V1,
    PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
    ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
    ZDEXFeeAllocationPolicyV1,
    zdex_fee_allocation_port_schema_root_v1,
)
from src.core.zdex_fee_allocation_v1 import (
    ZDEX_FEE_DESTINATIONS_V1,
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationOccurrenceV1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeStateV1,
    candidate_zdex_fee_allocation_policy_v1,
    transition_zdex_fee_allocation_v1,
)
from src.core.zdex_hyperdeflation_types_v1 import (
    ZDEXAmountBucketV1,
    ZDEXSupplyStateV1,
)
from src.core.zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXBurnReceiptCandidateV1,
    ZDEXLaneReceiptEnvelopeV1,
    ZDEXPurchaseReceiptCandidateV1,
    verify_zdex_amm_purchase_receipt_v1,
    verify_zdex_burn_receipt_v1,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEXAMMPurchaseJournalV1,
    ZDEXBurnJournalV1,
    ZDEXPurchaseBurnRouteRejectCodeV1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
)
from src.core.zdex_purchase_burn_route_v1 import (
    GovernedZDEXPurchaseBurnRouteV1,
    ZDEXPurchaseBurnRouteCandidateV1,
    ZDEXPurchaseBurnRouteRejectedV1,
    bind_zdex_purchase_burn_shadow_profile_v1,
    compose_zdex_purchase_burn_route_v1,
)
from src.core.zdex_tokenomics_fee_lane_coordinator_v1 import (
    ZDEXTokenomicsFeeAllocationLaneCandidateV1,
    compose_zdex_tokenomics_fee_allocation_lane_v1,
)
from src.core.zdex_tokenomics_fee_lane_receipt_verification_v1 import (
    ZDEXTokenomicsFeeLaneReceiptCandidateV1,
    verify_zdex_tokenomics_fee_lane_receipt_v1,
)
from src.core.zdex_tokenomics_fee_lane_v1 import (
    ZDEXTokenomicsFeeAllocationCoordinatorContextV1,
    build_zdex_tokenomics_fee_allocation_module_journal_v1,
    build_zdex_tokenomics_fee_allocation_private_port_v1,
)
from src.core.zdex_tokenomics_lane_v1 import (
    ZDEXTokenomicsLaneCompositionAcceptedV1,
    ZDEXTokenomicsLaneStateV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


class _HostileRoot(str):
    """Valid-looking scalar with attacker-controlled canonical behavior."""

    def to_canonical(self) -> str:
        return str(self)


def _lane_release(lane_id: LaneIdV1, ordinal: int) -> LaneModuleReleaseV1:
    offset = ordinal * 16
    command_variants: tuple[str, ...] = (PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,)
    if lane_id is LaneIdV1.ZDEX_TOKENOMICS:
        command_variants = (
            PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
            PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
        )
    return LaneModuleReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-shadow-test",
        state_schema_root=_root(100 + offset),
        command_variants=command_variants,
        terminal_command_variants=(),
        guest_image_id=_root(101 + offset),
        specification_root=_root(102 + offset),
        source_root=_root(103 + offset),
        toolchain_root=_root(104 + offset),
        terminal_coverage_root=_root(105 + offset),
        migration_compatibility_root=_root(106 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


def _route_release(
    spot_release: LaneModuleReleaseV1,
    burn_release: LaneModuleReleaseV1,
    *,
    dependency_roles: tuple[str, str] = ("AMM_PURCHASE_OUTPUT", "ZDEX_BURN_INPUT"),
    guest_image_id: str = _root(500),
) -> RouteReleaseV1:
    return RouteReleaseV1.build(
        semantic_version="1.0.0-shadow-test",
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        ordered_lanes=(LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS),
        module_release_ids=(spot_release.release_id, burn_release.release_id),
        dependency_roles=dependency_roles,
        port_schema_roots=(
            zdex_amm_purchase_port_schema_root_v1(),
            zdex_burn_port_schema_root_v1(),
        ),
        guest_image_id=guest_image_id,
        specification_root=_root(501),
        source_root=_root(502),
        toolchain_root=_root(503),
        oracle_policy_root=_root(504),
        issue_burn_policy_root=_root(505),
        max_cycles=2_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


def _allocation_route_release(
    burn_release: LaneModuleReleaseV1,
) -> RouteReleaseV1:
    return RouteReleaseV1.build(
        semantic_version="1.0.0-shadow-test",
        command_kind=PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
        ordered_lanes=(LaneIdV1.ZDEX_TOKENOMICS,),
        module_release_ids=(burn_release.release_id,),
        dependency_roles=(FEE_ALLOCATION_OUTPUT_ROLE_V1,),
        port_schema_roots=(zdex_fee_allocation_port_schema_root_v1(),),
        guest_image_id=_root(510),
        specification_root=_root(511),
        source_root=_root(512),
        toolchain_root=_root(513),
        oracle_policy_root=_root(514),
        issue_burn_policy_root=_root(515),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


def _coordinator_release(
    lane_id: LaneIdV1,
    ordinal: int,
) -> LaneCoordinatorReleaseV1:
    offset = ordinal * 16
    return LaneCoordinatorReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-shadow-test",
        coordinator_schema_root=_root(700 + offset),
        guest_image_id=_root(701 + offset),
        specification_root=_root(702 + offset),
        source_root=_root(703 + offset),
        toolchain_root=_root(704 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


def _governed_shadow_profile(
    *,
    spot_release: LaneModuleReleaseV1,
    tokenomics_release: LaneModuleReleaseV1,
    buyback_route: RouteReleaseV1,
    allocation_route: RouteReleaseV1,
    policy_root: str,
) -> tuple[EconomicProfileSnapshotV1, EconomicPolicyRegistryV1]:
    releases = []
    for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1):
        if lane_id is LaneIdV1.SPOT_LIQUIDITY:
            releases.append(spot_release)
        elif lane_id is LaneIdV1.ZDEX_TOKENOMICS:
            releases.append(tokenomics_release)
        else:
            releases.append(_lane_release(lane_id, ordinal + 10))
    lane_registry = LaneRegistryV1(tuple(releases))
    coordinator_registry = LaneCoordinatorRegistryV1(
        tuple(
            _coordinator_release(lane_id, ordinal)
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    route_registry = RouteRegistryV1(
        tuple(sorted((buyback_route, allocation_route), key=lambda route: route.command_kind))
    )
    policy_registry = EconomicPolicyRegistryV1(
        (
            EconomicPolicyBindingV1(
                ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
                PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
                policy_root,
            ),
        )
    )
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=11,
        lane_registry=lane_registry,
        lane_coordinator_registry=coordinator_registry,
        route_registry=route_registry,
        proof_shape_root=_root(810),
        root_image_id=_root(811),
        verifier_registry_root=_root(812),
        migration_registry_root=_root(813),
        policy_registry_root=policy_registry.registry_root,
        terminal_registry_root=_root(814),
        status=ProfileStatusV1.SHADOW,
    )
    return profile, policy_registry


def _occurrence(
    route: RouteReleaseV1,
    profile: EconomicProfileSnapshotV1,
) -> EconomicCommandOccurrenceV1:
    return EconomicCommandOccurrenceV1(
        chain_id="zenodex-shadow",
        deployment_root=_root(1),
        height=7,
        tx_index=2,
        op_index=1,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        command_body_hash=_root(3),
        route_release_id=route.route_release_id,
        subject_id="protocol-buyback-controller",
        grant_root=_root(2),
        nonce=9,
        profile_root=profile.profile_id,
        pre_state_root=_root(4),
        consumed_object_ids=(),
    )


def _purchase_journal(
    *,
    route: RouteReleaseV1,
    spot_release: LaneModuleReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    quote_atoms: int = 125,
    purchased_atoms: int = 40,
    quote_owned_atoms: int = 10_000,
    quote_supply_atoms: int = 10_000,
    zdex_owned_atoms: int = 1_000,
    zdex_supply_atoms: int = 1_000,
    effect_plan_root: str = _root(900),
) -> ZDEXAMMPurchaseJournalV1:
    return ZDEXAMMPurchaseJournalV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=11,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        spot_module_release_id=spot_release.release_id,
        issue_burn_policy_root=route.issue_burn_policy_root,
        buyback_budget_occurrence_root=_root(590),
        quote_asset_id=_root(600),
        zdex_asset_id=_root(601),
        quote_source_bucket_id="protocol-fee-buyback-reserve",
        quote_pool_bucket_id="pool:quote",
        zdex_pool_bucket_id="pool:zdex",
        burn_bucket_id="protocol:zdex-burn-transient",
        quote_amount_in_atoms=quote_atoms,
        purchased_zdex_atoms=purchased_atoms,
        quote_source_pre_atoms=1_000,
        quote_source_post_atoms=1_000 - quote_atoms,
        quote_pool_pre_atoms=2_000,
        quote_pool_post_atoms=2_000 + quote_atoms,
        zdex_pool_pre_atoms=500,
        zdex_pool_post_atoms=500 - purchased_atoms,
        burn_bucket_pre_atoms=0,
        burn_bucket_post_atoms=purchased_atoms,
        quote_owned_atoms=quote_owned_atoms,
        quote_supply_atoms=quote_supply_atoms,
        zdex_owned_atoms=zdex_owned_atoms,
        zdex_supply_atoms=zdex_supply_atoms,
        pre_spot_lane_root=_root(610),
        post_spot_lane_root=_root(611),
        effect_plan_root=effect_plan_root,
    )


def _purchase_effects(
    journal: ZDEXAMMPurchaseJournalV1,
) -> GlobalEconomicEffectPlanV1:
    rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.quote_source_bucket_id,
                    journal.quote_asset_id,
                    "zenoledger:protocol-buyback",
                    -journal.quote_amount_in_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.quote_pool_bucket_id,
                    journal.quote_asset_id,
                    "zenoledger:amm-pool",
                    journal.quote_amount_in_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.zdex_pool_bucket_id,
                    journal.zdex_asset_id,
                    "zenoledger:amm-pool",
                    -journal.purchased_zdex_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.burn_bucket_id,
                    journal.zdex_asset_id,
                    "zenoledger:protocol-burn",
                    journal.purchased_zdex_atoms,
                ),
            ),
            key=lambda row: row.key,
        )
    )
    conservation = tuple(
        sorted(
            (
                AssetConservationRowV1(
                    journal.quote_asset_id,
                    journal.quote_owned_atoms,
                    journal.quote_owned_atoms,
                    journal.quote_supply_atoms,
                    journal.quote_supply_atoms,
                    0,
                    0,
                ),
                AssetConservationRowV1(
                    journal.zdex_asset_id,
                    journal.zdex_owned_atoms,
                    journal.zdex_owned_atoms,
                    journal.zdex_supply_atoms,
                    journal.zdex_supply_atoms,
                    0,
                    0,
                ),
            ),
            key=lambda row: row.asset,
        )
    )
    return GlobalEconomicEffectPlanV1(
        rows=rows,
        asset_conservation=conservation,
        fee_conservation=(),
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.SPOT_LIQUIDITY,
                journal.pre_spot_lane_root,
                journal.post_spot_lane_root,
            ),
        ),
        occurrence_consumptions=(journal.command_occurrence_id,),
        external_outbox_enqueue=(),
    )


def _burn_journal(
    *,
    route: RouteReleaseV1,
    burn_release: LaneModuleReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    purchase: ZDEXAMMPurchaseJournalV1,
    burned_atoms: int | None = None,
    burn_bucket_id: str | None = None,
    purchase_occurrence_root: str | None = None,
    owned_pre_atoms: int | None = None,
    supply_pre_atoms: int | None = None,
    effect_plan_root: str = _root(901),
) -> ZDEXBurnJournalV1:
    burned = purchase.purchased_zdex_atoms if burned_atoms is None else burned_atoms
    owned_pre = purchase.zdex_owned_atoms if owned_pre_atoms is None else owned_pre_atoms
    supply_pre = purchase.zdex_supply_atoms if supply_pre_atoms is None else supply_pre_atoms
    return ZDEXBurnJournalV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=purchase.writer_epoch,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        tokenomics_module_release_id=burn_release.release_id,
        issue_burn_policy_root=route.issue_burn_policy_root,
        buyback_budget_occurrence_root=purchase.buyback_budget_occurrence_root,
        authorized_quote_input_atoms=purchase.quote_amount_in_atoms,
        purchase_occurrence_root=(
            purchase.journal_root
            if purchase_occurrence_root is None
            else purchase_occurrence_root
        ),
        route_context_root=_root(619),
        zdex_asset_id=purchase.zdex_asset_id,
        burn_bucket_id=(
            purchase.burn_bucket_id if burn_bucket_id is None else burn_bucket_id
        ),
        burned_zdex_atoms=burned,
        burn_bucket_pre_atoms=burned,
        burn_bucket_post_atoms=0,
        zdex_owned_pre_atoms=owned_pre,
        zdex_owned_post_atoms=owned_pre - burned,
        zdex_supply_pre_atoms=supply_pre,
        zdex_supply_post_atoms=supply_pre - burned,
        pre_tokenomics_burn_substate_root=_root(620),
        post_tokenomics_burn_substate_root=_root(621),
        effect_plan_root=effect_plan_root,
    )


def _burn_effects(journal: ZDEXBurnJournalV1) -> GlobalEconomicEffectPlanV1:
    rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.BURN,
                    "protocol:zdex-supply",
                    journal.zdex_asset_id,
                    "zenoledger:protocol-supply",
                    -journal.burned_zdex_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.burn_bucket_id,
                    journal.zdex_asset_id,
                    "zenoledger:protocol-burn",
                    -journal.burned_zdex_atoms,
                ),
            ),
            key=lambda row: row.key,
        )
    )
    return GlobalEconomicEffectPlanV1(
        rows=rows,
        asset_conservation=(
            AssetConservationRowV1(
                journal.zdex_asset_id,
                journal.zdex_owned_pre_atoms,
                journal.zdex_owned_post_atoms,
                journal.zdex_supply_pre_atoms,
                journal.zdex_supply_post_atoms,
                0,
                journal.burned_zdex_atoms,
            ),
        ),
        fee_conservation=(),
        lane_writes=(),
        occurrence_consumptions=(journal.command_occurrence_id,),
        external_outbox_enqueue=(),
    )


def _buyback_budget(
    *,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    policy: ZDEXFeeAllocationPolicyV1,
    allocation_route: RouteReleaseV1,
    route: RouteReleaseV1,
    burn_release: LaneModuleReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    purchase: ZDEXAMMPurchaseJournalV1,
) -> tuple[
    ZDEXFeeAllocationOccurrenceV1,
    VerifiedZDEXFeeAllocationV1,
    ZDEXFeeAllocationReceiptCandidateV1,
]:
    charged_fee_atoms = purchase.quote_amount_in_atoms * 5
    state = ZDEXFeeStateV1(
        fee_asset_id=purchase.quote_asset_id,
        policy_root=policy.policy_root,
        fee_ingress_atoms=charged_fee_atoms,
        unallocated_reserve_atoms=0,
        destination_balances=tuple(
            ZDEXFeeDestinationAmountV1(destination, 0)
            for destination in ZDEX_FEE_DESTINATIONS_V1
        ),
        owned_and_custodied_atoms=purchase.quote_owned_atoms,
        supply_atoms=purchase.quote_supply_atoms,
    )
    allocation_occurrence = EconomicCommandOccurrenceV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        height=occurrence.height,
        tx_index=occurrence.tx_index,
        op_index=0,
        command_kind=PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
        command_body_hash=_root(6),
        route_release_id=allocation_route.route_release_id,
        subject_id="protocol-fee-allocator",
        grant_root=_root(5),
        nonce=8,
        profile_root=occurrence.profile_root,
        pre_state_root=occurrence.pre_state_root,
        consumed_object_ids=(),
    )
    result = transition_zdex_fee_allocation_v1(
        ZDEXFeeAllocationContextV1(
            chain_id=occurrence.chain_id,
            deployment_root=occurrence.deployment_root,
            profile_root=occurrence.profile_root,
            writer_epoch=purchase.writer_epoch,
            allocation_route_release_id=allocation_route.route_release_id,
            authorized_buyback_route_release_id=route.route_release_id,
            tokenomics_module_release_id=burn_release.release_id,
            command_occurrence_id=allocation_occurrence.occurrence_id,
            policy_root=policy.policy_root,
        ),
        state,
        policy,
        ZDEXFeeAllocationCommandV1(charged_fee_atoms),
    )
    assert type(result) is ZDEXFeeAllocationAcceptedV1
    assert result.occurrence.buyback_quote_atoms == purchase.quote_amount_in_atoms
    receipt_candidate = ZDEXFeeAllocationReceiptCandidateV1(
        allocation_occurrence,
        policy,
        state,
        result.post_state,
        result.occurrence,
        result.effects,
        ZDEXLaneReceiptEnvelopeV1(
            ReceiptKindV1.SUCCINCT,
            b"fee-allocation-receipt",
        ),
    )
    governed = bind_zdex_fee_allocation_shadow_profile_v1(
        expected_profile_id=profile.profile_id,
        expected_authority_epoch=profile.authority_epoch,
        profile=profile,
        policy_registry=policy_registry,
    )
    verified = verify_zdex_fee_allocation_receipt_v1(
        receipt_candidate,
        governed,
        _Verifier(),
    )
    return result.occurrence, verified, receipt_candidate


class _Verifier:
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
            raise ValueError("test verifier rejection")


class _ExactVerifier:
    def __init__(self, receipt: bytes, image: str, journal: bytes) -> None:
        self.expected = (receipt, image, journal)
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        actual = (receipt_bytes, expected_image_id, expected_journal_bytes)
        self.calls.append(actual)
        if actual != self.expected:
            raise ValueError("fee lane exact receipt binding mismatch")


def _verified_fixture(
    *,
    purchase_overrides: dict[str, object] | None = None,
    burn_overrides: dict[str, object] | None = None,
    budget_overrides: dict[str, object] | None = None,
    consumed_object_ids_override: tuple[str, ...] | None = None,
    buyback_route_guest_image_id: str = _root(500),
) -> ZDEXPurchaseBurnRouteCandidateV1:
    spot_release = _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1)
    burn_release = _lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2)
    route = _route_release(
        spot_release,
        burn_release,
        guest_image_id=buyback_route_guest_image_id,
    )
    policy = candidate_zdex_fee_allocation_policy_v1()
    allocation_route = _allocation_route_release(burn_release)
    profile, policy_registry = _governed_shadow_profile(
        spot_release=spot_release,
        tokenomics_release=burn_release,
        buyback_route=route,
        allocation_route=allocation_route,
        policy_root=policy.policy_root,
    )
    occurrence = _occurrence(route, profile)
    purchase = _purchase_journal(
        route=route,
        spot_release=spot_release,
        occurrence=occurrence,
    )
    if purchase_overrides:
        normalized_purchase_overrides = dict(purchase_overrides)
        if "quote_amount_in_atoms" in normalized_purchase_overrides:
            quote_atoms = normalized_purchase_overrides["quote_amount_in_atoms"]
            assert isinstance(quote_atoms, int)
            normalized_purchase_overrides.setdefault("quote_source_pre_atoms", quote_atoms + 100)
            normalized_purchase_overrides.setdefault("quote_source_post_atoms", 100)
            normalized_purchase_overrides.setdefault("quote_pool_pre_atoms", 2_000)
            normalized_purchase_overrides.setdefault("quote_pool_post_atoms", 2_000 + quote_atoms)
            normalized_purchase_overrides.setdefault("quote_owned_atoms", quote_atoms * 5 + 2_100)
            normalized_purchase_overrides.setdefault("quote_supply_atoms", quote_atoms * 5 + 2_100)
        if "purchased_zdex_atoms" in normalized_purchase_overrides:
            purchased_atoms = normalized_purchase_overrides["purchased_zdex_atoms"]
            assert isinstance(purchased_atoms, int)
            normalized_purchase_overrides.setdefault("zdex_pool_pre_atoms", purchased_atoms + 60)
            normalized_purchase_overrides.setdefault("zdex_pool_post_atoms", 60)
            normalized_purchase_overrides.setdefault("burn_bucket_pre_atoms", 0)
            normalized_purchase_overrides.setdefault("burn_bucket_post_atoms", purchased_atoms)
            normalized_purchase_overrides.setdefault("zdex_owned_atoms", purchased_atoms + 100)
            normalized_purchase_overrides.setdefault("zdex_supply_atoms", purchased_atoms + 100)
        purchase = replace(purchase, **normalized_purchase_overrides)
    budget, verified_budget, budget_receipt_candidate = _buyback_budget(
        profile=profile,
        policy_registry=policy_registry,
        policy=policy,
        allocation_route=allocation_route,
        route=route,
        burn_release=burn_release,
        occurrence=occurrence,
        purchase=purchase,
    )
    purchase = replace(
        purchase,
        buyback_budget_occurrence_root=budget.occurrence_root,
    )
    if budget_overrides:
        budget = replace(budget, **budget_overrides)
    occurrence = replace(
        occurrence,
        consumed_object_ids=(
            (budget.occurrence_root,)
            if consumed_object_ids_override is None
            else consumed_object_ids_override
        ),
    )
    purchase = replace(purchase, command_occurrence_id=occurrence.occurrence_id)
    purchase_effects = _purchase_effects(purchase)
    purchase = replace(purchase, effect_plan_root=purchase_effects.effect_plan_root)
    purchase_effects = _purchase_effects(purchase)
    burn = _burn_journal(
        route=route,
        burn_release=burn_release,
        occurrence=occurrence,
        purchase=purchase,
    )
    if burn_overrides:
        normalized_burn_overrides = dict(burn_overrides)
        if "burned_zdex_atoms" in normalized_burn_overrides:
            burned_atoms = normalized_burn_overrides["burned_zdex_atoms"]
            assert isinstance(burned_atoms, int)
            normalized_burn_overrides.setdefault("burn_bucket_pre_atoms", burned_atoms)
            normalized_burn_overrides.setdefault("burn_bucket_post_atoms", 0)
        burn = replace(burn, **normalized_burn_overrides)
    burn_effects = _burn_effects(burn)
    burn = replace(burn, effect_plan_root=burn_effects.effect_plan_root)
    burn_effects = _burn_effects(burn)
    verifier = _Verifier()
    verified_purchase = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1(
            route,
            spot_release,
            occurrence,
            purchase,
            purchase_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"purchase-receipt"),
        ),
        verifier,
    )
    verified_burn = verify_zdex_burn_receipt_v1(
        ZDEXBurnReceiptCandidateV1(
            route,
            burn_release,
            occurrence,
            burn,
            burn_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"burn-receipt"),
        ),
        verifier,
    )
    governed_route = bind_zdex_purchase_burn_shadow_profile_v1(
        expected_profile_id=profile.profile_id,
        expected_authority_epoch=profile.authority_epoch,
        profile=profile,
    )
    return ZDEXPurchaseBurnRouteCandidateV1(
        governed_route,
        route,
        spot_release,
        burn_release,
        occurrence,
        budget,
        verified_budget,
        budget_receipt_candidate.policy,
        budget_receipt_candidate.pre_state,
        purchase,
        purchase_effects,
        verified_purchase,
        burn,
        burn_effects,
        verified_burn,
    )


def _fee_receipt_candidate_fixture(
    *,
    buyback_route_guest_image_id: str = _root(500),
) -> tuple[
    ZDEXFeeAllocationReceiptCandidateV1,
    GovernedZDEXFeeAllocationProfileV1,
]:
    spot_release = _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1)
    burn_release = _lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2)
    route = _route_release(
        spot_release,
        burn_release,
        guest_image_id=buyback_route_guest_image_id,
    )
    policy = candidate_zdex_fee_allocation_policy_v1()
    allocation_route = _allocation_route_release(burn_release)
    profile, policy_registry = _governed_shadow_profile(
        spot_release=spot_release,
        tokenomics_release=burn_release,
        buyback_route=route,
        allocation_route=allocation_route,
        policy_root=policy.policy_root,
    )
    occurrence = _occurrence(route, profile)
    purchase = _purchase_journal(
        route=route,
        spot_release=spot_release,
        occurrence=occurrence,
    )
    _, _, receipt_candidate = _buyback_budget(
        profile=profile,
        policy_registry=policy_registry,
        policy=policy,
        allocation_route=allocation_route,
        route=route,
        burn_release=burn_release,
        occurrence=occurrence,
        purchase=purchase,
    )
    governed = bind_zdex_fee_allocation_shadow_profile_v1(
        expected_profile_id=profile.profile_id,
        expected_authority_epoch=profile.authority_epoch,
        profile=profile,
        policy_registry=policy_registry,
    )
    return receipt_candidate, governed


def _assert_no_effect_reject(
    result: ZDEXPurchaseBurnRouteRejectedV1,
    code: ZDEXPurchaseBurnRouteRejectCodeV1,
) -> None:
    assert isinstance(result, ZDEXPurchaseBurnRouteRejectedV1)
    assert result.code is code
    assert result.effects.is_empty


def test_governed_purchase_burn_route_cannot_be_constructed_by_a_caller() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        GovernedZDEXPurchaseBurnRouteV1(object(), object(), _root(1), 1)


def _alternative_buyback_profile(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
) -> EconomicProfileSnapshotV1:
    fields = candidate.governed_profile._fields
    route = fields.route_release
    alternative_route = RouteReleaseV1.build(
        semantic_version=route.semantic_version,
        command_kind=route.command_kind,
        ordered_lanes=route.ordered_lanes,
        module_release_ids=route.module_release_ids,
        dependency_roles=route.dependency_roles,
        port_schema_roots=route.port_schema_roots,
        guest_image_id=_root(98_100),
        specification_root=route.specification_root,
        source_root=route.source_root,
        toolchain_root=route.toolchain_root,
        oracle_policy_root=route.oracle_policy_root,
        issue_burn_policy_root=route.issue_burn_policy_root,
        max_cycles=route.max_cycles,
        max_journal_bytes=route.max_journal_bytes,
        status=route.status,
        accepts_new_objects=route.accepts_new_objects,
        evidence_statuses=route.evidence_statuses,
    )
    allocation_route = next(
        registered
        for registered in fields.profile.route_registry.routes
        if registered.command_kind == PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1
    )
    route_registry = RouteRegistryV1(
        tuple(
            sorted(
                (allocation_route, alternative_route),
                key=lambda registered: registered.command_kind,
            )
        )
    )
    return EconomicProfileSnapshotV1.build(
        authority_epoch=fields.profile.authority_epoch,
        lane_registry=fields.profile.lane_registry,
        lane_coordinator_registry=fields.profile.lane_coordinator_registry,
        route_registry=route_registry,
        proof_shape_root=fields.profile.proof_shape_root,
        root_image_id=fields.profile.root_image_id,
        verifier_registry_root=fields.profile.verifier_registry_root,
        migration_registry_root=fields.profile.migration_registry_root,
        policy_registry_root=fields.profile.policy_registry_root,
        terminal_registry_root=fields.profile.terminal_registry_root,
        status=ProfileStatusV1.SHADOW,
    )


def test_self_consistent_alternative_buyback_profile_rejects_trusted_anchor() -> None:
    # Arrange
    candidate = _verified_fixture()
    fields = candidate.governed_profile._fields
    profile = _alternative_buyback_profile(candidate)

    # Act / Assert
    with pytest.raises(ValueError, match="expected profile mismatch"):
        bind_zdex_purchase_burn_shadow_profile_v1(
            expected_profile_id=fields.profile.profile_id,
            expected_authority_epoch=fields.profile.authority_epoch,
            profile=profile,
        )


def test_alternative_governed_route_rejects_without_effects() -> None:
    # Arrange
    candidate = _verified_fixture()
    profile = _alternative_buyback_profile(candidate)
    foreign = bind_zdex_purchase_burn_shadow_profile_v1(
        expected_profile_id=profile.profile_id,
        expected_authority_epoch=profile.authority_epoch,
        profile=profile,
    )

    # Act
    result = compose_zdex_purchase_burn_route_v1(
        replace(candidate, governed_profile=foreign)
    )

    # Assert
    _assert_no_effect_reject(
        result,
        ZDEXPurchaseBurnRouteRejectCodeV1.GOVERNED_PROFILE_MISMATCH,
    )


def test_retained_route_anchor_rejects_generation_swap_without_effects() -> None:
    # Arrange: retain the honestly anchored wrapper, then replace its graph.
    honest = _verified_fixture()
    alternate = _verified_fixture(
        buyback_route_guest_image_id=_root(98_100),
    )
    assert (
        honest.governed_profile._fields.profile.profile_id
        != alternate.governed_profile._fields.profile.profile_id
    )
    object.__setattr__(
        honest.governed_profile,
        "_fields",
        alternate.governed_profile._fields,
    )

    # Act
    result = compose_zdex_purchase_burn_route_v1(
        replace(alternate, governed_profile=honest.governed_profile)
    )

    # Assert
    _assert_no_effect_reject(
        result,
        ZDEXPurchaseBurnRouteRejectCodeV1.GOVERNED_PROFILE_MISMATCH,
    )


def test_governed_route_epoch_rejects_boolean_alias() -> None:
    candidate = _verified_fixture()
    fields = candidate.governed_profile._fields

    with pytest.raises(ValueError, match="expected authority epoch mismatch"):
        bind_zdex_purchase_burn_shadow_profile_v1(
            expected_profile_id=fields.profile.profile_id,
            expected_authority_epoch=True,
            profile=fields.profile,
        )


def test_governed_route_owns_profile_and_selected_release_graph() -> None:
    candidate = _verified_fixture()
    fields = candidate.governed_profile._fields

    assert fields.route_release is not candidate.route_release
    assert fields.purchase_module_release is not candidate.purchase_module_release
    assert fields.burn_module_release is not candidate.burn_module_release


def test_hostile_governed_profile_is_rejected_before_attribute_access() -> None:
    # Arrange
    candidate = _verified_fixture()
    fields = candidate.governed_profile._fields
    object.__setattr__(fields, "profile", object())

    # Act / Assert
    with pytest.raises(TypeError, match="profile must be exact typed data"):
        compose_zdex_purchase_burn_route_v1(candidate)


def test_verified_leaves_compose_shadow_effects_with_open_coordinator_obligation() -> None:
    candidate = _verified_fixture()

    result = compose_zdex_purchase_burn_route_v1(candidate)

    assert result.effects.occurrence_consumptions == (
        candidate.occurrence.occurrence_id,
    )
    assert candidate.occurrence.consumed_object_ids == (
        candidate.buyback_budget_occurrence.occurrence_root,
    )
    assert tuple(row.lane_id for row in result.effects.lane_writes) == (
        LaneIdV1.SPOT_LIQUIDITY,
    )
    assert sum(
        -row.delta_atoms
        for row in result.effects.rows
        if row.kind is EconomicEffectKindV1.BURN
    ) == candidate.purchase_journal.purchased_zdex_atoms
    assert all(
        row.principal != candidate.purchase_journal.burn_bucket_id
        for row in result.effects.rows
    )
    assert result.effects.external_outbox_enqueue == ()
    assert result.terminal_obligations_root == (
        "0xb3a804a59299dd1349592fafec630720031217d4b3340a385a345d544d4b4553"
    )


@pytest.mark.parametrize(
    "budget_overrides",
    (
        {"authorized_buyback_route_release_id": _root(992)},
        {"profile_root": _root(993)},
        {"fee_asset_id": _root(994)},
    ),
)
def test_unbound_buyback_budget_occurrence_rejects_without_effects(
    budget_overrides: dict[str, object],
) -> None:
    candidate = _verified_fixture(budget_overrides=budget_overrides)

    result = compose_zdex_purchase_burn_route_v1(candidate)

    _assert_no_effect_reject(
        result,
        ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH,
    )


def test_buyback_budget_cannot_be_redirected_to_another_source() -> None:
    candidate = _verified_fixture(
        purchase_overrides={"quote_source_bucket_id": "account:alice"}
    )

    result = compose_zdex_purchase_burn_route_v1(candidate)

    _assert_no_effect_reject(
        result,
        ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH,
    )


def test_budget_and_buyback_command_cannot_alias_replay_identity() -> None:
    candidate = _verified_fixture()
    aliased_budget = replace(
        candidate.buyback_budget_occurrence,
        command_occurrence_id=candidate.occurrence.occurrence_id,
    )

    result = compose_zdex_purchase_burn_route_v1(
        replace(candidate, buyback_budget_occurrence=aliased_budget)
    )

    _assert_no_effect_reject(
        result,
        ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH,
    )


@pytest.mark.parametrize("consumed_object_ids", ((), (_root(991),)))
def test_command_must_consume_exact_authenticated_budget_object(
    consumed_object_ids: tuple[str, ...],
) -> None:
    candidate = _verified_fixture(
        consumed_object_ids_override=consumed_object_ids,
    )

    result = compose_zdex_purchase_burn_route_v1(candidate)

    _assert_no_effect_reject(
        result,
        ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH,
    )


def test_fee_allocation_witness_cannot_be_constructed_by_a_caller() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedZDEXFeeAllocationV1(object(), object())


def test_governed_fee_profile_cannot_be_constructed_by_a_caller() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        GovernedZDEXFeeAllocationProfileV1(
            object(),
            object(),
            _root(1),
            1,
        )


def test_self_consistent_alternative_profile_rejects_trusted_profile_anchor() -> None:
    _, governed = _fee_receipt_candidate_fixture()
    fields = governed._fields
    original = fields.profile
    alternative = EconomicProfileSnapshotV1.build(
        authority_epoch=original.authority_epoch + 1,
        lane_registry=original.lane_registry,
        lane_coordinator_registry=original.lane_coordinator_registry,
        route_registry=original.route_registry,
        proof_shape_root=original.proof_shape_root,
        root_image_id=original.root_image_id,
        verifier_registry_root=original.verifier_registry_root,
        migration_registry_root=original.migration_registry_root,
        policy_registry_root=original.policy_registry_root,
        terminal_registry_root=original.terminal_registry_root,
        status=ProfileStatusV1.SHADOW,
    )

    with pytest.raises(ValueError, match="expected profile mismatch"):
        bind_zdex_fee_allocation_shadow_profile_v1(
            expected_profile_id=original.profile_id,
            expected_authority_epoch=original.authority_epoch,
            profile=alternative,
            policy_registry=fields.policy_registry,
        )


def test_retained_fee_anchor_rejects_generation_swap_before_callback() -> None:
    # Arrange
    _, honest = _fee_receipt_candidate_fixture()
    alternate_candidate, alternate = _fee_receipt_candidate_fixture(
        buyback_route_guest_image_id=_root(98_100),
    )
    assert honest._fields.profile.profile_id != alternate._fields.profile.profile_id
    object.__setattr__(honest, "_fields", alternate._fields)
    verifier = _Verifier()

    # Act / Assert
    with pytest.raises(ValueError, match="trusted profile anchor"):
        verify_zdex_fee_allocation_receipt_v1(
            alternate_candidate,
            honest,
            verifier,
        )
    assert verifier.calls == []


def test_profile_status_substitution_rejects_with_same_profile_id() -> None:
    _, governed = _fee_receipt_candidate_fixture()
    fields = governed._fields
    substituted = replace(fields.profile, status=ProfileStatusV1.CANDIDATE)

    with pytest.raises(ValueError, match="must remain SHADOW"):
        bind_zdex_fee_allocation_shadow_profile_v1(
            expected_profile_id=fields.profile.profile_id,
            expected_authority_epoch=fields.profile.authority_epoch,
            profile=substituted,
            policy_registry=fields.policy_registry,
        )


def test_wrong_expected_authority_epoch_rejects_trusted_profile_anchor() -> None:
    _, governed = _fee_receipt_candidate_fixture()
    fields = governed._fields

    with pytest.raises(ValueError, match="expected authority epoch mismatch"):
        bind_zdex_fee_allocation_shadow_profile_v1(
            expected_profile_id=fields.profile.profile_id,
            expected_authority_epoch=fields.profile.authority_epoch + 1,
            profile=fields.profile,
            policy_registry=fields.policy_registry,
        )


def test_policy_registry_substitution_rejects_before_receipt_verification() -> None:
    _, governed = _fee_receipt_candidate_fixture()
    fields = governed._fields
    substituted = EconomicPolicyRegistryV1(
        (
            EconomicPolicyBindingV1(
                ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
                PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
                _root(999),
            ),
        )
    )

    with pytest.raises(ValueError, match="outside the profile"):
        bind_zdex_fee_allocation_shadow_profile_v1(
            expected_profile_id=fields.profile.profile_id,
            expected_authority_epoch=fields.profile.authority_epoch,
            profile=fields.profile,
            policy_registry=substituted,
        )


@pytest.mark.parametrize("coordinate", ("occurrence_profile", "journal_epoch"))
def test_profile_coordinate_substitution_rejects_before_receipt_verification(
    coordinate: str,
) -> None:
    candidate, governed = _fee_receipt_candidate_fixture()
    if coordinate == "occurrence_profile":
        candidate = replace(
            candidate,
            occurrence=replace(candidate.occurrence, profile_root=_root(998)),
        )
    else:
        candidate = replace(
            candidate,
            journal=replace(candidate.journal, writer_epoch=candidate.journal.writer_epoch + 1),
        )
    verifier = _Verifier()

    with pytest.raises(ValueError, match="governed profile binding mismatch"):
        verify_zdex_fee_allocation_receipt_v1(candidate, governed, verifier)
    assert verifier.calls == []


def test_fee_receipt_callback_cannot_rebind_verified_bytes() -> None:
    # Arrange
    candidate, governed = _fee_receipt_candidate_fixture()
    authenticated_receipt = candidate.receipt.receipt_bytes

    class _MutatingVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            del expected_image_id, expected_journal_bytes
            assert receipt_bytes == authenticated_receipt
            object.__setattr__(candidate.receipt, "receipt_bytes", b"unauthenticated")

    # Act
    verified = verify_zdex_fee_allocation_receipt_v1(
        candidate,
        governed,
        _MutatingVerifier(),
    )

    # Assert
    assert verified.receipt_digest == (
        "0x" + hashlib.sha256(authenticated_receipt).hexdigest()
    )
    assert verified.receipt_digest != (
        "0x" + hashlib.sha256(candidate.receipt.receipt_bytes).hexdigest()
    )


def test_fee_receipt_callback_cannot_mutate_owned_witness_bindings() -> None:
    # Arrange
    candidate, governed = _fee_receipt_candidate_fixture()
    fields = governed._fields
    expected = (
        fields.allocation_route.route_release_id,
        fields.buyback_route.route_release_id,
        fields.module_release.release_id,
        candidate.occurrence.occurrence_id,
        candidate.occurrence.profile_root,
        candidate.journal.occurrence_root,
        candidate.effects.effect_plan_root,
        fields.module_release.guest_image_id,
        candidate.policy.policy_root,
        candidate.journal.fee_asset_id,
    )

    class _MutatingVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            del receipt_bytes, expected_image_id, expected_journal_bytes
            object.__setattr__(fields.allocation_route, "route_release_id", _root(97_001))
            object.__setattr__(fields.buyback_route, "route_release_id", _root(97_002))
            object.__setattr__(fields.module_release, "release_id", _root(97_003))
            object.__setattr__(fields.module_release, "guest_image_id", _root(97_004))
            object.__setattr__(candidate.journal, "fee_asset_id", _root(97_005))
            object.__setattr__(candidate, "effects", GlobalEconomicEffectPlanV1.empty())

    # Act
    verified = verify_zdex_fee_allocation_receipt_v1(
        candidate,
        governed,
        _MutatingVerifier(),
    )

    # Assert
    assert (
        verified.allocation_route_release_id,
        verified.authorized_buyback_route_release_id,
        verified.module_release_id,
        verified.command_occurrence_id,
        verified.profile_root,
        verified.journal_root,
        verified.effect_plan_root,
        verified.expected_image_id,
        verified.policy_root,
        verified.fee_asset_id,
    ) == expected


def test_fee_receipt_rejects_hostile_scalar_before_callback() -> None:
    # Arrange
    candidate, governed = _fee_receipt_candidate_fixture()
    candidate = replace(
        candidate,
        journal=replace(
            candidate.journal,
            fee_asset_id=_HostileRoot(candidate.journal.fee_asset_id),
        ),
    )
    verifier = _Verifier()

    # Act / Assert
    with pytest.raises(TypeError, match="exact primitive"):
        verify_zdex_fee_allocation_receipt_v1(candidate, governed, verifier)
    assert verifier.calls == []


def test_fee_receipt_rejects_hostile_governed_fields_before_attribute_access() -> None:
    # Arrange
    candidate, governed = _fee_receipt_candidate_fixture()

    class _HostileFields:
        def __init__(self) -> None:
            object.__setattr__(self, "events", [])

        def __getattribute__(self, name: str) -> object:
            if name == "events":
                return object.__getattribute__(self, name)
            events = object.__getattribute__(self, "events")
            events.append(name)
            raise AssertionError("hostile governed fields attribute access ran")

    hostile_fields = _HostileFields()
    object.__setattr__(governed, "_fields", hostile_fields)
    verifier = _Verifier()

    # Act / Assert
    with pytest.raises(TypeError, match="fields must be exact typed data"):
        verify_zdex_fee_allocation_receipt_v1(candidate, governed, verifier)
    assert hostile_fields.events == []
    assert verifier.calls == []


def test_policy_registry_root_matches_rust_golden_vector() -> None:
    _, governed = _fee_receipt_candidate_fixture()
    policy_registry = governed._fields.policy_registry

    assert policy_registry.registry_root == (
        "0x67554f616a2cb0413e0b72d6789ae0e08382475943b4ad8a14e009bb0779d0a9"
    )
    assert canonical_global_bytes_v1(policy_registry) == (
        b'{"bindings":[{"command_kind":"protocol_fee_allocation",'
        b'"policy_kind":"zdex_fee_allocation",'
        b'"policy_root":"0xd810507e5d15fd874a2e75b6f32b71b47174a799b8015301700e4554614032c2"}],'
        b'"schema":"zenodex/global-settlement-abi/v1"}'
    )


def test_policy_registry_rejects_duplicate_and_unsorted_binding_keys() -> None:
    first = EconomicPolicyBindingV1("a", "b", _root(991))
    second = EconomicPolicyBindingV1("a", "c", _root(992))

    with pytest.raises(ValueError, match="sorted and unique"):
        EconomicPolicyRegistryV1((first, first))
    with pytest.raises(ValueError, match="sorted and unique"):
        EconomicPolicyRegistryV1((second, first))


def test_policy_registry_rejects_wrong_command_lookup() -> None:
    _, governed = _fee_receipt_candidate_fixture()

    with pytest.raises(ValueError, match="binding is absent"):
        governed._fields.policy_registry.require_binding(
            policy_kind=ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
            command_kind="protocol_wrong_command",
        )


def test_policy_registry_accepts_256_and_rejects_257_bindings() -> None:
    bindings = tuple(
        EconomicPolicyBindingV1(f"policy_{index:03d}", "command", _root(991))
        for index in range(257)
    )

    assert len(EconomicPolicyRegistryV1(bindings[:256]).bindings) == 256
    with pytest.raises(ValueError, match="exceeds the ABI V1 bound"):
        EconomicPolicyRegistryV1(bindings)


def test_imported_python_token_cannot_authorize_shifted_allocation() -> None:
    from src.core import zdex_fee_allocation_receipt_verification_v1 as receipt_module

    candidate = _verified_fixture()
    allocations = list(candidate.buyback_budget_occurrence.allocations)
    allocations[2] = replace(
        allocations[2],
        allocation_atoms=allocations[2].allocation_atoms - 1,
    )
    allocations[3] = replace(
        allocations[3],
        allocation_atoms=allocations[3].allocation_atoms + 1,
    )
    shifted_budget = replace(
        candidate.buyback_budget_occurrence,
        allocations=tuple(allocations),
    )
    occurrence = replace(
        candidate.occurrence,
        consumed_object_ids=(shifted_budget.occurrence_root,),
    )
    purchase = replace(
        candidate.purchase_journal,
        command_occurrence_id=occurrence.occurrence_id,
        buyback_budget_occurrence_root=shifted_budget.occurrence_root,
    )
    purchase_effects = _purchase_effects(purchase)
    purchase = replace(purchase, effect_plan_root=purchase_effects.effect_plan_root)
    purchase_effects = _purchase_effects(purchase)
    burn = replace(
        candidate.burn_journal,
        command_occurrence_id=occurrence.occurrence_id,
        buyback_budget_occurrence_root=shifted_budget.occurrence_root,
        purchase_occurrence_root=purchase.journal_root,
    )
    burn_effects = _burn_effects(burn)
    burn = replace(burn, effect_plan_root=burn_effects.effect_plan_root)
    burn_effects = _burn_effects(burn)
    verifier = _Verifier()
    verified_purchase = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1(
            candidate.route_release,
            _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
            occurrence,
            purchase,
            purchase_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"shift-purchase"),
        ),
        verifier,
    )
    verified_burn = verify_zdex_burn_receipt_v1(
        ZDEXBurnReceiptCandidateV1(
            candidate.route_release,
            _lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2),
            occurrence,
            burn,
            burn_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"shift-burn"),
        ),
        verifier,
    )
    forged_fields = replace(
        candidate.verified_buyback_budget._fields,
        journal_root=shifted_budget.occurrence_root,
        journal_digest=(
            "0x"
            + hashlib.sha256(canonical_global_bytes_v1(shifted_budget)).hexdigest()
        ),
    )
    forged_witness = VerifiedZDEXFeeAllocationV1(
        receipt_module._VERIFIED_FEE_ALLOCATION_TOKEN,
        forged_fields,
    )
    forged_candidate = replace(
        candidate,
        occurrence=occurrence,
        buyback_budget_occurrence=shifted_budget,
        verified_buyback_budget=forged_witness,
        purchase_journal=purchase,
        purchase_effects=purchase_effects,
        verified_purchase=verified_purchase,
        burn_journal=burn,
        burn_effects=burn_effects,
        verified_burn=verified_burn,
    )

    result = compose_zdex_purchase_burn_route_v1(forged_candidate)

    _assert_no_effect_reject(
        result,
        ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH,
    )


def test_shifted_fee_allocation_rejects_before_receipt_verification() -> None:
    receipt_candidate, governed = _fee_receipt_candidate_fixture()
    allocations = list(receipt_candidate.journal.allocations)
    allocations[0] = replace(
        allocations[0],
        allocation_atoms=allocations[0].allocation_atoms - 1,
    )
    allocations[2] = replace(
        allocations[2],
        allocation_atoms=allocations[2].allocation_atoms + 1,
    )
    shifted = replace(
        receipt_candidate,
        journal=replace(
            receipt_candidate.journal,
            allocations=tuple(allocations),
        ),
    )
    verifier = _Verifier()

    with pytest.raises(ValueError, match="journal or effects mismatch"):
        verify_zdex_fee_allocation_receipt_v1(shifted, governed, verifier)
    assert verifier.calls == []


@pytest.mark.parametrize(
    ("receipt_kind", "receipt_bytes"),
    (
        (ReceiptKindV1.COMPOSITE, b"receipt"),
        (ReceiptKindV1.CONDITIONAL, b"receipt"),
        (ReceiptKindV1.FAKE, b"receipt"),
        (ReceiptKindV1.DEVELOPMENT, b"receipt"),
        (ReceiptKindV1.SUCCINCT, b""),
    ),
)
def test_fee_allocation_requires_nonempty_succinct_receipt_before_verifier(
    receipt_kind: ReceiptKindV1,
    receipt_bytes: bytes,
) -> None:
    candidate, governed = _fee_receipt_candidate_fixture()
    candidate = replace(
        candidate,
        receipt=ZDEXLaneReceiptEnvelopeV1(receipt_kind, receipt_bytes),
    )
    verifier = _Verifier()

    with pytest.raises(ValueError, match="succinct receipt|must be nonempty"):
        verify_zdex_fee_allocation_receipt_v1(candidate, governed, verifier)
    assert verifier.calls == []


def test_receipt_verifier_sees_exact_release_image_and_canonical_journal() -> None:
    candidate = _verified_fixture()
    verifier = _Verifier()

    verified = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1(
            candidate.route_release,
            _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
            candidate.occurrence,
            candidate.purchase_journal,
            candidate.purchase_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"exact"),
        ),
        verifier,
    )

    assert len(verifier.calls) == 1
    assert verifier.calls[0][1] == _lane_release(
        LaneIdV1.SPOT_LIQUIDITY, 1
    ).guest_image_id
    assert verified.journal_root == candidate.purchase_journal.journal_root
    assert verifier.calls[0][2] == canonical_global_bytes_v1(
        candidate.purchase_journal
    )


def test_purchase_receipt_callback_cannot_redirect_authenticated_effects() -> None:
    # Arrange
    route_candidate = _verified_fixture()
    receipt_candidate = ZDEXPurchaseReceiptCandidateV1(
        route_candidate.route_release,
        _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
        route_candidate.occurrence,
        route_candidate.purchase_journal,
        route_candidate.purchase_effects,
        ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"alias-attack"),
    )
    authenticated_effect_root = receipt_candidate.journal.effect_plan_root

    class _RedirectingVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            del expected_image_id, expected_journal_bytes
            assert receipt_bytes == b"alias-attack"
            rows = list(receipt_candidate.effects.rows)
            pool_index = next(
                index
                for index, row in enumerate(rows)
                if row.principal == receipt_candidate.journal.quote_pool_bucket_id
            )
            rows[pool_index] = replace(rows[pool_index], principal="attacker")
            object.__setattr__(
                receipt_candidate.effects,
                "rows",
                tuple(sorted(rows, key=lambda row: row.key)),
            )

    # Act
    verified = verify_zdex_amm_purchase_receipt_v1(
        receipt_candidate,
        _RedirectingVerifier(),
    )
    result = compose_zdex_purchase_burn_route_v1(
        replace(
            route_candidate,
            purchase_effects=receipt_candidate.effects,
            verified_purchase=verified,
        )
    )

    # Assert
    assert receipt_candidate.effects.effect_plan_root != authenticated_effect_root
    _assert_no_effect_reject(
        result,
        ZDEXPurchaseBurnRouteRejectCodeV1.PURCHASE_WITNESS_MISMATCH,
    )
    assert verified.effect_plan_root == authenticated_effect_root


def test_burn_receipt_callback_cannot_mutate_owned_witness_bindings() -> None:
    # Arrange
    fixture = _verified_fixture()
    candidate = ZDEXBurnReceiptCandidateV1(
        fixture.route_release,
        _lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2),
        fixture.occurrence,
        fixture.burn_journal,
        fixture.burn_effects,
        ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"burn-alias-attack"),
    )
    expected = (
        candidate.route_release.route_release_id,
        candidate.module_release.release_id,
        candidate.occurrence.occurrence_id,
        candidate.journal.journal_root,
        candidate.effects.effect_plan_root,
        candidate.module_release.guest_image_id,
        "0x" + hashlib.sha256(candidate.receipt.receipt_bytes).hexdigest(),
    )

    class _MutatingVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            del receipt_bytes, expected_image_id, expected_journal_bytes
            object.__setattr__(candidate.route_release, "route_release_id", _root(98_001))
            object.__setattr__(candidate.module_release, "release_id", _root(98_002))
            object.__setattr__(candidate.journal, "writer_epoch", 98_003)
            object.__setattr__(candidate, "effects", GlobalEconomicEffectPlanV1.empty())
            object.__setattr__(candidate.module_release, "guest_image_id", _root(98_004))
            object.__setattr__(candidate.receipt, "receipt_bytes", b"mutated-burn")

    # Act
    verified = verify_zdex_burn_receipt_v1(candidate, _MutatingVerifier())

    # Assert
    assert (
        verified.route_release_id,
        verified.module_release_id,
        verified.command_occurrence_id,
        verified.journal_root,
        verified.effect_plan_root,
        verified.expected_image_id,
        verified.receipt_digest,
    ) == expected


def test_burn_receipt_rejects_hostile_route_scalar_before_callback() -> None:
    # Arrange
    fixture = _verified_fixture()
    candidate = ZDEXBurnReceiptCandidateV1(
        fixture.route_release,
        _lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2),
        fixture.occurrence,
        replace(
            fixture.burn_journal,
            route_release_id=_HostileRoot(fixture.burn_journal.route_release_id),
        ),
        fixture.burn_effects,
        ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"hostile-scalar"),
    )
    verifier = _Verifier()

    # Act / Assert
    with pytest.raises(TypeError, match="exact primitive"):
        verify_zdex_burn_receipt_v1(candidate, verifier)
    assert verifier.calls == []


def test_verifier_rejection_produces_no_authenticated_purchase_witness() -> None:
    candidate = _verified_fixture()
    verifier = _Verifier(reject=True)

    with pytest.raises(ValueError, match="test verifier rejection"):
        verify_zdex_amm_purchase_receipt_v1(
            ZDEXPurchaseReceiptCandidateV1(
                candidate.route_release,
                _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
                candidate.occurrence,
                candidate.purchase_journal,
                candidate.purchase_effects,
                ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"rejected"),
            ),
            verifier,
        )


@pytest.mark.parametrize(
    ("receipt_kind", "receipt_bytes"),
    (
        (ReceiptKindV1.COMPOSITE, b"receipt"),
        (ReceiptKindV1.CONDITIONAL, b"receipt"),
        (ReceiptKindV1.FAKE, b"receipt"),
        (ReceiptKindV1.DEVELOPMENT, b"receipt"),
        (ReceiptKindV1.SUCCINCT, b""),
    ),
)
def test_non_authoritative_receipt_shapes_reject_before_verifier(
    receipt_kind: ReceiptKindV1,
    receipt_bytes: bytes,
) -> None:
    candidate = _verified_fixture()
    verifier = _Verifier()

    with pytest.raises(ValueError, match="succinct receipt|must be nonempty"):
        verify_zdex_amm_purchase_receipt_v1(
            ZDEXPurchaseReceiptCandidateV1(
                candidate.route_release,
                _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
                candidate.occurrence,
                candidate.purchase_journal,
                candidate.purchase_effects,
                ZDEXLaneReceiptEnvelopeV1(receipt_kind, receipt_bytes),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_active_release_cannot_cross_the_shadow_only_admission_boundary() -> None:
    candidate = _verified_fixture()
    active_route = replace(
        candidate.route_release,
        status=ReleaseStatusV1.ACTIVE_NEW,
        accepts_new_objects=True,
        evidence_statuses=tuple(
            sorted(REQUIRED_ACTIVE_EVIDENCE_V1, key=lambda item: item.value)
        ),
    )
    assert all(isinstance(item, EvidenceStatusV1) for item in active_route.evidence_statuses)
    verifier = _Verifier()

    with pytest.raises(ValueError, match="must remain SHADOW"):
        verify_zdex_amm_purchase_receipt_v1(
            ZDEXPurchaseReceiptCandidateV1(
                active_route,
                _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
                candidate.occurrence,
                candidate.purchase_journal,
                candidate.purchase_effects,
                ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"active"),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_quote_debit_mutant_rejects_before_receipt_verification() -> None:
    candidate = _verified_fixture()
    rows = list(candidate.purchase_effects.rows)
    source_index = next(
        index
        for index, row in enumerate(rows)
        if row.principal == candidate.purchase_journal.quote_source_bucket_id
    )
    rows[source_index] = replace(rows[source_index], delta_atoms=rows[source_index].delta_atoms + 1)
    mutated = replace(candidate.purchase_effects, rows=tuple(rows))
    mutated_journal = replace(
        candidate.purchase_journal,
        effect_plan_root=mutated.effect_plan_root,
    )
    verifier = _Verifier()

    with pytest.raises(ValueError, match="purchase effect rows"):
        verify_zdex_amm_purchase_receipt_v1(
            ZDEXPurchaseReceiptCandidateV1(
                candidate.route_release,
                _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
                candidate.occurrence,
                mutated_journal,
                mutated,
                ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"mutated"),
            ),
            verifier,
        )
    assert verifier.calls == []


@pytest.mark.parametrize(
    ("burn_overrides", "expected"),
    (
        ({"burned_zdex_atoms": 39, "zdex_owned_post_atoms": 961, "zdex_supply_post_atoms": 961}, ZDEXPurchaseBurnRouteRejectCodeV1.AMOUNT_MISMATCH),
        ({"burn_bucket_id": "protocol:other-burn"}, ZDEXPurchaseBurnRouteRejectCodeV1.BURN_BUCKET_MISMATCH),
        ({"purchase_occurrence_root": _root(999)}, ZDEXPurchaseBurnRouteRejectCodeV1.PURCHASE_OCCURRENCE_MISMATCH),
        ({"authorized_quote_input_atoms": 124}, ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH),
        ({"buyback_budget_occurrence_root": _root(998)}, ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH),
        ({"zdex_owned_pre_atoms": 999, "zdex_owned_post_atoms": 959}, ZDEXPurchaseBurnRouteRejectCodeV1.CONSERVATION_HISTORY_DISCONNECTED),
        ({"zdex_asset_id": _root(997)}, ZDEXPurchaseBurnRouteRejectCodeV1.ASSET_MISMATCH),
    ),
)
def test_port_substitution_rejects_without_effects(
    burn_overrides: dict[str, object],
    expected: ZDEXPurchaseBurnRouteRejectCodeV1,
) -> None:
    candidate = _verified_fixture(burn_overrides=burn_overrides)

    result = compose_zdex_purchase_burn_route_v1(candidate)

    _assert_no_effect_reject(result, expected)


def test_wrong_dependency_role_shape_cannot_authenticate_purchase() -> None:
    candidate = _verified_fixture()
    route = _route_release(
        _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
        _lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2),
        dependency_roles=("WRONG", "ZDEX_BURN_INPUT"),
    )
    verifier = _Verifier()

    with pytest.raises(ValueError, match="dependency roles"):
        verify_zdex_amm_purchase_receipt_v1(
            ZDEXPurchaseReceiptCandidateV1(
                route,
                _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1),
                candidate.occurrence,
                candidate.purchase_journal,
                candidate.purchase_effects,
                ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"wrong-route"),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_verified_leaf_for_another_journal_cannot_be_substituted() -> None:
    candidate = _verified_fixture()
    foreign = _verified_fixture(
        burn_overrides={"authorized_quote_input_atoms": 124}
    )
    substituted = replace(candidate, verified_burn=foreign.verified_burn)

    result = compose_zdex_purchase_burn_route_v1(substituted)

    _assert_no_effect_reject(
        result,
        ZDEXPurchaseBurnRouteRejectCodeV1.BURN_WITNESS_MISMATCH,
    )


@pytest.mark.parametrize(
    ("witness_name", "field_name", "expected"),
    (
        (
            "verified_purchase",
            "module_release_id",
            ZDEXPurchaseBurnRouteRejectCodeV1.PURCHASE_WITNESS_MISMATCH,
        ),
        (
            "verified_purchase",
            "expected_image_id",
            ZDEXPurchaseBurnRouteRejectCodeV1.PURCHASE_WITNESS_MISMATCH,
        ),
        (
            "verified_burn",
            "module_release_id",
            ZDEXPurchaseBurnRouteRejectCodeV1.BURN_WITNESS_MISMATCH,
        ),
        (
            "verified_burn",
            "expected_image_id",
            ZDEXPurchaseBurnRouteRejectCodeV1.BURN_WITNESS_MISMATCH,
        ),
        (
            "verified_buyback_budget",
            "module_release_id",
            ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH,
        ),
        (
            "verified_buyback_budget",
            "expected_image_id",
            ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH,
        ),
    ),
)
def test_mutated_verified_leaf_release_binding_rejects_without_effects(
    witness_name: str,
    field_name: str,
    expected: ZDEXPurchaseBurnRouteRejectCodeV1,
) -> None:
    # Arrange
    candidate = _verified_fixture()
    witness = getattr(candidate, witness_name)
    object.__setattr__(witness._fields, field_name, _root(97_500))

    # Act
    result = compose_zdex_purchase_burn_route_v1(candidate)

    # Assert
    _assert_no_effect_reject(result, expected)


@pytest.mark.parametrize(
    ("release_field", "lane_id"),
    (
        ("purchase_module_release", LaneIdV1.SPOT_LIQUIDITY),
        ("burn_module_release", LaneIdV1.ZDEX_TOKENOMICS),
    ),
)
def test_foreign_module_release_record_rejects_without_effects(
    release_field: str,
    lane_id: LaneIdV1,
) -> None:
    # Arrange
    candidate = _verified_fixture()
    foreign_release = _lane_release(lane_id, 97)
    candidate = replace(candidate, **{release_field: foreign_release})

    # Act
    result = compose_zdex_purchase_burn_route_v1(candidate)

    # Assert
    _assert_no_effect_reject(
        result,
        ZDEXPurchaseBurnRouteRejectCodeV1.GOVERNED_PROFILE_MISMATCH,
    )


@pytest.mark.parametrize(
    ("target_name", "field_name"),
    (
        ("verified_purchase", "expected_image_id"),
        ("verified_buyback_budget", "expected_image_id"),
        ("purchase_journal", "spot_module_release_id"),
        ("burn_journal", "tokenomics_module_release_id"),
    ),
)
def test_hostile_release_binding_scalar_rejects_before_composition(
    target_name: str,
    field_name: str,
) -> None:
    # Arrange
    candidate = _verified_fixture()
    target = getattr(candidate, target_name)
    if target_name.startswith("verified_"):
        target = target._fields
    value = getattr(target, field_name)
    object.__setattr__(target, field_name, _HostileRoot(value))

    # Act / Assert
    with pytest.raises(TypeError, match="exact primitive"):
        compose_zdex_purchase_burn_route_v1(candidate)


@pytest.mark.parametrize(
    "release_field",
    ("purchase_module_release", "burn_module_release"),
)
def test_route_release_snapshot_rejects_hostile_image_scalar(
    release_field: str,
) -> None:
    # Arrange
    candidate = _verified_fixture()
    release = getattr(candidate, release_field)
    object.__setattr__(
        release,
        "guest_image_id",
        _HostileRoot(release.guest_image_id),
    )

    # Act / Assert
    with pytest.raises(TypeError, match="exact primitive"):
        compose_zdex_purchase_burn_route_v1(candidate)


@pytest.mark.parametrize(
    ("burn_overrides", "expected"),
    (
        (
            {"profile_root": _root(996)},
            ZDEXPurchaseBurnRouteRejectCodeV1.PROFILE_OR_EPOCH_MISMATCH,
        ),
        (
            {"writer_epoch": 12},
            ZDEXPurchaseBurnRouteRejectCodeV1.PROFILE_OR_EPOCH_MISMATCH,
        ),
        (
            {"command_occurrence_id": _root(995)},
            ZDEXPurchaseBurnRouteRejectCodeV1.OCCURRENCE_MISMATCH,
        ),
        (
            {"chain_id": "other-chain"},
            ZDEXPurchaseBurnRouteRejectCodeV1.PROFILE_OR_EPOCH_MISMATCH,
        ),
        (
            {"deployment_root": _root(994)},
            ZDEXPurchaseBurnRouteRejectCodeV1.PROFILE_OR_EPOCH_MISMATCH,
        ),
    ),
)
def test_cross_layer_binding_mutants_reject_with_no_effects(
    burn_overrides: dict[str, object],
    expected: ZDEXPurchaseBurnRouteRejectCodeV1,
) -> None:
    candidate = _verified_fixture()
    mutated = replace(
        candidate,
        burn_journal=replace(candidate.burn_journal, **burn_overrides),
    )

    result = compose_zdex_purchase_burn_route_v1(mutated)

    _assert_no_effect_reject(result, expected)


@pytest.mark.parametrize(("quote_atoms", "purchased_atoms"), ((1, 1), (125, 40), (2**63, 2**32)))
def test_bva_positive_amounts_preserve_route_conservation(
    quote_atoms: int,
    purchased_atoms: int,
) -> None:
    candidate = _verified_fixture(
        purchase_overrides={
            "quote_amount_in_atoms": quote_atoms,
            "purchased_zdex_atoms": purchased_atoms,
            "zdex_owned_atoms": purchased_atoms + 100,
            "zdex_supply_atoms": purchased_atoms + 100,
        }
    )

    result = compose_zdex_purchase_burn_route_v1(candidate)

    assert result.effects.asset_conservation[-1].authorized_burn_atoms == purchased_atoms
    assert result.effects.asset_conservation[-1].supply_post_atoms == 100


def test_python_rust_golden_composition_root_is_stable() -> None:
    result = compose_zdex_purchase_burn_route_v1(_verified_fixture())

    assert result.composition_root == (
        "0xe4016bdba019f681a033744d30632102d8d34c3efd50dd85289c4e564e3b0a7b"
    )
    assert zdex_burn_port_schema_root_v1() == (
        "0x744c54af6df7c8a4fa0c5e0b152e0139add14c337d7cbcf1c8062e8aa2fa5289"
    )


@pytest.mark.parametrize("amount", (2**127, 2**128 - 1))
def test_effect_width_overflow_is_unrepresentable(amount: int) -> None:
    candidate = _verified_fixture()

    with pytest.raises(ValueError, match="signed effect atoms"):
        replace(candidate.purchase_journal, quote_amount_in_atoms=amount)


@pytest.mark.parametrize(
    ("field", "value"),
    (("burn_bucket_pre_atoms", 1), ("burn_bucket_post_atoms", 39)),
)
def test_purchase_cannot_mix_preexisting_inventory_into_burn(
    field: str,
    value: int,
) -> None:
    purchase = _verified_fixture().purchase_journal

    with pytest.raises(ValueError, match="transient burn bucket projection"):
        replace(purchase, **{field: value})


@pytest.mark.parametrize(
    ("field", "value"),
    (("burn_bucket_pre_atoms", 39), ("burn_bucket_post_atoms", 1)),
)
def test_burn_must_drain_the_purchased_output_exactly_once(
    field: str,
    value: int,
) -> None:
    burn = _verified_fixture().burn_journal

    with pytest.raises(ValueError, match="transient bucket projection"):
        replace(burn, **{field: value})


def test_quote_source_cannot_spend_more_than_its_committed_balance() -> None:
    purchase = _verified_fixture().purchase_journal

    with pytest.raises(ValueError, match="quote source projection"):
        replace(purchase, quote_source_pre_atoms=124, quote_source_post_atoms=0)


def _fee_lane_state(fee_state: ZDEXFeeStateV1) -> ZDEXTokenomicsLaneStateV1:
    return ZDEXTokenomicsLaneStateV1(
        supply_state=ZDEXSupplyStateV1(
            asset_id=_root(880),
            policy_root=_root(881),
            decimals=8,
            precision_epoch=0,
            live_supply_atoms=1_000,
            buckets=(ZDEXAmountBucketV1("wallet:alice", 1_000),),
            burn_budget_epoch=5,
            remaining_epoch_burn_cap_atoms=100,
        ),
        fee_allocation_states=(fee_state,),
        staking_state_root=_root(882),
        host_claims_state_root=_root(883),
        treasury_claims_state_root=_root(884),
        proof_rewards_state_root=_root(885),
        cover_reserve_state_root=_root(886),
        lp_rebates_state_root=_root(887),
    )


def _fee_lane_receipt_fixture(
    *,
    buyback_route_guest_image_id: str = _root(500),
) -> tuple[
    ZDEXTokenomicsFeeLaneReceiptCandidateV1,
    GovernedZDEXFeeAllocationProfileV1,
]:
    leaf, governed = _fee_receipt_candidate_fixture(
        buyback_route_guest_image_id=buyback_route_guest_image_id,
    )
    allocation = ZDEXFeeAllocationAcceptedV1(
        leaf.pre_state,
        leaf.post_state,
        leaf.effects,
        leaf.journal,
    )
    port = build_zdex_tokenomics_fee_allocation_private_port_v1(
        allocation,
        leaf.policy,
    )
    module = build_zdex_tokenomics_fee_allocation_module_journal_v1(
        allocation,
        leaf.policy,
        port,
    )
    occurrence = leaf.journal
    coordinator = governed._fields.coordinator_release
    context = ZDEXTokenomicsFeeAllocationCoordinatorContextV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=occurrence.writer_epoch,
        coordinator_release_id=coordinator.coordinator_release_id,
        allocation_route_release_id=occurrence.allocation_route_release_id,
        authorized_buyback_route_release_id=(
            occurrence.authorized_buyback_route_release_id
        ),
        tokenomics_module_release_id=occurrence.tokenomics_module_release_id,
        command_occurrence_id=occurrence.command_occurrence_id,
        policy_root=occurrence.policy_root,
    )
    lane = ZDEXTokenomicsFeeAllocationLaneCandidateV1(
        context,
        module,
        port,
        _fee_lane_state(allocation.pre_state),
        _fee_lane_state(allocation.post_state),
        allocation,
        leaf.policy,
    )
    verified_leaf = verify_zdex_fee_allocation_receipt_v1(
        leaf,
        governed,
        _Verifier(),
    )
    return (
        ZDEXTokenomicsFeeLaneReceiptCandidateV1(
            leaf.occurrence,
            lane,
            verified_leaf,
            ZDEXLaneReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"fee-tokenomics-lane-receipt",
            ),
        ),
        governed,
    )


def test_profile_selected_fee_leaf_and_coordinator_bind_complete_lane() -> None:
    # Arrange
    candidate, governed = _fee_lane_receipt_fixture()
    composed = compose_zdex_tokenomics_fee_allocation_lane_v1(
        candidate.lane_candidate
    )
    assert type(composed) is ZDEXTokenomicsLaneCompositionAcceptedV1
    verifier = _Verifier()
    assert (
        candidate.occurrence.pre_state_root
        != candidate.lane_candidate.allocation.pre_state.state_root
    )

    # Act
    verified = verify_zdex_tokenomics_fee_lane_receipt_v1(
        candidate,
        governed,
        verifier,
    )

    # Assert
    fields = governed._fields
    assert verified.profile_root == fields.profile.profile_id
    assert verified.route_release_id == fields.allocation_route.route_release_id
    assert verified.module_release_id == fields.module_release.release_id
    assert (
        verified.coordinator_release_id
        == fields.coordinator_release.coordinator_release_id
    )
    assert verified.pre_lane_root == candidate.lane_candidate.pre_state.state_root
    assert verified.post_lane_root == candidate.lane_candidate.post_state.state_root
    assert verified.binding_root == (
        "0x0734719e8e80b95ece0dff339bef408d584610b67533e9aa74a9f2e52a11aca8"
    )
    assert verifier.calls == [
        (
            candidate.receipt.receipt_bytes,
            fields.coordinator_release.guest_image_id,
            canonical_global_bytes_v1(composed.lane_journal),
        )
    ]


def test_retained_fee_lane_anchor_rejects_generation_swap_before_callback() -> None:
    # Arrange
    _, honest = _fee_lane_receipt_fixture()
    alternate_candidate, alternate = _fee_lane_receipt_fixture(
        buyback_route_guest_image_id=_root(98_100),
    )
    assert honest._fields.profile.profile_id != alternate._fields.profile.profile_id
    object.__setattr__(honest, "_fields", alternate._fields)
    verifier = _Verifier()

    # Act / Assert
    with pytest.raises(ValueError, match="trusted profile anchor"):
        verify_zdex_tokenomics_fee_lane_receipt_v1(
            alternate_candidate,
            honest,
            verifier,
        )
    assert verifier.calls == []


def test_fee_coordinator_callback_cannot_mutate_owned_witness_bindings() -> None:
    # Arrange
    candidate, governed = _fee_lane_receipt_fixture()
    fields = governed._fields
    expected = (
        fields.coordinator_release.coordinator_release_id,
        fields.coordinator_release.guest_image_id,
        "0x" + hashlib.sha256(candidate.receipt.receipt_bytes).hexdigest(),
        candidate.receipt.receipt_kind,
    )

    class _MutatingVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            del receipt_bytes, expected_image_id, expected_journal_bytes
            object.__setattr__(
                fields.coordinator_release,
                "coordinator_release_id",
                _root(99_001),
            )
            object.__setattr__(
                fields.coordinator_release,
                "guest_image_id",
                _root(99_002),
            )
            object.__setattr__(candidate.receipt, "receipt_bytes", b"mutated-lane")
            object.__setattr__(candidate.receipt, "receipt_kind", ReceiptKindV1.FAKE)

    # Act
    verified = verify_zdex_tokenomics_fee_lane_receipt_v1(
        candidate,
        governed,
        _MutatingVerifier(),
    )

    # Assert
    assert (
        verified.coordinator_release_id,
        verified.expected_image_id,
        verified.receipt_digest,
        verified.receipt_kind,
    ) == expected


def test_fee_coordinator_rejects_hostile_release_scalar_before_callback() -> None:
    # Arrange
    candidate, governed = _fee_lane_receipt_fixture()
    fields = governed._fields
    object.__setattr__(
        fields.coordinator_release,
        "guest_image_id",
        _HostileRoot(fields.coordinator_release.guest_image_id),
    )
    verifier = _Verifier()

    # Act / Assert
    with pytest.raises(TypeError, match="exact primitive"):
        verify_zdex_tokenomics_fee_lane_receipt_v1(
            candidate,
            governed,
            verifier,
        )
    assert verifier.calls == []


def test_unrelated_lane_root_substitution_requires_a_new_exact_receipt() -> None:
    # Arrange
    candidate, governed = _fee_lane_receipt_fixture()
    original = compose_zdex_tokenomics_fee_allocation_lane_v1(
        candidate.lane_candidate
    )
    assert type(original) is ZDEXTokenomicsLaneCompositionAcceptedV1
    verifier = _ExactVerifier(
        candidate.receipt.receipt_bytes,
        governed._fields.coordinator_release.guest_image_id,
        canonical_global_bytes_v1(original.lane_journal),
    )
    shifted_lane = replace(
        candidate.lane_candidate,
        pre_state=replace(
            candidate.lane_candidate.pre_state,
            staking_state_root=_root(999),
        ),
        post_state=replace(
            candidate.lane_candidate.post_state,
            staking_state_root=_root(999),
        ),
    )
    shifted = replace(candidate, lane_candidate=shifted_lane)

    # Act / Assert
    with pytest.raises(ValueError, match="exact receipt binding mismatch"):
        verify_zdex_tokenomics_fee_lane_receipt_v1(
            shifted,
            governed,
            verifier,
        )
    assert len(verifier.calls) == 1
    assert verifier.calls[0][2] != verifier.expected[2]


def test_fee_lane_context_and_receipt_shape_reject_before_verifier() -> None:
    # Arrange
    candidate, governed = _fee_lane_receipt_fixture()
    wrong_context = replace(
        candidate,
        lane_candidate=replace(
            candidate.lane_candidate,
            context=replace(
                candidate.lane_candidate.context,
                coordinator_release_id=_root(999),
            ),
        ),
    )
    wrong_receipt = replace(
        candidate,
        receipt=ZDEXLaneReceiptEnvelopeV1(
            ReceiptKindV1.CONDITIONAL,
            b"conditional",
        ),
    )
    verifier = _Verifier(reject=True)

    # Act / Assert
    with pytest.raises(ValueError):
        verify_zdex_tokenomics_fee_lane_receipt_v1(
            wrong_context,
            governed,
            verifier,
        )
    with pytest.raises(ValueError):
        verify_zdex_tokenomics_fee_lane_receipt_v1(
            wrong_receipt,
            governed,
            verifier,
        )
    assert verifier.calls == []


def test_mutated_governed_fee_profile_rejects_before_lane_verifier() -> None:
    # Arrange
    candidate, governed = _fee_lane_receipt_fixture()
    object.__setattr__(
        governed._fields.coordinator_release,
        "guest_image_id",
        _root(999),
    )
    verifier = _Verifier(reject=True)

    # Act / Assert
    with pytest.raises(ValueError):
        verify_zdex_tokenomics_fee_lane_receipt_v1(
            candidate,
            governed,
            verifier,
        )
    assert verifier.calls == []

#!/usr/bin/env python3
"""Render or check deterministic GlobalSettlementABI V1 parity vectors.

With no arguments, stdout is the canonical pretty-printed fixture and stderr
is empty. ``--write PATH`` performs canonical regeneration; ``--check PATH``
returns zero only when PATH is byte-identical to the current renderer output.
The vectors are research evidence and carry no proof-verification or
publication authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Final

from src.core.global_economic_proof_v1 import (
    CommandAggregationJournalV1,
    EconomicCommandOccurrenceV1,
    GlobalEconomicEpochCertificateV1,
    LaneCompositionJournalV1,
    LaneModuleTransitionJournalV1,
    MigrationObjectClassV1,
    MigrationObjectRowV1,
    ReceiptKindV1,
    RouteCompositionJournalV1,
    StateMigrationCertificateV1,
    derive_verified_economic_epoch_commit_id_v1,
)
from src.core.global_settlement_abi_v1 import (
    ALL_LANE_IDS_V1,
    MAX_ATOMS_V1,
    ZERO_ROOT_V1,
    AssetConservationRowV1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    EconomicInitialStateKindV1,
    EconomicProfileSnapshotV1,
    EvidenceStatusV1,
    ExternalOutboxEnqueueV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    LaneStateRootV1,
    LaneWriteV1,
    OutboxStateV1,
    OutboxStatusV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    ReplayStateV1,
    RouteRegistryV1,
    RouteReleaseV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
    canonical_global_bytes_v1,
    compose_asset_lane_epoch_effect_plans_v1,
    derive_economic_initial_state_outbox_continuity_root_v1,
    derive_economic_initial_state_replay_continuity_root_v1,
    derive_economic_initial_state_terminal_continuity_root_v1,
)
from src.core.route_composition_receipt_verification_v1 import (
    ROUTE_COMPOSITION_ASSUMPTION_SCHEMA_V1,
    derive_route_composition_assumption_root_v1,
)

FIXTURE_SCHEMA_V1: Final = "zenodex/global-settlement-abi-v1-golden/v1"
FIXTURE_PATH_V1: Final = Path("tests/data/global_settlement_abi_v1_golden.json")
_U64_NEIGHBOR_ATOMS: Final = (1 << 64) + 1


def _root(value: int) -> str:
    if not 0 < value <= MAX_ATOMS_V1:
        raise ValueError("fixture root ordinal is out of range")
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


def _module_release(lane_id: LaneIdV1, ordinal: int) -> LaneModuleReleaseV1:
    active = lane_id is LaneIdV1.ASSET_TRANSFER
    command_variants = ("transfer",) if active else ()
    offset = ordinal * 32
    return LaneModuleReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-golden",
        state_schema_root=_root(100 + offset),
        command_variants=command_variants,
        terminal_command_variants=command_variants,
        guest_image_id=_root(101 + offset),
        specification_root=_root(102 + offset),
        source_root=_root(103 + offset),
        toolchain_root=_root(104 + offset),
        terminal_coverage_root=_root(105 + offset),
        migration_compatibility_root=_root(106 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW if active else ReleaseStatusV1.SHADOW,
        accepts_new_objects=active,
        evidence_statuses=(
            _active_evidence() if active else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _coordinator_release(lane_id: LaneIdV1, ordinal: int) -> LaneCoordinatorReleaseV1:
    active = lane_id is LaneIdV1.ASSET_TRANSFER
    offset = ordinal * 32
    return LaneCoordinatorReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-golden",
        coordinator_schema_root=_root(500 + offset),
        guest_image_id=_root(501 + offset),
        specification_root=_root(502 + offset),
        source_root=_root(503 + offset),
        toolchain_root=_root(504 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW if active else ReleaseStatusV1.SHADOW,
        accepts_new_objects=active,
        evidence_statuses=(
            _active_evidence() if active else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _profile() -> tuple[EconomicProfileSnapshotV1, RouteReleaseV1]:
    releases = tuple(
        _module_release(lane_id, ordinal)
        for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
    )
    lane_registry = LaneRegistryV1(releases)
    lane_coordinator_registry = LaneCoordinatorRegistryV1(
        tuple(
            _coordinator_release(lane_id, ordinal)
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    asset_release = lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    route = RouteReleaseV1.build(
        semantic_version="1.0.0-golden",
        command_kind="transfer",
        ordered_lanes=(LaneIdV1.ASSET_TRANSFER,),
        module_release_ids=(asset_release.release_id,),
        dependency_roles=("VALUE_OWNER",),
        port_schema_roots=(_root(700),),
        guest_image_id=_root(703),
        specification_root=_root(704),
        source_root=_root(705),
        toolchain_root=_root(706),
        oracle_policy_root=_root(701),
        issue_burn_policy_root=_root(702),
        max_cycles=2_000_000,
        max_journal_bytes=131_072,
        status=ReleaseStatusV1.ACTIVE_NEW,
        accepts_new_objects=True,
        evidence_statuses=_active_evidence(),
    )
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=7,
        lane_registry=lane_registry,
        lane_coordinator_registry=lane_coordinator_registry,
        route_registry=RouteRegistryV1((route,)),
        proof_shape_root=_root(710),
        root_image_id=_root(711),
        verifier_registry_root=_root(712),
        migration_registry_root=_root(713),
        policy_registry_root=_root(714),
        terminal_registry_root=_root(715),
        status=ProfileStatusV1.ACTIVE,
    )
    return profile, route


def _canonical(value: object) -> object:
    return json.loads(canonical_global_bytes_v1(value))


def _vector(value: object, *, expected_root: str) -> dict[str, object]:
    canonical_bytes = canonical_global_bytes_v1(value)
    return {
        "canonical": json.loads(canonical_bytes),
        "canonical_bytes_sha256": hashlib.sha256(canonical_bytes).hexdigest(),
        "expected_root": expected_root,
    }


def _state(profile: EconomicProfileSnapshotV1) -> GlobalEconomicStateV1:
    lane_roots = tuple(
        LaneStateRootV1(
            lane_id=release.lane_id,
            module_release_id=release.release_id,
            enabled=release.accepts_new_objects,
            state_root=_root(1_000 + ordinal) if release.accepts_new_objects else ZERO_ROOT_V1,
        )
        for ordinal, release in enumerate(profile.lane_registry.releases)
    )
    return GlobalEconomicStateV1(
        chain_id="zeno-golden-chain",
        deployment_root=_root(800),
        writer_epoch=profile.authority_epoch,
        height=41,
        profile_root=profile.profile_id,
        lane_roots=lane_roots,
        balances=(EconomicAmountV1("alice", "USD", "accounts", _U64_NEIGHBOR_ATOMS),),
        supplies=(AssetSupplyV1("USD", _U64_NEIGHBOR_ATOMS),),
    )


def _replay_continuity_vector(
    state: GlobalEconomicStateV1,
) -> tuple[dict[str, object], str]:
    source_row = ReplayStateV1("replay-source", _root(1_501))
    predecessor_state = replace(state, replay_state=(source_row,))
    target_state = replace(
        predecessor_state,
        writer_epoch=predecessor_state.writer_epoch + 1,
        height=predecessor_state.height + 1,
        profile_root=_root(1_503),
        replay_state=(source_row,),
    )
    vector = {
        "kind": EconomicInitialStateKindV1.MIGRATION,
        "target_state": target_state,
        "predecessor_state": predecessor_state,
    }
    expected_root = derive_economic_initial_state_replay_continuity_root_v1(
        EconomicInitialStateKindV1.MIGRATION,
        target_state,
        predecessor_state,
    )
    return vector, expected_root


def _outbox_continuity_vector(
    state: GlobalEconomicStateV1,
) -> tuple[dict[str, object], str]:
    rows = (
        OutboxStateV1(
            effect_id=_root(1_511),
            destination_id="bridge:golden",
            payload_hash=_root(1_512),
            commit_id=_root(1_513),
            status=OutboxStatusV1.PENDING,
        ),
        OutboxStateV1(
            effect_id=_root(1_514),
            destination_id="bridge:golden",
            payload_hash=_root(1_515),
            commit_id=_root(1_516),
            status=OutboxStatusV1.ACKNOWLEDGED,
        ),
    )
    predecessor_state = replace(state, outbox=rows)
    target_state = replace(
        predecessor_state,
        writer_epoch=predecessor_state.writer_epoch + 1,
        height=predecessor_state.height + 1,
        profile_root=_root(1_517),
    )
    vector = {
        "kind": EconomicInitialStateKindV1.MIGRATION,
        "target_state": target_state,
        "predecessor_state": predecessor_state,
    }
    expected_root = derive_economic_initial_state_outbox_continuity_root_v1(
        EconomicInitialStateKindV1.MIGRATION,
        target_state,
        predecessor_state,
    )
    return vector, expected_root


def _terminal_continuity_vector(
    state: GlobalEconomicStateV1,
) -> tuple[dict[str, object], str]:
    rows = (
        TerminalObligationV1(
            "terminal-open",
            LaneIdV1.ZUSD_MONETARY,
            "alice",
            "zUSD",
            17,
            TerminalObligationStatusV1.OPEN,
        ),
        TerminalObligationV1(
            "terminal-drained",
            LaneIdV1.PROOF_REWARDS,
            "bob",
            "ZDEX",
            23,
            TerminalObligationStatusV1.DRAINED,
        ),
        TerminalObligationV1(
            "terminal-tombstoned",
            LaneIdV1.STRATEGY_ESCROW,
            "carol",
            "USD",
            29,
            TerminalObligationStatusV1.TOMBSTONED,
        ),
    )
    rows = tuple(sorted(rows, key=lambda row: row.obligation_id))
    predecessor_state = replace(state, terminal_obligations=rows)
    target_state = replace(
        predecessor_state,
        writer_epoch=predecessor_state.writer_epoch + 1,
        height=predecessor_state.height + 1,
        profile_root=_root(1_518),
    )
    vector = {
        "kind": EconomicInitialStateKindV1.MIGRATION,
        "target_state": target_state,
        "predecessor_state": predecessor_state,
    }
    expected_root = derive_economic_initial_state_terminal_continuity_root_v1(
        EconomicInitialStateKindV1.MIGRATION,
        target_state,
        predecessor_state,
    )
    return vector, expected_root


def _effect_plan(lane_roots: tuple[LaneStateRootV1, ...]) -> GlobalEconomicEffectPlanV1:
    effect_rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.ISSUE,
                    "issuer",
                    "USD",
                    "supply",
                    5,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.FEE_ALLOCATION,
                    "treasury",
                    "USD",
                    "reserve",
                    1,
                ),
            ),
            key=lambda item: item.key,
        )
    )
    return GlobalEconomicEffectPlanV1(
        rows=effect_rows,
        asset_conservation=(
            AssetConservationRowV1(
                asset="USD",
                owned_and_custodied_pre_atoms=_U64_NEIGHBOR_ATOMS,
                owned_and_custodied_post_atoms=_U64_NEIGHBOR_ATOMS + 5,
                supply_pre_atoms=_U64_NEIGHBOR_ATOMS,
                supply_post_atoms=_U64_NEIGHBOR_ATOMS + 5,
                authorized_issue_atoms=5,
                authorized_burn_atoms=0,
            ),
        ),
        fee_conservation=(FeeConservationRowV1("USD", 2, 1, 1),),
        lane_writes=tuple(
            sorted(
                (
                    LaneWriteV1(
                        LaneIdV1.ASSET_TRANSFER,
                        lane_roots[0].state_root,
                        _root(1_100),
                    ),
                    LaneWriteV1(
                        LaneIdV1.FARM_INCENTIVES,
                        ZERO_ROOT_V1,
                        _root(1_105),
                    ),
                    LaneWriteV1(
                        LaneIdV1.SPOT_LIQUIDITY,
                        ZERO_ROOT_V1,
                        _root(1_106),
                    ),
                ),
                key=lambda item: item.lane_id,
            ),
        ),
        occurrence_consumptions=(_root(1_101),),
        external_outbox_enqueue=(
            ExternalOutboxEnqueueV1(
                effect_id=_root(1_102),
                destination_id="ethereum:golden",
                payload_hash=_root(1_103),
                adapter_profile_root=_root(1_104),
            ),
        ),
    )


def _asset_route_effect_plan(
    *,
    occurrence_ordinal: int,
    pre_lane_ordinal: int,
    post_lane_ordinal: int,
    sender_delta_atoms: int,
    recipient_delta_atoms: int,
) -> GlobalEconomicEffectPlanV1:
    rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                    "alice",
                    "USD",
                    "accounts",
                    sender_delta_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                    "bob",
                    "USD",
                    "accounts",
                    recipient_delta_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                    "treasury",
                    "USD",
                    "accounts",
                    2,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.FEE_ALLOCATION,
                    "treasury",
                    "USD",
                    "fee_allocations",
                    2,
                ),
            ),
            key=lambda item: item.key,
        )
    )
    return GlobalEconomicEffectPlanV1(
        rows=rows,
        asset_conservation=(AssetConservationRowV1("USD", 100, 100, 100, 100, 0, 0),),
        fee_conservation=(FeeConservationRowV1("USD", 2, 2, 0),),
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.ASSET_TRANSFER,
                _root(pre_lane_ordinal),
                _root(post_lane_ordinal),
            ),
        ),
        occurrence_consumptions=(_root(occurrence_ordinal),),
        external_outbox_enqueue=(),
    )


def _epoch_route_effect_plans() -> tuple[GlobalEconomicEffectPlanV1, ...]:
    return (
        _asset_route_effect_plan(
            occurrence_ordinal=1_201,
            pre_lane_ordinal=1_210,
            post_lane_ordinal=1_211,
            sender_delta_atoms=-12,
            recipient_delta_atoms=10,
        ),
        _asset_route_effect_plan(
            occurrence_ordinal=1_202,
            pre_lane_ordinal=1_211,
            post_lane_ordinal=1_212,
            sender_delta_atoms=-7,
            recipient_delta_atoms=5,
        ),
    )


def _occurrence(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    state: GlobalEconomicStateV1,
) -> EconomicCommandOccurrenceV1:
    return EconomicCommandOccurrenceV1(
        chain_id=state.chain_id,
        deployment_root=state.deployment_root,
        height=state.height + 1,
        tx_index=2,
        op_index=3,
        command_kind=route.command_kind,
        command_body_hash=_root(1_203),
        route_release_id=route.route_release_id,
        subject_id="alice",
        grant_root=_root(1_200),
        nonce=9,
        profile_root=profile.profile_id,
        pre_state_root=state.state_root,
        consumed_object_ids=(_root(1_201), _root(1_202)),
    )


@dataclass(frozen=True, slots=True)
class _JournalChainV1:
    module: LaneModuleTransitionJournalV1
    lane: LaneCompositionJournalV1
    route: RouteCompositionJournalV1


def _journal_chain(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    state: GlobalEconomicStateV1,
    effect_plan: GlobalEconomicEffectPlanV1,
    occurrence: EconomicCommandOccurrenceV1,
) -> _JournalChainV1:
    lane_roots = state.lane_roots
    module_journal = LaneModuleTransitionJournalV1(
        chain_id=state.chain_id,
        deployment_root=state.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        lane_id=LaneIdV1.ASSET_TRANSFER,
        module_release_id=route.module_release_ids[0],
        command_occurrence_id=occurrence.occurrence_id,
        pre_lane_root=lane_roots[0].state_root,
        post_lane_root=_root(1_100),
        effect_plan_root=effect_plan.effect_plan_root,
        private_port_root=ZERO_ROOT_V1,
        receipt_root=_root(1_203),
        terminal_obligations_root=ZERO_ROOT_V1,
    )
    lane = LaneCompositionJournalV1(
        chain_id=state.chain_id,
        deployment_root=state.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        lane_id=LaneIdV1.ASSET_TRANSFER,
        coordinator_release_id=profile.lane_coordinator_registry.release_for(
            LaneIdV1.ASSET_TRANSFER
        ).coordinator_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        ordered_module_journal_roots=(module_journal.journal_root,),
        pre_lane_root=lane_roots[0].state_root,
        post_lane_root=_root(1_100),
        effect_plan_root=effect_plan.effect_plan_root,
        terminal_obligations_root=ZERO_ROOT_V1,
    )
    route_journal = RouteCompositionJournalV1(
        chain_id=state.chain_id,
        deployment_root=state.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        ordered_lane_journal_roots=(lane.journal_root,),
        pre_state_root=state.state_root,
        post_state_root=_root(1_300),
        effect_plan_root=effect_plan.effect_plan_root,
        terminal_obligations_root=ZERO_ROOT_V1,
    )
    return _JournalChainV1(module_journal, lane, route_journal)


def _epoch_certificate(
    profile: EconomicProfileSnapshotV1,
    state: GlobalEconomicStateV1,
    effect_plan: GlobalEconomicEffectPlanV1,
    occurrence: EconomicCommandOccurrenceV1,
    route_journal: RouteCompositionJournalV1,
) -> GlobalEconomicEpochCertificateV1:
    route = profile.route_registry.route_for_command(occurrence.command_kind)
    route_journal_digest = "0x" + hashlib.sha256(
        canonical_global_bytes_v1(route_journal)
    ).hexdigest()
    route_assumption_root = derive_route_composition_assumption_root_v1(
        profile_id=profile.profile_id,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        writer_epoch=profile.authority_epoch,
        route_journal_root=route_journal.journal_root,
        route_journal_digest=route_journal_digest,
        expected_image_id=route.guest_image_id,
    )
    certificate = GlobalEconomicEpochCertificateV1(
        chain_id=state.chain_id,
        deployment_root=state.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        height=state.height + 1,
        pre_state_root=state.state_root,
        post_state_root=route_journal.post_state_root,
        ordered_occurrence_ids=(occurrence.occurrence_id,),
        ordered_route_journal_roots=(route_journal.journal_root,),
        ordered_route_assumption_roots=(route_assumption_root,),
        module_leaf_occurrences=1,
        aggregation_fanout=8,
        aggregation_levels=0,
        effect_plan_root=effect_plan.effect_plan_root,
        terminal_obligations_root=ZERO_ROOT_V1,
        body_commitment=_root(1_301),
        data_availability_root=_root(1_302),
        finality_root=_root(1_303),
        source_manifest_root=_root(1_304),
        toolchain_manifest_root=_root(1_305),
        root_image_id=profile.root_image_id,
        receipt_root=_root(1_306),
        receipt_kind=ReceiptKindV1.SUCCINCT,
        journal_bytes=1,
        cycle_budget=2_000_000,
    )
    return replace(certificate, journal_bytes=len(certificate.canonical_journal_bytes))


def _migration(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    state: GlobalEconomicStateV1,
) -> StateMigrationCertificateV1:
    return StateMigrationCertificateV1(
        source_profile_root=profile.profile_id,
        target_profile_root=_root(1_400),
        predecessor_profile_root=profile.profile_id,
        source_state_root=state.state_root,
        target_state_root=_root(1_401),
        source_writer_epoch=profile.authority_epoch,
        target_writer_epoch=profile.authority_epoch + 1,
        object_rows=(
            MigrationObjectRowV1(
                source_object_id="vault:golden",
                source_release_id=route.module_release_ids[0],
                target_release_id=_root(1_402),
                classification=MigrationObjectClassV1.MIGRATED,
                source_object_root=_root(1_403),
                target_object_root=_root(1_404),
                continuity_root=_root(1_405),
            ),
        ),
        custody_continuity_root=_root(1_406),
        liability_continuity_root=_root(1_407),
        terminal_continuity_root=_root(1_408),
        replay_continuity_root=_root(1_409),
        root_image_id=_root(1_410),
        proof_receipt_root=_root(1_411),
        receipt_kind=ReceiptKindV1.SUCCINCT,
    )


def build_vectors_v1() -> dict[str, object]:
    """Build the bounded typed corpus used by Python and Rust parity tests."""

    profile, route = _profile()
    state = _state(profile)
    replay_continuity, replay_continuity_root = _replay_continuity_vector(state)
    outbox_continuity, outbox_continuity_root = _outbox_continuity_vector(state)
    terminal_continuity, terminal_continuity_root = _terminal_continuity_vector(state)
    effect_plan = _effect_plan(state.lane_roots)
    epoch_route_effect_plans = _epoch_route_effect_plans()
    epoch_composed_effect_plan = compose_asset_lane_epoch_effect_plans_v1(
        epoch_route_effect_plans
    )
    occurrence = _occurrence(profile, route, state)
    journals = _journal_chain(profile, route, state, effect_plan, occurrence)
    certificate = _epoch_certificate(profile, state, effect_plan, occurrence, journals.route)
    route_journal_digest = "0x" + hashlib.sha256(
        canonical_global_bytes_v1(journals.route)
    ).hexdigest()
    route_assumption = {
        "schema": ROUTE_COMPOSITION_ASSUMPTION_SCHEMA_V1,
        "profile_id": profile.profile_id,
        "route_release_id": route.route_release_id,
        "command_occurrence_id": occurrence.occurrence_id,
        "writer_epoch": profile.authority_epoch,
        "route_journal_root": journals.route.journal_root,
        "route_journal_digest": route_journal_digest,
        "expected_image_id": route.guest_image_id,
    }
    route_assumption_root = derive_route_composition_assumption_root_v1(
        profile_id=profile.profile_id,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        writer_epoch=profile.authority_epoch,
        route_journal_root=journals.route.journal_root,
        route_journal_digest=route_journal_digest,
        expected_image_id=route.guest_image_id,
    )
    command_aggregation = CommandAggregationJournalV1(
        chain_id=state.chain_id,
        deployment_root=state.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        epoch_height=certificate.height,
        group_index=0,
        first_command_index=0,
        ordered_occurrence_ids=(occurrence.occurrence_id,),
        ordered_route_journal_roots=(journals.route.journal_root,),
        ordered_route_assumption_roots=(route_assumption_root,),
        pre_state_root=state.state_root,
        post_state_root=journals.route.post_state_root,
        module_leaf_occurrences=1,
    )
    migration = _migration(profile, route, state)
    verified_route_binding_roots = (_root(1_307),)
    verified_epoch_commit = {
        "certificate_root": certificate.certificate_root,
        "ordered_route_binding_roots": verified_route_binding_roots,
        "receipt_digest": certificate.receipt_root,
    }
    vectors = {
        "lane_module_release": _vector(
            profile.lane_registry.releases[0],
            expected_root=profile.lane_registry.releases[0].release_id,
        ),
        "lane_registry": _vector(
            profile.lane_registry,
            expected_root=profile.lane_registry.registry_root,
        ),
        "lane_coordinator_release": _vector(
            profile.lane_coordinator_registry.releases[0],
            expected_root=profile.lane_coordinator_registry.releases[0].coordinator_release_id,
        ),
        "lane_coordinator_registry": _vector(
            profile.lane_coordinator_registry,
            expected_root=profile.lane_coordinator_registry.registry_root,
        ),
        "route_release": _vector(route, expected_root=route.route_release_id),
        "route_registry": _vector(
            profile.route_registry,
            expected_root=profile.route_registry.registry_root,
        ),
        "economic_profile": _vector(profile, expected_root=profile.profile_id),
        "global_state": _vector(state, expected_root=state.state_root),
        "economic_initial_state_replay_continuity": _vector(
            replay_continuity,
            expected_root=replay_continuity_root,
        ),
        "economic_initial_state_outbox_continuity": _vector(
            outbox_continuity,
            expected_root=outbox_continuity_root,
        ),
        "economic_initial_state_terminal_continuity": _vector(
            terminal_continuity,
            expected_root=terminal_continuity_root,
        ),
        "effect_plan": _vector(effect_plan, expected_root=effect_plan.effect_plan_root),
        "epoch_route_effect_plan_1": _vector(
            epoch_route_effect_plans[0],
            expected_root=epoch_route_effect_plans[0].effect_plan_root,
        ),
        "epoch_route_effect_plan_2": _vector(
            epoch_route_effect_plans[1],
            expected_root=epoch_route_effect_plans[1].effect_plan_root,
        ),
        "epoch_composed_effect_plan": _vector(
            epoch_composed_effect_plan,
            expected_root=epoch_composed_effect_plan.effect_plan_root,
        ),
        "command_occurrence": _vector(occurrence, expected_root=occurrence.occurrence_id),
        "module_journal": _vector(journals.module, expected_root=journals.module.journal_root),
        "lane_journal": _vector(journals.lane, expected_root=journals.lane.journal_root),
        "route_journal": _vector(journals.route, expected_root=journals.route.journal_root),
        "route_assumption": _vector(
            route_assumption,
            expected_root=route_assumption_root,
        ),
        "command_aggregation_journal": _vector(
            command_aggregation,
            expected_root=command_aggregation.journal_root,
        ),
        "epoch_certificate": {
            **_vector(certificate, expected_root=certificate.certificate_root),
            "journal_canonical": _canonical(certificate.journal_canonical()),
            "journal_bytes_len": len(certificate.canonical_journal_bytes),
            "journal_bytes_sha256": hashlib.sha256(certificate.canonical_journal_bytes).hexdigest(),
        },
        "verified_epoch_commit": _vector(
            verified_epoch_commit,
            expected_root=derive_verified_economic_epoch_commit_id_v1(
                certificate_root=certificate.certificate_root,
                ordered_route_binding_roots=verified_route_binding_roots,
                receipt_digest=certificate.receipt_root,
            ),
        ),
        "migration_certificate": _vector(migration, expected_root=migration.certificate_root),
    }
    return {"fixture_schema": FIXTURE_SCHEMA_V1, "vectors": vectors}


def render_vectors_v1() -> str:
    return json.dumps(build_vectors_v1(), indent=2, sort_keys=True) + "\n"


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    output = parser.add_mutually_exclusive_group()
    output.add_argument(
        "--check",
        type=Path,
        metavar="PATH",
        help="fail unless PATH exactly matches the rendered fixture",
    )
    output.add_argument(
        "--write",
        type=Path,
        metavar="PATH",
        help="write the canonical rendered fixture to PATH",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    rendered = render_vectors_v1()
    if args.write is not None:
        args.write.write_text(rendered, encoding="utf-8")
        print(f"global ABI fixture written: {args.write}")
        return 0
    if args.check is None:
        sys.stdout.write(rendered)
        return 0
    try:
        observed = args.check.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"global ABI fixture check failed: {exc}", file=sys.stderr)
        return 1
    if observed != rendered:
        print(f"global ABI fixture drift: {args.check}", file=sys.stderr)
        return 1
    print(f"global ABI fixture match: {args.check}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

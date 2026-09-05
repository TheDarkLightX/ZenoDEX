"""Deterministic input and journal assembly using the existing economic kernels.

These owned local values are proof inputs, with no receipt or publication authority.
"""

from __future__ import annotations

import dataclasses
import json

from src.core import global_economic_proof_v1 as proof
from src.core import global_settlement_types_v1 as abi
from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1
from src.core.asset_lane_projection_v1 import (
    AssetLaneCompositionAcceptedV1,
    AssetLaneCoordinatorContextV1,
    AssetLaneModuleCompatibilityV1,
)
from src.core.asset_transfer_global_allocation_v1 import (
    _global_allocation_binding_reject_v1,
)
from src.core.asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
    transition_asset_transfer_lane_module_v1,
)
from src.core.asset_transfer_policy_registry_v1 import AssetTransferPolicyRegistryV1
from src.core.asset_transfer_types_v1 import (
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferStateV1,
)
from src.core.economic_initial_state_atom_coverage_v1 import (
    EconomicInitialStateAtomClassificationV1 as Classification,
)
from src.core.economic_initial_state_atom_coverage_v1 import (
    EconomicInitialStateAtomSourceV1 as Source,
)
from src.core.economic_initial_state_atom_coverage_v1 import (
    EconomicInitialStateKindV1 as Kind,
)
from src.core.economic_initial_state_atom_coverage_v1 import (
    EconomicInitialStateSourceManifestV1 as SourceManifest,
)
from src.core.economic_initial_state_atom_coverage_v1 import (
    derive_economic_initial_state_atom_occurrences_v1,
    economic_initial_state_atom_coverage_policy_binding_v1,
    validate_economic_initial_state_atom_coverage_profile_binding_v1,
    validate_economic_initial_state_atom_coverage_v1,
)
from src.core.economic_initial_state_outbox_continuity_v1 import (
    derive_economic_initial_state_outbox_continuity_root_v1 as outbox_root,
)
from src.core.economic_initial_state_replay_continuity_v1 import (
    derive_economic_initial_state_replay_continuity_root_v1 as replay_root,
)
from src.core.economic_initial_state_terminal_continuity_v1 import (
    derive_economic_initial_state_terminal_continuity_root_v1 as terminal_root,
)
from src.core.global_economic_state_decoder_v1 import decode_global_economic_state_v1
from src.core.global_economic_state_effect_refinement_v1 import (
    GlobalEconomicStateEffectRefinementCandidateV1,
    refine_route_global_economic_state_effects_v1,
)
from src.core.lane_module_release_route_binding_v1 import (
    AssetTransferReleaseRouteBindingCandidateV1,
    _bind_asset_transfer_lane_output_structural_v1,
)
from src.core.route_composition_receipt_verification_v1 import (
    derive_route_composition_assumption_root_v1,
)
from src.core.route_global_state_projection_v1 import (
    RouteGlobalStateProjectionCandidateV1,
    project_route_global_state_v1,
)
from tools.isolated_bls_evidence_v1 import (
    sha256,
)
from zk.asset_transfer_route_composer_risc0.check_reference import profile as decode_profile
from zk.asset_transfer_route_composer_risc0.check_reference import record


def _flat(cls, raw):
    value = dict(raw)
    value.pop("schema", None)
    return record(cls, value)


def decode_module(raw: dict) -> AssetTransferLaneModuleInputV1:
    state = raw["pre_state"]
    return AssetTransferLaneModuleInputV1(
        _flat(AssetTransferContextV1, raw["context"]),
        AssetTransferStateV1(
            module_release_id=state["module_release_id"],
            balances=tuple(_flat(abi.EconomicAmountV1, r) for r in state["balances"]),
            supplies=tuple(_flat(abi.AssetSupplyV1, r) for r in state["supplies"]),
            policies=tuple(_flat(AssetTransferPolicyV1, r) for r in state["policies"]),
        ),
        _flat(AssetTransferCommandV1, raw["command"]),
        raw["asset_policy_registry_root"],
        raw["fee_policy_registry_root"],
        tuple(_flat(abi.EconomicAmountV1, r) for r in raw["custody"]),
    )


def _coordinator(raw: dict) -> AssetLaneCoordinatorContextV1:
    value = dict(raw)
    value["compatible_modules"] = tuple(
        _flat(AssetLaneModuleCompatibilityV1, row) for row in value["compatible_modules"]
    )
    return _flat(AssetLaneCoordinatorContextV1, value)


def genesis_source(pre):
    if pre.height != 0 or pre.replay_state or pre.custody:
        raise ValueError("isolated seed requires empty replay/custody at genesis")
    occurrences = derive_economic_initial_state_atom_occurrences_v1(pre)
    assumption = {
        "schema": "zenodex/isolated-genesis-allocation-rows/v1",
        "source_authorization_verified": False,
        "chain_id": pre.chain_id,
        "deployment_root": pre.deployment_root,
        "writer_epoch": pre.writer_epoch,
        "atom_occurrences": occurrences,
    }
    authorization_root = abi.hash_global_v1("isolated-genesis-allocation-rows-v1", assumption)
    manifest = SourceManifest(
        Kind.GENESIS,
        tuple(
            Source(row, Classification.GENESIS_ALLOCATION, authorization_root)
            for row in occurrences
        ),
    )
    return assumption, manifest


def rebind(value, signatures, authorizations, source_manifest):
    previous = decode_profile(value)
    coverage = economic_initial_state_atom_coverage_policy_binding_v1(source_manifest)
    roots = {
        "command_authentication_registry": authorizations.registry_root,
        "command_signature_verifier_registry": signatures.registry_root,
        coverage.policy_kind: coverage.policy_root,
    }
    policies = abi.EconomicPolicyRegistryV1(
        tuple(
            dataclasses.replace(
                record(abi.EconomicPolicyBindingV1, row),
                policy_root=roots.get(row["policy_kind"], row["policy_root"]),
            )
            for row in value["policy_registry"]["bindings"]
        )
    )
    fields = {
        f.name: getattr(previous, f.name)
        for f in dataclasses.fields(previous)
        if f.name != "profile_id"
    }
    selected = abi.EconomicProfileSnapshotV1.build(
        **(fields | {"policy_registry_root": policies.registry_root})
    )
    value["profile"], value["policy_registry"] = (
        json.loads(abi.canonical_global_bytes_v1(selected)),
        json.loads(abi.canonical_global_bytes_v1(policies)),
    )
    for name in ("pre_state", "post_state"):
        value[name]["profile_root"] = selected.profile_id
    pre = decode_global_economic_state_v1(value["pre_state"])
    value["occurrence"].update(profile_root=selected.profile_id, pre_state_root=pre.state_root)
    occurrence = record(proof.EconomicCommandOccurrenceV1, value["occurrence"])
    for context in (
        value["lane_input"]["module_input"]["context"],
        value["lane_input"]["coordinator_context"],
    ):
        context.update(
            profile_root=selected.profile_id, command_occurrence_id=occurrence.occurrence_id
        )
    value["post_state"]["replay_state"] = [
        {"replay_id": occurrence.replay_id, "occurrence_id": occurrence.occurrence_id}
    ]
    validate_economic_initial_state_atom_coverage_v1(pre, source_manifest)
    validate_economic_initial_state_atom_coverage_profile_binding_v1(
        selected, policies, source_manifest
    )
    return selected, policies, pre, occurrence


def economic_preflight(value, selected, policies, occurrence):
    module = decode_module(value["lane_input"]["module_input"])
    accepted = transition_asset_transfer_lane_module_v1(module)
    if type(accepted) is not AssetTransferLaneModuleAcceptedV1:
        raise ValueError("prepared module transition rejected")
    asset_policy = AssetTransferPolicyRegistryV1(
        module.pre_state.module_release_id, module.pre_state.policies
    )
    binding = _bind_asset_transfer_lane_output_structural_v1(
        AssetTransferReleaseRouteBindingCandidateV1(
            selected, policies, asset_policy, occurrence, module, accepted
        )
    )
    lane = compose_asset_lane_single_v1(
        _coordinator(value["lane_input"]["coordinator_context"]),
        accepted.module_journal,
        accepted.private_port,
        accepted.effects,
    )
    if type(lane) is not AssetLaneCompositionAcceptedV1:
        raise ValueError("prepared coordinator transition rejected")
    pre, post = (
        decode_global_economic_state_v1(value[name]) for name in ("pre_state", "post_state")
    )
    rejected = _global_allocation_binding_reject_v1(accepted, occurrence, pre, post)
    if rejected is not None:
        raise ValueError(f"prepared allocation rejected: {rejected}")
    journal = proof.RouteCompositionJournalV1(
        pre.chain_id,
        pre.deployment_root,
        selected.profile_id,
        pre.writer_epoch,
        occurrence.route_release_id,
        occurrence.occurrence_id,
        (lane.lane_journal.journal_root,),
        pre.state_root,
        post.state_root,
        lane.effects.effect_plan_root,
        lane.lane_journal.terminal_obligations_root,
    )
    projection = project_route_global_state_v1(
        RouteGlobalStateProjectionCandidateV1(
            selected, selected.route_registry.routes[0], (lane.lane_journal,), journal, pre, post
        )
    )
    refinement = refine_route_global_economic_state_effects_v1(
        GlobalEconomicStateEffectRefinementCandidateV1(
            pre, post, lane.effects, (occurrence,), (journal,)
        )
    )
    if {r.owner: r.amount_atoms for r in post.balances} != {"alice": 68, "bob": 40, "treasury": 7}:
        raise ValueError("independent seed arithmetic differs")
    return (
        module,
        accepted,
        lane,
        journal,
        {
            "projection_root": projection.projection_root,
            "refinement_root": refinement.refinement_root,
            "release_route_binding_root": binding.binding_root,
        },
    )


def initial_input(selected, policies, pre, source_manifest, roots):
    statement = dict(
        schema=abi.GLOBAL_SETTLEMENT_ABI_V1,
        kind=Kind.GENESIS,
        chain_id=pre.chain_id,
        deployment_root=pre.deployment_root,
        profile_root=selected.profile_id,
        writer_epoch=pre.writer_epoch,
        height=0,
        state_root=pre.state_root,
        source_profile_root=abi.ZERO_ROOT_V1,
        source_state_root=abi.ZERO_ROOT_V1,
        source_writer_epoch=0,
        source_height=0,
        state_atom_coverage_root=source_manifest.manifest_root,
        lane_object_coverage_root=abi.hash_global_v1(
            "isolated-initial-lane-disclosure-v1", {"lane_roots": pre.lane_roots}
        ),
        replay_continuity_root=replay_root(Kind.GENESIS, pre, None),
        terminal_continuity_root=terminal_root(Kind.GENESIS, pre, None),
        outbox_continuity_root=outbox_root(Kind.GENESIS, pre, None),
        source_manifest_root=roots["source-manifest.json"],
        toolchain_manifest_root=roots["runtime-manifest.json"],
        root_image_id=selected.root_image_id,
    )
    return dict(
        schema="zenodex/economic-initial-state-guest-input/v1",
        profile=selected,
        policy_registry=policies,
        state=pre,
        predecessor_state=None,
        source_manifest=source_manifest,
        statement=statement,
    )


def epoch_input(selected, occurrence, journal, roots):
    raw = abi.canonical_global_bytes_v1(journal)
    image = selected.route_registry.routes[0].guest_image_id
    assumption = derive_route_composition_assumption_root_v1(
        profile_id=selected.profile_id,
        route_release_id=journal.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        writer_epoch=journal.writer_epoch,
        route_journal_root=journal.journal_root,
        route_journal_digest="0x" + sha256(raw),
        expected_image_id=image,
    )
    statement = dict(
        schema=abi.GLOBAL_SETTLEMENT_ABI_V1,
        chain_id=journal.chain_id,
        deployment_root=journal.deployment_root,
        profile_root=selected.profile_id,
        writer_epoch=journal.writer_epoch,
        height=1,
        pre_state_root=journal.pre_state_root,
        post_state_root=journal.post_state_root,
        ordered_occurrence_ids=[occurrence.occurrence_id],
        ordered_route_journal_roots=[journal.journal_root],
        ordered_route_assumption_roots=[assumption],
        module_leaf_occurrences=1,
        aggregation_fanout=8,
        aggregation_levels=0,
        effect_plan_root=journal.effect_plan_root,
        terminal_obligations_root=journal.terminal_obligations_root,
        body_commitment=occurrence.command_body_hash,
        data_availability_root=roots["source-manifest.json"],
        finality_root=abi.hash_global_v1(
            "isolated-finality-assumption-v1", {"external_finality_verified": False}
        ),
        source_manifest_root=roots["source-manifest.json"],
        toolchain_manifest_root=roots["runtime-manifest.json"],
        root_image_id=selected.root_image_id,
    )
    words = [int.from_bytes(bytes.fromhex(image[2:])[i : i + 4], "little") for i in range(0, 32, 4)]
    return {
        "DirectEpoch": {
            "certificate_journal_bytes": list(abi.canonical_global_bytes_v1(statement)),
            "route_receipts": [{"image_id": words, "journal_bytes": list(raw)}],
        }
    }

"""Mutation-killing ownership tests for the V2 asset-origin packet."""

from __future__ import annotations

from dataclasses import replace

from src.core.asset_origin_registry_types_v2 import (
    ASSET_ORIGIN_REGISTRATION_COMMAND_V2,
    AssetOriginKindV2,
    AssetOriginRegistrationAcceptedV2,
    AssetOriginRegistrationCommandV2,
    AssetOriginRegistrationContextV2,
    AssetOriginRegistrationPolicyV2,
    AssetOriginRegistrationRejectCodeV2,
    AssetOriginRegistrationRejectedV2,
    AssetOriginRegistryStateV2,
)
from src.core.asset_origin_registry_v2 import transition_asset_origin_registration_v2
from src.core.asset_transfer_types_v2 import ASSET_ATOM_DECIMALS_V2, AssetClassV2
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    GlobalEconomicEffectPlanV2,
    hash_global_v2,
)


def _root(label: str) -> str:
    return hash_global_v2("asset-origin-ownership-test-v2", {"label": label})


def _command() -> AssetOriginRegistrationCommandV2:
    return AssetOriginRegistrationCommandV2(
        command_kind=ASSET_ORIGIN_REGISTRATION_COMMAND_V2,
        asset="USD",
        origin_kind=AssetOriginKindV2.TAU_ORIGINATED,
        origin_root=_root("origin"),
        transfer_policy_root=_root("transfer-policy"),
        issue_policy_root=ZERO_ROOT_V2,
        decimals=ASSET_ATOM_DECIMALS_V2,
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
    )


def _state() -> AssetOriginRegistryStateV2:
    return AssetOriginRegistryStateV2(
        module_release_id=_root("module-release"),
        policy=AssetOriginRegistrationPolicyV2(
            authority_subject="governance",
            authority_grant_root=_root("grant"),
            allow_native=True,
            allow_tau_originated=True,
        ),
        assets=(),
    )


def _context(
    state: AssetOriginRegistryStateV2,
    command: AssetOriginRegistrationCommandV2,
) -> AssetOriginRegistrationContextV2:
    global_pre_state_root = _root("global-pre")
    return AssetOriginRegistrationContextV2(
        writer_epoch=3,
        module_release_id=state.module_release_id,
        global_pre_state_root=global_pre_state_root,
        occurrence=EconomicCommandOccurrenceV2(
            chain_id="asset-origin-ownership-test",
            deployment_root=_root("deployment"),
            height=8,
            tx_index=0,
            op_index=0,
            command_kind=command.command_kind,
            command_body_hash=command.command_body_hash,
            route_release_id=_root("route-release"),
            subject_id="governance",
            grant_root=_root("grant"),
            nonce=1,
            profile_root=_root("profile"),
            pre_state_root=global_pre_state_root,
            consumed_object_ids=(),
        ),
    )


def _accepted() -> AssetOriginRegistrationAcceptedV2:
    state = _state()
    command = _command()
    result = transition_asset_origin_registration_v2(
        _context(state, command),
        state,
        command,
    )
    assert isinstance(result, AssetOriginRegistrationAcceptedV2)
    return result


def test_state_getters_do_not_expose_policy_or_record_backing() -> None:
    accepted = _accepted()
    state = accepted.post_state
    root = state.state_root
    borrowed_policy = state.policy
    borrowed_record = state.assets[0]

    object.__setattr__(borrowed_policy, "allow_tau_originated", False)
    object.__setattr__(borrowed_record, "origin_root", _root("mutated-origin"))

    assert state.state_root == root
    assert state.policy.allow_tau_originated is True
    assert state.assets[0].origin_root == _root("origin")


def test_context_getter_does_not_expose_occurrence_backing() -> None:
    state = _state()
    command = _command()
    context = _context(state, command)
    borrowed_occurrence = context.occurrence
    assert borrowed_occurrence is not None

    object.__setattr__(borrowed_occurrence, "subject_id", "mallory")

    assert context.occurrence is not None
    assert context.occurrence.subject_id == "governance"
    result = transition_asset_origin_registration_v2(context, state, command)
    assert isinstance(result, AssetOriginRegistrationAcceptedV2)


def test_accepted_getters_do_not_expose_owned_graphs() -> None:
    accepted = _accepted()
    post_root = accepted.post_state.state_root
    effect_root = accepted.effects.effect_plan_root
    receipt_root = accepted.module_journal.receipt_root
    borrowed_state = accepted.post_state
    borrowed_effects = accepted.effects
    borrowed_journal = accepted.module_journal

    object.__setattr__(borrowed_state, "module_release_id", _root("mutated-release"))
    object.__setattr__(borrowed_effects, "_occurrence_consumptions", ())
    object.__setattr__(borrowed_journal, "receipt_root", _root("mutated-receipt"))

    assert accepted.post_state.state_root == post_root
    assert accepted.effects.effect_plan_root == effect_root
    assert accepted.module_journal.receipt_root == receipt_root


def test_rejected_effect_getter_does_not_expose_backing() -> None:
    state = _state()
    rejected = AssetOriginRegistrationRejectedV2(
        code=AssetOriginRegistrationRejectCodeV2.MISSING_OCCURRENCE,
        pre_state_root=state.state_root,
        post_state_root=state.state_root,
        effects=GlobalEconomicEffectPlanV2.empty(),
    )
    borrowed_effects = rejected.effects

    object.__setattr__(borrowed_effects, "_occurrence_consumptions", (_root("event"),))

    assert rejected.effects.is_empty


def test_dataclass_replace_preserves_public_graph_fields_and_canonical_values() -> None:
    accepted = _accepted()
    state = accepted.post_state
    context = _context(_state(), _command())
    rejected = AssetOriginRegistrationRejectedV2(
        code=AssetOriginRegistrationRejectCodeV2.MISSING_OCCURRENCE,
        pre_state_root=_state().state_root,
        post_state_root=_state().state_root,
        effects=GlobalEconomicEffectPlanV2.empty(),
    )

    replaced_state = replace(state)
    replaced_context = replace(context)
    replaced_accepted = replace(accepted)
    replaced_rejected = replace(rejected)

    assert replaced_state.to_canonical() == state.to_canonical()
    assert replaced_context.to_canonical() == context.to_canonical()
    assert replaced_accepted.post_state.to_canonical() == accepted.post_state.to_canonical()
    assert replaced_accepted.effects.effect_plan_root == accepted.effects.effect_plan_root
    assert replaced_accepted.module_journal == accepted.module_journal
    assert replaced_rejected.effects.is_empty
    assert state.state_root == (
        "0x462784891b954c481dc520783e866d0145399fe26d04a30b6e6ae13e6c9d880a"
    )

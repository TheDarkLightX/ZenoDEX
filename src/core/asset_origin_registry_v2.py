"""Deterministic SHADOW transition and policy binding for asset origins."""

from __future__ import annotations

from dataclasses import replace

from .asset_origin_registry_types_v2 import (
    ASSET_ORIGIN_REGISTRATION_COMMAND_V2,
    AssetOriginKindV2,
    AssetOriginRecordV2,
    AssetOriginRegistrationAcceptedV2,
    AssetOriginRegistrationCommandV2,
    AssetOriginRegistrationContextV2,
    AssetOriginRegistrationRejectCodeV2,
    AssetOriginRegistrationRejectedV2,
    AssetOriginRegistrationResultV2,
    AssetOriginRegistryStateV2,
    _snapshot_registration_command_v2,
    _snapshot_registration_context_v2,
    _snapshot_registry_state_v2,
)
from .asset_transfer_types_v2 import (
    ASSET_ATOM_DECIMALS_V2,
    AssetTransferPolicyV2,
)
from .global_economic_proof_v2 import LaneModuleTransitionJournalV2
from .global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    GlobalEconomicEffectPlanV2,
    LaneIdV2,
    LaneWriteV2,
    hash_global_v2,
)
from .managed_asset_lifecycle_types_v2 import ManagedAssetLifecyclePolicyV2


def _reject(
    code: AssetOriginRegistrationRejectCodeV2,
    state: AssetOriginRegistryStateV2,
) -> AssetOriginRegistrationRejectedV2:
    return AssetOriginRegistrationRejectedV2(
        code=code,
        pre_state_root=state.state_root,
        post_state_root=state.state_root,
        effects=GlobalEconomicEffectPlanV2.empty(),
    )


def asset_transfer_policy_root_v2(policy: AssetTransferPolicyV2) -> str:
    """Commit one exact V2 transfer policy for origin-registry membership."""

    if type(policy) is not AssetTransferPolicyV2:
        raise TypeError("asset transfer policy must have the exact V2 type")
    return hash_global_v2("asset-transfer-policy-v2", replace(policy))


def validate_asset_transfer_policy_origin_v2(
    registry: AssetOriginRegistryStateV2,
    policy: AssetTransferPolicyV2,
) -> AssetOriginRecordV2:
    """Return the owned record proving structural policy-origin membership.

    Authentication of ``registry.state_root`` against an active profile remains
    a separate verifier premise.  This function closes the deterministic
    relation between that registry snapshot and a transfer-policy snapshot.
    """

    owned_registry = _snapshot_registry_state_v2(registry)
    if type(policy) is not AssetTransferPolicyV2:
        raise TypeError("asset transfer policy must have the exact V2 type")
    owned_policy = replace(policy)
    record = owned_registry.record_for(owned_policy.asset)
    if record is None:
        raise ValueError("asset transfer policy has no registered origin")
    if owned_policy.asset_origin_root is None:
        raise ValueError("asset transfer policy origin is absent")
    if (
        record.asset_class is not owned_policy.asset_class
        or record.origin_root != owned_policy.asset_origin_root
        or record.decimals != owned_policy.atom_decimals
    ):
        raise ValueError("asset transfer policy identity does not match its origin")
    if record.transfer_policy_root != asset_transfer_policy_root_v2(owned_policy):
        raise ValueError("asset transfer policy root does not match its origin")
    return record


def managed_asset_policy_root_v2(policy: ManagedAssetLifecyclePolicyV2) -> str:
    """Commit one exact V2 managed issue/burn policy."""

    if type(policy) is not ManagedAssetLifecyclePolicyV2:
        raise TypeError("managed asset policy must have the exact V2 type")
    return hash_global_v2("managed-asset-lifecycle-policy-v2", replace(policy))


def validate_managed_asset_policy_origin_v2(
    registry: AssetOriginRegistryStateV2,
    policy: ManagedAssetLifecyclePolicyV2,
) -> AssetOriginRecordV2:
    """Bind a generic managed-asset policy to one governed origin row."""

    owned_registry = _snapshot_registry_state_v2(registry)
    if type(policy) is not ManagedAssetLifecyclePolicyV2:
        raise TypeError("managed asset policy must have the exact V2 type")
    owned_policy = replace(policy)
    record = owned_registry.record_for(owned_policy.asset)
    if record is None:
        raise ValueError("managed asset policy has no registered origin")
    if owned_policy.asset_origin_root is None:
        raise ValueError("managed asset policy origin is absent")
    if (
        record.asset_class is not owned_policy.asset_class
        or record.origin_root != owned_policy.asset_origin_root
        or record.decimals != owned_policy.atom_decimals
    ):
        raise ValueError("managed asset policy identity does not match its origin")
    if record.issue_policy_root == ZERO_ROOT_V2:
        raise ValueError("managed asset issue policy is disabled at its origin")
    if record.issue_policy_root != managed_asset_policy_root_v2(owned_policy):
        raise ValueError("managed asset issue policy root does not match its origin")
    return record


def transition_asset_origin_registration_v2(
    context: AssetOriginRegistrationContextV2,
    pre_state: AssetOriginRegistryStateV2,
    command: AssetOriginRegistrationCommandV2,
) -> AssetOriginRegistrationResultV2:
    """Register provenance without issuing value or granting authority."""

    if type(context) is not AssetOriginRegistrationContextV2:
        raise TypeError("asset origin context must be an exact typed value")
    if type(pre_state) is not AssetOriginRegistryStateV2:
        raise TypeError("asset origin pre-state must be an exact typed value")
    if type(command) is not AssetOriginRegistrationCommandV2:
        raise TypeError("asset origin command must be an exact typed value")
    owned_context = _snapshot_registration_context_v2(context)
    owned_state = _snapshot_registry_state_v2(pre_state)
    owned_command = _snapshot_registration_command_v2(command)
    occurrence = owned_context.occurrence
    if occurrence is None:
        return _reject(AssetOriginRegistrationRejectCodeV2.MISSING_OCCURRENCE, owned_state)
    if (
        occurrence.pre_state_root != owned_context.global_pre_state_root
        or occurrence.consumed_object_ids != ()
    ):
        return _reject(
            AssetOriginRegistrationRejectCodeV2.OCCURRENCE_BINDING_MISMATCH,
            owned_state,
        )
    if owned_context.module_release_id != owned_state.module_release_id:
        return _reject(AssetOriginRegistrationRejectCodeV2.RELEASE_MISMATCH, owned_state)
    if owned_command.command_kind != ASSET_ORIGIN_REGISTRATION_COMMAND_V2:
        return _reject(AssetOriginRegistrationRejectCodeV2.UNKNOWN_COMMAND, owned_state)
    if (
        occurrence.command_kind != owned_command.command_kind
        or occurrence.command_body_hash != owned_command.command_body_hash
    ):
        return _reject(
            AssetOriginRegistrationRejectCodeV2.OCCURRENCE_COMMAND_MISMATCH,
            owned_state,
        )
    if occurrence.subject_id != owned_state.policy.authority_subject:
        return _reject(
            AssetOriginRegistrationRejectCodeV2.UNAUTHORIZED_SUBJECT,
            owned_state,
        )
    if occurrence.grant_root != owned_state.policy.authority_grant_root:
        return _reject(AssetOriginRegistrationRejectCodeV2.GRANT_MISMATCH, owned_state)
    if owned_command.decimals != ASSET_ATOM_DECIMALS_V2:
        return _reject(
            AssetOriginRegistrationRejectCodeV2.DECIMAL_SCALE_MISMATCH,
            owned_state,
        )
    enabled = {
        AssetOriginKindV2.NATIVE: owned_state.policy.allow_native,
        AssetOriginKindV2.TAU_ORIGINATED: owned_state.policy.allow_tau_originated,
    }[owned_command.origin_kind]
    if not enabled:
        return _reject(
            AssetOriginRegistrationRejectCodeV2.DISABLED_ORIGIN_KIND,
            owned_state,
        )
    if owned_command.origin_kind is AssetOriginKindV2.NATIVE:
        return _reject(
            AssetOriginRegistrationRejectCodeV2.NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED,
            owned_state,
        )
    if owned_state.record_for(owned_command.asset) is not None:
        return _reject(AssetOriginRegistrationRejectCodeV2.DUPLICATE_ASSET, owned_state)
    if any(row.origin_root == owned_command.origin_root for row in owned_state.assets):
        return _reject(AssetOriginRegistrationRejectCodeV2.DUPLICATE_ORIGIN, owned_state)

    record = AssetOriginRecordV2(
        asset=owned_command.asset,
        origin_kind=owned_command.origin_kind,
        origin_root=owned_command.origin_root,
        transfer_policy_root=owned_command.transfer_policy_root,
        issue_policy_root=owned_command.issue_policy_root,
        decimals=owned_command.decimals,
        asset_class=owned_command.asset_class,
    )
    post_state = AssetOriginRegistryStateV2(
        module_release_id=owned_state.module_release_id,
        policy=owned_state.policy,
        assets=tuple(sorted((*owned_state.assets, record), key=lambda row: row.asset)),
    )
    effects = GlobalEconomicEffectPlanV2(
        rows=(),
        asset_conservation=(),
        fee_conservation=(),
        lane_writes=(
            LaneWriteV2(
                LaneIdV2.ASSET_TRANSFER,
                owned_state.state_root,
                post_state.state_root,
            ),
        ),
        occurrence_consumptions=(occurrence.occurrence_id,),
        external_outbox_enqueue=(),
    )
    receipt_root = hash_global_v2(
        "asset-origin-registration-receipt-v2",
        {
            "occurrence_id": occurrence.occurrence_id,
            "command_body_hash": owned_command.command_body_hash,
            "pre_state_root": owned_state.state_root,
            "post_state_root": post_state.state_root,
            "effect_plan_root": effects.effect_plan_root,
            "private_port_root": ZERO_ROOT_V2,
            "terminal_obligations_root": ZERO_ROOT_V2,
            "oracle_occurrence_plan_root": ZERO_ROOT_V2,
        },
    )
    journal = LaneModuleTransitionJournalV2(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=owned_context.writer_epoch,
        lane_id=LaneIdV2.ASSET_TRANSFER,
        module_release_id=owned_context.module_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        pre_lane_root=owned_state.state_root,
        post_lane_root=post_state.state_root,
        effect_plan_root=effects.effect_plan_root,
        private_port_root=ZERO_ROOT_V2,
        receipt_root=receipt_root,
        terminal_obligations_root=ZERO_ROOT_V2,
        oracle_occurrence_plan_root=ZERO_ROOT_V2,
    )
    return AssetOriginRegistrationAcceptedV2(post_state, effects, journal)


__all__ = [
    "asset_transfer_policy_root_v2",
    "validate_asset_transfer_policy_origin_v2",
    "managed_asset_policy_root_v2",
    "validate_managed_asset_policy_origin_v2",
    "transition_asset_origin_registration_v2",
]

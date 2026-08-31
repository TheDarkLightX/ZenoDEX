"""Pure V2 managed-asset issue/burn transition.

This SHADOW leaf derives a candidate only.  Profile admission, replay
publication, registry authentication, external custody, and settlement remain
outside its authority boundary.
"""

from __future__ import annotations

from dataclasses import dataclass

from .asset_transfer_types_v2 import AssetClassV2
from .global_economic_proof_v2 import LaneModuleTransitionJournalV2
from .global_settlement_types_v2 import (
    MAX_ATOMS_V2,
    MAX_DELTA_ATOMS_V2,
    MIN_DELTA_ATOMS_V2,
    ZERO_ROOT_V2,
    AssetConservationRowV2,
    AssetSupplyV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    GlobalEconomicEffectPlanV2,
    LaneIdV2,
    LaneWriteV2,
    hash_global_v2,
)
from .managed_asset_lifecycle_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    MANAGED_ASSET_BURN_COMMAND_KIND_V2,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleContextV2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleRejectCodeV2,
    ManagedAssetLifecycleRejectedV2,
    ManagedAssetLifecycleResultV2,
    ManagedAssetLifecycleStateV2,
    _snapshot_command_v2,
    _snapshot_context_v2,
    _snapshot_state_v2,
)


def _reject(
    code: ManagedAssetLifecycleRejectCodeV2,
    pre_state: ManagedAssetLifecycleStateV2,
) -> ManagedAssetLifecycleRejectedV2:
    return ManagedAssetLifecycleRejectedV2(
        code=code,
        pre_state_root=pre_state.state_root,
        post_state_root=pre_state.state_root,
        effects=GlobalEconomicEffectPlanV2.empty(),
    )


def _policy_for(
    state: ManagedAssetLifecycleStateV2,
    asset: str,
) -> ManagedAssetLifecyclePolicyV2 | None:
    return next((policy for policy in state.policies if policy.asset == asset), None)


@dataclass(frozen=True, slots=True)
class _PreparedLifecycleV2:
    context: ManagedAssetLifecycleContextV2
    pre_state: ManagedAssetLifecycleStateV2
    command: ManagedAssetLifecycleCommandV2
    policy: ManagedAssetLifecyclePolicyV2
    is_issue: bool
    signed_amount: int


def _authorize(
    context: ManagedAssetLifecycleContextV2,
    pre_state: ManagedAssetLifecycleStateV2,
    command: ManagedAssetLifecycleCommandV2,
) -> _PreparedLifecycleV2 | ManagedAssetLifecycleRejectCodeV2:
    occurrence = context.occurrence
    if occurrence is None:
        return ManagedAssetLifecycleRejectCodeV2.MISSING_OCCURRENCE
    if (
        occurrence.pre_state_root != context.global_pre_state_root
        or occurrence.consumed_object_ids != ()
    ):
        return ManagedAssetLifecycleRejectCodeV2.OCCURRENCE_BINDING_MISMATCH
    if context.module_release_id != pre_state.module_release_id:
        return ManagedAssetLifecycleRejectCodeV2.RELEASE_MISMATCH
    if command.command_kind not in {
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
        MANAGED_ASSET_BURN_COMMAND_KIND_V2,
    }:
        return ManagedAssetLifecycleRejectCodeV2.UNKNOWN_COMMAND
    if (
        occurrence.command_kind != command.command_kind
        or occurrence.command_body_hash != command.command_body_hash
    ):
        return ManagedAssetLifecycleRejectCodeV2.OCCURRENCE_COMMAND_MISMATCH
    policy = _policy_for(pre_state, command.asset)
    if policy is None:
        return ManagedAssetLifecycleRejectCodeV2.UNKNOWN_ASSET
    if not policy.enabled:
        return ManagedAssetLifecycleRejectCodeV2.DISABLED_ASSET
    if command.asset_class is not policy.asset_class:
        return ManagedAssetLifecycleRejectCodeV2.ASSET_CLASS_MISMATCH
    if command.atom_decimals != policy.atom_decimals:
        return ManagedAssetLifecycleRejectCodeV2.ASSET_DECIMALS_MISMATCH
    if policy.asset_origin_root is None or command.asset_origin_root is None:
        return ManagedAssetLifecycleRejectCodeV2.UNREGISTERED_ASSET
    if command.asset_origin_root != policy.asset_origin_root:
        return ManagedAssetLifecycleRejectCodeV2.ASSET_ORIGIN_MISMATCH
    if policy.asset_class is not AssetClassV2.REGISTERED_ORDINARY_TOKEN:
        return ManagedAssetLifecycleRejectCodeV2.GENERIC_AUTHORITY_FORBIDDEN

    is_issue = command.command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V2
    expected_authorization_root: str | None
    if is_issue:
        if policy.issue_authorization_root is None:
            return ManagedAssetLifecycleRejectCodeV2.ISSUE_DISABLED
        if occurrence.subject_id != policy.issue_authority_subject:
            return ManagedAssetLifecycleRejectCodeV2.UNAUTHORIZED_SUBJECT
        expected_authorization_root = policy.issue_authorization_root
    else:
        if policy.burn_authorization_root is None:
            return ManagedAssetLifecycleRejectCodeV2.BURN_DISABLED
        if occurrence.subject_id != command.account_owner:
            return ManagedAssetLifecycleRejectCodeV2.UNAUTHORIZED_SUBJECT
        expected_authorization_root = policy.burn_authorization_root
    if (
        occurrence.grant_root != expected_authorization_root
        or command.authorization_root != expected_authorization_root
    ):
        return ManagedAssetLifecycleRejectCodeV2.AUTHORIZATION_ROOT_MISMATCH
    if command.amount_atoms == 0:
        return ManagedAssetLifecycleRejectCodeV2.ZERO_AMOUNT
    max_signed_magnitude = MAX_DELTA_ATOMS_V2 if is_issue else -MIN_DELTA_ATOMS_V2
    if command.amount_atoms > max_signed_magnitude:
        return ManagedAssetLifecycleRejectCodeV2.EFFECT_DELTA_OVERFLOW
    return _PreparedLifecycleV2(
        context,
        pre_state,
        command,
        policy,
        is_issue,
        command.amount_atoms if is_issue else -command.amount_atoms,
    )


def _post_supply(
    prepared: _PreparedLifecycleV2,
) -> tuple[AssetSupplyV2, ...] | ManagedAssetLifecycleRejectCodeV2:
    command = prepared.command
    current = prepared.pre_state.supply_atoms(command.asset)
    if prepared.is_issue:
        if current > MAX_ATOMS_V2 - command.amount_atoms:
            return ManagedAssetLifecycleRejectCodeV2.SUPPLY_OVERFLOW
        post = current + command.amount_atoms
    else:
        if current < command.amount_atoms:
            return ManagedAssetLifecycleRejectCodeV2.INSUFFICIENT_BALANCE
        post = current - command.amount_atoms
    return tuple(
        AssetSupplyV2(row.asset, post if row.asset == command.asset else row.amount_atoms)
        for row in prepared.pre_state.supplies
    )


def _post_balances(
    prepared: _PreparedLifecycleV2,
) -> tuple[EconomicAmountV2, ...] | ManagedAssetLifecycleRejectCodeV2:
    command = prepared.command
    values = {(row.asset, row.owner): row.amount_atoms for row in prepared.pre_state.balances}
    key = (command.asset, command.account_owner)
    current = values.get(key, 0)
    if prepared.signed_amount < 0 and current < command.amount_atoms:
        return ManagedAssetLifecycleRejectCodeV2.INSUFFICIENT_BALANCE
    if prepared.signed_amount > 0 and current > MAX_ATOMS_V2 - command.amount_atoms:
        return ManagedAssetLifecycleRejectCodeV2.BALANCE_OVERFLOW
    post = current + prepared.signed_amount
    if post == 0:
        values.pop(key, None)
    else:
        values[key] = post
    return tuple(
        EconomicAmountV2(owner, asset, ACCOUNT_CUSTODY_DOMAIN_V2, amount)
        for (asset, owner), amount in sorted(values.items())
    )


def _account_total(state: ManagedAssetLifecycleStateV2, asset: str) -> int:
    return sum(row.amount_atoms for row in state.balances if row.asset == asset)


def _effect_plan(
    prepared: _PreparedLifecycleV2,
    post_state: ManagedAssetLifecycleStateV2,
) -> GlobalEconomicEffectPlanV2:
    occurrence = prepared.context.occurrence
    if occurrence is None:
        raise RuntimeError("prepared managed asset transition lost occurrence")
    command = prepared.command
    supply_kind = EconomicEffectKindV2.ISSUE if prepared.is_issue else EconomicEffectKindV2.BURN
    issue_atoms = command.amount_atoms if prepared.is_issue else 0
    burn_atoms = 0 if prepared.is_issue else command.amount_atoms
    return GlobalEconomicEffectPlanV2(
        rows=tuple(
            sorted(
                (
                    EconomicEffectRowV2(
                        EconomicEffectKindV2.ACCOUNT_MOVEMENT,
                        command.account_owner,
                        command.asset,
                        ACCOUNT_CUSTODY_DOMAIN_V2,
                        prepared.signed_amount,
                    ),
                    EconomicEffectRowV2(
                        supply_kind,
                        command.account_owner,
                        command.asset,
                        ACCOUNT_CUSTODY_DOMAIN_V2,
                        prepared.signed_amount,
                    ),
                ),
                key=lambda row: row.key,
            )
        ),
        asset_conservation=(
            AssetConservationRowV2(
                asset=command.asset,
                owned_and_custodied_pre_atoms=_account_total(
                    prepared.pre_state,
                    command.asset,
                ),
                owned_and_custodied_post_atoms=_account_total(post_state, command.asset),
                supply_pre_atoms=prepared.pre_state.supply_atoms(command.asset),
                supply_post_atoms=post_state.supply_atoms(command.asset),
                authorized_issue_atoms=issue_atoms,
                authorized_burn_atoms=burn_atoms,
            ),
        ),
        fee_conservation=(),
        lane_writes=(
            LaneWriteV2(
                LaneIdV2.ASSET_TRANSFER,
                prepared.pre_state.state_root,
                post_state.state_root,
            ),
        ),
        occurrence_consumptions=(occurrence.occurrence_id,),
        external_outbox_enqueue=(),
    )


def _accept(
    prepared: _PreparedLifecycleV2,
    balances: tuple[EconomicAmountV2, ...],
    supplies: tuple[AssetSupplyV2, ...],
) -> ManagedAssetLifecycleAcceptedV2:
    occurrence = prepared.context.occurrence
    if occurrence is None:
        raise RuntimeError("prepared managed asset transition lost occurrence")
    pre_state = prepared.pre_state
    command = prepared.command
    post_state = ManagedAssetLifecycleStateV2(
        pre_state.module_release_id,
        pre_state.policies,
        balances,
        supplies,
    )
    effects = _effect_plan(prepared, post_state)
    receipt_root = hash_global_v2(
        "managed-asset-lifecycle-receipt-v2",
        {
            "context": prepared.context,
            "command": command,
            "pre_state_root": pre_state.state_root,
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
        writer_epoch=prepared.context.writer_epoch,
        lane_id=LaneIdV2.ASSET_TRANSFER,
        module_release_id=prepared.context.module_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        pre_lane_root=pre_state.state_root,
        post_lane_root=post_state.state_root,
        effect_plan_root=effects.effect_plan_root,
        private_port_root=ZERO_ROOT_V2,
        receipt_root=receipt_root,
        terminal_obligations_root=ZERO_ROOT_V2,
        oracle_occurrence_plan_root=ZERO_ROOT_V2,
    )
    return ManagedAssetLifecycleAcceptedV2(post_state, effects, journal)


def transition_managed_asset_lifecycle_v2(
    context: ManagedAssetLifecycleContextV2,
    pre_state: ManagedAssetLifecycleStateV2,
    command: ManagedAssetLifecycleCommandV2,
) -> ManagedAssetLifecycleResultV2:
    """Return one exact V2 issue/burn candidate or an untouched rejection."""

    if type(context) is not ManagedAssetLifecycleContextV2:
        raise TypeError("managed asset context must be an exact typed value")
    if type(pre_state) is not ManagedAssetLifecycleStateV2:
        raise TypeError("managed asset pre-state must be an exact typed value")
    if type(command) is not ManagedAssetLifecycleCommandV2:
        raise TypeError("managed asset command must be an exact typed value")
    owned_context = _snapshot_context_v2(context)
    owned_state = _snapshot_state_v2(pre_state)
    owned_command = _snapshot_command_v2(command)
    prepared = _authorize(owned_context, owned_state, owned_command)
    if isinstance(prepared, ManagedAssetLifecycleRejectCodeV2):
        return _reject(prepared, owned_state)
    supplies = _post_supply(prepared)
    if isinstance(supplies, ManagedAssetLifecycleRejectCodeV2):
        return _reject(supplies, owned_state)
    balances = _post_balances(prepared)
    if isinstance(balances, ManagedAssetLifecycleRejectCodeV2):
        return _reject(balances, owned_state)
    return _accept(prepared, balances, supplies)


__all__ = ["transition_managed_asset_lifecycle_v2"]

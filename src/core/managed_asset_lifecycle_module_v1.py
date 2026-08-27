"""Deterministic generic issue/burn core for registered ordinary assets.

The module is research-only and owns no publication capability. Protocol-
managed assets reject this generic authority because their supply changes must
arrive through their named economic transition.
"""

from __future__ import annotations

from dataclasses import dataclass

from .global_economic_proof_v1 import LaneModuleTransitionJournalV1
from .global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    ZERO_ROOT_V1,
    AssetConservationRowV1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
    hash_global_v1,
)
from .managed_asset_lifecycle_types_v1 import (
    ACCOUNT_CUSTODY_DOMAIN_V1,
    MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    ManagedAssetClassV1,
    ManagedAssetLifecycleAcceptedV1,
    ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleRejectCodeV1,
    ManagedAssetLifecycleRejectedV1,
    ManagedAssetLifecycleResultV1,
    ManagedAssetLifecycleStateV1,
)


def _reject(
    code: ManagedAssetLifecycleRejectCodeV1,
    pre_state: ManagedAssetLifecycleStateV1,
) -> ManagedAssetLifecycleRejectedV1:
    return ManagedAssetLifecycleRejectedV1(
        code=code,
        pre_state_root=pre_state.state_root,
        post_state_root=pre_state.state_root,
        effects=GlobalEconomicEffectPlanV1.empty(),
    )


def _policy_for(
    state: ManagedAssetLifecycleStateV1,
    asset: str,
) -> ManagedAssetLifecyclePolicyV1 | None:
    return next((policy for policy in state.policies if policy.asset == asset), None)


@dataclass(frozen=True, slots=True)
class _PreparedLifecycleV1:
    context: ManagedAssetLifecycleContextV1
    pre_state: ManagedAssetLifecycleStateV1
    command: ManagedAssetLifecycleCommandV1
    policy: ManagedAssetLifecyclePolicyV1
    is_issue: bool
    signed_amount: int


def _authorize(
    context: ManagedAssetLifecycleContextV1,
    pre_state: ManagedAssetLifecycleStateV1,
    command: ManagedAssetLifecycleCommandV1,
) -> _PreparedLifecycleV1 | ManagedAssetLifecycleRejectCodeV1:
    if context.module_release_id != pre_state.module_release_id:
        return ManagedAssetLifecycleRejectCodeV1.RELEASE_MISMATCH
    if command.command_kind not in {
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    }:
        return ManagedAssetLifecycleRejectCodeV1.UNKNOWN_COMMAND
    policy = _policy_for(pre_state, command.asset)
    if policy is None:
        return ManagedAssetLifecycleRejectCodeV1.UNKNOWN_ASSET
    if not policy.enabled:
        return ManagedAssetLifecycleRejectCodeV1.DISABLED_ASSET
    if policy.asset_class is not ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN:
        return ManagedAssetLifecycleRejectCodeV1.GENERIC_AUTHORITY_FORBIDDEN

    is_issue = command.command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V1
    if is_issue:
        if policy.issue_policy_root is None:
            return ManagedAssetLifecycleRejectCodeV1.ISSUE_DISABLED
        if context.subject_id != policy.issue_authority_subject:
            return ManagedAssetLifecycleRejectCodeV1.UNAUTHORIZED_SUBJECT
        expected_grant = policy.issue_policy_root
    else:
        if policy.burn_policy_root is None:
            return ManagedAssetLifecycleRejectCodeV1.BURN_DISABLED
        if context.subject_id != command.account_owner:
            return ManagedAssetLifecycleRejectCodeV1.UNAUTHORIZED_SUBJECT
        expected_grant = policy.burn_policy_root
    if context.grant_root != expected_grant:
        return ManagedAssetLifecycleRejectCodeV1.AUTHORITY_PROFILE_MISMATCH
    if command.amount_atoms == 0:
        return ManagedAssetLifecycleRejectCodeV1.ZERO_AMOUNT
    max_signed_magnitude = (
        MAX_DELTA_ATOMS_V1 if is_issue else -MIN_DELTA_ATOMS_V1
    )
    if command.amount_atoms > max_signed_magnitude:
        return ManagedAssetLifecycleRejectCodeV1.EFFECT_DELTA_OVERFLOW
    signed_amount = command.amount_atoms if is_issue else -command.amount_atoms
    return _PreparedLifecycleV1(
        context,
        pre_state,
        command,
        policy,
        is_issue,
        signed_amount,
    )


def _post_supply(
    prepared: _PreparedLifecycleV1,
) -> tuple[AssetSupplyV1, ...] | ManagedAssetLifecycleRejectCodeV1:
    command = prepared.command
    pre_supply = prepared.pre_state.supply_atoms(command.asset)
    if prepared.is_issue:
        if pre_supply > MAX_ATOMS_V1 - command.amount_atoms:
            return ManagedAssetLifecycleRejectCodeV1.SUPPLY_OVERFLOW
        post_supply = pre_supply + command.amount_atoms
    else:
        if pre_supply < command.amount_atoms:
            return ManagedAssetLifecycleRejectCodeV1.INSUFFICIENT_BALANCE
        post_supply = pre_supply - command.amount_atoms
    return tuple(
        AssetSupplyV1(row.asset, post_supply if row.asset == command.asset else row.amount_atoms)
        for row in prepared.pre_state.supplies
    )


def _post_balances(
    prepared: _PreparedLifecycleV1,
) -> tuple[EconomicAmountV1, ...] | ManagedAssetLifecycleRejectCodeV1:
    command = prepared.command
    values = {
        (row.asset, row.owner): row.amount_atoms for row in prepared.pre_state.balances
    }
    key = (command.asset, command.account_owner)
    current_atoms = values.get(key, 0)
    if prepared.signed_amount < 0 and current_atoms < command.amount_atoms:
        return ManagedAssetLifecycleRejectCodeV1.INSUFFICIENT_BALANCE
    if prepared.signed_amount > 0 and current_atoms > MAX_ATOMS_V1 - command.amount_atoms:
        return ManagedAssetLifecycleRejectCodeV1.BALANCE_OVERFLOW
    post_atoms = current_atoms + prepared.signed_amount
    if post_atoms == 0:
        values.pop(key, None)
    else:
        values[key] = post_atoms
    return tuple(
        EconomicAmountV1(owner, asset, ACCOUNT_CUSTODY_DOMAIN_V1, amount_atoms)
        for (asset, owner), amount_atoms in sorted(values.items())
    )


def _account_total(state: ManagedAssetLifecycleStateV1, asset: str) -> int:
    return sum(row.amount_atoms for row in state.balances if row.asset == asset)


def _effect_plan(
    prepared: _PreparedLifecycleV1,
    post_state: ManagedAssetLifecycleStateV1,
) -> GlobalEconomicEffectPlanV1:
    context = prepared.context
    pre_state = prepared.pre_state
    command = prepared.command
    supply_kind = (
        EconomicEffectKindV1.ISSUE if prepared.is_issue else EconomicEffectKindV1.BURN
    )
    issue_atoms = command.amount_atoms if prepared.is_issue else 0
    burn_atoms = 0 if prepared.is_issue else command.amount_atoms
    rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                    command.account_owner,
                    command.asset,
                    ACCOUNT_CUSTODY_DOMAIN_V1,
                    prepared.signed_amount,
                ),
                EconomicEffectRowV1(
                    supply_kind,
                    command.account_owner,
                    command.asset,
                    ACCOUNT_CUSTODY_DOMAIN_V1,
                    prepared.signed_amount,
                ),
            ),
            key=lambda row: row.key,
        )
    )
    return GlobalEconomicEffectPlanV1(
        rows=rows,
        asset_conservation=(
            AssetConservationRowV1(
                asset=command.asset,
                owned_and_custodied_pre_atoms=_account_total(pre_state, command.asset),
                owned_and_custodied_post_atoms=_account_total(post_state, command.asset),
                supply_pre_atoms=pre_state.supply_atoms(command.asset),
                supply_post_atoms=post_state.supply_atoms(command.asset),
                authorized_issue_atoms=issue_atoms,
                authorized_burn_atoms=burn_atoms,
            ),
        ),
        fee_conservation=(),
        lane_writes=(
            LaneWriteV1(LaneIdV1.ASSET_TRANSFER, pre_state.state_root, post_state.state_root),
        ),
        occurrence_consumptions=(context.command_occurrence_id,),
        external_outbox_enqueue=(),
    )


def _accept(
    prepared: _PreparedLifecycleV1,
    balances: tuple[EconomicAmountV1, ...],
    supplies: tuple[AssetSupplyV1, ...],
) -> ManagedAssetLifecycleAcceptedV1:
    context = prepared.context
    pre_state = prepared.pre_state
    command = prepared.command
    post_state = ManagedAssetLifecycleStateV1(
        module_release_id=pre_state.module_release_id,
        policies=pre_state.policies,
        balances=balances,
        supplies=supplies,
    )
    effects = _effect_plan(prepared, post_state)
    receipt_root = hash_global_v1(
        "managed-asset-lifecycle-receipt-v1",
        {
            "context": context,
            "command": command,
            "pre_state_root": pre_state.state_root,
            "post_state_root": post_state.state_root,
            "effect_plan_root": effects.effect_plan_root,
            "private_port_root": ZERO_ROOT_V1,
            "terminal_obligations_root": ZERO_ROOT_V1,
        },
    )
    module_journal = LaneModuleTransitionJournalV1(
        chain_id=context.chain_id,
        deployment_root=context.deployment_root,
        profile_root=context.profile_root,
        writer_epoch=context.writer_epoch,
        lane_id=LaneIdV1.ASSET_TRANSFER,
        module_release_id=context.module_release_id,
        command_occurrence_id=context.command_occurrence_id,
        pre_lane_root=pre_state.state_root,
        post_lane_root=post_state.state_root,
        effect_plan_root=effects.effect_plan_root,
        private_port_root=ZERO_ROOT_V1,
        receipt_root=receipt_root,
        terminal_obligations_root=ZERO_ROOT_V1,
    )
    return ManagedAssetLifecycleAcceptedV1(post_state, effects, module_journal)


def _snapshot_context(
    context: ManagedAssetLifecycleContextV1,
) -> ManagedAssetLifecycleContextV1:
    if type(context) is not ManagedAssetLifecycleContextV1:
        raise TypeError("managed asset lifecycle context must be the exact typed value")
    for field_name in (
        "chain_id",
        "deployment_root",
        "profile_root",
        "module_release_id",
        "command_occurrence_id",
        "subject_id",
        "grant_root",
    ):
        if type(getattr(context, field_name)) is not str:
            raise TypeError(f"managed asset context {field_name} must be an exact string")
    if type(context.writer_epoch) is not int:
        raise TypeError("managed asset context writer_epoch must be an exact integer")
    return ManagedAssetLifecycleContextV1(
        chain_id=context.chain_id,
        deployment_root=context.deployment_root,
        profile_root=context.profile_root,
        writer_epoch=context.writer_epoch,
        module_release_id=context.module_release_id,
        command_occurrence_id=context.command_occurrence_id,
        subject_id=context.subject_id,
        grant_root=context.grant_root,
    )


def _snapshot_policy(
    policy: ManagedAssetLifecyclePolicyV1,
) -> ManagedAssetLifecyclePolicyV1:
    if type(policy) is not ManagedAssetLifecyclePolicyV1:
        raise TypeError("managed asset lifecycle policies must contain exact typed values")
    if type(policy.asset) is not str:
        raise TypeError("managed asset policy asset must be an exact string")
    if type(policy.asset_class) is not ManagedAssetClassV1:
        raise TypeError("managed asset policy class must be an exact closed value")
    for field_name in (
        "issue_authority_subject",
        "issue_policy_root",
        "burn_policy_root",
    ):
        value = getattr(policy, field_name)
        if value is not None and type(value) is not str:
            raise TypeError(f"managed asset policy {field_name} must be exact text")
    if type(policy.enabled) is not bool:
        raise TypeError("managed asset policy enabled must be an exact bool")
    return ManagedAssetLifecyclePolicyV1(
        asset=policy.asset,
        asset_class=policy.asset_class,
        issue_authority_subject=policy.issue_authority_subject,
        issue_policy_root=policy.issue_policy_root,
        burn_policy_root=policy.burn_policy_root,
        enabled=policy.enabled,
    )


def _snapshot_balance(row: EconomicAmountV1) -> EconomicAmountV1:
    if type(row) is not EconomicAmountV1:
        raise TypeError("managed asset lifecycle balances must contain exact typed values")
    for field_name in ("owner", "asset", "custody_domain"):
        if type(getattr(row, field_name)) is not str:
            raise TypeError(f"managed asset balance {field_name} must be an exact string")
    if type(row.amount_atoms) is not int:
        raise TypeError("managed asset balance amount must be an exact integer")
    return EconomicAmountV1(
        owner=row.owner,
        asset=row.asset,
        custody_domain=row.custody_domain,
        amount_atoms=row.amount_atoms,
    )


def _snapshot_supply(row: AssetSupplyV1) -> AssetSupplyV1:
    if type(row) is not AssetSupplyV1:
        raise TypeError("managed asset lifecycle supplies must contain exact typed values")
    if type(row.asset) is not str:
        raise TypeError("managed asset supply asset must be an exact string")
    if type(row.amount_atoms) is not int:
        raise TypeError("managed asset supply amount must be an exact integer")
    return AssetSupplyV1(asset=row.asset, amount_atoms=row.amount_atoms)


def _snapshot_state(
    pre_state: ManagedAssetLifecycleStateV1,
) -> ManagedAssetLifecycleStateV1:
    if type(pre_state) is not ManagedAssetLifecycleStateV1:
        raise TypeError("managed asset lifecycle pre-state must be the exact typed value")
    if type(pre_state.policies) is not tuple:
        raise TypeError("managed asset lifecycle policies must be an exact tuple")
    if type(pre_state.balances) is not tuple:
        raise TypeError("managed asset lifecycle balances must be an exact tuple")
    if type(pre_state.supplies) is not tuple:
        raise TypeError("managed asset lifecycle supplies must be an exact tuple")
    if type(pre_state.module_release_id) is not str:
        raise TypeError("managed asset state release must be an exact string")
    return ManagedAssetLifecycleStateV1(
        module_release_id=pre_state.module_release_id,
        policies=tuple(_snapshot_policy(policy) for policy in pre_state.policies),
        balances=tuple(_snapshot_balance(row) for row in pre_state.balances),
        supplies=tuple(_snapshot_supply(row) for row in pre_state.supplies),
    )


def _snapshot_command(
    command: ManagedAssetLifecycleCommandV1,
) -> ManagedAssetLifecycleCommandV1:
    if type(command) is not ManagedAssetLifecycleCommandV1:
        raise TypeError("managed asset lifecycle command must be the exact typed value")
    for field_name in ("command_kind", "asset", "account_owner"):
        if type(getattr(command, field_name)) is not str:
            raise TypeError(f"managed asset command {field_name} must be an exact string")
    if type(command.amount_atoms) is not int:
        raise TypeError("managed asset command amount must be an exact integer")
    return ManagedAssetLifecycleCommandV1(
        command_kind=command.command_kind,
        asset=command.asset,
        account_owner=command.account_owner,
        amount_atoms=command.amount_atoms,
    )


def transition_managed_asset_lifecycle_v1(
    context: ManagedAssetLifecycleContextV1,
    pre_state: ManagedAssetLifecycleStateV1,
    command: ManagedAssetLifecycleCommandV1,
) -> ManagedAssetLifecycleResultV1:
    """Apply one profile-bound generic issue or self-burn transition."""

    context = _snapshot_context(context)
    pre_state = _snapshot_state(pre_state)
    command = _snapshot_command(command)
    prepared = _authorize(context, pre_state, command)
    if isinstance(prepared, ManagedAssetLifecycleRejectCodeV1):
        return _reject(prepared, pre_state)
    supplies = _post_supply(prepared)
    if isinstance(supplies, ManagedAssetLifecycleRejectCodeV1):
        return _reject(supplies, pre_state)
    balances = _post_balances(prepared)
    if isinstance(balances, ManagedAssetLifecycleRejectCodeV1):
        return _reject(balances, pre_state)
    return _accept(prepared, balances, supplies)


__all__ = ["transition_managed_asset_lifecycle_v1"]

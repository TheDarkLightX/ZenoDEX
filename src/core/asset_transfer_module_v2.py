"""Occurrence- and origin-bound V2 asset-transfer functional core.

The transition is a deterministic SHADOW candidate.  Its policy snapshot is an
explicit premise and is not yet authenticated against a governed profile.  It
implements no native-coin accounting, issue, burn, external custody, runtime
mount, or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass

from .asset_transfer_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_TRANSFER_COMMAND_KIND_V2,
    AssetClassV2,
    AssetTransferAcceptedV2,
    AssetTransferCommandV2,
    AssetTransferContextV2,
    AssetTransferPolicyV2,
    AssetTransferRejectCodeV2,
    AssetTransferRejectedV2,
    AssetTransferResultV2,
    AssetTransferStateV2,
    _snapshot_asset_transfer_command_v2,
    _snapshot_asset_transfer_context_v2,
    _snapshot_asset_transfer_state_v2,
)
from .global_economic_proof_v2 import LaneModuleTransitionJournalV2
from .global_settlement_types_v2 import (
    MAX_ATOMS_V2,
    MAX_DELTA_ATOMS_V2,
    MIN_DELTA_ATOMS_V2,
    ZERO_ROOT_V2,
    AssetConservationRowV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    FeeConservationRowV2,
    GlobalEconomicEffectPlanV2,
    LaneIdV2,
    LaneWriteV2,
    hash_global_v2,
)


def _reject(
    code: AssetTransferRejectCodeV2,
    pre_state: AssetTransferStateV2,
) -> AssetTransferRejectedV2:
    return AssetTransferRejectedV2(
        code=code,
        pre_state_root=pre_state.state_root,
        post_state_root=pre_state.state_root,
        effects=GlobalEconomicEffectPlanV2.empty(),
    )


def _policy_for(
    state: AssetTransferStateV2,
    asset: str,
) -> AssetTransferPolicyV2 | None:
    return next((policy for policy in state.policies if policy.asset == asset), None)


def _account_totals(state: AssetTransferStateV2, asset: str) -> int:
    return sum(row.amount_atoms for row in state.balances if row.asset == asset)


def _post_balances(
    state: AssetTransferStateV2,
    *,
    asset: str,
    deltas: tuple[tuple[str, int], ...],
) -> tuple[EconomicAmountV2, ...] | AssetTransferRejectCodeV2:
    values = {(row.asset, row.owner): row.amount_atoms for row in state.balances}
    for owner, delta_atoms in deltas:
        current_atoms = values.get((asset, owner), 0)
        post_atoms = current_atoms + delta_atoms
        if post_atoms < 0:
            return AssetTransferRejectCodeV2.INSUFFICIENT_BALANCE
        if post_atoms > MAX_ATOMS_V2:
            return AssetTransferRejectCodeV2.BALANCE_OVERFLOW
        if post_atoms == 0:
            values.pop((asset, owner), None)
        else:
            values[(asset, owner)] = post_atoms
    return tuple(
        EconomicAmountV2(
            owner,
            row_asset,
            ACCOUNT_CUSTODY_DOMAIN_V2,
            amount_atoms,
        )
        for (row_asset, owner), amount_atoms in sorted(values.items())
    )


def _effect_rows(
    *,
    asset: str,
    fee_owner: str,
    fee_atoms: int,
    deltas: tuple[tuple[str, int], ...],
) -> tuple[EconomicEffectRowV2, ...]:
    rows = [
        EconomicEffectRowV2(
            EconomicEffectKindV2.ACCOUNT_MOVEMENT,
            owner,
            asset,
            ACCOUNT_CUSTODY_DOMAIN_V2,
            delta_atoms,
        )
        for owner, delta_atoms in deltas
        if delta_atoms != 0
    ]
    if fee_atoms:
        rows.append(
            EconomicEffectRowV2(
                EconomicEffectKindV2.FEE_ALLOCATION,
                fee_owner,
                asset,
                ACCOUNT_CUSTODY_DOMAIN_V2,
                fee_atoms,
            )
        )
    return tuple(sorted(rows, key=lambda row: row.key))


def _transfer_policy(
    context: AssetTransferContextV2,
    pre_state: AssetTransferStateV2,
    command: AssetTransferCommandV2,
) -> AssetTransferPolicyV2 | AssetTransferRejectCodeV2:
    occurrence = context.occurrence
    if occurrence is None:
        return AssetTransferRejectCodeV2.MISSING_OCCURRENCE
    if (
        occurrence.pre_state_root != context.global_pre_state_root
        or occurrence.consumed_object_ids != ()
    ):
        return AssetTransferRejectCodeV2.OCCURRENCE_BINDING_MISMATCH
    if context.module_release_id != pre_state.module_release_id:
        return AssetTransferRejectCodeV2.RELEASE_MISMATCH
    if command.command_kind != ASSET_TRANSFER_COMMAND_KIND_V2:
        return AssetTransferRejectCodeV2.UNKNOWN_COMMAND
    if (
        occurrence.command_kind != command.command_kind
        or occurrence.command_body_hash != command.command_body_hash
    ):
        return AssetTransferRejectCodeV2.OCCURRENCE_COMMAND_MISMATCH
    policy = _policy_for(pre_state, command.asset)
    if policy is None:
        return AssetTransferRejectCodeV2.UNKNOWN_ASSET
    if not policy.enabled:
        return AssetTransferRejectCodeV2.DISABLED_ASSET
    if policy.asset_origin_root is None or command.asset_origin_root is None:
        return AssetTransferRejectCodeV2.UNREGISTERED_ASSET
    if command.asset_origin_root != policy.asset_origin_root:
        return AssetTransferRejectCodeV2.ASSET_ORIGIN_MISMATCH
    if policy.asset_class is AssetClassV2.TAU_NATIVE_COIN:
        return AssetTransferRejectCodeV2.NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED
    if command.sender != occurrence.subject_id:
        return AssetTransferRejectCodeV2.UNAUTHORIZED_SUBJECT
    if command.sender == command.recipient:
        return AssetTransferRejectCodeV2.SELF_TRANSFER
    if command.amount_atoms == 0:
        return AssetTransferRejectCodeV2.ZERO_AMOUNT
    if policy.transfer_fee_atoms > command.max_fee_atoms:
        return AssetTransferRejectCodeV2.FEE_LIMIT_EXCEEDED
    return policy


def _transfer_deltas(
    command: AssetTransferCommandV2,
    policy: AssetTransferPolicyV2,
) -> tuple[tuple[str, int], ...] | AssetTransferRejectCodeV2:
    deltas = {
        command.sender: -command.amount_atoms - policy.transfer_fee_atoms,
        command.recipient: command.amount_atoms,
    }
    deltas[policy.fee_owner] = deltas.get(policy.fee_owner, 0) + policy.transfer_fee_atoms
    if any(
        delta_atoms < MIN_DELTA_ATOMS_V2 or delta_atoms > MAX_DELTA_ATOMS_V2
        for delta_atoms in (*deltas.values(), policy.transfer_fee_atoms)
    ):
        return AssetTransferRejectCodeV2.EFFECT_DELTA_OVERFLOW
    return tuple(sorted(deltas.items()))


@dataclass(frozen=True, slots=True)
class _PreparedTransferV2:
    context: AssetTransferContextV2
    pre_state: AssetTransferStateV2
    command: AssetTransferCommandV2
    policy: AssetTransferPolicyV2
    deltas: tuple[tuple[str, int], ...]


def _prepare_transfer(
    context: AssetTransferContextV2,
    pre_state: AssetTransferStateV2,
    command: AssetTransferCommandV2,
) -> _PreparedTransferV2 | AssetTransferRejectCodeV2:
    policy = _transfer_policy(context, pre_state, command)
    if isinstance(policy, AssetTransferRejectCodeV2):
        return policy
    deltas = _transfer_deltas(command, policy)
    if isinstance(deltas, AssetTransferRejectCodeV2):
        return deltas
    return _PreparedTransferV2(context, pre_state, command, policy, deltas)


def _effect_plan(
    prepared: _PreparedTransferV2,
    post_state: AssetTransferStateV2,
) -> GlobalEconomicEffectPlanV2:
    context = prepared.context
    occurrence = context.occurrence
    if occurrence is None:
        raise RuntimeError("prepared transfer lost its required occurrence")
    pre_state = prepared.pre_state
    command = prepared.command
    policy = prepared.policy
    fee_rows = (
        (
            FeeConservationRowV2(
                command.asset,
                policy.transfer_fee_atoms,
                policy.transfer_fee_atoms,
                0,
            ),
        )
        if policy.transfer_fee_atoms
        else ()
    )
    return GlobalEconomicEffectPlanV2(
        rows=_effect_rows(
            asset=command.asset,
            fee_owner=policy.fee_owner,
            fee_atoms=policy.transfer_fee_atoms,
            deltas=prepared.deltas,
        ),
        asset_conservation=(
            AssetConservationRowV2(
                asset=command.asset,
                owned_and_custodied_pre_atoms=_account_totals(
                    pre_state,
                    command.asset,
                ),
                owned_and_custodied_post_atoms=_account_totals(
                    post_state,
                    command.asset,
                ),
                supply_pre_atoms=pre_state.supply_atoms(command.asset),
                supply_post_atoms=post_state.supply_atoms(command.asset),
                authorized_issue_atoms=0,
                authorized_burn_atoms=0,
            ),
        ),
        fee_conservation=fee_rows,
        lane_writes=(
            LaneWriteV2(
                LaneIdV2.ASSET_TRANSFER,
                pre_state.state_root,
                post_state.state_root,
            ),
        ),
        occurrence_consumptions=(occurrence.occurrence_id,),
        external_outbox_enqueue=(),
    )


def _accept_transfer(
    prepared: _PreparedTransferV2,
    balances: tuple[EconomicAmountV2, ...],
) -> AssetTransferAcceptedV2:
    context = prepared.context
    occurrence = context.occurrence
    if occurrence is None:
        raise RuntimeError("prepared transfer lost its required occurrence")
    pre_state = prepared.pre_state
    command = prepared.command
    post_state = AssetTransferStateV2(
        module_release_id=pre_state.module_release_id,
        policies=pre_state.policies,
        balances=balances,
        supplies=pre_state.supplies,
    )
    effects = _effect_plan(prepared, post_state)
    receipt_root = hash_global_v2(
        "asset-transfer-receipt-v2",
        {
            "context": context,
            "command": command,
            "pre_state_root": pre_state.state_root,
            "post_state_root": post_state.state_root,
            "effect_plan_root": effects.effect_plan_root,
            "private_port_root": ZERO_ROOT_V2,
            "terminal_obligations_root": ZERO_ROOT_V2,
            "oracle_occurrence_plan_root": ZERO_ROOT_V2,
        },
    )
    module_journal = LaneModuleTransitionJournalV2(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=context.writer_epoch,
        lane_id=LaneIdV2.ASSET_TRANSFER,
        module_release_id=context.module_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        pre_lane_root=pre_state.state_root,
        post_lane_root=post_state.state_root,
        effect_plan_root=effects.effect_plan_root,
        private_port_root=ZERO_ROOT_V2,
        receipt_root=receipt_root,
        terminal_obligations_root=ZERO_ROOT_V2,
        oracle_occurrence_plan_root=ZERO_ROOT_V2,
    )
    return AssetTransferAcceptedV2(post_state, effects, module_journal)


def transition_asset_transfer_v2(
    context: AssetTransferContextV2,
    pre_state: AssetTransferStateV2,
    command: AssetTransferCommandV2,
) -> AssetTransferResultV2:
    """Apply one transfer with fixed rejection precedence and no hidden inputs."""

    if type(context) is not AssetTransferContextV2:
        raise TypeError("asset transfer context must be an exact typed value")
    if type(pre_state) is not AssetTransferStateV2:
        raise TypeError("asset transfer pre-state must be an exact typed value")
    if type(command) is not AssetTransferCommandV2:
        raise TypeError("asset transfer command must be an exact typed value")
    owned_context = _snapshot_asset_transfer_context_v2(context)
    owned_state = _snapshot_asset_transfer_state_v2(pre_state)
    owned_command = _snapshot_asset_transfer_command_v2(command)
    prepared = _prepare_transfer(owned_context, owned_state, owned_command)
    if isinstance(prepared, AssetTransferRejectCodeV2):
        return _reject(prepared, owned_state)
    balances = _post_balances(
        owned_state,
        asset=owned_command.asset,
        deltas=prepared.deltas,
    )
    if isinstance(balances, AssetTransferRejectCodeV2):
        return _reject(balances, owned_state)
    return _accept_transfer(prepared, balances)


__all__ = ["transition_asset_transfer_v2"]

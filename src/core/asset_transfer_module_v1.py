"""Deterministic research core for the `ASSET_TRANSFER` lane.

This first module slice implements authenticated account-to-account transfer
with a flat fee read from the pre-state policy row. The transition consults no
governed registry; release-route binding separately requires that row to be an
exact member of the active profile's typed asset-transfer policy registry. It
does not implement issue, burn, external custody, release activation, or
publication authority. Rejections return the exact pre-state root and an empty
`GlobalEconomicEffectPlanV1`.
"""

from __future__ import annotations

from dataclasses import dataclass

from .asset_transfer_types_v1 import (
    ACCOUNT_CUSTODY_DOMAIN_V1,
    ASSET_TRANSFER_COMMAND_KIND_V1,
    ASSET_TRANSFER_MODULE_SCHEMA_V1,
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectCodeV1,
    AssetTransferRejectedV1,
    AssetTransferResultV1,
    AssetTransferStateV1,
)
from .global_economic_proof_v1 import LaneModuleTransitionJournalV1
from .global_settlement_types_v1 import (
    MAX_ASSET_BALANCE_ROWS_V1,
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    ZERO_ROOT_V1,
    AssetConservationRowV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
    hash_global_v1,
)


def _reject(
    code: AssetTransferRejectCodeV1,
    pre_state: AssetTransferStateV1,
) -> AssetTransferRejectedV1:
    return AssetTransferRejectedV1(
        code=code,
        pre_state_root=pre_state.state_root,
        post_state_root=pre_state.state_root,
        effects=GlobalEconomicEffectPlanV1.empty(),
    )


def _policy_for(
    state: AssetTransferStateV1,
    asset: str,
) -> AssetTransferPolicyV1 | None:
    return next((policy for policy in state.policies if policy.asset == asset), None)


def _account_totals(state: AssetTransferStateV1, asset: str) -> int:
    return sum(row.amount_atoms for row in state.balances if row.asset == asset)


def _post_balances(
    state: AssetTransferStateV1,
    *,
    asset: str,
    deltas: dict[str, int],
) -> tuple[EconomicAmountV1, ...] | AssetTransferRejectCodeV1:
    values = {(row.asset, row.owner): row.amount_atoms for row in state.balances}
    for owner, delta_atoms in deltas.items():
        current_atoms = values.get((asset, owner), 0)
        post_atoms = current_atoms + delta_atoms
        if post_atoms < 0:
            return AssetTransferRejectCodeV1.INSUFFICIENT_BALANCE
        if post_atoms > MAX_ATOMS_V1:
            return AssetTransferRejectCodeV1.BALANCE_OVERFLOW
        if post_atoms == 0:
            values.pop((asset, owner), None)
        else:
            values[(asset, owner)] = post_atoms
    if len(values) > MAX_ASSET_BALANCE_ROWS_V1:
        return AssetTransferRejectCodeV1.POST_STATE_RESOURCE_BOUND_EXCEEDED
    return tuple(
        EconomicAmountV1(owner, row_asset, ACCOUNT_CUSTODY_DOMAIN_V1, amount_atoms)
        for (row_asset, owner), amount_atoms in sorted(values.items())
    )


def _effect_rows(
    *,
    asset: str,
    fee_owner: str,
    fee_atoms: int,
    deltas: dict[str, int],
) -> tuple[EconomicEffectRowV1, ...]:
    rows = [
        EconomicEffectRowV1(
            EconomicEffectKindV1.ACCOUNT_MOVEMENT,
            owner,
            asset,
            ACCOUNT_CUSTODY_DOMAIN_V1,
            delta_atoms,
        )
        for owner, delta_atoms in deltas.items()
        if delta_atoms != 0
    ]
    if fee_atoms:
        rows.append(
            EconomicEffectRowV1(
                EconomicEffectKindV1.FEE_ALLOCATION,
                fee_owner,
                asset,
                ACCOUNT_CUSTODY_DOMAIN_V1,
                fee_atoms,
            )
        )
    return tuple(sorted(rows, key=lambda row: row.key))


def _transfer_policy(
    context: AssetTransferContextV1,
    pre_state: AssetTransferStateV1,
    command: AssetTransferCommandV1,
) -> AssetTransferPolicyV1 | AssetTransferRejectCodeV1:
    if context.module_release_id != pre_state.module_release_id:
        return AssetTransferRejectCodeV1.RELEASE_MISMATCH
    if command.command_kind != ASSET_TRANSFER_COMMAND_KIND_V1:
        return AssetTransferRejectCodeV1.UNKNOWN_COMMAND
    policy = _policy_for(pre_state, command.asset)
    if policy is None:
        return AssetTransferRejectCodeV1.UNKNOWN_ASSET
    if not policy.enabled:
        return AssetTransferRejectCodeV1.DISABLED_ASSET
    if command.sender != context.subject_id:
        return AssetTransferRejectCodeV1.UNAUTHORIZED_SUBJECT
    if command.sender == command.recipient:
        return AssetTransferRejectCodeV1.SELF_TRANSFER
    if command.amount_atoms == 0:
        return AssetTransferRejectCodeV1.ZERO_AMOUNT
    if policy.transfer_fee_atoms > command.max_fee_atoms:
        return AssetTransferRejectCodeV1.FEE_LIMIT_EXCEEDED
    return policy


def _transfer_deltas(
    command: AssetTransferCommandV1,
    policy: AssetTransferPolicyV1,
) -> dict[str, int] | AssetTransferRejectCodeV1:
    deltas = {
        command.sender: -command.amount_atoms - policy.transfer_fee_atoms,
        command.recipient: command.amount_atoms,
    }
    deltas[policy.fee_owner] = deltas.get(policy.fee_owner, 0) + policy.transfer_fee_atoms
    if any(
        delta_atoms < MIN_DELTA_ATOMS_V1 or delta_atoms > MAX_DELTA_ATOMS_V1
        for delta_atoms in (*deltas.values(), policy.transfer_fee_atoms)
    ):
        return AssetTransferRejectCodeV1.EFFECT_DELTA_OVERFLOW
    return deltas


@dataclass(frozen=True, slots=True)
class _PreparedTransferV1:
    context: AssetTransferContextV1
    pre_state: AssetTransferStateV1
    command: AssetTransferCommandV1
    policy: AssetTransferPolicyV1
    deltas: dict[str, int]


def _prepare_transfer(
    context: AssetTransferContextV1,
    pre_state: AssetTransferStateV1,
    command: AssetTransferCommandV1,
) -> _PreparedTransferV1 | AssetTransferRejectCodeV1:
    policy = _transfer_policy(context, pre_state, command)
    if isinstance(policy, AssetTransferRejectCodeV1):
        return policy
    deltas = _transfer_deltas(command, policy)
    if isinstance(deltas, AssetTransferRejectCodeV1):
        return deltas
    return _PreparedTransferV1(context, pre_state, command, policy, deltas)


def _effect_plan(
    prepared: _PreparedTransferV1,
    post_state: AssetTransferStateV1,
) -> GlobalEconomicEffectPlanV1:
    context = prepared.context
    pre_state = prepared.pre_state
    command = prepared.command
    policy = prepared.policy
    fee_rows = (
        (
            FeeConservationRowV1(
                command.asset,
                policy.transfer_fee_atoms,
                policy.transfer_fee_atoms,
                0,
            ),
        )
        if policy.transfer_fee_atoms
        else ()
    )
    return GlobalEconomicEffectPlanV1(
        rows=_effect_rows(
            asset=command.asset,
            fee_owner=policy.fee_owner,
            fee_atoms=policy.transfer_fee_atoms,
            deltas=prepared.deltas,
        ),
        asset_conservation=(
            AssetConservationRowV1(
                asset=command.asset,
                owned_and_custodied_pre_atoms=_account_totals(pre_state, command.asset),
                owned_and_custodied_post_atoms=_account_totals(post_state, command.asset),
                supply_pre_atoms=pre_state.supply_atoms(command.asset),
                supply_post_atoms=post_state.supply_atoms(command.asset),
                authorized_issue_atoms=0,
                authorized_burn_atoms=0,
            ),
        ),
        fee_conservation=fee_rows,
        lane_writes=(
            LaneWriteV1(LaneIdV1.ASSET_TRANSFER, pre_state.state_root, post_state.state_root),
        ),
        occurrence_consumptions=(context.command_occurrence_id,),
        external_outbox_enqueue=(),
    )


def _accept_transfer(
    prepared: _PreparedTransferV1,
    balances: tuple[EconomicAmountV1, ...],
) -> AssetTransferAcceptedV1:
    context = prepared.context
    pre_state = prepared.pre_state
    command = prepared.command
    post_state = AssetTransferStateV1(
        module_release_id=pre_state.module_release_id,
        policies=pre_state.policies,
        balances=balances,
        supplies=pre_state.supplies,
    )
    effects = _effect_plan(prepared, post_state)
    receipt_root = hash_global_v1(
        "asset-transfer-receipt-v1",
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
    return AssetTransferAcceptedV1(post_state, effects, module_journal)


def transition_asset_transfer_v1(
    context: AssetTransferContextV1,
    pre_state: AssetTransferStateV1,
    command: AssetTransferCommandV1,
) -> AssetTransferResultV1:
    """Apply one transfer with fixed rejection precedence and no hidden inputs.

    ABI row ceilings still reject oversized input states at construction. For a
    valid pre-state at the balance-row ceiling, any accepted-looking transfer
    that would grow the post-state beyond that ceiling is totalised here as
    ``POST_STATE_RESOURCE_BOUND_EXCEEDED`` before post-state construction.
    """

    # Opus P27 NEW-21: exact-type checks, mirroring the managed sibling. A
    # subclass can skip __post_init__ and override derived roots; isinstance
    # admits it, `type(...) is` refuses it.
    if type(context) is not AssetTransferContextV1:
        raise TypeError("asset transfer context must be the exact typed value")
    if type(pre_state) is not AssetTransferStateV1:
        raise TypeError("asset transfer pre-state must be the exact typed value")
    if type(command) is not AssetTransferCommandV1:
        raise TypeError("asset transfer command must be the exact typed value")
    prepared = _prepare_transfer(context, pre_state, command)
    if isinstance(prepared, AssetTransferRejectCodeV1):
        return _reject(prepared, pre_state)
    balances = _post_balances(pre_state, asset=command.asset, deltas=prepared.deltas)
    if isinstance(balances, AssetTransferRejectCodeV1):
        return _reject(balances, pre_state)
    return _accept_transfer(prepared, balances)


__all__ = [
    "ASSET_TRANSFER_MODULE_SCHEMA_V1",
    "ASSET_TRANSFER_COMMAND_KIND_V1",
    "ACCOUNT_CUSTODY_DOMAIN_V1",
    "AssetTransferRejectCodeV1",
    "AssetTransferPolicyV1",
    "AssetTransferStateV1",
    "AssetTransferContextV1",
    "AssetTransferCommandV1",
    "AssetTransferAcceptedV1",
    "AssetTransferRejectedV1",
    "AssetTransferResultV1",
    "transition_asset_transfer_v1",
]

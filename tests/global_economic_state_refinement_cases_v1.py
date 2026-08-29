"""Reusable full-state cases for GlobalSettlementABI V1 refinement tests."""

from __future__ import annotations

from dataclasses import dataclass, replace

from src.core.global_economic_state_effect_refinement_v1 import (
    GlobalEconomicStateEffectRefinementCandidateV1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    FEE_RESIDUE_CONTROL_DOMAIN_V1,
    FEE_RESIDUE_PRINCIPAL_V1,
    AssetConservationRowV1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    LaneWriteV1,
)


@dataclass(frozen=True, slots=True)
class FeeResidueFlowCaseV1:
    asset: str
    carried_atoms: int
    spent_atoms: int = 0


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _lane_roots(asset_root: int) -> tuple[LaneStateRootV1, ...]:
    return tuple(
        LaneStateRootV1(
            lane_id,
            _root(100 + index),
            True,
            _root(asset_root if lane_id is LaneIdV1.ASSET_TRANSFER else 2_000 + index),
        )
        for index, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
    )


def _amounts(rows: list[EconomicAmountV1]) -> tuple[EconomicAmountV1, ...]:
    return tuple(sorted(rows, key=lambda row: row.key))


def fee_residue_flow_candidate_v1(
    flows: tuple[FeeResidueFlowCaseV1, ...],
) -> GlobalEconomicStateEffectRefinementCandidateV1:
    """Build a complete fee-to-reserve flow, including any same-plan spend."""

    pre_balances: list[EconomicAmountV1] = []
    pre_reserves: list[EconomicAmountV1] = []
    post_balances: list[EconomicAmountV1] = []
    post_reserves: list[EconomicAmountV1] = []
    supplies: list[AssetSupplyV1] = []
    effects: list[EconomicEffectRowV1] = []
    conservation: list[AssetConservationRowV1] = []
    fees: list[FeeConservationRowV1] = []

    for flow in flows:
        total_atoms = flow.carried_atoms + flow.spent_atoms
        pre_balances.append(
            EconomicAmountV1("protocol:fee-ingress", flow.asset, "accounts", flow.carried_atoms)
        )
        if flow.spent_atoms > 0:
            pre_reserves.append(
                EconomicAmountV1(
                    FEE_RESIDUE_PRINCIPAL_V1,
                    flow.asset,
                    FEE_RESIDUE_CONTROL_DOMAIN_V1,
                    flow.spent_atoms,
                )
            )
            post_balances.append(
                EconomicAmountV1("protocol:fee-spend-sink", flow.asset, "accounts", flow.spent_atoms)
            )
            effects.append(
                EconomicEffectRowV1(
                    EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                    "protocol:fee-spend-sink",
                    flow.asset,
                    "accounts",
                    flow.spent_atoms,
                )
            )
        post_reserves.append(
            EconomicAmountV1(
                FEE_RESIDUE_PRINCIPAL_V1,
                flow.asset,
                FEE_RESIDUE_CONTROL_DOMAIN_V1,
                flow.carried_atoms,
            )
        )
        effects.append(
            EconomicEffectRowV1(
                EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                "protocol:fee-ingress",
                flow.asset,
                "accounts",
                -flow.carried_atoms,
            )
        )
        reserve_delta = flow.carried_atoms - flow.spent_atoms
        if reserve_delta != 0:
            effects.append(
                EconomicEffectRowV1(
                    EconomicEffectKindV1.RESERVE,
                    FEE_RESIDUE_PRINCIPAL_V1,
                    flow.asset,
                    FEE_RESIDUE_CONTROL_DOMAIN_V1,
                    reserve_delta,
                )
            )
        supplies.append(AssetSupplyV1(flow.asset, total_atoms))
        conservation.append(
            AssetConservationRowV1(
                flow.asset,
                total_atoms,
                total_atoms,
                total_atoms,
                total_atoms,
                0,
                0,
            )
        )
        fees.append(FeeConservationRowV1(flow.asset, flow.carried_atoms, 0, flow.carried_atoms))

    pre_state = GlobalEconomicStateV1(
        chain_id="zeno-fee-residue-test",
        deployment_root=_root(1_000),
        writer_epoch=17,
        height=41,
        profile_root=_root(1_001),
        lane_roots=_lane_roots(2_001),
        balances=_amounts(pre_balances),
        supplies=tuple(sorted(supplies, key=lambda row: row.asset)),
        reserves=_amounts(pre_reserves),
    )
    post_state = GlobalEconomicStateV1(
        chain_id=pre_state.chain_id,
        deployment_root=pre_state.deployment_root,
        writer_epoch=pre_state.writer_epoch,
        height=pre_state.height,
        profile_root=pre_state.profile_root,
        lane_roots=_lane_roots(9_001),
        balances=_amounts(post_balances),
        supplies=tuple(sorted(supplies, key=lambda row: row.asset)),
        reserves=_amounts(post_reserves),
    )
    effect_plan = GlobalEconomicEffectPlanV1(
        rows=tuple(sorted(effects, key=lambda row: row.key)),
        asset_conservation=tuple(sorted(conservation, key=lambda row: row.asset)),
        fee_conservation=tuple(sorted(fees, key=lambda row: row.asset)),
        lane_writes=(LaneWriteV1(LaneIdV1.ASSET_TRANSFER, _root(2_001), _root(9_001)),),
        occurrence_consumptions=(),
        external_outbox_enqueue=(),
    )
    return GlobalEconomicStateEffectRefinementCandidateV1(pre_state, post_state, effect_plan)


def fee_residue_full_spend_candidate_v1(
    pre_state: GlobalEconomicStateV1,
    *,
    asset: str,
) -> GlobalEconomicStateEffectRefinementCandidateV1:
    """Spend one previously carried reserve in a separate full-state transition."""

    reserve = next(
        row
        for row in pre_state.reserves
        if row.owner == FEE_RESIDUE_PRINCIPAL_V1
        and row.asset == asset
        and row.custody_domain == FEE_RESIDUE_CONTROL_DOMAIN_V1
    )
    post_lane_roots = tuple(
        replace(row, state_root=_root(9_002))
        if row.lane_id is LaneIdV1.ASSET_TRANSFER
        else row
        for row in pre_state.lane_roots
    )
    sink = EconomicAmountV1(
        "protocol:fee-spend-sink",
        asset,
        "accounts",
        reserve.amount_atoms,
    )
    post_state = replace(
        pre_state,
        lane_roots=post_lane_roots,
        balances=_amounts([*pre_state.balances, sink]),
        reserves=tuple(row for row in pre_state.reserves if row.key != reserve.key),
    )
    effects = GlobalEconomicEffectPlanV1(
        rows=tuple(
            sorted(
                (
                    EconomicEffectRowV1(
                        EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                        sink.owner,
                        sink.asset,
                        sink.custody_domain,
                        sink.amount_atoms,
                    ),
                    EconomicEffectRowV1(
                        EconomicEffectKindV1.RESERVE,
                        reserve.owner,
                        reserve.asset,
                        reserve.custody_domain,
                        -reserve.amount_atoms,
                    ),
                ),
                key=lambda row: row.key,
            )
        ),
        asset_conservation=(
            AssetConservationRowV1(
                asset,
                reserve.amount_atoms,
                reserve.amount_atoms,
                reserve.amount_atoms,
                reserve.amount_atoms,
                0,
                0,
            ),
        ),
        fee_conservation=(),
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.ASSET_TRANSFER,
                next(
                    row.state_root
                    for row in pre_state.lane_roots
                    if row.lane_id is LaneIdV1.ASSET_TRANSFER
                ),
                _root(9_002),
            ),
        ),
        occurrence_consumptions=(),
        external_outbox_enqueue=(),
    )
    return GlobalEconomicStateEffectRefinementCandidateV1(pre_state, post_state, effects)


__all__ = [
    "FeeResidueFlowCaseV1",
    "fee_residue_flow_candidate_v1",
    "fee_residue_full_spend_candidate_v1",
]

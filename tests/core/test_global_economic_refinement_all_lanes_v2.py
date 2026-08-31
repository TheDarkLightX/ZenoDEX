"""All-lane structural obligations for GlobalSettlementABI V2 refinement.

These cases exercise the common global relation. They do not assert that an
economic transition exists or is enabled for every product lane.
"""

from __future__ import annotations

import pytest

from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_economic_state_effect_refinement_v2 import (
    GlobalEconomicStateEffectRefinementCandidateV2,
    refine_global_economic_state_effects_v2,
)
from src.core.global_economic_state_v2 import (
    GlobalEconomicStateV2,
    LaneStateRootV2,
    ReplayStateV2,
)
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    ZERO_ROOT_V2,
    AssetConservationRowV2,
    AssetSupplyV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    LaneWriteV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _lane_roots(
    *,
    target: LaneIdV2,
    target_root: str | None = None,
    target_enabled: bool = True,
) -> tuple[LaneStateRootV2, ...]:
    return tuple(
        LaneStateRootV2(
            lane_id=lane,
            module_release_id=_root(index + 1),
            enabled=target_enabled if lane is target else True,
            state_root=(
                target_root
                if lane is target and target_root is not None
                else _root(index + 101)
            ),
        )
        for index, lane in enumerate(ALL_LANE_IDS_V2)
    )


def _candidate(
    lane: LaneIdV2,
    *,
    enabled: bool = True,
) -> GlobalEconomicStateEffectRefinementCandidateV2:
    pre_lane_roots = _lane_roots(target=lane, target_enabled=enabled)
    obligation = TerminalObligationV2(
        obligation_id="claim:alice:usd",
        lane_id=lane,
        claimant="alice",
        asset="USD",
        liability_domain="claim-backing",
        amount_atoms=3,
        status=TerminalObligationStatusV2.OPEN,
    )
    pre = GlobalEconomicStateV2(
        chain_id="zeno-v2-all-lanes",
        deployment_root=_root(301),
        writer_epoch=5,
        height=9,
        profile_root=_root(302),
        lane_roots=pre_lane_roots,
        balances=(
            EconomicAmountV2("carol", "EUR", "accounts", 6),
            EconomicAmountV2("alice", "USD", "accounts", 10),
        ),
        supplies=(AssetSupplyV2("EUR", 6), AssetSupplyV2("USD", 15)),
        custody=(EconomicAmountV2("vault", "USD", "claim-backing", 3),),
        liabilities=(EconomicAmountV2("alice", "USD", "claim-backing", 3),),
        reserves=(EconomicAmountV2("reserve", "USD", "reserve-domain", 2),),
        terminal_obligations=(obligation,),
        history_root=ZERO_ROOT_V2,
    )
    occurrence = EconomicCommandOccurrenceV2(
        chain_id=pre.chain_id,
        deployment_root=pre.deployment_root,
        height=pre.height + 1,
        tx_index=0,
        op_index=0,
        command_kind="all_lane_structural_move",
        command_body_hash=_root(303),
        route_release_id=_root(304),
        subject_id="alice",
        grant_root=_root(305),
        nonce=1,
        profile_root=pre.profile_root,
        pre_state_root=pre.state_root,
        consumed_object_ids=(),
    )
    post_lane_root = _root(400 + ALL_LANE_IDS_V2.index(lane))
    post = GlobalEconomicStateV2(
        chain_id=pre.chain_id,
        deployment_root=pre.deployment_root,
        writer_epoch=pre.writer_epoch,
        height=pre.height + 1,
        profile_root=pre.profile_root,
        lane_roots=_lane_roots(
            target=lane,
            target_root=post_lane_root,
            target_enabled=enabled,
        ),
        balances=(
            EconomicAmountV2("carol", "EUR", "accounts", 6),
            EconomicAmountV2("alice", "USD", "accounts", 9),
            EconomicAmountV2("bob", "USD", "accounts", 1),
        ),
        supplies=pre.supplies,
        custody=pre.custody,
        liabilities=pre.liabilities,
        reserves=pre.reserves,
        replay_state=(ReplayStateV2(occurrence.replay_id, occurrence.occurrence_id),),
        terminal_obligations=pre.terminal_obligations,
        history_root=pre.history_root,
    )
    pre_lane_root = pre_lane_roots[ALL_LANE_IDS_V2.index(lane)].state_root
    effects = GlobalEconomicEffectPlanV2(
        rows=(
            EconomicEffectRowV2(
                EconomicEffectKindV2.ACCOUNT_MOVEMENT,
                "alice",
                "USD",
                "accounts",
                -1,
            ),
            EconomicEffectRowV2(
                EconomicEffectKindV2.ACCOUNT_MOVEMENT,
                "bob",
                "USD",
                "accounts",
                1,
            ),
        ),
        asset_conservation=(AssetConservationRowV2("USD", 15, 15, 15, 15, 0, 0),),
        fee_conservation=(),
        lane_writes=(LaneWriteV2(lane, pre_lane_root, post_lane_root),),
        occurrence_consumptions=(occurrence.occurrence_id,),
        external_outbox_enqueue=(),
    )
    return GlobalEconomicStateEffectRefinementCandidateV2(
        pre,
        post,
        effects,
        (occurrence,),
        GlobalTerminalObligationPlanV2.empty(),
        GlobalOracleOccurrencePlanV2.empty(),
    )


@pytest.mark.parametrize("lane", ALL_LANE_IDS_V2, ids=lambda lane: lane.value)
def test_common_global_relation_reconciles_each_declared_lane(
    lane: LaneIdV2,
) -> None:
    candidate = _candidate(lane)

    witness = refine_global_economic_state_effects_v2(candidate)

    assert witness.pre_state_root == candidate.pre_state.state_root
    assert witness.post_state_root == candidate.post_state.state_root
    assert witness.effect_plan_root == candidate.effect_plan.effect_plan_root


def test_disabled_lane_cannot_change_its_committed_state_root() -> None:
    with pytest.raises(ValueError, match="disabled lane"):
        refine_global_economic_state_effects_v2(
            _candidate(LaneIdV2.EXTERNAL_CUSTODY, enabled=False)
        )

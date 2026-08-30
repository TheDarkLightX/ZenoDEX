"""RIPR evidence for exact economic-table and lane-write refinement.

The independent oracle derives deltas directly from full pre/post state tables.
Golden-root parity detects Python/Rust canonical encoding drift.
"""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

import src.core.global_economic_state_effect_refinement_v1 as refinement_module
from src.core.global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    RouteCompositionJournalV1,
)
from src.core.global_economic_state_effect_refinement_v1 import (
    GlobalEconomicStateEffectRefinementCandidateV1,
    refine_global_economic_state_effects_v1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    FEE_RESIDUE_CONTROL_DOMAIN_V1,
    FEE_RESIDUE_PRINCIPAL_V1,
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    ZERO_ROOT_V1,
    AssetConservationRowV1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    ExternalOutboxEnqueueV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    LaneWriteV1,
    OracleOccurrenceStateV1,
    OutboxStateV1,
    OutboxStatusV1,
    ReplayStateV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
)
from tests.global_economic_state_refinement_cases_v1 import (
    FeeResidueFlowCaseV1,
    fee_residue_flow_candidate_v1,
    fee_residue_full_spend_candidate_v1,
)

FEE_RESIDUE_VECTOR = (
    Path(__file__).resolve().parents[1]
    / "fixtures"
    / "global_economic_state_fee_residue_v1.json"
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _amounts(*rows: tuple[str, str, str, int]) -> tuple[EconomicAmountV1, ...]:
    return tuple(
        sorted(
            (EconomicAmountV1(owner, asset, domain, atoms) for owner, asset, domain, atoms in rows),
            key=lambda row: row.key,
        )
    )


def _lane_roots(*, asset_root: int) -> tuple[LaneStateRootV1, ...]:
    return tuple(
        LaneStateRootV1(
            lane_id,
            _root(100 + index),
            True,
            _root(asset_root if lane_id is LaneIdV1.ASSET_TRANSFER else 2_000 + index),
        )
        for index, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
    )


def _pre_state() -> GlobalEconomicStateV1:
    return GlobalEconomicStateV1(
        chain_id="zeno-refinement-test",
        deployment_root=_root(1_000),
        writer_epoch=17,
        height=41,
        profile_root=_root(1_001),
        lane_roots=_lane_roots(asset_root=2_001),
        balances=_amounts(("alice", "USD", "accounts", 100)),
        supplies=(AssetSupplyV1("USD", 175),),
        custody=_amounts(
            ("burn-bucket", "USD", "protocol-burn", 20),
            ("pool", "USD", "amm-pool", 50),
        ),
        liabilities=_amounts(("vault", "USD", "vault-debt", 10)),
        reserves=_amounts(("treasury", "USD", "reserve", 5)),
    )


def _post_state() -> GlobalEconomicStateV1:
    return GlobalEconomicStateV1(
        chain_id="zeno-refinement-test",
        deployment_root=_root(1_000),
        writer_epoch=17,
        height=41,
        profile_root=_root(1_001),
        lane_roots=_lane_roots(asset_root=9_001),
        balances=_amounts(
            ("alice", "USD", "accounts", 95),
            ("bob", "USD", "accounts", 10),
            ("treasury", "USD", "accounts", 2),
        ),
        supplies=(AssetSupplyV1("USD", 178),),
        custody=_amounts(
            ("burn-bucket", "USD", "protocol-burn", 16),
            ("escrow", "USD", "strategy-escrow", 5),
            ("pool", "USD", "amm-pool", 44),
        ),
        liabilities=_amounts(("vault", "USD", "vault-debt", 13)),
        reserves=_amounts(("treasury", "USD", "reserve", 6)),
    )


def _effect_plan() -> GlobalEconomicEffectPlanV1:
    rows = (
        EconomicEffectRowV1(EconomicEffectKindV1.ACCOUNT_MOVEMENT, "alice", "USD", "accounts", -5),
        EconomicEffectRowV1(EconomicEffectKindV1.ACCOUNT_MOVEMENT, "bob", "USD", "accounts", 10),
        EconomicEffectRowV1(
            EconomicEffectKindV1.ACCOUNT_MOVEMENT,
            "treasury",
            "USD",
            "accounts",
            2,
        ),
        EconomicEffectRowV1(EconomicEffectKindV1.BURN, "supply", "USD", "supply", -4),
        EconomicEffectRowV1(
            EconomicEffectKindV1.CUSTODY,
            "burn-bucket",
            "USD",
            "protocol-burn",
            -4,
        ),
        EconomicEffectRowV1(
            EconomicEffectKindV1.CUSTODY,
            "escrow",
            "USD",
            "strategy-escrow",
            5,
        ),
        EconomicEffectRowV1(EconomicEffectKindV1.CUSTODY, "pool", "USD", "amm-pool", -6),
        EconomicEffectRowV1(
            EconomicEffectKindV1.FEE_ALLOCATION,
            "treasury",
            "USD",
            "accounts",
            2,
        ),
        EconomicEffectRowV1(EconomicEffectKindV1.ISSUE, "supply", "USD", "supply", 7),
        EconomicEffectRowV1(EconomicEffectKindV1.LIABILITY, "vault", "USD", "vault-debt", 3),
        EconomicEffectRowV1(EconomicEffectKindV1.RESERVE, "treasury", "USD", "reserve", 1),
    )
    return GlobalEconomicEffectPlanV1(
        rows=tuple(sorted(rows, key=lambda row: row.key)),
        asset_conservation=(AssetConservationRowV1("USD", 175, 178, 175, 178, 7, 4),),
        fee_conservation=(FeeConservationRowV1("USD", 2, 2, 0),),
        lane_writes=(LaneWriteV1(LaneIdV1.ASSET_TRANSFER, _root(2_001), _root(9_001)),),
        occurrence_consumptions=(),
        external_outbox_enqueue=(),
    )


def _candidate() -> GlobalEconomicStateEffectRefinementCandidateV1:
    return GlobalEconomicStateEffectRefinementCandidateV1(
        _pre_state(),
        _post_state(),
        _effect_plan(),
    )


def _fee_residue_candidate(
    *,
    principal: str = FEE_RESIDUE_PRINCIPAL_V1,
    control_domain: str = FEE_RESIDUE_CONTROL_DOMAIN_V1,
    effect_atoms: int = 1,
) -> GlobalEconomicStateEffectRefinementCandidateV1:
    pre_state = replace(
        _pre_state(),
        reserves=_amounts((principal, "USD", control_domain, 5)),
    )
    post_state = replace(
        _post_state(),
        reserves=_amounts((principal, "USD", control_domain, 6)),
    )
    effects = _effect_plan()
    rows = tuple(
        EconomicEffectRowV1(row.kind, principal, row.asset, control_domain, effect_atoms)
        if row.kind is EconomicEffectKindV1.RESERVE
        else row
        for row in effects.rows
    )
    return GlobalEconomicStateEffectRefinementCandidateV1(
        pre_state,
        post_state,
        replace(
            effects,
            rows=tuple(sorted(rows, key=lambda row: row.key)),
            fee_conservation=(FeeConservationRowV1("USD", 3, 2, 1),),
        ),
    )


def _occurrence(
    *,
    subject_id: str = "alice",
    nonce: int = 11,
    command_kind: str = "TRANSFER",
    chain_id: str = "zeno-refinement-test",
    tx_index: int = 3,
    pre_state_root: str | None = None,
) -> EconomicCommandOccurrenceV1:
    return EconomicCommandOccurrenceV1(
        chain_id=chain_id,
        deployment_root=_root(1_000),
        height=42,
        tx_index=tx_index,
        op_index=1,
        command_kind=command_kind,
        command_body_hash=_root(5_000 + tx_index),
        route_release_id=_root(4_001),
        subject_id=subject_id,
        grant_root=_root(4_002),
        nonce=nonce,
        profile_root=_root(1_001),
        pre_state_root=_pre_state().state_root if pre_state_root is None else pre_state_root,
        consumed_object_ids=(),
    )


def _route_journal(
    occurrence: EconomicCommandOccurrenceV1,
    post_state_root: str,
) -> RouteCompositionJournalV1:
    return RouteCompositionJournalV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=17,
        route_release_id=occurrence.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        ordered_lane_journal_roots=(_root(20_000 + occurrence.tx_index),),
        pre_state_root=occurrence.pre_state_root,
        post_state_root=post_state_root,
        effect_plan_root=_root(30_000 + occurrence.tx_index),
        terminal_obligations_root=ZERO_ROOT_V1,
    )


def _replay_candidate(
    occurrence: EconomicCommandOccurrenceV1 | None = None,
) -> GlobalEconomicStateEffectRefinementCandidateV1:
    consumed = _occurrence() if occurrence is None else occurrence
    effect_plan = replace(
        _effect_plan(),
        occurrence_consumptions=(consumed.occurrence_id,),
    )
    post_state = replace(
        _post_state(),
        height=42,
        replay_state=(ReplayStateV1(consumed.replay_id, consumed.occurrence_id),),
    )
    return GlobalEconomicStateEffectRefinementCandidateV1(
        _pre_state(),
        post_state,
        effect_plan,
        (consumed,),
        (_route_journal(consumed, post_state.state_root),),
    )


def _with_replay_post(
    candidate: GlobalEconomicStateEffectRefinementCandidateV1,
    replay_state: tuple[ReplayStateV1, ...],
) -> GlobalEconomicStateEffectRefinementCandidateV1:
    post_state = replace(candidate.post_state, replay_state=replay_state)
    route_journals = candidate.route_journals
    if route_journals:
        route_journals = (
            *route_journals[:-1],
            replace(route_journals[-1], post_state_root=post_state.state_root),
        )
    return replace(
        candidate,
        post_state=post_state,
        route_journals=route_journals,
    )


def _replay_batch(
    count: int,
    *,
    pre_state: GlobalEconomicStateV1 | None = None,
) -> GlobalEconomicStateEffectRefinementCandidateV1:
    pre = _pre_state() if pre_state is None else pre_state
    current = pre
    occurrences: list[EconomicCommandOccurrenceV1] = []
    journals: list[RouteCompositionJournalV1] = []
    for index in range(count):
        occurrence = _occurrence(
            nonce=index,
            tx_index=index,
            pre_state_root=current.state_root,
        )
        replay_row = ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id)
        next_state = replace(
            current,
            height=42,
            replay_state=tuple(
                sorted((*current.replay_state, replay_row), key=lambda row: row.replay_id)
            ),
        )
        occurrences.append(occurrence)
        journals.append(_route_journal(occurrence, next_state.state_root))
        current = next_state
    effect_plan = replace(
        GlobalEconomicEffectPlanV1.empty(),
        occurrence_consumptions=tuple(
            sorted(occurrence.occurrence_id for occurrence in occurrences)
        ),
    )
    return GlobalEconomicStateEffectRefinementCandidateV1(
        pre,
        current,
        effect_plan,
        tuple(occurrences),
        tuple(journals),
    )


def _replace_amount(
    state: GlobalEconomicStateV1,
    field: str,
    owner: str,
    atoms: int,
) -> GlobalEconomicStateV1:
    rows = tuple(
        replace(row, amount_atoms=atoms) if row.owner == owner else row
        for row in getattr(state, field)
    )
    return replace(state, **{field: rows})


def test_refinement_matches_cross_language_golden_root() -> None:
    candidate = _candidate()

    refinement = refine_global_economic_state_effects_v1(candidate)

    assert refinement.pre_state_root == candidate.pre_state.state_root
    assert refinement.post_state_root == candidate.post_state.state_root
    assert refinement.effect_plan_root == candidate.effect_plan.effect_plan_root
    assert refinement.refinement_root == (
        "0x5026263a651e46d40e4ee6d818c3e222a7d36f484ac48a180500047f51725fdc"
    )


@pytest.mark.parametrize(
    ("field", "owner", "atoms", "message"),
    (
        ("balances", "alice", 96, "balance delta mismatch"),
        ("custody", "pool", 45, "custody delta mismatch"),
        ("liabilities", "vault", 12, "liability delta mismatch"),
        ("reserves", "treasury", 7, "reserve delta mismatch"),
    ),
)
def test_refinement_rejects_each_amount_table_one_defect(
    field: str,
    owner: str,
    atoms: int,
    message: str,
) -> None:
    candidate = _candidate()
    post_state = _replace_amount(candidate.post_state, field, owner, atoms)

    with pytest.raises(ValueError, match=message):
        refine_global_economic_state_effects_v1(replace(candidate, post_state=post_state))


def test_refinement_rejects_supply_and_lane_write_substitution() -> None:
    candidate = _candidate()
    wrong_supply = replace(candidate.post_state, supplies=(AssetSupplyV1("USD", 179),))
    wrong_lane = replace(
        candidate.effect_plan,
        lane_writes=(LaneWriteV1(LaneIdV1.ASSET_TRANSFER, _root(2_001), _root(9_002)),),
    )

    with pytest.raises(ValueError, match="supply delta mismatch"):
        refine_global_economic_state_effects_v1(replace(candidate, post_state=wrong_supply))
    with pytest.raises(ValueError, match="lane write mismatch"):
        refine_global_economic_state_effects_v1(replace(candidate, effect_plan=wrong_lane))


def test_refinement_rejects_self_consistent_wrong_conservation_claim() -> None:
    candidate = _candidate()
    wrong = replace(
        candidate.effect_plan,
        asset_conservation=(AssetConservationRowV1("USD", 176, 179, 176, 179, 7, 4),),
    )

    with pytest.raises(ValueError, match="conservation state mismatch"):
        refine_global_economic_state_effects_v1(replace(candidate, effect_plan=wrong))


def test_refinement_requires_fee_label_to_mirror_real_value_delta() -> None:
    candidate = _candidate()
    rows = tuple(
        replace(row, principal="unfunded-fee")
        if row.kind is EconomicEffectKindV1.FEE_ALLOCATION
        else row
        for row in candidate.effect_plan.rows
    )
    wrong = replace(candidate.effect_plan, rows=tuple(sorted(rows, key=lambda row: row.key)))

    with pytest.raises(ValueError, match="fee allocation is not mirrored"):
        refine_global_economic_state_effects_v1(replace(candidate, effect_plan=wrong))


def test_fee_mirror_accepts_netted_destination_increase_and_rejects_predecessor() -> None:
    # Arrange
    candidate = _candidate()

    def with_treasury_delta(
        delta_atoms: int,
    ) -> GlobalEconomicStateEffectRefinementCandidateV1:
        alice_delta = -3 - delta_atoms
        rows = tuple(
            replace(
                row,
                delta_atoms=(
                    alice_delta if row.principal == "alice" else delta_atoms
                ),
            )
            if row.kind is EconomicEffectKindV1.ACCOUNT_MOVEMENT
            and row.principal in {"alice", "treasury"}
            else row
            for row in candidate.effect_plan.rows
        )
        post_state = replace(
            candidate.post_state,
            balances=_amounts(
                ("alice", "USD", "accounts", 100 + alice_delta),
                ("bob", "USD", "accounts", 10),
                ("treasury", "USD", "accounts", delta_atoms),
            ),
        )
        return replace(
            candidate,
            post_state=post_state,
            effect_plan=replace(
                candidate.effect_plan,
                rows=tuple(sorted(rows, key=lambda row: row.key)),
            ),
        )

    aggregate = with_treasury_delta(3)
    predecessor = with_treasury_delta(1)

    # Act / Assert
    refine_global_economic_state_effects_v1(aggregate)
    with pytest.raises(ValueError, match="fee allocation is not mirrored"):
        refine_global_economic_state_effects_v1(predecessor)


def test_fee_mirror_sums_cross_kind_deltas_before_accepting_allocation() -> None:
    # Arrange: the destination gains ten custody atoms while losing eight
    # balance atoms under the same economic key. Its net increase is only two.
    candidate = _candidate()
    pre_state = replace(
        candidate.pre_state,
        balances=_amounts(
            ("alice", "USD", "accounts", 100),
            ("treasury", "USD", "accounts", 10),
        ),
        supplies=(AssetSupplyV1("USD", 185),),
    )
    post_state = replace(
        candidate.post_state,
        custody=_amounts(
            ("burn-bucket", "USD", "protocol-burn", 16),
            ("escrow", "USD", "strategy-escrow", 5),
            ("pool", "USD", "amm-pool", 44),
            ("treasury", "USD", "accounts", 10),
        ),
        supplies=(AssetSupplyV1("USD", 188),),
    )
    rows = tuple(
        replace(row, delta_atoms=-8)
        if row.kind is EconomicEffectKindV1.ACCOUNT_MOVEMENT
        and row.principal == "treasury"
        and row.custody_domain == "accounts"
        else replace(row, delta_atoms=10)
        if row.kind is EconomicEffectKindV1.FEE_ALLOCATION
        else row
        for row in candidate.effect_plan.rows
    ) + (
        EconomicEffectRowV1(
            EconomicEffectKindV1.CUSTODY,
            "treasury",
            "USD",
            "accounts",
            10,
        ),
    )
    effect_plan = replace(
        candidate.effect_plan,
        rows=tuple(sorted(rows, key=lambda row: row.key)),
        asset_conservation=(AssetConservationRowV1("USD", 185, 188, 185, 188, 7, 4),),
        fee_conservation=(FeeConservationRowV1("USD", 10, 10, 0),),
    )

    # Act / Assert: last-write-wins would observe +10 and accept; exact
    # cross-kind aggregation observes -8 + 10 = +2 and rejects the +10 label.
    with pytest.raises(ValueError, match="fee allocation is not mirrored"):
        refine_global_economic_state_effects_v1(
            replace(
                candidate,
                pre_state=pre_state,
                post_state=post_state,
                effect_plan=effect_plan,
            )
        )


def test_refinement_accepts_fee_residue_in_exact_named_reserve() -> None:
    candidate = _fee_residue_candidate()

    refinement = refine_global_economic_state_effects_v1(candidate)

    assert refinement.pre_state_root == candidate.pre_state.state_root
    assert refinement.post_state_root == candidate.post_state.state_root
    assert refinement.refinement_root == (
        "0x58da8bc5aed457f0b938e0e73318d58b59c1b62afd46dd7046e10009770307c6"
    )


def test_refinement_matches_shared_fee_residue_golden_vector() -> None:
    vector = json.loads(FEE_RESIDUE_VECTOR.read_text(encoding="utf-8"))
    candidate = _fee_residue_candidate(
        principal=vector["principal"],
        control_domain=vector["control_domain"],
        effect_atoms=int(vector["reserve_effect_delta_atoms"]),
    )

    refinement = refine_global_economic_state_effects_v1(candidate)

    assert vector["schema"] == "zenodex/global-economic-state-fee-residue-vector/v1"
    assert candidate.pre_state.reserves[0].amount_atoms == int(vector["pre_reserve_atoms"])
    assert candidate.post_state.reserves[0].amount_atoms == int(vector["post_reserve_atoms"])
    assert candidate.effect_plan.fee_conservation[0].fee_charged_atoms == int(
        vector["fee_charged_atoms"]
    )
    assert candidate.effect_plan.fee_conservation[0].current_allocations_atoms == int(
        vector["current_allocations_atoms"]
    )
    assert candidate.effect_plan.fee_conservation[0].carried_residue_atoms == int(
        vector["carried_residue_atoms"]
    )
    assert refinement.refinement_root == vector["expected_refinement_root"]


def test_refinement_rejects_fee_residue_without_state_bucket() -> None:
    candidate = _candidate()
    wrong = replace(
        candidate.effect_plan,
        fee_conservation=(FeeConservationRowV1("USD", 3, 2, 1),),
    )

    with pytest.raises(ValueError, match="fee residue state mapping mismatch"):
        refine_global_economic_state_effects_v1(replace(candidate, effect_plan=wrong))


@pytest.mark.parametrize(
    ("principal", "control_domain"),
    (
        ("wrong-residue-principal", FEE_RESIDUE_CONTROL_DOMAIN_V1),
        (FEE_RESIDUE_PRINCIPAL_V1, "wrong-residue-control-domain"),
    ),
)
def test_refinement_rejects_fee_residue_aliases(
    principal: str,
    control_domain: str,
) -> None:
    candidate = _fee_residue_candidate(
        principal=principal,
        control_domain=control_domain,
    )

    with pytest.raises(ValueError, match="fee residue state mapping mismatch"):
        refine_global_economic_state_effects_v1(candidate)


def test_refinement_rejects_fee_residue_amount_mismatch() -> None:
    candidate = _fee_residue_candidate(effect_atoms=2)

    with pytest.raises(ValueError, match="fee residue state mapping mismatch"):
        refine_global_economic_state_effects_v1(candidate)


def test_refinement_rejects_fee_residue_when_reserve_state_delta_disagrees() -> None:
    candidate = _fee_residue_candidate()
    wrong_post = replace(
        candidate.post_state,
        reserves=_amounts(
            (
                FEE_RESIDUE_PRINCIPAL_V1,
                "USD",
                FEE_RESIDUE_CONTROL_DOMAIN_V1,
                7,
            )
        ),
    )

    with pytest.raises(ValueError):
        refine_global_economic_state_effects_v1(replace(candidate, post_state=wrong_post))


def test_refinement_accepts_fee_residue_at_signed_effect_maximum() -> None:
    candidate = fee_residue_flow_candidate_v1(
        (FeeResidueFlowCaseV1("USD", MAX_DELTA_ATOMS_V1),)
    )

    refinement = refine_global_economic_state_effects_v1(candidate)

    assert refinement.pre_state_root == candidate.pre_state.state_root
    assert refinement.post_state_root == candidate.post_state.state_root


def test_refinement_rejects_fee_residue_above_signed_effect_maximum() -> None:
    with pytest.raises(ValueError, match="signed 128-bit integer"):
        fee_residue_flow_candidate_v1(
            (FeeResidueFlowCaseV1("USD", MAX_DELTA_ATOMS_V1 + 1),)
        )


def test_refinement_accepts_two_asset_fee_residue_in_canonical_order() -> None:
    candidate = fee_residue_flow_candidate_v1(
        (
            FeeResidueFlowCaseV1("ASSET-A", 1),
            FeeResidueFlowCaseV1("ASSET-B", 2),
        )
    )

    refinement = refine_global_economic_state_effects_v1(candidate)

    assert tuple(row.asset for row in candidate.effect_plan.fee_conservation) == (
        "ASSET-A",
        "ASSET-B",
    )
    assert refinement.effect_plan_root == candidate.effect_plan.effect_plan_root


def test_refinement_rejects_reversed_two_asset_fee_residue_order() -> None:
    candidate = fee_residue_flow_candidate_v1(
        (
            FeeResidueFlowCaseV1("ASSET-A", 1),
            FeeResidueFlowCaseV1("ASSET-B", 2),
        )
    )
    with pytest.raises(ValueError, match="canonically ordered and unique"):
        replace(
            candidate.effect_plan,
            fee_conservation=tuple(reversed(candidate.effect_plan.fee_conservation)),
        )


def test_refinement_rejects_duplicate_exact_fee_residue_effect() -> None:
    candidate = fee_residue_flow_candidate_v1((FeeResidueFlowCaseV1("USD", 1),))
    residue = next(
        row
        for row in candidate.effect_plan.rows
        if row.kind is EconomicEffectKindV1.RESERVE
    )

    with pytest.raises(ValueError, match="canonically ordered and unique"):
        replace(
            candidate.effect_plan,
            rows=tuple(sorted((*candidate.effect_plan.rows, residue), key=lambda row: row.key)),
        )


def test_refinement_rejects_orphan_positive_fee_residue_reserve() -> None:
    candidate = fee_residue_flow_candidate_v1((FeeResidueFlowCaseV1("USD", 1),))
    orphan = replace(candidate.effect_plan, fee_conservation=())

    with pytest.raises(ValueError, match="fee residue state mapping mismatch"):
        refine_global_economic_state_effects_v1(replace(candidate, effect_plan=orphan))


def test_refinement_rejects_same_plan_carry_and_spend_but_accepts_later_spend() -> None:
    carry = fee_residue_flow_candidate_v1((FeeResidueFlowCaseV1("USD", 1),))
    refine_global_economic_state_effects_v1(carry)
    later_spend = fee_residue_full_spend_candidate_v1(carry.post_state, asset="USD")

    later_refinement = refine_global_economic_state_effects_v1(later_spend)

    assert later_refinement.pre_state_root == carry.post_state.state_root
    combined = fee_residue_flow_candidate_v1((FeeResidueFlowCaseV1("USD", 1, 1),))
    with pytest.raises(ValueError, match="fee residue state mapping mismatch"):
        refine_global_economic_state_effects_v1(combined)


def test_refinement_rejects_zero_fee_conservation_row() -> None:
    state = _pre_state()
    effects = replace(
        GlobalEconomicEffectPlanV1.empty(),
        fee_conservation=(FeeConservationRowV1("USD", 0, 0, 0),),
    )

    with pytest.raises(ValueError, match="zero fee conservation row is non-canonical"):
        refine_global_economic_state_effects_v1(
            GlobalEconomicStateEffectRefinementCandidateV1(state, state, effects)
        )


@pytest.mark.parametrize("kind", (EconomicEffectKindV1.REWARD, EconomicEffectKindV1.SLASH))
def test_refinement_rejects_unmapped_reward_and_slash_labels(
    kind: EconomicEffectKindV1,
) -> None:
    candidate = _candidate()
    rows = tuple(
        sorted(
            (
                *candidate.effect_plan.rows,
                EconomicEffectRowV1(kind, "actor", "USD", "accounts", 1),
            ),
            key=lambda row: row.key,
        )
    )
    wrong = replace(candidate.effect_plan, rows=rows)

    with pytest.raises(ValueError, match="reward and slash labels are unmapped"):
        refine_global_economic_state_effects_v1(replace(candidate, effect_plan=wrong))


@pytest.mark.parametrize(
    "post_change",
    (
        {"history_root": _root(7_001)},
        {"oracle_occurrences": (OracleOccurrenceStateV1("oracle", _root(7_002), 41, True),)},
        {
            "terminal_obligations": (
                TerminalObligationV1(
                    "claim",
                    LaneIdV1.ZUSD_MONETARY,
                    "alice",
                    "USD",
                    1,
                    TerminalObligationStatusV1.OPEN,
                ),
            )
        },
        {
            "outbox": (
                OutboxStateV1(
                    _root(7_004),
                    "bridge:test",
                    _root(7_005),
                    _root(7_006),
                    OutboxStatusV1.PENDING,
                ),
            )
        },
    ),
)
def test_refinement_rejects_unsupported_global_field_change(
    post_change: dict[str, object],
) -> None:
    candidate = _candidate()

    with pytest.raises(ValueError, match="unsupported global field changed"):
        refine_global_economic_state_effects_v1(
            replace(
                candidate,
                post_state=replace(
                    candidate.post_state,
                    **post_change,
                ),
            )
        )


def test_refinement_height_progression_is_zero_for_static_and_one_for_epoch() -> None:
    static = _candidate()
    with pytest.raises(ValueError, match="state height progression mismatch"):
        refine_global_economic_state_effects_v1(
            replace(static, post_state=replace(static.post_state, height=42))
        )

    epoch = _replay_candidate()
    with pytest.raises(ValueError, match="state height progression mismatch"):
        refine_global_economic_state_effects_v1(
            replace(epoch, post_state=replace(epoch.post_state, height=41))
        )

    with pytest.raises(ValueError, match="state height overflow"):
        refine_global_economic_state_effects_v1(
            replace(
                epoch,
                pre_state=replace(epoch.pre_state, height=(1 << 64) - 1),
                post_state=replace(epoch.post_state, height=(1 << 64) - 1),
            )
        )


def test_refinement_rejects_external_outbox_until_commit_binding_exists() -> None:
    candidate = _candidate()
    wrong = replace(
        candidate.effect_plan,
        external_outbox_enqueue=(
            ExternalOutboxEnqueueV1(
                _root(8_001),
                "bridge:test",
                _root(8_002),
                _root(8_003),
            ),
        ),
    )

    with pytest.raises(ValueError, match="external outbox refinement is unavailable"):
        refine_global_economic_state_effects_v1(replace(candidate, effect_plan=wrong))


def test_refinement_rejects_occurrence_without_replay_application() -> None:
    candidate = _candidate()
    wrong = replace(
        candidate.effect_plan,
        occurrence_consumptions=(_root(5_000),),
    )

    with pytest.raises(ValueError, match="occurrence disclosure mismatch"):
        refine_global_economic_state_effects_v1(replace(candidate, effect_plan=wrong))


def test_replay_refinement_derives_subject_nonce_identity_and_exact_post_row() -> None:
    candidate = _replay_candidate()
    occurrence = candidate.consumed_occurrences[0]

    refinement = refine_global_economic_state_effects_v1(candidate)

    assert occurrence.replay_id == (
        "0xf417802071c3267b5954ae64c2a3b74195af67dbf8f8123d0f4f9a24760a2f4b"
    )
    assert candidate.post_state.replay_state == (
        ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id),
    )
    assert refinement.post_state_root == candidate.post_state.state_root


def test_replay_refinement_rejects_missing_or_substituted_occurrence_disclosure() -> None:
    candidate = _replay_candidate()
    substituted = _occurrence(nonce=12)

    with pytest.raises(ValueError, match="occurrence disclosure mismatch"):
        refine_global_economic_state_effects_v1(
            replace(candidate, consumed_occurrences=(), route_journals=())
        )
    with pytest.raises(ValueError, match="occurrence disclosure mismatch"):
        refine_global_economic_state_effects_v1(
            replace(candidate, consumed_occurrences=(substituted,))
        )


def test_replay_refinement_rejects_missing_extra_or_mutated_post_row() -> None:
    candidate = _replay_candidate()
    expected = candidate.post_state.replay_state[0]

    with pytest.raises(ValueError, match="replay state delta mismatch"):
        refine_global_economic_state_effects_v1(
            _with_replay_post(candidate, ())
        )
    with pytest.raises(ValueError, match="replay state delta mismatch"):
        refine_global_economic_state_effects_v1(
            replace(
                _candidate(),
                post_state=replace(
                    _candidate().post_state,
                    replay_state=(ReplayStateV1("unexpected", _root(7_003)),),
                ),
            )
        )
    with pytest.raises(ValueError, match="replay state delta mismatch"):
        refine_global_economic_state_effects_v1(
            _with_replay_post(
                candidate,
                (replace(expected, occurrence_id=_root(7_004)),),
            )
        )


def test_replay_refinement_rejects_cross_context_and_previously_consumed_nonce() -> None:
    foreign = _occurrence(chain_id="foreign-chain")
    foreign_candidate = _replay_candidate(foreign)
    candidate = _replay_candidate()
    replay = candidate.post_state.replay_state[0]
    replayed_pre = replace(candidate.pre_state, replay_state=(replay,))
    replayed_occurrence = _occurrence(pre_state_root=replayed_pre.state_root)
    replayed_effects = replace(
        candidate.effect_plan,
        occurrence_consumptions=(replayed_occurrence.occurrence_id,),
    )
    replayed_post = replace(candidate.post_state, replay_state=(replay,))
    replayed = GlobalEconomicStateEffectRefinementCandidateV1(
        replayed_pre,
        replayed_post,
        replayed_effects,
        (replayed_occurrence,),
        (_route_journal(replayed_occurrence, replayed_post.state_root),),
    )

    with pytest.raises(ValueError, match="occurrence state context mismatch"):
        refine_global_economic_state_effects_v1(foreign_candidate)
    with pytest.raises(ValueError, match="replay identity already consumed"):
        refine_global_economic_state_effects_v1(replayed)


@pytest.mark.parametrize(
    "override",
    (
        {"deployment_root": _root(91_001)},
        {"profile_root": _root(91_002)},
        {"height": 40},
        {"pre_state_root": _root(91_003)},
    ),
)
def test_replay_refinement_rejects_each_execution_context_mutant(
    override: dict[str, object],
) -> None:
    occurrence = replace(_occurrence(), **override)

    with pytest.raises(ValueError, match="occurrence state context mismatch"):
        refine_global_economic_state_effects_v1(_replay_candidate(occurrence))


@pytest.mark.parametrize(
    "override",
    (
        {"chain_id": "foreign-chain"},
        {"deployment_root": _root(93_001)},
        {"profile_root": _root(93_002)},
        {"writer_epoch": 18},
        {"route_release_id": _root(93_003)},
        {"command_occurrence_id": _root(93_004)},
        {"pre_state_root": _root(93_005)},
    ),
)
def test_replay_refinement_rejects_each_route_chain_context_mutant(
    override: dict[str, object],
) -> None:
    candidate = _replay_candidate()
    journal = replace(candidate.route_journals[0], **override)

    with pytest.raises(ValueError, match="occurrence state context mismatch"):
        refine_global_economic_state_effects_v1(
            replace(candidate, route_journals=(journal,))
        )


def test_replay_refinement_rejects_route_chain_count_and_terminal_mutants() -> None:
    candidate = _replay_candidate()
    terminal = replace(candidate.route_journals[0], post_state_root=_root(93_006))

    with pytest.raises(ValueError, match="route-state chain count mismatch"):
        refine_global_economic_state_effects_v1(
            replace(candidate, route_journals=())
        )
    with pytest.raises(ValueError, match="route-state chain terminal mismatch"):
        refine_global_economic_state_effects_v1(
            replace(candidate, route_journals=(terminal,))
        )


def test_replay_refinement_rejects_reordered_execution_history() -> None:
    candidate = _replay_batch(2)

    with pytest.raises(ValueError, match="occurrence order mismatch"):
        refine_global_economic_state_effects_v1(
            replace(
                candidate,
                consumed_occurrences=tuple(reversed(candidate.consumed_occurrences)),
                route_journals=tuple(reversed(candidate.route_journals)),
            )
        )


@pytest.mark.parametrize("nonce", (0, (1 << 64) - 1))
def test_replay_refinement_accepts_nonce_unsigned_64_bit_boundaries(nonce: int) -> None:
    candidate = _replay_candidate(_occurrence(nonce=nonce))

    refinement = refine_global_economic_state_effects_v1(candidate)

    assert refinement.post_state_root == candidate.post_state.state_root


@pytest.mark.parametrize("count", (0, 1, 64))
def test_replay_refinement_accepts_zero_one_and_sixty_four_disclosures(
    count: int,
) -> None:
    candidate = _replay_batch(count)

    refinement = refine_global_economic_state_effects_v1(candidate)

    assert refinement.post_state_root == candidate.post_state.state_root


def test_replay_refinement_rejects_sixty_five_disclosures_before_chain_work() -> None:
    with pytest.raises(ValueError, match="occurrence count exceeds epoch bound"):
        refine_global_economic_state_effects_v1(_replay_batch(65))


def test_replay_refinement_preserves_unrelated_preexisting_replay_row() -> None:
    pre = replace(
        _pre_state(),
        replay_state=(ReplayStateV1("legacy-unrelated", _root(92_001)),),
    )
    candidate = _replay_batch(1, pre_state=pre)

    refine_global_economic_state_effects_v1(candidate)

    assert ReplayStateV1("legacy-unrelated", _root(92_001)) in (
        candidate.post_state.replay_state
    )


def test_two_occurrence_replay_refinement_has_cross_language_golden_root() -> None:
    refinement = refine_global_economic_state_effects_v1(_replay_batch(2))

    assert refinement.refinement_root == (
        "0x04a52daea5b87169f428fc698537e115fa14330a1eea885db0e8db7a7b503517"
    )


def test_replay_refinement_rejects_duplicate_subject_nonce_under_distinct_occurrences() -> None:
    first = _occurrence(command_kind="TRANSFER")
    first_row = ReplayStateV1(first.replay_id, first.occurrence_id)
    intermediate = replace(_pre_state(), height=42, replay_state=(first_row,))
    second = _occurrence(
        command_kind="MANAGED_BURN",
        tx_index=4,
        pre_state_root=intermediate.state_root,
    )
    occurrences = (first, second)
    effects = replace(
        _effect_plan(),
        occurrence_consumptions=tuple(sorted(item.occurrence_id for item in occurrences)),
    )
    post = replace(
        _post_state(),
        height=42,
        replay_state=(first_row,),
    )

    with pytest.raises(ValueError, match="duplicate replay identity"):
        refine_global_economic_state_effects_v1(
            GlobalEconomicStateEffectRefinementCandidateV1(
                _pre_state(),
                post,
                effects,
                occurrences,
                (
                    _route_journal(first, intermediate.state_root),
                    _route_journal(second, post.state_root),
                ),
            )
        )


def test_replay_refinement_rejects_hostile_scalar_subclasses_before_comparison() -> None:
    class AlwaysEqual(str):
        def __eq__(self, other: object) -> bool:
            return True

        __hash__ = str.__hash__

    occurrence_candidate = _replay_candidate()
    object.__setattr__(
        occurrence_candidate.consumed_occurrences[0],
        "chain_id",
        AlwaysEqual("foreign-chain"),
    )
    state_candidate = _candidate()
    object.__setattr__(state_candidate.pre_state, "chain_id", AlwaysEqual("foreign-chain"))

    with pytest.raises(TypeError, match="must be an exact primitive"):
        refine_global_economic_state_effects_v1(occurrence_candidate)
    with pytest.raises(TypeError, match="must be an exact primitive"):
        refine_global_economic_state_effects_v1(state_candidate)


def test_replay_refinement_rejects_hostile_string_enum_before_comparison() -> None:
    from enum import Enum

    class AlwaysEqualEnum(str, Enum):
        FORGED = _root(99_001)

        def __eq__(self, other: object) -> bool:
            return True

        __hash__ = str.__hash__

    candidate = _replay_candidate()
    object.__setattr__(
        candidate.post_state.replay_state[0],
        "occurrence_id",
        AlwaysEqualEnum.FORGED,
    )

    with pytest.raises(TypeError, match="must be an exact primitive"):
        refine_global_economic_state_effects_v1(candidate)


def test_global_state_rejects_one_occurrence_under_two_replay_aliases() -> None:
    occurrence_id = _root(90_001)

    with pytest.raises(ValueError, match="replay occurrence ids must be unique"):
        replace(
            _pre_state(),
            replay_state=(
                ReplayStateV1("alias-a", occurrence_id),
                ReplayStateV1("alias-b", occurrence_id),
            ),
        )


def test_refinement_uses_one_owned_snapshot_under_retained_alias_mutation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    expected = refine_global_economic_state_effects_v1(_candidate())
    candidate = _candidate()
    original_derive = refinement_module._derive_global_economic_state_delta_v1

    def mutate_retained_alias_then_derive(
        pre_state: GlobalEconomicStateV1,
        post_state: GlobalEconomicStateV1,
        effect_plan: GlobalEconomicEffectPlanV1,
        replay_insertions: tuple[ReplayStateV1, ...],
    ) -> object:
        object.__setattr__(candidate.post_state.balances[0], "amount_atoms", 94)
        return original_derive(
            pre_state,
            post_state,
            effect_plan,
            replay_insertions,
        )

    monkeypatch.setattr(
        refinement_module,
        "_derive_global_economic_state_delta_v1",
        mutate_retained_alias_then_derive,
    )

    actual = refinement_module.refine_global_economic_state_effects_v1(candidate)

    assert candidate.post_state.balances[0].amount_atoms == 94
    assert actual.refinement_root == expected.refinement_root


def test_refinement_rejects_lane_metadata_and_owned_supply_drift() -> None:
    candidate = _candidate()
    lane = candidate.post_state.lane_roots[0]
    metadata_state = replace(
        candidate.post_state,
        lane_roots=(replace(lane, enabled=False), *candidate.post_state.lane_roots[1:]),
    )
    supply_pre = replace(candidate.pre_state, supplies=(AssetSupplyV1("USD", 180),))
    supply_post = replace(candidate.post_state, supplies=(AssetSupplyV1("USD", 183),))
    conservation = replace(
        candidate.effect_plan,
        asset_conservation=(AssetConservationRowV1("USD", 175, 178, 180, 183, 7, 4),),
    )

    with pytest.raises(ValueError, match="unsupported lane metadata changed"):
        refine_global_economic_state_effects_v1(
            replace(candidate, post_state=metadata_state)
        )
    with pytest.raises(ValueError, match="owned total does not equal supply"):
        refine_global_economic_state_effects_v1(
            GlobalEconomicStateEffectRefinementCandidateV1(
                supply_pre,
                supply_post,
                conservation,
            )
        )


def test_refinement_rejects_unchanged_preexisting_owned_supply_drift() -> None:
    state = _replace_amount(_pre_state(), "balances", "alice", 101)

    with pytest.raises(ValueError, match="owned total does not equal supply"):
        refine_global_economic_state_effects_v1(
            GlobalEconomicStateEffectRefinementCandidateV1(
                state,
                state,
                GlobalEconomicEffectPlanV1.empty(),
            )
        )


def test_refinement_allows_exact_burn_to_zero_supply() -> None:
    candidate = _candidate()
    pre = replace(
        candidate.pre_state,
        balances=_amounts(("alice", "USD", "accounts", 1)),
        supplies=(AssetSupplyV1("USD", 1),),
        custody=(),
        liabilities=(),
        reserves=(),
    )
    post = replace(
        candidate.post_state,
        balances=(),
        supplies=(AssetSupplyV1("USD", 0),),
        custody=(),
        liabilities=(),
        reserves=(),
    )
    effects = GlobalEconomicEffectPlanV1(
        rows=(
            EconomicEffectRowV1(
                EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                "alice",
                "USD",
                "accounts",
                -1,
            ),
            EconomicEffectRowV1(
                EconomicEffectKindV1.BURN,
                "supply",
                "USD",
                "supply",
                -1,
            ),
        ),
        asset_conservation=(AssetConservationRowV1("USD", 1, 0, 1, 0, 0, 1),),
        fee_conservation=(),
        lane_writes=(LaneWriteV1(LaneIdV1.ASSET_TRANSFER, _root(2_001), _root(9_001)),),
        occurrence_consumptions=(),
        external_outbox_enqueue=(),
    )

    refinement = refine_global_economic_state_effects_v1(
        GlobalEconomicStateEffectRefinementCandidateV1(pre, post, effects)
    )

    assert refinement.post_state_root == post.state_root


def test_refinement_aggregates_issue_and_burn_without_signed_order_overflow() -> None:
    pre = _pre_state()
    post = replace(pre, lane_roots=_lane_roots(asset_root=9_001))
    boundary = 1 << 127
    effects = GlobalEconomicEffectPlanV1(
        rows=(
            EconomicEffectRowV1(
                EconomicEffectKindV1.BURN,
                "burn-all",
                "USD",
                "supply",
                -boundary,
            ),
            EconomicEffectRowV1(
                EconomicEffectKindV1.ISSUE,
                "issue-a",
                "USD",
                "supply",
                boundary - 1,
            ),
            EconomicEffectRowV1(
                EconomicEffectKindV1.ISSUE,
                "issue-b",
                "USD",
                "supply",
                1,
            ),
        ),
        asset_conservation=(
            AssetConservationRowV1("USD", 175, 175, 175, 175, boundary, boundary),
        ),
        fee_conservation=(),
        lane_writes=(LaneWriteV1(LaneIdV1.ASSET_TRANSFER, _root(2_001), _root(9_001)),),
        occurrence_consumptions=(),
        external_outbox_enqueue=(),
    )

    refinement = refine_global_economic_state_effects_v1(
        GlobalEconomicStateEffectRefinementCandidateV1(pre, post, effects)
    )

    assert refinement.effect_plan_root == effects.effect_plan_root


def test_refinement_signed_delta_bva_and_owned_total_overflow() -> None:
    candidate = _candidate()
    maximum_delta = (1 << 127) - 1
    pre = replace(
        candidate.pre_state,
        balances=(),
        supplies=(AssetSupplyV1("USD", 0),),
        custody=(),
        liabilities=(),
        reserves=(),
    )
    post = replace(
        candidate.post_state,
        balances=_amounts(("alice", "USD", "accounts", maximum_delta)),
        supplies=(AssetSupplyV1("USD", maximum_delta),),
        custody=(),
        liabilities=(),
        reserves=(),
    )
    effects = GlobalEconomicEffectPlanV1(
        rows=(
            EconomicEffectRowV1(
                EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                "alice",
                "USD",
                "accounts",
                maximum_delta,
            ),
            EconomicEffectRowV1(
                EconomicEffectKindV1.ISSUE,
                "supply",
                "USD",
                "supply",
                maximum_delta,
            ),
        ),
        asset_conservation=(
            AssetConservationRowV1(
                "USD",
                0,
                maximum_delta,
                0,
                maximum_delta,
                maximum_delta,
                0,
            ),
        ),
        fee_conservation=(),
        lane_writes=(LaneWriteV1(LaneIdV1.ASSET_TRANSFER, _root(2_001), _root(9_001)),),
        occurrence_consumptions=(),
        external_outbox_enqueue=(),
    )

    refine_global_economic_state_effects_v1(
        GlobalEconomicStateEffectRefinementCandidateV1(pre, post, effects)
    )

    adjacent_post = replace(
        post,
        balances=_amounts(("alice", "USD", "accounts", 1 << 127)),
        supplies=(AssetSupplyV1("USD", 1 << 127),),
    )
    lane_only = GlobalEconomicEffectPlanV1(
        rows=(),
        asset_conservation=(),
        fee_conservation=(),
        lane_writes=(LaneWriteV1(LaneIdV1.ASSET_TRANSFER, _root(2_001), _root(9_001)),),
        occurrence_consumptions=(),
        external_outbox_enqueue=(),
    )
    with pytest.raises(ValueError, match="state delta exceeds signed 128-bit bounds"):
        refine_global_economic_state_effects_v1(
            GlobalEconomicStateEffectRefinementCandidateV1(pre, adjacent_post, lane_only)
        )

    overflow_state = replace(
        candidate.pre_state,
        balances=_amounts(("alice", "USD", "accounts", MAX_ATOMS_V1)),
        supplies=(AssetSupplyV1("USD", MAX_ATOMS_V1),),
        custody=_amounts(("pool", "USD", "amm-pool", 1)),
        liabilities=(),
        reserves=(),
    )
    with pytest.raises(ValueError, match="owned total exceeds unsigned 128-bit bounds"):
        refine_global_economic_state_effects_v1(
            GlobalEconomicStateEffectRefinementCandidateV1(
                overflow_state,
                overflow_state,
                GlobalEconomicEffectPlanV1.empty(),
            )
        )


def test_refinement_rejects_zero_amount_rows_and_hostile_mutation() -> None:
    candidate = _candidate()
    zero_row = EconomicAmountV1("ghost", "USD", "accounts", 0)
    zero_state = replace(
        candidate.post_state,
        balances=tuple(sorted((*candidate.post_state.balances, zero_row), key=lambda row: row.key)),
    )
    object.__setattr__(candidate.effect_plan.rows[0], "delta_atoms", 0)

    with pytest.raises(ValueError, match="effect delta must be nonzero"):
        refine_global_economic_state_effects_v1(candidate)
    with pytest.raises(ValueError, match="zero economic amount"):
        refine_global_economic_state_effects_v1(
            replace(_candidate(), post_state=zero_state)
        )

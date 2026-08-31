from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.asset_transfer_module_v2 import transition_asset_transfer_v2
from src.core.asset_transfer_types_v2 import (
    ASSET_ATOM_DECIMALS_V2,
    ASSET_TRANSFER_COMMAND_KIND_V2,
    AssetClassV2,
    AssetTransferAcceptedV2,
    AssetTransferCommandV2,
    AssetTransferContextV2,
    AssetTransferPolicyV2,
    AssetTransferStateV2,
)
from src.core.global_economic_lifecycle_plan_v2 import (
    derive_global_oracle_occurrence_plan_v2,
    derive_global_terminal_obligation_plan_v2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_economic_state_effect_refinement_v2 import (
    GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_AUTHORITY_V2,
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
    FEE_RESIDUE_CONTROL_DOMAIN_V2,
    FEE_RESIDUE_PRINCIPAL_V2,
    MAX_ATOMS_V2,
    ZERO_ROOT_V2,
    AssetConservationRowV2,
    AssetSupplyV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    ExternalOutboxEnqueueV2,
    FeeConservationRowV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    LaneWriteV2,
    OracleOccurrenceStateV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _lane_roots(
    replacements: dict[LaneIdV2, str] | None = None,
) -> tuple[LaneStateRootV2, ...]:
    selected = {} if replacements is None else replacements
    return tuple(
        LaneStateRootV2(
            lane_id=lane,
            module_release_id=_root(index + 1),
            enabled=lane is not LaneIdV2.EXTERNAL_CUSTODY,
            state_root=selected.get(lane, _root(index + 101)),
        )
        for index, lane in enumerate(ALL_LANE_IDS_V2)
    )


def _global_state(
    *,
    lane_roots: tuple[LaneStateRootV2, ...],
    height: int = 7,
    balances: tuple[EconomicAmountV2, ...] = (),
    supplies: tuple[AssetSupplyV2, ...] = (),
    custody: tuple[EconomicAmountV2, ...] = (),
    liabilities: tuple[EconomicAmountV2, ...] = (),
    reserves: tuple[EconomicAmountV2, ...] = (),
    oracle_occurrences: tuple[OracleOccurrenceStateV2, ...] = (),
    replay_state: tuple[ReplayStateV2, ...] = (),
    terminal_obligations: tuple[TerminalObligationV2, ...] = (),
    history_root: str = ZERO_ROOT_V2,
) -> GlobalEconomicStateV2:
    return GlobalEconomicStateV2(
        chain_id="zeno-v2-refinement",
        deployment_root=_root(201),
        writer_epoch=4,
        height=height,
        profile_root=_root(202),
        lane_roots=lane_roots,
        balances=balances,
        supplies=supplies,
        custody=custody,
        liabilities=liabilities,
        reserves=reserves,
        oracle_occurrences=oracle_occurrences,
        replay_state=replay_state,
        terminal_obligations=terminal_obligations,
        history_root=history_root,
        outbox=(),
    )


def _occurrence(
    pre_state: GlobalEconomicStateV2,
    *,
    command_kind: str,
    command_body_hash: str,
    subject: str = "alice",
    nonce: int = 1,
) -> EconomicCommandOccurrenceV2:
    return EconomicCommandOccurrenceV2(
        chain_id=pre_state.chain_id,
        deployment_root=pre_state.deployment_root,
        height=pre_state.height + 1,
        tx_index=0,
        op_index=0,
        command_kind=command_kind,
        command_body_hash=command_body_hash,
        route_release_id=_root(203),
        subject_id=subject,
        grant_root=_root(204),
        nonce=nonce,
        profile_root=pre_state.profile_root,
        pre_state_root=pre_state.state_root,
        consumed_object_ids=(),
    )


def _post_lane_roots(
    pre: GlobalEconomicStateV2,
    lane: LaneIdV2,
    post_root: str,
) -> tuple[LaneStateRootV2, ...]:
    return tuple(
        replace(row, state_root=post_root) if row.lane_id is lane else row
        for row in pre.lane_roots
    )


def _asset_transfer_candidate(
    *,
    fee_owner: str = "treasury",
) -> GlobalEconomicStateEffectRefinementCandidateV2:
    policy = AssetTransferPolicyV2(
        asset="USD",
        fee_owner=fee_owner,
        transfer_fee_atoms=2,
        enabled=True,
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(205),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
    )
    local_pre = AssetTransferStateV2(
        module_release_id=_root(1),
        policies=(policy,),
        balances=(EconomicAmountV2("alice", "USD", "accounts", 100),),
        supplies=(AssetSupplyV2("USD", 100),),
    )
    pre = _global_state(
        lane_roots=_lane_roots({LaneIdV2.ASSET_TRANSFER: local_pre.state_root}),
        balances=local_pre.balances,
        supplies=local_pre.supplies,
    )
    command = AssetTransferCommandV2(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V2,
        asset="USD",
        sender="alice",
        recipient="bob",
        amount_atoms=25,
        max_fee_atoms=2,
        asset_origin_root=_root(205),
    )
    occurrence = _occurrence(
        pre,
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
    )
    context = AssetTransferContextV2(
        writer_epoch=pre.writer_epoch,
        module_release_id=local_pre.module_release_id,
        global_pre_state_root=pre.state_root,
        occurrence=occurrence,
    )
    local_result = transition_asset_transfer_v2(context, local_pre, command)
    assert isinstance(local_result, AssetTransferAcceptedV2)
    post = _global_state(
        lane_roots=_post_lane_roots(
            pre,
            LaneIdV2.ASSET_TRANSFER,
            local_result.post_state.state_root,
        ),
        height=pre.height + 1,
        balances=local_result.post_state.balances,
        supplies=local_result.post_state.supplies,
        replay_state=(ReplayStateV2(occurrence.replay_id, occurrence.occurrence_id),),
    )
    return GlobalEconomicStateEffectRefinementCandidateV2(
        pre_state=pre,
        post_state=post,
        effect_plan=local_result.effects,
        consumed_occurrences=(occurrence,),
        terminal_plan=GlobalTerminalObligationPlanV2.empty(),
        oracle_plan=GlobalOracleOccurrencePlanV2.empty(),
    )


def test_asset_transfer_refines_exact_global_state_and_effects() -> None:
    candidate = _asset_transfer_candidate()
    witness = refine_global_economic_state_effects_v2(candidate)

    assert witness.pre_state_root == candidate.pre_state.state_root
    assert witness.post_state_root == candidate.post_state.state_root
    assert witness.effect_plan_root == candidate.effect_plan.effect_plan_root
    assert witness.production_authority == GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_AUTHORITY_V2


def test_refinement_candidate_getters_do_not_expose_authoritative_aliases() -> None:
    candidate = _asset_transfer_candidate()
    pre_root = candidate.pre_state.state_root
    effect_root = candidate.effect_plan.effect_plan_root
    occurrence_id = candidate.consumed_occurrences[0].occurrence_id

    borrowed_pre = candidate.pre_state
    borrowed_effects = candidate.effect_plan
    borrowed_occurrence = candidate.consumed_occurrences[0]
    object.__setattr__(borrowed_pre, "profile_root", _root(280))
    object.__setattr__(borrowed_effects, "lane_writes", ())
    object.__setattr__(borrowed_occurrence, "nonce", 999)

    assert candidate.pre_state.state_root == pre_root
    assert candidate.effect_plan.effect_plan_root == effect_root
    assert candidate.consumed_occurrences[0].occurrence_id == occurrence_id
    assert replace(candidate) == candidate


def test_zero_occurrence_static_state_has_one_exact_refinement() -> None:
    state = _global_state(lane_roots=_lane_roots())
    candidate = GlobalEconomicStateEffectRefinementCandidateV2(
        state,
        state,
        GlobalEconomicEffectPlanV2.empty(),
        (),
        GlobalTerminalObligationPlanV2.empty(),
        GlobalOracleOccurrencePlanV2.empty(),
    )

    witness = refine_global_economic_state_effects_v2(candidate)

    assert witness.pre_state_root == witness.post_state_root == state.state_root


def test_zero_occurrence_change_and_external_outbox_fail_closed() -> None:
    state = _global_state(lane_roots=_lane_roots())
    with pytest.raises(ValueError, match="zero-occurrence"):
        refine_global_economic_state_effects_v2(
            GlobalEconomicStateEffectRefinementCandidateV2(
                state,
                replace(state, height=state.height + 1),
                GlobalEconomicEffectPlanV2.empty(),
                (),
                GlobalTerminalObligationPlanV2.empty(),
                GlobalOracleOccurrencePlanV2.empty(),
            )
        )

    candidate = _asset_transfer_candidate()
    outbox_effects = GlobalEconomicEffectPlanV2(
        rows=candidate.effect_plan.rows,
        asset_conservation=candidate.effect_plan.asset_conservation,
        fee_conservation=candidate.effect_plan.fee_conservation,
        lane_writes=candidate.effect_plan.lane_writes,
        occurrence_consumptions=candidate.effect_plan.occurrence_consumptions,
        external_outbox_enqueue=(
            ExternalOutboxEnqueueV2(
                _root(260),
                "external:test",
                _root(261),
                _root(262),
            ),
        ),
    )
    with pytest.raises(ValueError, match="O-009 publisher"):
        refine_global_economic_state_effects_v2(
            replace(candidate, effect_plan=outbox_effects)
        )


def test_fee_annotation_requires_a_same_key_positive_state_credit() -> None:
    candidate = _asset_transfer_candidate(fee_owner="alice")

    with pytest.raises(ValueError, match="fee allocation is not mirrored"):
        refine_global_economic_state_effects_v2(candidate)


def test_zero_fee_conservation_row_is_noncanonical_at_global_refinement() -> None:
    candidate = _asset_transfer_candidate()
    effects = GlobalEconomicEffectPlanV2(
        rows=tuple(
            row
            for row in candidate.effect_plan.rows
            if row.kind is not EconomicEffectKindV2.FEE_ALLOCATION
        ),
        asset_conservation=candidate.effect_plan.asset_conservation,
        fee_conservation=(FeeConservationRowV2("USD", 0, 0, 0),),
        lane_writes=candidate.effect_plan.lane_writes,
        occurrence_consumptions=candidate.effect_plan.occurrence_consumptions,
        external_outbox_enqueue=(),
    )

    with pytest.raises(ValueError, match="zero fee conservation row"):
        refine_global_economic_state_effects_v2(
            replace(candidate, effect_plan=effects)
        )


def test_fee_residue_requires_the_designated_reserve_mapping() -> None:
    candidate = _asset_transfer_candidate()
    wrong_reserve = EconomicEffectRowV2(
        EconomicEffectKindV2.RESERVE,
        "reserve:wrong",
        "USD",
        "zenoledger:wrong-residue",
        2,
    )
    effects = GlobalEconomicEffectPlanV2(
        rows=tuple(
            sorted(
                (
                    *(
                        row
                        for row in candidate.effect_plan.rows
                        if row.kind is not EconomicEffectKindV2.FEE_ALLOCATION
                        and not (
                            row.kind is EconomicEffectKindV2.ACCOUNT_MOVEMENT
                            and row.principal == "treasury"
                        )
                    ),
                    wrong_reserve,
                ),
                key=lambda row: row.key,
            )
        ),
        asset_conservation=candidate.effect_plan.asset_conservation,
        fee_conservation=(FeeConservationRowV2("USD", 2, 0, 2),),
        lane_writes=candidate.effect_plan.lane_writes,
        occurrence_consumptions=candidate.effect_plan.occurrence_consumptions,
        external_outbox_enqueue=(),
    )
    post_state = replace(
        candidate.post_state,
        balances=tuple(
            row for row in candidate.post_state.balances if row.owner != "treasury"
        ),
        reserves=(
            EconomicAmountV2(
                "reserve:wrong",
                "USD",
                "zenoledger:wrong-residue",
                2,
            ),
        ),
    )

    with pytest.raises(ValueError, match="fee residue state mapping"):
        refine_global_economic_state_effects_v2(
            replace(candidate, post_state=post_state, effect_plan=effects)
        )

    correct_reserve = replace(
        wrong_reserve,
        principal=FEE_RESIDUE_PRINCIPAL_V2,
        custody_domain=FEE_RESIDUE_CONTROL_DOMAIN_V2,
    )
    correct_effects = replace(
        effects,
        rows=tuple(
            sorted(
                (
                    *(
                        row
                        for row in effects.rows
                        if row.principal != "reserve:wrong"
                    ),
                    correct_reserve,
                ),
                key=lambda row: row.key,
            )
        ),
    )
    correct_post_state = replace(
        post_state,
        reserves=(
            EconomicAmountV2(
                FEE_RESIDUE_PRINCIPAL_V2,
                "USD",
                FEE_RESIDUE_CONTROL_DOMAIN_V2,
                2,
            ),
        ),
    )
    assert refine_global_economic_state_effects_v2(
        replace(
            candidate,
            post_state=correct_post_state,
            effect_plan=correct_effects,
        )
    )


@pytest.mark.parametrize(
    ("mutation", "message"),
    (
        (
            lambda candidate: replace(
                candidate,
                post_state=replace(
                    candidate.post_state,
                    balances=(
                        EconomicAmountV2("alice", "USD", "accounts", 72),
                        EconomicAmountV2("bob", "USD", "accounts", 25),
                        EconomicAmountV2("treasury", "USD", "accounts", 2),
                    ),
                ),
            ),
            "balances state/effect mismatch",
        ),
        (
            lambda candidate: replace(
                candidate,
                post_state=replace(
                    candidate.post_state,
                    lane_roots=candidate.pre_state.lane_roots,
                ),
            ),
            "lane write",
        ),
        (
            lambda candidate: replace(
                candidate,
                post_state=replace(candidate.post_state, replay_state=()),
            ),
            "replay",
        ),
        (
            lambda candidate: replace(
                candidate,
                post_state=replace(candidate.post_state, history_root=_root(250)),
            ),
            "fixed context",
        ),
    ),
)
def test_global_refinement_mutants_fail_closed(
    mutation: object,
    message: str,
) -> None:
    candidate = _asset_transfer_candidate()
    mutated = mutation(candidate)  # type: ignore[operator]
    with pytest.raises(ValueError, match=message):
        refine_global_economic_state_effects_v2(mutated)


def test_supply_and_conservation_coverage_mutants_fail_closed() -> None:
    candidate = _asset_transfer_candidate()
    with pytest.raises(ValueError, match="supply issue/burn"):
        refine_global_economic_state_effects_v2(
            replace(
                candidate,
                post_state=replace(
                    candidate.post_state,
                    supplies=(AssetSupplyV2("USD", 99),),
                ),
            )
        )
    without_conservation = GlobalEconomicEffectPlanV2(
        rows=candidate.effect_plan.rows,
        asset_conservation=(),
        fee_conservation=candidate.effect_plan.fee_conservation,
        lane_writes=candidate.effect_plan.lane_writes,
        occurrence_consumptions=candidate.effect_plan.occurrence_consumptions,
        external_outbox_enqueue=(),
    )
    with pytest.raises(ValueError, match="conservation asset coverage"):
        refine_global_economic_state_effects_v2(
            replace(candidate, effect_plan=without_conservation)
        )


def test_liability_must_be_backed_even_for_a_static_candidate() -> None:
    state = _global_state(
        lane_roots=_lane_roots(),
        balances=(EconomicAmountV2("alice", "USD", "accounts", 7),),
        custody=(EconomicAmountV2("vault", "USD", "claims", 3),),
        liabilities=(EconomicAmountV2("alice", "USD", "claims", 4),),
        supplies=(AssetSupplyV2("USD", 10),),
    )
    candidate = GlobalEconomicStateEffectRefinementCandidateV2(
        state,
        state,
        GlobalEconomicEffectPlanV2.empty(),
        (),
        GlobalTerminalObligationPlanV2.empty(),
        GlobalOracleOccurrencePlanV2.empty(),
    )

    with pytest.raises(ValueError, match="liabilities exceed"):
        refine_global_economic_state_effects_v2(candidate)


def test_liability_total_overflow_across_domains_fails_before_backing() -> None:
    state = _global_state(
        lane_roots=_lane_roots(),
        balances=(EconomicAmountV2("carol", "EUR", "accounts", 1),),
        custody=(),
        liabilities=(
            EconomicAmountV2("alice", "USD", "claims-a", MAX_ATOMS_V2),
            EconomicAmountV2("bob", "USD", "claims-b", 1),
        ),
        supplies=(AssetSupplyV2("EUR", 1),),
    )
    candidate = GlobalEconomicStateEffectRefinementCandidateV2(
        state,
        state,
        GlobalEconomicEffectPlanV2.empty(),
        (),
        GlobalTerminalObligationPlanV2.empty(),
        GlobalOracleOccurrencePlanV2.empty(),
    )

    with pytest.raises(ValueError, match="global liability total"):
        refine_global_economic_state_effects_v2(candidate)


def test_open_terminal_amount_must_fit_its_exact_liability_row() -> None:
    obligation = TerminalObligationV2(
        obligation_id="perps:alice:one",
        lane_id=LaneIdV2.PERPS_MARKET,
        claimant="alice",
        asset="USD",
        liability_domain="claims",
        amount_atoms=3,
        status=TerminalObligationStatusV2.OPEN,
    )
    state = _global_state(
        lane_roots=_lane_roots(),
        balances=(EconomicAmountV2("alice", "USD", "accounts", 6),),
        custody=(EconomicAmountV2("vault", "USD", "claims", 4),),
        liabilities=(EconomicAmountV2("alice", "USD", "claims", 2),),
        supplies=(AssetSupplyV2("USD", 10),),
        terminal_obligations=(obligation,),
    )
    candidate = GlobalEconomicStateEffectRefinementCandidateV2(
        state,
        state,
        GlobalEconomicEffectPlanV2.empty(),
        (),
        GlobalTerminalObligationPlanV2.empty(),
        GlobalOracleOccurrencePlanV2.empty(),
    )

    with pytest.raises(ValueError, match="open terminal obligations exceed"):
        refine_global_economic_state_effects_v2(candidate)


def test_consumed_occurrence_context_and_height_are_exact() -> None:
    candidate = _asset_transfer_candidate()
    original = candidate.consumed_occurrences[0]
    mutated = replace(original, profile_root=_root(270))
    effects = GlobalEconomicEffectPlanV2(
        rows=candidate.effect_plan.rows,
        asset_conservation=candidate.effect_plan.asset_conservation,
        fee_conservation=candidate.effect_plan.fee_conservation,
        lane_writes=candidate.effect_plan.lane_writes,
        occurrence_consumptions=(mutated.occurrence_id,),
        external_outbox_enqueue=(),
    )
    post = replace(
        candidate.post_state,
        replay_state=(ReplayStateV2(mutated.replay_id, mutated.occurrence_id),),
    )

    with pytest.raises(ValueError, match="occurrence context"):
        refine_global_economic_state_effects_v2(
            replace(
                candidate,
                post_state=post,
                effect_plan=effects,
                consumed_occurrences=(mutated,),
            )
        )


def test_terminal_plan_requires_exact_liability_effect_and_backing() -> None:
    perps_pre_root = _root(301)
    pre = _global_state(
        lane_roots=_lane_roots({LaneIdV2.PERPS_MARKET: perps_pre_root}),
        custody=(EconomicAmountV2("vault", "USD", "claims", 10),),
        supplies=(AssetSupplyV2("USD", 10),),
    )
    occurrence = _occurrence(
        pre,
        command_kind="open_perps_liability",
        command_body_hash=_root(302),
    )
    obligation = TerminalObligationV2(
        obligation_id="perps:alice:one",
        lane_id=LaneIdV2.PERPS_MARKET,
        claimant="alice",
        asset="USD",
        liability_domain="claims",
        amount_atoms=4,
        status=TerminalObligationStatusV2.OPEN,
    )
    post = _global_state(
        lane_roots=_post_lane_roots(pre, LaneIdV2.PERPS_MARKET, _root(303)),
        height=pre.height + 1,
        custody=pre.custody,
        liabilities=(EconomicAmountV2("alice", "USD", "claims", 4),),
        supplies=pre.supplies,
        replay_state=(ReplayStateV2(occurrence.replay_id, occurrence.occurrence_id),),
        terminal_obligations=(obligation,),
    )
    effects = GlobalEconomicEffectPlanV2(
        rows=(EconomicEffectRowV2(EconomicEffectKindV2.LIABILITY, "alice", "USD", "claims", 4),),
        asset_conservation=(AssetConservationRowV2("USD", 10, 10, 10, 10, 0, 0),),
        fee_conservation=(),
        lane_writes=(LaneWriteV2(LaneIdV2.PERPS_MARKET, perps_pre_root, _root(303)),),
        occurrence_consumptions=(occurrence.occurrence_id,),
        external_outbox_enqueue=(),
    )
    terminal_plan = derive_global_terminal_obligation_plan_v2((), (obligation,))
    candidate = GlobalEconomicStateEffectRefinementCandidateV2(
        pre,
        post,
        effects,
        (occurrence,),
        terminal_plan,
        GlobalOracleOccurrencePlanV2.empty(),
    )

    assert refine_global_economic_state_effects_v2(candidate).terminal_plan_root == terminal_plan.plan_root
    with pytest.raises(ValueError, match="terminal obligation"):
        refine_global_economic_state_effects_v2(
            replace(candidate, terminal_plan=GlobalTerminalObligationPlanV2.empty())
        )
    wrong_obligation = replace(obligation, lane_id=LaneIdV2.SPOT_LIQUIDITY)
    with pytest.raises(ValueError, match="owning lane"):
        refine_global_economic_state_effects_v2(
            replace(
                candidate,
                post_state=replace(
                    candidate.post_state,
                    terminal_obligations=(wrong_obligation,),
                ),
                terminal_plan=derive_global_terminal_obligation_plan_v2(
                    (),
                    (wrong_obligation,),
                ),
            )
        )


def test_oracle_plan_updates_only_the_bound_oracle_registry_and_lane() -> None:
    oracle_pre_root = _root(401)
    before = OracleOccurrenceStateV2("oracle:usd", _root(402), 6, False)
    after = OracleOccurrenceStateV2("oracle:usd", _root(403), 7, True)
    pre = _global_state(
        lane_roots=_lane_roots({LaneIdV2.ORACLE_MARKET: oracle_pre_root}),
        balances=(EconomicAmountV2("alice", "USD", "accounts", 10),),
        supplies=(AssetSupplyV2("USD", 10),),
        oracle_occurrences=(before,),
    )
    occurrence = _occurrence(
        pre,
        command_kind="finalize_oracle_occurrence",
        command_body_hash=_root(404),
    )
    post = _global_state(
        lane_roots=_post_lane_roots(pre, LaneIdV2.ORACLE_MARKET, _root(405)),
        height=pre.height + 1,
        balances=pre.balances,
        supplies=pre.supplies,
        oracle_occurrences=(after,),
        replay_state=(ReplayStateV2(occurrence.replay_id, occurrence.occurrence_id),),
    )
    effects = GlobalEconomicEffectPlanV2(
        rows=(),
        asset_conservation=(),
        fee_conservation=(),
        lane_writes=(LaneWriteV2(LaneIdV2.ORACLE_MARKET, oracle_pre_root, _root(405)),),
        occurrence_consumptions=(occurrence.occurrence_id,),
        external_outbox_enqueue=(),
    )
    oracle_plan = derive_global_oracle_occurrence_plan_v2((before,), (after,))
    candidate = GlobalEconomicStateEffectRefinementCandidateV2(
        pre,
        post,
        effects,
        (occurrence,),
        GlobalTerminalObligationPlanV2.empty(),
        oracle_plan,
    )

    assert refine_global_economic_state_effects_v2(candidate).oracle_plan_root == oracle_plan.plan_root
    with pytest.raises(ValueError, match="Oracle occurrence"):
        refine_global_economic_state_effects_v2(
            replace(candidate, oracle_plan=GlobalOracleOccurrencePlanV2.empty())
        )
    wrong_lane_root = _root(406)
    with pytest.raises(ValueError, match="Oracle lane write"):
        refine_global_economic_state_effects_v2(
            replace(
                candidate,
                post_state=replace(
                    candidate.post_state,
                    lane_roots=_post_lane_roots(
                        pre,
                        LaneIdV2.SPOT_LIQUIDITY,
                        wrong_lane_root,
                    ),
                ),
                effect_plan=GlobalEconomicEffectPlanV2(
                    rows=(),
                    asset_conservation=(),
                    fee_conservation=(),
                    lane_writes=(
                        LaneWriteV2(
                            LaneIdV2.SPOT_LIQUIDITY,
                            pre.lane_roots[1].state_root,
                            wrong_lane_root,
                        ),
                    ),
                    occurrence_consumptions=(occurrence.occurrence_id,),
                    external_outbox_enqueue=(),
                ),
            )
        )


def test_reward_annotation_requires_an_exact_state_bearing_mirror() -> None:
    candidate = _asset_transfer_candidate()
    forged_rows = tuple(
        sorted(
            (
                *candidate.effect_plan.rows,
                EconomicEffectRowV2(
                    EconomicEffectKindV2.REWARD,
                    "bob",
                    "USD",
                    "accounts",
                    1,
                ),
            ),
            key=lambda row: row.key,
        )
    )
    forged_effects = GlobalEconomicEffectPlanV2(
        rows=forged_rows,
        asset_conservation=candidate.effect_plan.asset_conservation,
        fee_conservation=candidate.effect_plan.fee_conservation,
        lane_writes=candidate.effect_plan.lane_writes,
        occurrence_consumptions=candidate.effect_plan.occurrence_consumptions,
        external_outbox_enqueue=(),
    )

    with pytest.raises(ValueError, match="reward or slash"):
        refine_global_economic_state_effects_v2(
            replace(candidate, effect_plan=forged_effects)
        )

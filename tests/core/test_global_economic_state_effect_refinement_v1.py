"""RIPR evidence for exact economic-table and lane-write refinement.

The independent oracle derives deltas directly from full pre/post state tables.
Golden-root parity detects Python/Rust canonical encoding drift.
"""

from __future__ import annotations

from dataclasses import replace

import pytest

import src.core.global_economic_state_effect_refinement_v1 as refinement_module
from src.core.global_economic_state_effect_refinement_v1 import (
    GlobalEconomicStateEffectRefinementCandidateV1,
    refine_global_economic_state_effects_v1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    MAX_ATOMS_V1,
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
        "0xa390b8bc7bf078478dab2d03a62e8d0824199b4a8c6dcfb03ef97e5578e7fd31"
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


def test_refinement_rejects_fee_residue_without_state_bucket() -> None:
    candidate = _candidate()
    wrong = replace(
        candidate.effect_plan,
        fee_conservation=(FeeConservationRowV1("USD", 3, 2, 1),),
    )

    with pytest.raises(ValueError, match="fee residue has no state-bearing mapping"):
        refine_global_economic_state_effects_v1(replace(candidate, effect_plan=wrong))


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
        {"height": 42},
        {"history_root": _root(7_001)},
        {"oracle_occurrences": (OracleOccurrenceStateV1("oracle", _root(7_002), 41, True),)},
        {"replay_state": (ReplayStateV1("replay", _root(7_003)),)},
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
            replace(candidate, post_state=replace(candidate.post_state, **post_change))
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

    with pytest.raises(ValueError, match="replay occurrence refinement is unavailable"):
        refine_global_economic_state_effects_v1(replace(candidate, effect_plan=wrong))


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
    ) -> object:
        object.__setattr__(candidate.post_state.balances[0], "amount_atoms", 94)
        return original_derive(pre_state, post_state, effect_plan)

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

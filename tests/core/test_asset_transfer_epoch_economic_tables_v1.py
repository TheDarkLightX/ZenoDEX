"""Bounded custody transfer histories refine actual epoch economic tables.

The independent oracle sums endpoint row lists by owner, asset and domain. Tests
exercise the actual custody transition, coordinator, epoch composer and table
checker, including malformed rows, reordered history, arity and signed-prefix
overflow. The overflow witness uses an allowed synthetic zero-fee parameter;
it selects no deployed policy. Intermediate states are prospective disclosures.
No receipt, authorization, store, publication or universal refinement is claimed.
"""


from __future__ import annotations

import hashlib
from dataclasses import replace
from functools import lru_cache
from typing import Callable

from src.core import epoch_effect_composition_v1 as epoch_composition
from src.core.asset_lane_projection_v1 import project_asset_transfer_state_v1
from src.core.asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
)
from src.core.asset_transfer_types_v1 import (
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferStateV1,
)
from src.core.epoch_effect_composition_v1 import (
    compose_asset_lane_epoch_effect_plans_v1,
)
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1
from src.core.global_economic_state_delta_v1 import (
    _AmountDeltaRowV1,
    _derive_global_economic_state_delta_v1,
    _DerivedGlobalEconomicStateDeltaV1,
    _require_amount_table_refinement_v1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    MAX_DELTA_ATOMS_V1,
    MAX_U64_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    canonical_global_bytes_v1,
)
from tests.formal.test_lean_asset_transfer_epoch_state_closure_v1 import (
    SharedHeightPair,
    _prospective_post,
)
from tests.formal.test_lean_asset_transfer_global_successor_v1 import (
    ASSET_REGISTRY,
    FEE_REGISTRY,
    RELEASE,
    RuntimeWitness,
    _normalise,
    _run_custody_module,
    _runtime_witness,
)

TABLES = ("balances", "custody", "liabilities", "reserves")


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _digest(value: object) -> str:
    return hashlib.sha256(canonical_global_bytes_v1(value)).hexdigest()


def _expect_error(call: Callable[[], object]) -> tuple[str, str]:
    try:
        call()
    except Exception as error:  # The exact class and text are part of each control.
        return type(error).__name__, str(error)
    raise AssertionError("expected the bounded control to reject")


def _amount_rows_view(
    rows: tuple[_AmountDeltaRowV1, ...],
) -> tuple[tuple[object, ...], ...]:
    return tuple(
        (
            row.owner,
            row.asset,
            row.custody_domain,
            row.delta_atoms,
        )
        for row in rows
    )


def _four_tables_from_delta(
    delta: _DerivedGlobalEconomicStateDeltaV1,
) -> tuple[tuple[str, tuple[tuple[object, ...], ...]], ...]:
    amount_deltas = delta.amount_deltas
    return tuple(
        (
            table,
            _amount_rows_view(tuple(row for row in amount_deltas if row.table == table)),
        )
        for table in TABLES
    )


def _endpoint_table_oracle(
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
) -> tuple[tuple[str, tuple[tuple[object, ...], ...]], ...]:
    """Sum endpoint row lists independently, then sort by owner/asset/domain."""

    result: list[tuple[str, tuple[tuple[object, ...], ...]]] = []
    for table in TABLES:
        sums: dict[tuple[str, str, str], int] = {}
        for row in getattr(post_state, table):
            coordinate = (row.owner, row.asset, row.custody_domain)
            sums[coordinate] = sums.get(coordinate, 0) + row.amount_atoms
        for row in getattr(pre_state, table):
            coordinate = (row.owner, row.asset, row.custody_domain)
            sums[coordinate] = sums.get(coordinate, 0) - row.amount_atoms
        rows = tuple(
            (*coordinate, delta)
            for coordinate, delta in sorted(sums.items())
            if delta
        )
        result.append((table, tuple(rows)))
    return tuple(result)


def _replay_insertions(
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
) -> tuple[object, ...]:
    return tuple(row for row in post_state.replay_state if row not in pre_state.replay_state)


def _pair_plans(pair: SharedHeightPair) -> tuple[GlobalEconomicEffectPlanV1, ...]:
    first = _normalise(pair.first, pair.first_accepted)
    return (first, pair.second_effects)


def _shared_height_tables(height: int) -> dict[str, object]:
    pair = SharedHeightPair(height=height)
    assert pair.source.height == height
    assert pair.first.occurrence.height == pair.second.occurrence.height == height + 1
    assert pair.first_post.height == pair.second_post.height == height + 1
    plans = _pair_plans(pair)
    composed = compose_asset_lane_epoch_effect_plans_v1(plans)
    delta = _derive_global_economic_state_delta_v1(
        pair.source,
        pair.second_post,
        composed,
        _replay_insertions(pair.source, pair.second_post),
    )
    actual = _four_tables_from_delta(delta)
    expected = _endpoint_table_oracle(pair.source, pair.second_post)
    assert actual == expected, (actual, expected)
    assert _require_amount_table_refinement_v1(
        pair.source, pair.second_post, composed
    ) == delta.amount_deltas
    assert delta.supply_deltas == ()
    return {
        "case": "two_actual_transfers_full_four_table_oracle",
        "height": height,
        "occurrence_count": len(composed.occurrence_consumptions),
        "occurrence_ids": list(composed.occurrence_consumptions),
        "actual_tables": actual,
        "endpoint_oracle_tables": expected,
        "effect_plan_digest": _digest(composed),
        "delta_root": delta.delta_root,
        "synthetic_nonclaim": "unit-only actual Python transitions; no cryptographic or publication evidence",
    }


def test_actual_two_transfer_tables_match_endpoint_oracle_at_height_7() -> None:
    _shared_height_tables(7)


def test_actual_two_transfer_tables_match_endpoint_oracle_at_u64_maximum_neighbour() -> None:
    _shared_height_tables(MAX_U64_V1 - 1)


def _mutated_plan(
    plan: GlobalEconomicEffectPlanV1,
    mutation: str,
) -> GlobalEconomicEffectPlanV1:
    index = next(
        index
        for index, row in enumerate(plan.rows)
        if row.kind is EconomicEffectKindV1.ACCOUNT_MOVEMENT and row.principal == "alice"
    )
    original = plan.rows[index]
    if mutation == "wrong_owner":
        replacement = replace(original, principal="mallory")
    elif mutation == "wrong_domain":
        replacement = replace(original, custody_domain="escrow")
    elif mutation == "wrong_table":
        replacement = replace(original, kind=EconomicEffectKindV1.CUSTODY)
    else:
        raise AssertionError(mutation)
    rows = list(plan.rows)
    rows[index] = replacement
    return replace(plan, rows=tuple(sorted(rows, key=lambda row: row.key)))


def _table_mutation_controls() -> dict[str, object]:
    pair = SharedHeightPair(height=7)
    plan = compose_asset_lane_epoch_effect_plans_v1(_pair_plans(pair))
    before = _digest((pair.source, pair.second_post, plan))
    controls = []
    for mutation in ("wrong_owner", "wrong_domain", "wrong_table"):
        bad_plan = _mutated_plan(plan, mutation)
        bad_before = _digest(bad_plan)
        error_type, error_message = _expect_error(
            lambda bad_plan=bad_plan: _require_amount_table_refinement_v1(
                pair.source, pair.second_post, bad_plan
            )
        )
        assert (error_type, error_message) == (
            "ValueError",
            "economic refinement balance delta mismatch",
        )
        assert _digest((pair.source, pair.second_post, plan)) == before
        assert _digest(bad_plan) == bad_before
        controls.append(
            {
                "mutation": mutation,
                "error_type": error_type,
                "error": error_message,
                "input_digest_unchanged": (
                    _digest((pair.source, pair.second_post, plan)) == before
                    and _digest(bad_plan) == bad_before
                ),
            }
        )
    return {"case": "four_table_refinement_mutations", "controls": controls}


def test_wrong_owner_domain_and_table_reject_without_mutation() -> None:
    _table_mutation_controls()


def _reversed_history_control() -> dict[str, object]:
    pair = SharedHeightPair(height=7)
    first, second = _pair_plans(pair)
    before = _digest((first, second))
    error_type, error_message = _expect_error(
        lambda: compose_asset_lane_epoch_effect_plans_v1((second, first))
    )
    assert (error_type, error_message) == (
        "ValueError",
        "asset-lane epoch lane-write history is disconnected",
    )
    assert _digest((first, second)) == before
    return {
        "case": "reversed_actual_route_history",
        "error_type": error_type,
        "error": error_message,
        "input_digest_unchanged": _digest((first, second)) == before,
    }


def test_reversed_actual_route_history_rejects_without_mutation() -> None:
    _reversed_history_control()


def _high_initial_witness() -> RuntimeWitness:
    template = _runtime_witness(height=7, amount=MAX_DELTA_ATOMS_V1)
    policies = (AssetTransferPolicyV1("USD", "treasury", 0, True),)
    initial_atoms = 2 * MAX_DELTA_ATOMS_V1
    balances = (EconomicAmountV1("alice", "USD", "accounts", initial_atoms),)
    supplies = (AssetSupplyV1("USD", initial_atoms),)
    custody: tuple[EconomicAmountV1, ...] = ()
    liabilities: tuple[EconomicAmountV1, ...] = ()
    pre_state = AssetTransferStateV1(RELEASE, policies, balances, supplies)
    projection = project_asset_transfer_state_v1(
        pre_state,
        asset_policy_registry_root=ASSET_REGISTRY,
        fee_policy_registry_root=FEE_REGISTRY,
        custody=custody,
    )
    lane_roots = tuple(
        LaneStateRootV1(
            lane,
            RELEASE,
            lane is LaneIdV1.ASSET_TRANSFER,
            projection.state_root if lane is LaneIdV1.ASSET_TRANSFER else _root(0x100 + index),
        )
        for index, lane in enumerate(ALL_LANE_IDS_V1)
    )
    pre_global = replace(
        template.pre_global,
        lane_roots=lane_roots,
        balances=balances,
        supplies=supplies,
        custody=custody,
        liabilities=liabilities,
        oracle_occurrences=(),
        replay_state=(),
    )
    command = AssetTransferCommandV1(
        "asset_transfer", "USD", "alice", "bob", MAX_DELTA_ATOMS_V1, 0
    )
    occurrence = replace(
        template.occurrence,
        command_body_hash=command.command_body_hash,
        pre_state_root=pre_global.state_root,
    )
    context = replace(
        template.module_input.context,
        command_occurrence_id=occurrence.occurrence_id,
    )
    module_input = AssetTransferLaneModuleInputV1(
        context,
        pre_state,
        command,
        ASSET_REGISTRY,
        FEE_REGISTRY,
        custody,
    )
    return RuntimeWitness(
        module_input,
        pre_global,
        occurrence,
        projection.state_root,
        liabilities,
    )


def _directional_witness(
    previous: RuntimeWitness,
    previous_accepted: AssetTransferLaneModuleAcceptedV1,
    previous_post: GlobalEconomicStateV1,
    *,
    sender: str,
    recipient: str,
    amount: int,
    max_fee: int,
    nonce: int,
    op_index: int,
) -> RuntimeWitness:
    command = AssetTransferCommandV1(
        "asset_transfer", "USD", sender, recipient, amount, max_fee
    )
    occurrence = EconomicCommandOccurrenceV1(
        chain_id=previous_post.chain_id,
        deployment_root=previous_post.deployment_root,
        height=previous_post.height,
        tx_index=0,
        op_index=op_index,
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=previous.occurrence.route_release_id,
        subject_id=sender,
        grant_root=previous.occurrence.grant_root,
        nonce=nonce,
        profile_root=previous_post.profile_root,
        pre_state_root=previous_post.state_root,
        consumed_object_ids=(),
    )
    context = AssetTransferContextV1(
        previous_post.chain_id,
        previous_post.deployment_root,
        previous_post.profile_root,
        previous.module_input.context.writer_epoch,
        previous.module_input.context.module_release_id,
        occurrence.occurrence_id,
        sender,
        previous.occurrence.grant_root,
    )
    module_input = AssetTransferLaneModuleInputV1(
        context,
        previous_accepted.post_state,
        command,
        previous.module_input.asset_policy_registry_root,
        previous.module_input.fee_policy_registry_root,
        previous_accepted.private_port.post_state.custody,
    )
    return RuntimeWitness(
        module_input,
        previous_post,
        occurrence,
        previous_accepted.private_port.post_state.state_root,
        previous.liabilities,
    )


def _high_prefix_history() -> tuple[tuple[RuntimeWitness, AssetTransferLaneModuleAcceptedV1, GlobalEconomicEffectPlanV1, GlobalEconomicStateV1], ...]:
    witness = _high_initial_witness()
    directions = (
        ("alice", "bob"),
        ("alice", "bob"),
        ("bob", "alice"),
        ("bob", "alice"),
    )
    records = []
    for index in range(len(directions)):
        accepted = _run_custody_module(witness)
        plan = _normalise(witness, accepted)
        post = _prospective_post(witness.pre_global, witness.occurrence, accepted)
        expected_height = (
            witness.pre_global.height + 1
            if index == 0
            else records[-1][3].height
        )
        assert witness.occurrence.height == expected_height
        assert post.height == witness.occurrence.height
        records.append((witness, accepted, plan, post))
        if index + 1 < len(directions):
            witness = _directional_witness(
                witness,
                accepted,
                post,
                sender=directions[index + 1][0],
                recipient=directions[index + 1][1],
                amount=MAX_DELTA_ATOMS_V1,
                max_fee=0,
                nonce=100 + index,
                op_index=index + 1,
            )
    assert len({record[0].occurrence.occurrence_id for record in records}) == 4
    return tuple(records)


def _endpoint_only_effect_totals(
    plans: tuple[GlobalEconomicEffectPlanV1, ...],
) -> tuple[tuple[tuple[str, str, str, str], int], ...]:
    totals: dict[tuple[str, str, str, str], int] = {}
    for plan in plans:
        for row in plan.rows:
            totals[row.key] = totals.get(row.key, 0) + row.delta_atoms
    return tuple((key, value) for key, value in sorted(totals.items()) if value)


def _deferred_prefix_mutant(
    plans: tuple[GlobalEconomicEffectPlanV1, ...],
) -> GlobalEconomicEffectPlanV1:
    """Run the actual composer with only its signed-prefix helper disabled in memory."""

    original_checked_i128 = epoch_composition._checked_i128
    try:
        epoch_composition._checked_i128 = lambda value, *, name: value
        mutant_result = compose_asset_lane_epoch_effect_plans_v1(plans)
    finally:
        epoch_composition._checked_i128 = original_checked_i128
    assert type(mutant_result) is GlobalEconomicEffectPlanV1
    return mutant_result


def _high_prefix_overflow_control() -> dict[str, object]:
    history = _high_prefix_history()
    plans = tuple(record[2] for record in history)
    source, final = history[0][0].pre_global, history[-1][3]
    assert _endpoint_table_oracle(source, final) == tuple((table, ()) for table in TABLES)
    assert _endpoint_only_effect_totals(plans) == ()
    mutant_result = _deferred_prefix_mutant(plans)
    assert mutant_result.rows == ()
    before = _digest(plans)
    error_type, error_message = _expect_error(
        lambda: compose_asset_lane_epoch_effect_plans_v1(plans)
    )
    assert (error_type, error_message) == (
        "ValueError",
        "epoch effect row total exceeds signed 128-bit atoms",
    )
    assert _digest(plans) == before
    return {
        "case": "actual_valid_leaves_prefix_i128_overflow",
        "leaf_count": len(history),
        "leaf_accepted_types": [type(record[1]).__name__ for record in history],
        "endpoint_only_effect_totals": (),
        "endpoint_tables": tuple((table, ()) for table in TABLES),
        "deferred_prefix_mutant_accepted": True,
        "deferred_prefix_mutant_rows": len(mutant_result.rows),
        "deferred_prefix_mutant_digest": _digest(mutant_result),
        "aggregate_error_type": error_type,
        "aggregate_error": error_message,
        "input_digest_unchanged": _digest(plans) == before,
        "synthetic_nonclaim": "actual leaf transitions only; no cryptographic authority",
    }


def test_actual_valid_leaves_kill_final_only_endpoint_mutant_at_i128_prefix() -> None:
    _high_prefix_overflow_control()


def _rich_initial_witness() -> RuntimeWitness:
    template = _runtime_witness(height=7, amount=1)
    policies = template.module_input.pre_state.policies
    balances = tuple(
        sorted(
            (
                EconomicAmountV1("alice", "EUR", "accounts", 9),
                EconomicAmountV1("alice", "USD", "accounts", 500),
                EconomicAmountV1("bob", "USD", "accounts", 5),
            ),
            key=lambda row: row.key,
        )
    )
    supplies = (AssetSupplyV1("EUR", 9), AssetSupplyV1("USD", 515))
    pre_state = AssetTransferStateV1(RELEASE, policies, balances, supplies)
    projection = project_asset_transfer_state_v1(
        pre_state,
        asset_policy_registry_root=ASSET_REGISTRY,
        fee_policy_registry_root=FEE_REGISTRY,
        custody=template.module_input.custody,
    )
    lane_roots = tuple(
        LaneStateRootV1(
            lane,
            RELEASE,
            lane is LaneIdV1.ASSET_TRANSFER,
            projection.state_root if lane is LaneIdV1.ASSET_TRANSFER else _root(0x200 + index),
        )
        for index, lane in enumerate(ALL_LANE_IDS_V1)
    )
    pre_global = replace(
        template.pre_global,
        lane_roots=lane_roots,
        balances=balances,
        supplies=supplies,
    )
    occurrence = replace(
        template.occurrence,
        pre_state_root=pre_global.state_root,
    )
    context = replace(
        template.module_input.context,
        command_occurrence_id=occurrence.occurrence_id,
    )
    module_input = AssetTransferLaneModuleInputV1(
        context,
        pre_state,
        template.module_input.command,
        ASSET_REGISTRY,
        FEE_REGISTRY,
        template.module_input.custody,
    )
    return RuntimeWitness(
        module_input,
        pre_global,
        occurrence,
        projection.state_root,
        template.liabilities,
    )


@lru_cache(maxsize=None)
def _actual_route_chain(length: int) -> tuple[tuple[RuntimeWitness, AssetTransferLaneModuleAcceptedV1, GlobalEconomicEffectPlanV1, GlobalEconomicStateV1], ...]:
    if not 1 <= length <= 65:
        raise ValueError(length)
    witness = _rich_initial_witness()
    records = []
    for index in range(length):
        accepted = _run_custody_module(witness)
        plan = _normalise(witness, accepted)
        post = _prospective_post(witness.pre_global, witness.occurrence, accepted)
        expected_height = (
            witness.pre_global.height + 1
            if index == 0
            else records[-1][3].height
        )
        assert witness.occurrence.height == expected_height
        assert post.height == witness.occurrence.height
        records.append((witness, accepted, plan, post))
        if index + 1 < length:
            witness = _directional_witness(
                witness,
                accepted,
                post,
                sender="alice",
                recipient="bob",
                amount=2,
                max_fee=1,
                nonce=100 + index,
                op_index=index + 1,
            )
    occurrence_ids = tuple(record[0].occurrence.occurrence_id for record in records)
    assert len(occurrence_ids) == len(set(occurrence_ids)) == length
    return tuple(records)


def _route_arity_edges() -> dict[str, object]:
    error_type, error_message = _expect_error(
        lambda: compose_asset_lane_epoch_effect_plans_v1(())
    )
    assert (error_type, error_message) == (
        "ValueError",
        "asset-lane epoch requires between one and 64 route effect plans",
    )

    one = tuple(record[2] for record in _actual_route_chain(1))
    one_result = compose_asset_lane_epoch_effect_plans_v1(one)
    assert len(one_result.occurrence_consumptions) == 1

    sixty_four_records = _actual_route_chain(64)
    sixty_four = tuple(record[2] for record in sixty_four_records)
    sixty_four_result = compose_asset_lane_epoch_effect_plans_v1(sixty_four)
    assert len(sixty_four_result.occurrence_consumptions) == 64

    sixty_five_records = _actual_route_chain(65)
    sixty_five = tuple(record[2] for record in sixty_five_records)
    before = _digest(sixty_five)
    high_error_type, high_error_message = _expect_error(
        lambda: compose_asset_lane_epoch_effect_plans_v1(sixty_five)
    )
    assert (high_error_type, high_error_message) == (
        "ValueError",
        "asset-lane epoch requires between one and 64 route effect plans",
    )
    assert _digest(sixty_five) == before
    return {
        "case": "actual_route_arity_edges",
        "zero": {"error_type": error_type, "error": error_message},
        "one": {
            "actual_leaf_count": len(one),
            "accepted_occurrences": len(one_result.occurrence_consumptions),
            "plan_digest": _digest(one),
        },
        "sixty_four": {
            "actual_leaf_count": len(sixty_four),
            "accepted_occurrences": len(sixty_four_result.occurrence_consumptions),
            "plan_digest": _digest(sixty_four),
        },
        "sixty_five": {
            "actual_leaf_count": len(sixty_five),
            "error_type": high_error_type,
            "error": high_error_message,
            "input_digest_unchanged": _digest(sixty_five) == before,
        },
    }


def test_actual_route_arity_edges_use_unique_custody_complete_chains() -> None:
    _route_arity_edges()

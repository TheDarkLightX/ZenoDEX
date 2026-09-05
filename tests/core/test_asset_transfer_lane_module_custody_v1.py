"""Successor wrapper controls; no cryptographic or publication authority."""

from dataclasses import replace

import pytest

from src.core import asset_transfer_lane_module_custody_v1 as successor
from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1
from src.core.asset_lane_projection_v1 import (
    AssetLaneCompositionAcceptedV1,
    AssetLaneCoordinatorRejectCodeV1,
)
from src.core.asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    transition_asset_transfer_lane_module_v1,
)
from src.core.asset_transfer_types_v1 import AssetTransferRejectedV1
from src.core.global_settlement_types_v1 import EconomicAmountV1, canonical_global_bytes_v1
from tests.core.test_asset_transfer_lane_module_v1 import _coordinator_context, _input

MAX_ATOMS = (1 << 128) - 1


def _custody_input(atoms=1, *, fee_owner="treasury"):
    original = _input()
    state = replace(
        original.pre_state,
        policies=(replace(original.pre_state.policies[0], fee_owner=fee_owner),),
        supplies=(replace(original.pre_state.supplies[0], amount_atoms=115 + atoms),),
    )
    custody = () if atoms == 0 else (EconomicAmountV1("vault", "USD", "escrow", atoms),)
    return replace(original, pre_state=state, custody=custody)


def _observation(accepted):
    return canonical_global_bytes_v1(
        {
            "statement": accepted.statement_root,
            "state": accepted.post_state,
            "effects": accepted.effects,
            "port": accepted.private_port,
            "journal": accepted.module_journal,
        }
    )


@pytest.mark.parametrize("atoms", (0, 1, 7, 1 << 127, MAX_ATOMS - 116, MAX_ATOMS - 115))
def test_successor_completes_exact_physical_totals_and_coordinator_accepts(atoms):
    module_input = _custody_input(atoms)
    original_bytes = canonical_global_bytes_v1(module_input.to_canonical())
    legacy = transition_asset_transfer_lane_module_v1(module_input)
    result = successor.transition_asset_transfer_lane_module_custody_v1(module_input)
    assert isinstance(result, AssetTransferLaneModuleAcceptedV1)
    row = result.effects.asset_conservation[0]
    independent_pre = sum(r.amount_atoms for r in module_input.pre_state.balances) + atoms
    independent_post = sum(r.amount_atoms for r in result.post_state.balances) + atoms
    assert row.owned_and_custodied_pre_atoms == independent_pre == 115 + atoms
    assert row.owned_and_custodied_post_atoms == independent_post == row.supply_post_atoms
    assert row.authorized_issue_atoms == row.authorized_burn_atoms == 0
    assert result.post_state == legacy.post_state
    assert result.effects.rows == legacy.effects.rows
    assert result.effects.fee_conservation == legacy.effects.fee_conservation
    assert result.effects.lane_writes == legacy.effects.lane_writes
    assert result.effects.occurrence_consumptions == legacy.effects.occurrence_consumptions
    assert result.effects.external_outbox_enqueue == legacy.effects.external_outbox_enqueue == ()
    assert (
        result.private_port.pre_state.custody
        == result.private_port.post_state.custody
        == module_input.custody
    )
    assert result.private_port.pre_state == legacy.private_port.pre_state
    assert result.private_port.post_state == legacy.private_port.post_state
    assert (
        result.module_journal.effect_plan_root
        == result.private_port.module_effect_plan_root
        == result.effects.effect_plan_root
    )
    assert result.module_journal.private_port_root == result.private_port.port_root
    composed = compose_asset_lane_single_v1(
        _coordinator_context(), result.module_journal, result.private_port, result.effects
    )
    assert isinstance(composed, AssetLaneCompositionAcceptedV1)
    assert canonical_global_bytes_v1(module_input.to_canonical()) == original_bytes
    assert successor.recompute_asset_transfer_lane_module_custody_v1(module_input, result) == result
    if atoms == 0:
        assert _observation(result) == _observation(legacy)
    else:
        assert result.effects.effect_plan_root != legacy.effects.effect_plan_root
        assert result.receipt_root != legacy.receipt_root


@pytest.mark.parametrize("fee_owner", ("alice", "bob", "treasury"))
def test_fee_owner_aliases_preserve_leaf_movements_and_complete_custody(fee_owner):
    module_input = _custody_input(7, fee_owner=fee_owner)
    legacy = transition_asset_transfer_lane_module_v1(module_input)
    result = successor.transition_asset_transfer_lane_module_custody_v1(module_input)
    assert result.post_state == legacy.post_state
    assert result.effects.rows == legacy.effects.rows
    assert result.effects.fee_conservation == legacy.effects.fee_conservation
    assert result.effects.asset_conservation[0].owned_and_custodied_post_atoms == 122


@pytest.mark.parametrize("failure", ("zero", "fee", "balance", "subject"))
def test_leaf_rejections_remain_exact_no_ops(failure):
    module_input = _custody_input(7)
    if failure == "subject":
        module_input = replace(
            module_input, context=replace(module_input.context, subject_id="mallory")
        )
    else:
        change = {
            "zero": {"amount_atoms": 0},
            "fee": {"max_fee_atoms": 1},
            "balance": {"amount_atoms": 1000},
        }
        module_input = replace(
            module_input, command=replace(module_input.command, **change[failure])
        )
    legacy = transition_asset_transfer_lane_module_v1(module_input)
    result = successor.transition_asset_transfer_lane_module_custody_v1(module_input)
    assert isinstance(result, AssetTransferRejectedV1)
    assert result == legacy
    assert result.effects.is_empty
    assert result.pre_state_root == result.post_state_root == module_input.pre_state.state_root


def test_overflowing_complete_total_is_rejected_at_owned_boundary():
    module_input = _custody_input(MAX_ATOMS - 115)
    object.__setattr__(module_input.custody[0], "amount_atoms", MAX_ATOMS - 114)
    with pytest.raises(ValueError, match="owned and custodied total must equal supply"):
        successor.transition_asset_transfer_lane_module_custody_v1(module_input)


@pytest.mark.parametrize("count", (1, 4096))
def test_every_custody_row_contributes_without_changing_identity(count):
    module_input = _custody_input(count)
    rows = tuple(EconomicAmountV1(f"vault-{i:04d}", "USD", "escrow", 1) for i in range(count))
    module_input = replace(module_input, custody=rows)
    result = successor.transition_asset_transfer_lane_module_custody_v1(module_input)
    assert result.effects.asset_conservation[0].owned_and_custodied_post_atoms == 115 + count
    assert result.private_port.pre_state.custody == result.private_port.post_state.custody == rows


def test_custody_ceiling_and_duplicate_keys_reject_before_partial_result():
    module_input = _custody_input(4097)
    rows = tuple(EconomicAmountV1(f"vault-{i:04d}", "USD", "escrow", 1) for i in range(4097))
    object.__setattr__(module_input, "custody", rows)
    with pytest.raises(ValueError, match="4096-item ceiling"):
        successor.transition_asset_transfer_lane_module_custody_v1(module_input)
    module_input = _custody_input(2)
    row = EconomicAmountV1("vault", "USD", "escrow", 1)
    object.__setattr__(module_input, "custody", (row, row))
    with pytest.raises(ValueError):
        successor.transition_asset_transfer_lane_module_custody_v1(module_input)


def test_foreign_asset_custody_is_not_added_to_transferred_asset_total():
    module_input = _custody_input(7)
    state = module_input.pre_state
    eur_policy = replace(state.policies[0], asset="EUR")
    eur_supply = replace(state.supplies[0], asset="EUR", amount_atoms=9)
    module_input = replace(
        module_input,
        pre_state=replace(
            state, policies=(eur_policy, *state.policies), supplies=(eur_supply, *state.supplies)
        ),
        custody=(EconomicAmountV1("other-vault", "EUR", "other", 9), *module_input.custody),
    )
    result = successor.transition_asset_transfer_lane_module_custody_v1(module_input)
    assert result.effects.asset_conservation[0].asset == "USD"
    assert result.effects.asset_conservation[0].owned_and_custodied_pre_atoms == 122
    assert (
        result.private_port.pre_state.custody
        == result.private_port.post_state.custody
        == module_input.custody
    )


def test_recomputation_refuses_legacy_and_coherent_foreign_outputs():
    module_input = _custody_input(7)
    legacy = transition_asset_transfer_lane_module_v1(module_input)
    with pytest.raises(ValueError, match="differs from recomputation"):
        successor.recompute_asset_transfer_lane_module_custody_v1(module_input, legacy)
    foreign = successor.transition_asset_transfer_lane_module_custody_v1(
        replace(module_input, command=replace(module_input.command, amount_atoms=1))
    )
    with pytest.raises(ValueError, match="differs from recomputation"):
        successor.recompute_asset_transfer_lane_module_custody_v1(module_input, foreign)
    with pytest.raises(ValueError, match="recomputes to rejection"):
        successor.recompute_asset_transfer_lane_module_custody_v1(
            replace(module_input, command=replace(module_input.command, amount_atoms=0)), foreign
        )


def test_retained_mutable_input_alias_cannot_change_owned_result():
    module_input = _custody_input(7)
    result = successor.transition_asset_transfer_lane_module_custody_v1(module_input)
    before = _observation(result)
    object.__setattr__(module_input.custody[0], "amount_atoms", 8)
    assert _observation(result) == before


def test_balances_only_mutant_is_refused_by_existing_coordinator():
    import inspect

    module_input = _custody_input(7)
    legacy = transition_asset_transfer_lane_module_v1(module_input)
    source = inspect.getsource(successor._complete_owned_result_v1)
    for side in ("pre", "post"):
        target = f"port.{side}_state.owned_and_custodied_atoms(row.asset)"
        assert source.count(target) == 1
        source = source.replace(target, f"row.owned_and_custodied_{side}_atoms", 1)
    namespace = dict(vars(successor))
    exec(compile(source, "<custody-total-mutant>", "exec"), namespace)
    mutant = namespace["_complete_owned_result_v1"](legacy)
    result = compose_asset_lane_single_v1(
        _coordinator_context(), mutant.module_journal, mutant.private_port, mutant.effects
    )
    assert result.code is AssetLaneCoordinatorRejectCodeV1.CONSERVATION_STATE_MISMATCH


def test_omitted_port_root_rebind_is_rejected_by_owned_accepted_constructor():
    import inspect

    legacy = transition_asset_transfer_lane_module_v1(_custody_input(7))
    source = inspect.getsource(successor._complete_owned_result_v1)
    target = "private_port_root=port.port_root,"
    assert source.count(target) == 1
    source = source.replace(target, "private_port_root=legacy.module_journal.private_port_root,", 1)
    namespace = dict(vars(successor))
    exec(compile(source, "<custody-port-root-mutant>", "exec"), namespace)
    with pytest.raises(ValueError, match="private-port root mismatch"):
        namespace["_complete_owned_result_v1"](legacy)


def _high_balance_input():
    module_input = _input()
    state = module_input.pre_state
    return replace(
        module_input,
        pre_state=replace(
            state,
            balances=(replace(state.balances[0], amount_atoms=1 << 127), *state.balances[1:]),
            supplies=(replace(state.supplies[0], amount_atoms=(1 << 127) + 15),),
        ),
    )


def test_python_coordinator_accepts_high_absolute_account_and_small_delta():
    module_input = _high_balance_input()
    result = successor.transition_asset_transfer_lane_module_custody_v1(module_input)
    assert result.post_state.balance_atoms("alice", "USD") == (1 << 127) - 32
    composed = compose_asset_lane_single_v1(
        _coordinator_context(), result.module_journal, result.private_port, result.effects
    )
    assert isinstance(composed, AssetLaneCompositionAcceptedV1)


def test_successor_golden_matches_current_sources():
    from tools.render_asset_transfer_lane_module_custody_v1_golden import FIXTURE, render

    assert FIXTURE.read_text() == render()

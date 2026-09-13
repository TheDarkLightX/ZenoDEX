"""Retained adversarial cases for the pure margin/global candidate boundary."""

from dataclasses import replace

import pytest

from src.core import perps_margin_claims_v2 as claims
from src.core import perps_margin_global_v2 as global_margin
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.global_settlement_types_v2 import LaneIdV2
from src.core.perps_margin_global_v2 import (
    PerpsMarginGlobalAcceptedV2,
    transition_perps_margin_global_v2,
)
from src.core.perps_margin_global_v2 import (
    PerpsMarginGlobalRejectCodeV2 as Reject,
)
from src.core.perps_margin_state_v2 import PerpsMarginStateV2
from tests.core.test_asset_lane_coordinator_v2 import _registry, _root
from tests.core.test_perps_margin_global_v2 import (
    DEPOSIT,
    WITHDRAW,
    _assert_reject,
    _command,
    _initial,
    _occurrence,
    _step,
)


def test_unsupported_consumed_objects_do_not_consume_replay_or_move_value():
    assets, margin, state = _initial()
    command = _command(DEPOSIT, 1, 1)
    occurrence = replace(_occurrence(state, command, 1), consumed_object_ids=("unowned-object",))
    _assert_reject(transition_perps_margin_global_v2(
        assets, margin, state, command, occurrence,
    ), state, Reject.OCCURRENCE_COMMAND_MISMATCH)
    # The same valid occurrence still succeeds after the rejected attempt.
    _step((assets, margin, state), command, 1)


def test_subject_replay_is_independent_of_the_valid_next_account_nonce():
    _, (assets, margin, state) = _step(_initial(), _command(DEPOSIT, 5, 1), 1)
    command = _command(DEPOSIT, 1, 2)
    _assert_reject(transition_perps_margin_global_v2(
        assets, margin, state, command, _occurrence(state, command, 1),
    ), state, Reject.REPLAY_ALREADY_CONSUMED)
    _step((assets, margin, state), command, 2)


def _result_roots(result):
    return (result.post_assets.state_root, result.post_margin.state_root,
            result.post_state.state_root, result.effects.effect_plan_root,
            result.terminal_plan.plan_root)


def test_accepted_constructor_and_getters_own_the_complete_result_graph():
    original, _ = _step(_initial(), _command(DEPOSIT, 5, 1), 1)
    sources = (original.post_assets, original.post_margin, original.post_state,
               original.effects, original.terminal_plan)
    result = PerpsMarginGlobalAcceptedV2(*sources, original.refinement, original.statement_root)
    expected = _result_roots(result)
    borrowed = (result.post_assets, result.post_margin, result.post_state,
                result.effects, result.terminal_plan)
    # Reflection models a hostile holder of a returned/source object, not code
    # with access to the result's private fields or the publisher process.
    for assets, margin, state, effects, plan in (sources, borrowed):
        object.__setattr__(assets, "_custody", ())
        object.__setattr__(margin, "_active_claims", ())
        object.__setattr__(state, "height", state.height + 1)
        object.__setattr__(effects, "_rows", ())
        object.__setattr__(plan, "_deltas", ())
    assert _result_roots(result) == expected
    assert result.refinement.post_state_root == result.post_state.state_root
    assert result.refinement.effect_plan_root == result.effects.effect_plan_root
    assert result.refinement.terminal_plan_root == result.terminal_plan.plan_root


def test_rejection_plans_are_independent_empty_values():
    assets, margin, state = _initial()
    command = _command(DEPOSIT, 101, 1)
    rejected = transition_perps_margin_global_v2(
        assets, margin, state, command, _occurrence(state, command, 1),
    )
    accepted, _ = _step(_initial(), _command(DEPOSIT, 5, 1), 1)
    object.__setattr__(rejected.effects, "_rows", accepted.effects.rows)
    object.__setattr__(rejected.terminal_plan, "_deltas", accepted.terminal_plan.deltas)
    object.__setattr__(rejected.oracle_plan, "_deltas", (object(),))
    _assert_reject(rejected, state, Reject.INSUFFICIENT_BALANCE)


@pytest.mark.parametrize("defect", ["owner", "amount", "domain", "lane", "missing", "extra"])
def test_forged_terminal_attribution_rejects_even_with_a_matching_global_head(defect):
    _, (assets, margin, state) = _step(_initial(), _command(DEPOSIT, 20, 1), 1)
    claim = state.terminal_obligations[0]
    changed = {
        "owner": {"claimant": "mallory"}, "amount": {"amount_atoms": 19},
        "domain": {"liability_domain": "elsewhere"}, "lane": {"lane_id": LaneIdV2.ZUSD_MONETARY},
    }
    if defect == "missing":
        terminals = ()
    elif defect == "extra":
        terminals = tuple(sorted((claim, replace(claim, obligation_id=_root("extra"))),
                                 key=lambda row: row.obligation_id))
    else:
        terminals = (replace(claim, **changed[defect]),)
    forged = replace(state, terminal_obligations=terminals)
    command = _command(WITHDRAW, 1, 2)
    _assert_reject(transition_perps_margin_global_v2(
        assets, margin, forged, command, _occurrence(forged, command, 2),
    ), forged, Reject.PROJECTION_MISMATCH)


def test_swapped_same_owner_bindings_cannot_reattribute_unequal_account_claims():
    _, inputs = _step(_initial(), _command(DEPOSIT, 20, 1), 1)
    _, (assets, margin, state) = _step(inputs, _command(DEPOSIT, 30, 1, "margin-b"), 2)
    first, second = margin.active_claims
    forged = PerpsMarginStateV2(margin.economic_state, (
        replace(first, obligation_id=second.obligation_id),
        replace(second, obligation_id=first.obligation_id),
    ))
    state = replace(state, lane_roots=tuple(
        replace(row, state_root=forged.state_root) if row.lane_id is LaneIdV2.PERPS_MARKET else row
        for row in state.lane_roots
    ))
    command = _command(WITHDRAW, 1, 2)
    _assert_reject(transition_perps_margin_global_v2(
        assets, forged, state, command, _occurrence(state, command, 3),
    ), state, Reject.PROJECTION_MISMATCH)


def test_policy_origin_mismatch_is_checked_after_complete_frame_binding():
    assets, margin, state = _initial()
    leaf = assets.transfer_state
    policies = tuple(replace(p, asset_origin_root=_root("forged-origin")) for p in leaf.policies)
    managed = tuple(replace(p, asset_origin_root=_root("forged-origin")) for p in assets.managed_policies)
    forged = AssetLaneCustodyStateV2(
        replace(leaf, policies=policies), assets.origin_registry, managed, assets.custody,
    )
    state = replace(state, lane_roots=tuple(
        replace(row, state_root=forged.state_root) if row.lane_id is LaneIdV2.ASSET_TRANSFER else row
        for row in state.lane_roots
    ))
    command = _command(DEPOSIT, 1, 1)
    _assert_reject(transition_perps_margin_global_v2(
        forged, margin, state, command, _occurrence(state, command, 1),
    ), state, Reject.ASSET_ORIGIN_MISMATCH)


@pytest.mark.parametrize("defect,code", [("unknown", Reject.UNKNOWN_COLLATERAL),
                                       ("disabled", Reject.DISABLED_COLLATERAL)])
def test_collateral_must_be_registered_and_enabled_in_the_bound_frame(defect, code):
    assets, margin, state = _initial()
    if defect == "unknown":
        margin = PerpsMarginStateV2(replace(margin.economic_state, collateral_asset="EUR"), ())
    else:
        leaf = assets.transfer_state
        policies = tuple(replace(p, enabled=False) for p in leaf.policies)
        assets = AssetLaneCustodyStateV2(
            replace(leaf, policies=policies), _registry(policies, assets.managed_policies),
            assets.managed_policies, assets.custody,
        )
    roots = {LaneIdV2.ASSET_TRANSFER: assets.state_root, LaneIdV2.PERPS_MARKET: margin.state_root}
    state = replace(state, lane_roots=tuple(
        replace(row, state_root=roots[row.lane_id]) if row.lane_id in roots else row
        for row in state.lane_roots
    ))
    command = _command(DEPOSIT, 1, 1)
    _assert_reject(transition_perps_margin_global_v2(
        assets, margin, state, command, _occurrence(state, command, 1),
    ), state, code)


def test_refill_collision_cannot_reopen_a_drained_claim(monkeypatch):
    _, inputs = _step(_initial(), _command(DEPOSIT, 5, 1), 1)
    _, (assets, margin, state) = _step(inputs, _command(WITHDRAW, 5, 2), 2)
    old = state.terminal_obligations[0]
    monkeypatch.setattr(claims, "margin_claim_id_v2", lambda *args: old.obligation_id)
    command = _command(DEPOSIT, 5, 3)
    _assert_reject(transition_perps_margin_global_v2(
        assets, margin, state, command, _occurrence(state, command, 3),
    ), state, Reject.SUCCESSOR_REJECTED)
    assert state.terminal_obligations == (old,)


@pytest.mark.parametrize("fault", ["stale-asset-root", "missing-liability", "wrong-custody-owner"])
def test_projection_and_refinement_reject_corrupted_successor_construction(monkeypatch, fault):
    assets, margin, state = _initial()
    real_rows = global_margin._command_effect_rows
    real_replace = global_margin.replace

    def faulty_rows(command):
        rows = real_rows(command)
        if fault == "missing-liability":
            return rows[:-1]
        return (rows[0], replace(rows[1], principal="mallory"), rows[2])

    def stale_asset_root(row, **fields):
        if getattr(row, "lane_id", None) is LaneIdV2.ASSET_TRANSFER:
            return row
        return real_replace(row, **fields)

    if fault == "stale-asset-root":
        monkeypatch.setattr(global_margin, "replace", stale_asset_root)
    else:
        monkeypatch.setattr(global_margin, "_command_effect_rows", faulty_rows)
    command = _command(DEPOSIT, 1, 1)
    _assert_reject(transition_perps_margin_global_v2(
        assets, margin, state, command, _occurrence(state, command, 1),
    ), state, Reject.SUCCESSOR_REJECTED)

"""Connected margin/asset histories over actual pure V2 global candidates."""

from dataclasses import replace

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_global_v2 import derive_asset_lane_custody_global_post_v2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_economic_state_v2 import GlobalEconomicStateV2, LaneStateRootV2
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    ZERO_ROOT_V2,
    LaneIdV2,
    TerminalObligationStatusV2,
    hash_economic_command_body_v2,
)
from src.core.perps_margin_global_v2 import (
    PerpsMarginGlobalAcceptedV2,
    PerpsMarginGlobalRejectCodeV2,
    PerpsMarginGlobalRejectedV2,
    transition_perps_margin_global_v2,
)
from src.core.perps_margin_state_v2 import PerpsMarginStateV2
from src.core.perps_margin_types_v1 import (
    PERPS_MARGIN_CLOSE_COMMAND_KIND_V1 as CLOSE,
)
from src.core.perps_margin_types_v1 import (
    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1 as DEPOSIT,
)
from src.core.perps_margin_types_v1 import (
    PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1 as WITHDRAW,
)
from src.core.perps_margin_types_v1 import (
    PerpsMarginAccountStatusV1,
    PerpsMarginCommandV1,
    PerpsMarginRejectCodeV1,
)
from tests.core.test_asset_lane_coordinator_v2 import _root, _transfer_command
from tests.core.test_asset_lane_custody_v2 import custody_state
from tests.core.test_perps_margin_module_v1 import _state


def _initial():
    assets = custody_state(accounts=100, custody=0)
    margin = PerpsMarginStateV2(replace(_state(), collateral_asset="USD"), ())
    roots = {
        LaneIdV2.ASSET_TRANSFER: (assets.transfer_state.module_release_id, assets.state_root),
        LaneIdV2.PERPS_MARKET: (margin.economic_state.module_release_id, margin.state_root),
    }
    state = GlobalEconomicStateV2(
        "margin-test", _root("deployment"), 7, 0, _root("profile"),
        tuple(LaneStateRootV2(
            lane, roots.get(lane, (_root(lane.value), ZERO_ROOT_V2))[0],
            lane in roots, roots.get(lane, (None, ZERO_ROOT_V2))[1],
        ) for lane in ALL_LANE_IDS_V2),
        balances=assets.transfer_state.balances,
        supplies=assets.transfer_state.supplies,
    )
    return assets, margin, state


def _command(kind, amount, nonce, account="margin-a", owner="alice"):
    return PerpsMarginCommandV1(kind, account, "perp-btc-usd", owner, "USD", amount, nonce)


def _occurrence(state, command, nonce):
    return EconomicCommandOccurrenceV2(
        state.chain_id, state.deployment_root, state.height + 1, 0, 0,
        command.command_kind,
        hash_economic_command_body_v2(command.command_kind, command),
        _root("route"), command.owner, _root("grant"), nonce,
        state.profile_root, state.state_root, (),
    )


def _step(inputs, command, outer_nonce):
    assets, margin, state = inputs
    before = (assets.state_root, margin.state_root, state.state_root)
    result = transition_perps_margin_global_v2(
        assets, margin, state, command, _occurrence(state, command, outer_nonce)
    )
    assert (assets.state_root, margin.state_root, state.state_root) == before
    assert type(result) is PerpsMarginGlobalAcceptedV2
    assert result.refinement.post_state_root == result.post_state.state_root
    assert result.refinement.production_authority == "NONE"
    assert result.post_state.supplies == state.supplies
    return result, (result.post_assets, result.post_margin, result.post_state)


def _assert_reject(result, state, code):
    assert type(result) is PerpsMarginGlobalRejectedV2
    assert result.code is code
    assert result.pre_state_root == result.post_state_root == state.state_root
    assert result.effects.is_empty
    assert result.terminal_plan.deltas == ()
    assert result.oracle_plan.deltas == ()


def test_given_margin_claim_when_drained_transferred_refilled_and_closed_then_history_composes():
    inputs = _initial()
    deposited, inputs = _step(inputs, _command(DEPOSIT, 40, 1), 1)
    old_claim = deposited.post_margin.claim_id("margin-a")
    assert {w.lane_id for w in deposited.effects.lane_writes} == {
        LaneIdV2.ASSET_TRANSFER, LaneIdV2.PERPS_MARKET,
    }
    _, inputs = _step(inputs, _command(WITHDRAW, 10, 2), 2)
    drained, inputs = _step(inputs, _command(WITHDRAW, 30, 3), 3)
    old_record = drained.post_state.terminal_obligations[0]
    assert old_record.obligation_id == old_claim
    assert old_record.status is TerminalObligationStatusV2.DRAINED
    assert old_record.amount_atoms == 30
    assert drained.post_margin.claim_id("margin-a") is None
    assert drained.post_margin.economic_state.accounts[0].status is PerpsMarginAccountStatusV1.OPEN

    # The existing ordinary-transfer implementation consumes the synchronized
    # asset frame. Its authenticated context remains synthetic in this test.
    assets, margin, state = inputs
    transfer = _transfer_command(amount_atoms=5)
    occurrence = EconomicCommandOccurrenceV2(
        state.chain_id, state.deployment_root, state.height + 1, 0, 0,
        transfer.command_kind, transfer.command_body_hash,
        _root("asset-route"), "alice", _root("grant"), 4,
        state.profile_root, state.state_root, (),
    )
    accepted = transition_asset_lane_custody_v2(
        AssetLaneContextV2(state.writer_epoch, assets.transfer_state.module_release_id,
                           state.state_root, occurrence), assets, transfer,
    )
    assert type(accepted) is AssetLaneCustodyAcceptedV2
    after_transfer = derive_asset_lane_custody_global_post_v2(assets, accepted, state, occurrence)
    assert after_transfer.terminal_obligations == state.terminal_obligations
    assert next(r.state_root for r in after_transfer.lane_roots
                if r.lane_id is LaneIdV2.PERPS_MARKET) == margin.state_root
    inputs = (accepted.post_state, margin, after_transfer)

    refilled, inputs = _step(inputs, _command(DEPOSIT, 20, 4), 5)
    assert refilled.post_margin.claim_id("margin-a") != old_claim
    assert old_record in refilled.post_state.terminal_obligations
    _, inputs = _step(inputs, _command(WITHDRAW, 20, 5), 6)
    closed, inputs = _step(inputs, _command(CLOSE, 0, 6), 7)
    assert closed.post_margin.economic_state.accounts[0].status is PerpsMarginAccountStatusV1.CLOSED
    assert closed.terminal_plan.deltas == ()
    assert {w.lane_id for w in closed.effects.lane_writes} == {LaneIdV2.PERPS_MARKET}
    assert len(closed.post_state.replay_state) == 7
    assert all(r.status is TerminalObligationStatusV2.DRAINED
               for r in closed.post_state.terminal_obligations)
    assets, margin, state = inputs
    command = _command(DEPOSIT, 1, 7)
    result = transition_perps_margin_global_v2(
        assets, margin, state, command, _occurrence(state, command, 8)
    )
    _assert_reject(result, state, PerpsMarginRejectCodeV1.ACCOUNT_CLOSED)


def test_same_owner_accounts_have_distinct_claims_and_independent_account_nonces():
    _, inputs = _step(_initial(), _command(DEPOSIT, 25, 1, "margin-a"), 1)
    second, inputs = _step(inputs, _command(DEPOSIT, 25, 1, "margin-b"), 2)
    assert len({r.obligation_id for r in second.post_state.terminal_obligations}) == 2
    assert second.post_state.liabilities[0].amount_atoms == 50
    _, inputs = _step(inputs, _command(WITHDRAW, 25, 2, "margin-a"), 3)
    _, margin, state = inputs
    assert margin.claim_id("margin-a") is None
    assert margin.claim_id("margin-b") is not None
    assert state.liabilities[0].amount_atoms == 25


@pytest.mark.parametrize("defect,code", [
    ("body", PerpsMarginGlobalRejectCodeV2.OCCURRENCE_COMMAND_MISMATCH),
    ("head", PerpsMarginGlobalRejectCodeV2.OCCURRENCE_CONTEXT_MISMATCH),
    ("balance", PerpsMarginGlobalRejectCodeV2.INSUFFICIENT_BALANCE),
    ("subject", PerpsMarginRejectCodeV1.UNAUTHORIZED_SUBJECT),
])
def test_rejected_attempts_preserve_global_claims_replay_and_all_inputs(defect, code):
    assets, margin, state = _initial()
    command = _command(DEPOSIT, 101 if defect == "balance" else 10, 1)
    occurrence = _occurrence(state, command, 1)
    if defect == "body":
        occurrence = replace(occurrence, command_body_hash=_root("wrong-body"))
    elif defect == "head":
        occurrence = replace(occurrence, pre_state_root=_root("stale-head"))
    elif defect == "subject":
        occurrence = replace(occurrence, subject_id="mallory")
    before = (assets.state_root, margin.state_root, state.state_root)
    for _ in range(2):
        _assert_reject(transition_perps_margin_global_v2(
            assets, margin, state, command, occurrence
        ), state, code)
        assert (assets.state_root, margin.state_root, state.state_root) == before


def test_stale_asset_frame_cannot_follow_a_valid_margin_withdrawal():
    initial = _initial()
    _, inputs = _step(initial, _command(DEPOSIT, 25, 1), 1)
    command = _command(WITHDRAW, 5, 2)
    assets, margin, state = inputs
    _assert_reject(transition_perps_margin_global_v2(
        initial[0], margin, state, command, _occurrence(state, command, 2)
    ), state, PerpsMarginGlobalRejectCodeV2.PROJECTION_MISMATCH)


@given(st.lists(st.tuples(st.sampled_from((DEPOSIT, WITHDRAW)), st.integers(0, 110),
                          st.sampled_from(("margin-a", "margin-b"))), max_size=16))
@settings(max_examples=16, deadline=None, derandomize=True)
def test_histories_match_independent_wallet_custody_and_claim_accounting(actions):
    inputs = _initial()
    wallet, accepted_count = 100, 0
    collateral, nonces, drained = {}, {}, {}
    # Every generated history reaches a drained claim before arbitrary actions.
    actions = [(DEPOSIT, 1, "margin-a"), (WITHDRAW, 1, "margin-a"), *actions]
    for outer_nonce, (kind, amount, account) in enumerate(actions, 1):
        assets, margin, state = inputs
        command = _command(kind, amount, nonces.get(account, 0) + 1, account)
        before = tuple(value.state_root for value in inputs)
        result = transition_perps_margin_global_v2(
            assets, margin, state, command, _occurrence(state, command, outer_nonce),
        )
        available = wallet if kind == DEPOSIT else collateral.get(account, 0)
        should_accept = 0 < amount <= available
        assert (type(result) is PerpsMarginGlobalAcceptedV2) == should_accept
        assert tuple(value.state_root for value in inputs) == before
        if not should_accept:
            _assert_reject(result, state, result.code)
            continue
        delta = amount if kind == DEPOSIT else -amount
        wallet -= delta
        collateral[account] = collateral.get(account, 0) + delta
        nonces[account] = command.nonce
        accepted_count += 1
        inputs = result.post_assets, result.post_margin, result.post_state
        _, margin, state = inputs
        assert sum(row.amount_atoms for row in state.balances) == wallet
        assert {row.owner: row.amount_atoms for row in state.custody} == {
            key: amount for key, amount in collateral.items() if amount
        }
        total = sum(collateral.values())
        assert wallet + total == 100
        assert sum(row.amount_atoms for row in state.liabilities) == total
        assert len(state.replay_state) == accepted_count
        assert {row.account_id: row.nonce for row in margin.economic_state.accounts} == nonces
        terminals = {row.obligation_id: row for row in state.terminal_obligations}
        assert all(terminals[key] == record for key, record in drained.items())
        assert sum(row.amount_atoms for row in terminals.values()
                   if row.status is TerminalObligationStatusV2.OPEN) == total
        drained.update((key, row) for key, row in terminals.items()
                       if row.status is TerminalObligationStatusV2.DRAINED)

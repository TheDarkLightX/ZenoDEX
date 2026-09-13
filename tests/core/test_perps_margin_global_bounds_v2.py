"""Resource and lifecycle boundaries for the connected margin V2 candidate."""

from dataclasses import replace

import pytest

import src.core.global_economic_state_v2 as global_state_module
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_transfer_types_v2 import AssetTransferStateV2
from src.core.global_economic_state_ownership_v2 import ReplayStateV2
from src.core.global_settlement_types_v2 import (
    MAX_BALANCE_ROWS_PER_ASSET_STATE_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    LaneIdV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
    hash_global_v2,
)
from src.core.perps_margin_global_v2 import (
    PerpsMarginGlobalAcceptedV2,
    PerpsMarginGlobalRejectCodeV2,
    PerpsMarginOracleV2,
    transition_perps_margin_global_v2,
)
from src.core.perps_margin_state_v2 import (
    PerpsMarginClaimBindingV2,
    PerpsMarginStateV2,
    margin_claim_id_v2,
)
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
    PerpsMarginMarketStatusV1,
    PerpsMarginRejectCodeV1,
)
from tests.core.test_perps_margin_global_v2 import (
    _assert_reject,
    _command,
    _initial,
    _occurrence,
    _step,
)
from tests.core.test_perps_margin_module_v1 import _counterparty


def _root(label: str) -> str:
    return hash_global_v2("perps-margin-bounds-test-v2", {"label": label})


def _with_margin_status(inputs, status: PerpsMarginMarketStatusV1):
    assets, margin, state = inputs
    successor = PerpsMarginStateV2(
        replace(margin.economic_state, market_status=status), margin.active_claims
    )
    lane_roots = tuple(
        replace(row, state_root=successor.state_root)
        if row.lane_id is LaneIdV2.PERPS_MARKET
        else row
        for row in state.lane_roots
    )
    return assets, successor, replace(state, lane_roots=lane_roots)


def _full_terminal_rows(
    open_row: TerminalObligationV2, capacity: int
) -> tuple[TerminalObligationV2, ...]:
    fillers = tuple(
        TerminalObligationV2(
            f"terminal-filler-{index:05d}",
            LaneIdV2.ASSET_TRANSFER,
            "terminal-filler",
            "USD",
            "terminal-filler",
            1,
            TerminalObligationStatusV2.DRAINED,
        )
        for index in range(capacity - 1)
    )
    return tuple(sorted((*fillers, open_row), key=lambda row: row.obligation_id))


def _full_asset_balance_inputs(inputs):
    assets, margin, state = inputs
    balances = tuple(
        EconomicAmountV2(f"account-{index:04d}", "USD", "accounts", 1)
        for index in range(MAX_BALANCE_ROWS_PER_ASSET_STATE_V2)
    )
    supply = (AssetSupplyV2("USD", MAX_BALANCE_ROWS_PER_ASSET_STATE_V2 + 1),)
    leaf = assets.transfer_state
    full_assets = AssetLaneCustodyStateV2(
        AssetTransferStateV2(leaf.module_release_id, leaf.policies, balances, supply),
        assets.origin_registry,
        assets.managed_policies,
        assets.custody,
    )
    lane_roots = tuple(
        replace(row, state_root=full_assets.state_root)
        if row.lane_id is LaneIdV2.ASSET_TRANSFER
        else row
        for row in state.lane_roots
    )
    return (
        full_assets,
        margin,
        replace(state, balances=balances, supplies=supply, lane_roots=lane_roots),
    )


def _nonflat_inputs():
    deposited, inputs = _step(
        _initial(), _command(DEPOSIT, 25, 1, "perps-account-1", "alice"), 1
    )
    assets, margin, state = inputs
    first = replace(margin.economic_state.accounts[0], position_base=1, entry_price_e8=1)
    second = _counterparty(collateral_atoms=25, position_base=-1, entry_price_e8=1)
    economic = replace(
        margin.economic_state,
        index_price_e8=1,
        accounts=(first, second),
    )
    first_claim = margin.claim_id("perps-account-1")
    assert first_claim is not None
    second_claim = margin_claim_id_v2(economic, "perps-account-2", _root("opening-b"))
    successor_margin = PerpsMarginStateV2(
        economic,
        (
            PerpsMarginClaimBindingV2("perps-account-1", first_claim),
            PerpsMarginClaimBindingV2("perps-account-2", second_claim),
        ),
    )
    second_obligation = TerminalObligationV2(
        second_claim,
        LaneIdV2.PERPS_MARKET,
        "bob",
        "USD",
        "perps_margin",
        25,
        TerminalObligationStatusV2.OPEN,
    )
    terminals = tuple(
        sorted((*state.terminal_obligations, second_obligation), key=lambda row: row.obligation_id)
    )
    balances = (EconomicAmountV2("alice", "USD", "accounts", 50),)
    custody = (
        EconomicAmountV2("perps-account-1", "USD", "perps_margin", 25),
        EconomicAmountV2("perps-account-2", "USD", "perps_margin", 25),
    )
    leaf = assets.transfer_state
    successor_assets = AssetLaneCustodyStateV2(
        AssetTransferStateV2(leaf.module_release_id, leaf.policies, balances, leaf.supplies),
        assets.origin_registry,
        assets.managed_policies,
        custody,
    )
    lane_roots = tuple(
        replace(
            row,
            state_root=(
                successor_assets.state_root
                if row.lane_id is LaneIdV2.ASSET_TRANSFER
                else successor_margin.state_root
            ),
        )
        if row.lane_id in {LaneIdV2.ASSET_TRANSFER, LaneIdV2.PERPS_MARKET}
        else row
        for row in state.lane_roots
    )
    successor_state = replace(
        state,
        balances=balances,
        custody=custody,
        liabilities=(
            EconomicAmountV2("alice", "USD", "perps_margin", 25),
            EconomicAmountV2("bob", "USD", "perps_margin", 25),
        ),
        terminal_obligations=terminals,
        lane_roots=lane_roots,
    )
    return successor_assets, successor_margin, successor_state


def test_replay_table_exhaustion_rejects_without_partial_result(monkeypatch):
    assets, margin, state = _initial()
    # The production table is 65,536 rows; this scoped seam keeps the branch
    # test fast while leaving the production constant untouched after the test.
    capacity = 1
    monkeypatch.setattr(global_state_module, "MAX_GLOBAL_REPLAY_ROWS_V2", capacity)
    replay = tuple(
        ReplayStateV2(f"replay-{index:05d}", _root(f"occurrence-{index}"))
        for index in range(capacity)
    )
    full = replace(state, replay_state=replay)
    before = (assets.state_root, margin.state_root, full.state_root)
    command = _command(DEPOSIT, 1, 1)
    result = transition_perps_margin_global_v2(
        assets, margin, full, command, _occurrence(full, command, 1)
    )
    _assert_reject(result, full, PerpsMarginGlobalRejectCodeV2.SUCCESSOR_REJECTED)
    assert (assets.state_root, margin.state_root, full.state_root) == before


def test_terminal_table_exhaustion_allows_existing_lifecycle_without_new_slot(monkeypatch):
    deposited, inputs = _step(_initial(), _command(DEPOSIT, 40, 1), 1)
    assets, margin, state = inputs
    claim_id = margin.claim_id("margin-a")
    assert claim_id is not None
    open_row = next(row for row in state.terminal_obligations if row.obligation_id == claim_id)
    # A two-row seam exercises the same post-state overflow branch without a
    # repeated 65,536-row canonical snapshot for every lifecycle step.
    capacity = 2
    monkeypatch.setattr(global_state_module, "MAX_GLOBAL_TERMINAL_ROWS_V2", capacity)
    full = replace(state, terminal_obligations=_full_terminal_rows(open_row, capacity))
    inputs = assets, margin, full

    updated, inputs = _step(inputs, _command(WITHDRAW, 10, 2), 2)
    assert len(updated.post_state.terminal_obligations) == capacity
    assert next(row for row in updated.post_state.terminal_obligations if row.obligation_id == claim_id).amount_atoms == 30
    drained, inputs = _step(inputs, _command(WITHDRAW, 30, 3), 3)
    drained_row = next(row for row in drained.post_state.terminal_obligations if row.obligation_id == claim_id)
    assert len(drained.post_state.terminal_obligations) == capacity
    assert drained_row.status is TerminalObligationStatusV2.DRAINED

    assets, margin, state = inputs
    before = (assets.state_root, margin.state_root, state.state_root)
    refill = _command(DEPOSIT, 20, 4)
    result = transition_perps_margin_global_v2(
        assets, margin, state, refill, _occurrence(state, refill, 4)
    )
    _assert_reject(result, state, PerpsMarginGlobalRejectCodeV2.SUCCESSOR_REJECTED)
    assert (assets.state_root, margin.state_root, state.state_root) == before

    closed, inputs = _step(inputs, _command(CLOSE, 0, 4), 4)
    assert len(closed.post_state.terminal_obligations) == capacity
    assert closed.post_margin.economic_state.accounts[0].status is PerpsMarginAccountStatusV1.CLOSED


def test_absent_withdrawal_destination_at_asset_balance_capacity_is_noop():
    deposited, inputs = _step(_initial(), _command(DEPOSIT, 1, 1), 1)
    saturated = _full_asset_balance_inputs(inputs)
    assets, margin, state = saturated
    command = _command(WITHDRAW, 1, 2)
    before = (assets.state_root, margin.state_root, state.state_root)
    result = transition_perps_margin_global_v2(
        assets, margin, state, command, _occurrence(state, command, 2)
    )
    _assert_reject(result, state, PerpsMarginGlobalRejectCodeV2.SUCCESSOR_REJECTED)
    assert (assets.state_root, margin.state_root, state.state_root) == before


def test_drain_only_allows_withdraw_and_empty_close_but_rejects_deposit():
    _, inputs = _step(_initial(), _command(DEPOSIT, 10, 1), 1)
    inputs = _with_margin_status(inputs, PerpsMarginMarketStatusV1.DRAIN_ONLY)
    assets, margin, state = inputs
    deposit = _command(DEPOSIT, 1, 2)
    _assert_reject(
        transition_perps_margin_global_v2(
            assets, margin, state, deposit, _occurrence(state, deposit, 2)
        ),
        state,
        PerpsMarginRejectCodeV1.MARKET_DRAIN_ONLY,
    )
    _, inputs = _step(inputs, _command(WITHDRAW, 10, 2), 2)
    closed, _ = _step(inputs, _command(CLOSE, 0, 3), 3)
    assert closed.post_margin.economic_state.accounts[0].status is PerpsMarginAccountStatusV1.CLOSED


@pytest.mark.parametrize(
    ("kind", "amount"),
    ((DEPOSIT, 1), (WITHDRAW, 1), (CLOSE, 0)),
    ids=("deposit", "withdraw", "close"),
)
def test_halted_market_rejects_every_margin_command(kind: str, amount: int):
    inputs = _with_margin_status(_initial(), PerpsMarginMarketStatusV1.HALTED)
    assets, margin, state = inputs
    command = _command(kind, amount, 1)
    result = transition_perps_margin_global_v2(
        assets, margin, state, command, _occurrence(state, command, 1)
    )
    _assert_reject(result, state, PerpsMarginRejectCodeV1.HALTED_MARKET)


@pytest.mark.parametrize(
    ("amount", "oracle", "expected"),
    (
        (24, PerpsMarginOracleV2(_root("authority"), _root("oracle"), 1), None),
        (24, None, PerpsMarginRejectCodeV1.ORACLE_AUTHORITY_MISSING),
        (24, PerpsMarginOracleV2(_root("authority"), _root("oracle"), 2), PerpsMarginRejectCodeV1.ORACLE_PRICE_MISMATCH),
        (25, PerpsMarginOracleV2(_root("authority"), _root("oracle"), 1), PerpsMarginRejectCodeV1.MAINTENANCE_BREACH),
    ),
    ids=("maintenance-edge-accepted", "oracle-missing", "oracle-wrong-price", "maintenance-breach"),
)
def test_nonflat_plus_minus_one_positions_use_oracle_and_maintenance_boundaries(
    amount: int, oracle: PerpsMarginOracleV2 | None, expected: PerpsMarginRejectCodeV1 | None
):
    inputs = _nonflat_inputs()
    assets, margin, state = inputs
    command = _command(WITHDRAW, amount, 2, "perps-account-1", "alice")
    result = transition_perps_margin_global_v2(
        assets, margin, state, command, _occurrence(state, command, 2), oracle
    )
    if expected is None:
        assert type(result) is PerpsMarginGlobalAcceptedV2
        assert result.post_margin.economic_state.accounts[0].collateral_atoms == 1
        assert result.post_margin.economic_state.accounts[0].position_base == 1
        assert result.post_margin.economic_state.accounts[1].position_base == -1
    else:
        _assert_reject(result, state, expected)

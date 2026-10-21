from __future__ import annotations

from typing import cast

from src.core.dex import DexState
from src.core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
from src.core.perp_v2.math import MAX_COLLATERAL
from src.core.perps import (
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpMarketState,
    PerpsState,
)
from src.integration.perp_engine import PerpEngineConfig, PerpTxResult, apply_perp_ops
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.perps_funding_transitions import (
    IsolatedFundingTransitionOkV1,
    apply_isolated_funding_auto_v1,
)
from src.state.perps_settlement_transitions import (
    IsolatedSettlementTransitionOkV1,
    apply_isolated_settle_epoch_v1,
)
from src.state.perps_state_transitions import (
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
)
from src.state.state_snapshot_values import (
    CommittedPerpMarketStateV1,
)
from src.state.state_snapshots import snapshot_perps

_ALICE = "0x" + "11" * 48
_BOB = "0x" + "22" * 48
_OPERATOR = "00" * 48
_MARKET_ID = "perp:test"
_QUOTE_ASSET = "0x" + "44" * 32


def _global(
    *,
    index_price_e8: int = 100_000_000,
    clearing_price_e8: int = 105_000_000,
    fee_pool_quote: int = 0,
    min_notional_for_bounty: int = 200,
) -> dict[str, int | bool]:
    return {
        "now_epoch": 3,
        "epoch_phase": 1,
        "breaker_active": False,
        "breaker_last_trigger_epoch": 0,
        "clearing_price_seen": True,
        "clearing_price_epoch": 3,
        "clearing_price_e8": clearing_price_e8,
        "mark_price_source_kind": MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
        "oracle_seen": True,
        "oracle_last_update_epoch": 2,
        "index_price_e8": index_price_e8,
        "max_oracle_staleness_epochs": 2,
        "max_oracle_move_bps": 500,
        "initial_margin_bps": 1_000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 50,
        "max_position_abs": 1_000_000,
        "fee_pool_quote": fee_pool_quote,
        "funding_rate_bps": 0,
        "funding_cap_bps": 100,
        "insurance_balance": fee_pool_quote,
        "initial_insurance": 0,
        "fee_income": fee_pool_quote,
        "claims_paid": 0,
        "min_notional_for_bounty": min_notional_for_bounty,
    }


def _account(
    *,
    position_base: int,
    entry_price_e8: int = 100_000_000,
    collateral_quote: int = 100_000,
    funding_last_applied_epoch: int = 2,
) -> PerpAccountState:
    return PerpAccountState(
        position_base=position_base,
        entry_price_e8=0 if position_base == 0 else entry_price_e8,
        collateral_quote=collateral_quote,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=funding_last_applied_epoch,
        liquidated_this_step=False,
    )


def _exact_market(
    accounts: dict[str, PerpAccountState],
    *,
    global_state: dict[str, int | bool] | None = None,
) -> CommittedPerpMarketStateV1:
    committed = snapshot_perps(
        PerpsState(
            version=PERPS_STATE_VERSION_V5,
            markets={
                _MARKET_ID: PerpMarketState(
                    quote_asset=_QUOTE_ASSET,
                    global_state=_global() if global_state is None else global_state,
                    accounts=accounts,
                )
            },
        )
    )
    assert committed is not None
    market = committed.get_market(_MARKET_ID)
    assert type(market) is CommittedPerpMarketStateV1
    return market


def _legacy_market(pre: CommittedPerpMarketStateV1) -> PerpMarketState:
    accounts = {
        account_pubkey: PerpAccountState(
            position_base=account.position_base,
            entry_price_e8=account.entry_price_e8,
            collateral_quote=account.collateral_quote,
            funding_paid_cumulative=account.funding_paid_cumulative,
            funding_last_applied_epoch=account.funding_last_applied_epoch,
            liquidated_this_step=account.liquidated_this_step,
        )
        for account_pubkey, account in pre.account_entries
    }
    return PerpMarketState(
        quote_asset=pre.quote_asset,
        global_state=dict(pre.global_entries),
        accounts=accounts,
    )


def _mounted_result(
    pre: CommittedPerpMarketStateV1,
    *,
    action: str,
) -> PerpTxResult:
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION_V5,
            markets={_MARKET_ID: _legacy_market(pre)},
        ),
    )
    return apply_perp_ops(
        config=PerpEngineConfig(
            operator_pubkey=_OPERATOR,
            allow_isolated_markets=True,
        ),
        state=state,
        operations={
            "5": [
                {
                    "module": "TauPerp",
                    "version": "0.1",
                    "market_id": _MARKET_ID,
                    "action": action,
                }
            ]
        },
        tx_sender_pubkey=_OPERATOR,
        block_timestamp=0,
    )


def _mounted_market(
    pre: CommittedPerpMarketStateV1,
    *,
    action: str,
) -> CommittedPerpMarketStateV1:
    result = _mounted_result(pre, action=action)
    assert result.ok is True, result.error
    assert result.state is not None
    assert result.state.perps is not None
    mounted = result.state.perps.markets[_MARKET_ID]
    if type(mounted) is CommittedPerpMarketStateV1:
        return mounted
    assert type(mounted) is PerpMarketState
    return _exact_market(
        dict(mounted.accounts),
        global_state=dict(mounted.global_state),
    )


def _assert_patches_replay(
    pre: CommittedPerpMarketStateV1,
    result: IsolatedFundingTransitionOkV1 | IsolatedSettlementTransitionOkV1,
) -> None:
    replayed_globals = dict(pre.global_entries)
    if result.global_patch is not None:
        for global_write in result.global_patch.writes:
            assert replayed_globals[global_write.field] == global_write.expected
            replayed_globals[global_write.field] = global_write.replacement
    assert replayed_globals == dict(result.market.global_entries)

    replayed_accounts = dict(pre.account_entries)
    if result.account_patch is not None:
        keys = tuple(write.account_pubkey for write in result.account_patch.writes)
        assert keys == tuple(sorted(keys))
        for account_write in result.account_patch.writes:
            assert replayed_accounts[account_write.account_pubkey] is account_write.expected
            replayed_accounts[account_write.account_pubkey] = account_write.replacement
    assert tuple(sorted(replayed_accounts.items())) == result.market.account_entries


def test_funding_candidate_matches_mounted_path_and_replays_both_patches() -> None:
    pre = _exact_market(
        {
            _ALICE: _account(position_base=2_000, collateral_quote=100_000),
            _BOB: _account(position_base=-1_000, collateral_quote=100_000),
        }
    )

    result = apply_isolated_funding_auto_v1(pre, operator_authorized=True)

    assert type(result) is IsolatedFundingTransitionOkV1
    assert result.market == _mounted_market(pre, action="apply_funding_auto")
    assert result.applied_account_count == 2
    assert result.projected_net_funding_quote > 0
    assert result.account_patch is not None
    assert result.global_patch is not None
    _assert_patches_replay(pre, result)
    assert pre.global_value("fee_pool_quote") == 0
    assert pre.get_account(_ALICE).funding_last_applied_epoch == 2


def test_funding_empty_open_interest_shares_accounts_and_matches_mount() -> None:
    pre = _exact_market({_ALICE: _account(position_base=0, collateral_quote=10)})

    result = apply_isolated_funding_auto_v1(pre, operator_authorized=True)

    assert type(result) is IsolatedFundingTransitionOkV1
    assert result.market == _mounted_market(pre, action="apply_funding_auto")
    assert result.account_patch is None
    assert result.market.accounts is pre.accounts
    assert result.applied_account_count == 0
    _assert_patches_replay(pre, result)


def test_funding_rejects_candidate_that_would_destroy_settlement_path() -> None:
    fee_pool = MAX_COLLATERAL - 120_000
    short_account = "0x" + "ff" * 48
    accounts = {
        "0x" + f"{index + 1:096x}": _account(
            position_base=1_000_000,
            collateral_quote=70_000,
        )
        for index in range(13)
    }
    accounts[short_account] = _account(
        position_base=-1_000_000,
        collateral_quote=60_000,
    )
    pre = _exact_market(
        accounts,
        global_state=_global(
            fee_pool_quote=fee_pool,
            min_notional_for_bounty=0,
        ),
    )

    result = apply_isolated_funding_auto_v1(pre, operator_authorized=True)
    mounted = _mounted_result(pre, action="apply_funding_auto")

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.SETTLEMENT_PATH,
        ("state", "settlement", "kernel", "accounts", short_account),
        "guard",
    )
    assert not hasattr(result, "market")
    assert mounted.ok is False
    assert mounted.state is None
    assert mounted.effects is None
    assert pre.global_value("fee_pool_quote") == fee_pool


def test_funding_operator_and_epoch_rejections_have_no_candidate() -> None:
    pre = _exact_market({_ALICE: _account(position_base=1_000)})
    unauthorized = apply_isolated_funding_auto_v1(pre, operator_authorized=False)
    already_applied = _exact_market(
        {
            _ALICE: _account(
                position_base=1_000,
                funding_last_applied_epoch=3,
            )
        }
    )
    repeated = apply_isolated_funding_auto_v1(
        already_applied,
        operator_authorized=True,
    )

    assert unauthorized == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
        ("gate",),
        "OperatorOnly",
    )
    assert repeated == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.FUNDING_GATE,
        ("gate", "funding"),
        "funding already applied this epoch",
    )
    assert not hasattr(unauthorized, "market")
    assert not hasattr(repeated, "market")


def test_settlement_candidate_matches_mount_and_replays_aggregate_patch() -> None:
    index_price = 100_000_000_000
    pre = _exact_market(
        {
            _ALICE: _account(
                position_base=1_000_000,
                entry_price_e8=index_price,
                collateral_quote=100_000_000,
            ),
            _BOB: _account(
                position_base=-1_000_000,
                entry_price_e8=index_price,
                collateral_quote=100_000_000,
            ),
        },
        global_state=_global(
            index_price_e8=index_price,
            clearing_price_e8=95_000_000_000,
        ),
    )

    result = apply_isolated_settle_epoch_v1(pre, operator_authorized=True)

    assert type(result) is IsolatedSettlementTransitionOkV1
    assert result.market == _mounted_market(pre, action="settle_epoch")
    assert result.fee_pool_delta_quote == 4_750_000
    assert result.account_patch is not None
    assert len(result.account_patch.writes) == 2
    _assert_patches_replay(pre, result)
    assert result.market.get_account(_ALICE).position_base == 0
    assert result.market.get_account(_BOB).position_base == -1_000_000


def test_settlement_flat_accounts_share_the_account_table() -> None:
    pre = _exact_market({_ALICE: _account(position_base=0, collateral_quote=10)})

    result = apply_isolated_settle_epoch_v1(pre, operator_authorized=True)

    assert type(result) is IsolatedSettlementTransitionOkV1
    assert result.market == _mounted_market(pre, action="settle_epoch")
    assert result.account_patch is None
    assert result.market.accounts is pre.accounts
    assert result.fee_pool_delta_quote == 0
    _assert_patches_replay(pre, result)


def test_settlement_rejects_aggregate_fee_overflow_after_individual_checks() -> None:
    index_price = 100_000_000_000
    fee_pool = MAX_COLLATERAL - 5_000_000
    pre = _exact_market(
        {
            _ALICE: _account(
                position_base=1_000_000,
                entry_price_e8=index_price,
                collateral_quote=100_000_000,
            ),
            _BOB: _account(
                position_base=1_000_000,
                entry_price_e8=index_price,
                collateral_quote=100_000_000,
            ),
        },
        global_state=_global(
            index_price_e8=index_price,
            clearing_price_e8=95_000_000_000,
            fee_pool_quote=fee_pool,
        ),
    )

    result = apply_isolated_settle_epoch_v1(pre, operator_authorized=True)
    mounted = _mounted_result(pre, action="settle_epoch")

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.SETTLEMENT_PATH,
        ("state", "global"),
        "fee_or_insurance_out_of_bounds",
    )
    assert not hasattr(result, "market")
    assert mounted.ok is False
    assert mounted.state is None
    assert mounted.effects is None
    assert pre.global_value("fee_pool_quote") == fee_pool


def test_settlement_operator_precedence_and_corrupted_prestate_fail_closed() -> None:
    pre = _exact_market({_ALICE: _account(position_base=0)})
    unauthorized = apply_isolated_settle_epoch_v1(pre, operator_authorized=False)
    object.__setattr__(pre.accounts, "_schema_id", "corrupted")
    corrupted = apply_isolated_settle_epoch_v1(pre, operator_authorized=True)

    assert unauthorized == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
        ("gate",),
        "OperatorOnly",
    )
    assert corrupted == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.INVALID_PRESTATE,
        ("state",),
    )


def test_epoch_candidates_are_independent_of_source_account_insertion_order() -> None:
    accounts = {
        _ALICE: _account(position_base=2_000),
        _BOB: _account(position_base=-1_000),
    }
    forward = _exact_market(accounts)
    reverse = _exact_market(dict(reversed(tuple(accounts.items()))))

    assert forward == reverse
    assert apply_isolated_funding_auto_v1(
        forward,
        operator_authorized=True,
    ) == apply_isolated_funding_auto_v1(
        reverse,
        operator_authorized=True,
    )
    assert apply_isolated_settle_epoch_v1(
        forward,
        operator_authorized=True,
    ) == apply_isolated_settle_epoch_v1(
        reverse,
        operator_authorized=True,
    )


def test_wrong_exact_prestate_rejects_before_operator_or_kernel_work() -> None:
    wrong = cast(CommittedPerpMarketStateV1, object())

    funding = apply_isolated_funding_auto_v1(wrong, operator_authorized=False)
    settlement = apply_isolated_settle_epoch_v1(wrong, operator_authorized=False)

    expected = IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
        ("state",),
    )
    assert funding == expected
    assert settlement == expected

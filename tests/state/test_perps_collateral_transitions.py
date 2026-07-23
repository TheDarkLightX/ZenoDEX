from __future__ import annotations

from typing import cast

from src.core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
from src.core.perp_epoch import perp_epoch_isolated_default_apply
from src.core.perps import (
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpMarketState,
    PerpsState,
)
from src.state.balances import BalanceTable
from src.state.perps_collateral_transitions import (
    IsolatedCollateralTransitionOkV1,
    apply_isolated_deposit_collateral_v1,
    apply_isolated_withdraw_collateral_v1,
)
from src.state.perps_state_transitions import (
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
)
from src.state.state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedPerpAccountStateV1,
    CommittedPerpMarketStateV1,
)
from src.state.state_snapshots import snapshot_balance_table, snapshot_perps
from src.state.state_transitions import BalancePatchCodeV1

_ALICE = "0x" + "11" * 48
_BOB = "0x" + "22" * 48
_QUOTE = "zUSD"


def _global() -> dict[str, int | bool]:
    return {
        "now_epoch": 1,
        "epoch_phase": 0,
        "breaker_active": False,
        "breaker_last_trigger_epoch": 0,
        "clearing_price_seen": False,
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
        "mark_price_source_kind": MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
        "oracle_seen": True,
        "oracle_last_update_epoch": 0,
        "index_price_e8": 100_000_000,
        "max_oracle_staleness_epochs": 2,
        "max_oracle_move_bps": 500,
        "initial_margin_bps": 1_000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 50,
        "max_position_abs": 1_000_000,
        "fee_pool_quote": 0,
        "funding_rate_bps": 0,
        "funding_cap_bps": 100,
        "insurance_balance": 0,
        "initial_insurance": 0,
        "fee_income": 0,
        "claims_paid": 0,
        "min_notional_for_bounty": 100_000_000,
    }


def _legacy_account(
    *,
    collateral_quote: int = 1_000,
    position_base: int = 0,
) -> PerpAccountState:
    return PerpAccountState(
        position_base=position_base,
        entry_price_e8=100_000_000 if position_base else 0,
        collateral_quote=collateral_quote,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )


def _exact_market(
    accounts: dict[str, PerpAccountState],
) -> CommittedPerpMarketStateV1:
    committed = snapshot_perps(
        PerpsState(
            version=PERPS_STATE_VERSION_V5,
            markets={
                "perp:test": PerpMarketState(
                    quote_asset=_QUOTE,
                    global_state=_global(),
                    accounts=accounts,
                )
            },
        )
    )
    assert committed is not None
    market = committed.get_market("perp:test")
    assert type(market) is CommittedPerpMarketStateV1
    return market


def _exact_balances(
    amount: int,
) -> tuple[CommittedBalanceTableV1, BalanceTable]:
    source = BalanceTable()
    source.set(_ALICE, _QUOTE, amount)
    return snapshot_balance_table(source), source


def _kernel_account(
    pre: CommittedPerpMarketStateV1,
    account: CommittedPerpAccountStateV1,
    *,
    action: str,
    amount: int,
) -> dict[str, int | bool]:
    state = {
        **dict(pre.global_entries),
        "position_base": account.position_base,
        "entry_price_e8": account.entry_price_e8,
        "collateral_quote": account.collateral_quote,
        "funding_paid_cumulative": account.funding_paid_cumulative,
        "funding_last_applied_epoch": account.funding_last_applied_epoch,
        "liquidated_this_step": account.liquidated_this_step,
    }
    result = perp_epoch_isolated_default_apply(
        state=state,
        action=action,
        params={"amount": amount, "auth_ok": True},
    )
    assert result.ok is True
    assert result.state is not None
    return {
        key: result.state[key]
        for key in (
            "position_base",
            "entry_price_e8",
            "collateral_quote",
            "funding_paid_cumulative",
            "funding_last_applied_epoch",
            "liquidated_this_step",
        )
    }


def _account_fields(account: CommittedPerpAccountStateV1) -> dict[str, int | bool]:
    return {
        "position_base": account.position_base,
        "entry_price_e8": account.entry_price_e8,
        "collateral_quote": account.collateral_quote,
        "funding_paid_cumulative": account.funding_paid_cumulative,
        "funding_last_applied_epoch": account.funding_last_applied_epoch,
        "liquidated_this_step": account.liquidated_this_step,
    }


def test_deposit_returns_one_atomic_balance_and_account_candidate() -> None:
    market = _exact_market({_ALICE: _legacy_account()})
    balances, source_balances = _exact_balances(2_000)
    pre_account = market.get_account(_ALICE)
    assert pre_account is not None

    result = apply_isolated_deposit_collateral_v1(
        market,
        balances,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        amount=250,
    )

    assert type(result) is IsolatedCollateralTransitionOkV1
    assert result.market.global_state is market.global_state
    assert result.balances.get(_ALICE, _QUOTE) == 1_750
    assert result.balance_patch.writes[0].expected_old == 2_000
    assert result.balance_patch.writes[0].replacement == 1_750
    assert result.account_patch.writes[0].expected is pre_account
    post_account = result.market.get_account(_ALICE)
    assert post_account is not None
    assert _account_fields(post_account) == _kernel_account(
        market,
        pre_account,
        action="deposit_collateral",
        amount=250,
    )

    source_balances.set(_ALICE, _QUOTE, 99_999)
    assert balances.get(_ALICE, _QUOTE) == 2_000
    assert result.balances.get(_ALICE, _QUOTE) == 1_750


def test_withdraw_returns_one_atomic_account_and_new_wallet_cell() -> None:
    market = _exact_market({_ALICE: _legacy_account()})
    balances, _source_balances = _exact_balances(0)
    pre_account = market.get_account(_ALICE)
    assert pre_account is not None

    result = apply_isolated_withdraw_collateral_v1(
        market,
        balances,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        amount=250,
    )

    assert type(result) is IsolatedCollateralTransitionOkV1
    assert result.balances.get(_ALICE, _QUOTE) == 250
    assert result.balance_patch.writes[0].expected_old == 0
    assert result.balance_patch.writes[0].replacement == 250
    post_account = result.market.get_account(_ALICE)
    assert post_account is not None
    assert _account_fields(post_account) == _kernel_account(
        market,
        pre_account,
        action="withdraw_collateral",
        amount=250,
    )


def test_deposit_into_absent_account_creates_only_the_exact_candidate() -> None:
    market = _exact_market({})
    balances, _source_balances = _exact_balances(500)

    result = apply_isolated_deposit_collateral_v1(
        market,
        balances,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        amount=500,
    )

    assert type(result) is IsolatedCollateralTransitionOkV1
    assert result.balances.get(_ALICE, _QUOTE) == 0
    assert result.account_patch.writes[0].expected is None
    post_account = result.market.get_account(_ALICE)
    assert post_account is not None
    assert post_account.collateral_quote == 500


def test_insufficient_deposit_rejects_without_either_candidate() -> None:
    market = _exact_market({_ALICE: _legacy_account()})
    balances, _source_balances = _exact_balances(100)
    pre_account = market.get_account(_ALICE)

    result = apply_isolated_deposit_collateral_v1(
        market,
        balances,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        amount=101,
    )

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.INSUFFICIENT_BALANCE,
        ("balances", _ALICE, _QUOTE),
    )
    assert not hasattr(result, "market")
    assert not hasattr(result, "balances")
    assert balances.get(_ALICE, _QUOTE) == 100
    assert market.get_account(_ALICE) is pre_account


def test_kernel_withdraw_rejection_leaves_both_exact_prestates_unchanged() -> None:
    market = _exact_market({_ALICE: _legacy_account(collateral_quote=100)})
    balances, _source_balances = _exact_balances(50)

    result = apply_isolated_withdraw_collateral_v1(
        market,
        balances,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        amount=101,
    )

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
        ("kernel",),
        "guard",
    )
    assert balances.get(_ALICE, _QUOTE) == 50
    account = market.get_account(_ALICE)
    assert account is not None
    assert account.collateral_quote == 100


def test_sender_binding_precedes_collateral_amount_typing() -> None:
    market = _exact_market({_ALICE: _legacy_account()})
    balances, _source_balances = _exact_balances(500)

    result = apply_isolated_deposit_collateral_v1(
        market,
        balances,
        account_pubkey=_ALICE,
        sender_pubkey=_BOB,
        amount=cast(int, True),
    )

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
        ("gate",),
        "SenderBindingInvalid",
    )


def test_zero_amount_rejects_in_the_scalar_kernel_without_candidates() -> None:
    market = _exact_market({_ALICE: _legacy_account()})
    balances, _source_balances = _exact_balances(500)

    deposit = apply_isolated_deposit_collateral_v1(
        market,
        balances,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        amount=0,
    )
    withdraw = apply_isolated_withdraw_collateral_v1(
        market,
        balances,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        amount=0,
    )

    expected = IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
        ("kernel",),
        "param_domain:amount",
    )
    assert deposit == expected
    assert withdraw == expected


def test_negative_amount_rejects_before_any_balance_patch_can_be_built() -> None:
    market = _exact_market({_ALICE: _legacy_account()})
    balances, _source_balances = _exact_balances(500)

    deposit = apply_isolated_deposit_collateral_v1(
        market,
        balances,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        amount=-1,
    )
    withdraw = apply_isolated_withdraw_collateral_v1(
        market,
        balances,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        amount=-1,
    )

    expected = IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
        ("kernel",),
        "param_domain:amount",
    )
    assert deposit == expected
    assert withdraw == expected
    assert balances.get(_ALICE, _QUOTE) == 500


def test_corrupted_balance_prestate_rejects_before_command_evaluation() -> None:
    market = _exact_market({_ALICE: _legacy_account()})
    balances, _source_balances = _exact_balances(500)
    object.__setattr__(balances._balances, "_schema_id", "corrupted")

    result = apply_isolated_deposit_collateral_v1(
        market,
        balances,
        account_pubkey=_ALICE,
        sender_pubkey=_BOB,
        amount=cast(int, True),
    )

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.BALANCE_PATCH,
        ("balances", "state", "balances"),
        BalancePatchCodeV1.INVALID_PRESTATE.value,
    )

from __future__ import annotations

import pytest

from src.core.perps import (
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
    PerpAccountState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpMarketState,
)
from src.core.perps_token_accounting import (
    E8_SCALE,
    PerpsTokenAmountNonIntegral,
    perps_market_locked_quote_e8,
    perps_market_locked_quote_units,
)

QUOTE_ASSET = "0x" + "11" * 32
ACCOUNT_A = "0x" + "aa" * 48
ACCOUNT_B = "0x" + "bb" * 48
ACCOUNT_C = "0x" + "cc" * 48


def _isolated_market() -> PerpMarketState:
    from tests.core.test_perps_market_state_strictness import _legacy_global_state

    global_state = _legacy_global_state()
    global_state["fee_pool_quote"] = 7
    global_state["fee_income"] = 7
    global_state["initial_insurance"] = 0
    global_state["claims_paid"] = 0
    global_state["insurance_balance"] = 7
    return PerpMarketState(
        quote_asset=QUOTE_ASSET,
        global_state=global_state,
        accounts={
            "0x" + "aa" * 48: PerpAccountState(
                position_base=0,
                entry_price_e8=0,
                collateral_quote=16,
                funding_paid_cumulative=0,
                funding_last_applied_epoch=0,
                liquidated_this_step=False,
            ),
        },
    )


def test_isolated_projection_does_not_count_mirrored_fee_pool_twice() -> None:
    market = _isolated_market()

    assert perps_market_locked_quote_units(market) == 23
    assert perps_market_locked_quote_e8(market) == 23 * E8_SCALE


def test_isolated_projection_rejects_behavior_changing_market_subclass() -> None:
    class DerivedPerpMarketState(PerpMarketState):
        pass

    base = _isolated_market()
    derived = DerivedPerpMarketState(
        quote_asset=base.quote_asset,
        global_state=dict(base.global_state),
        accounts=dict(base.accounts),
        pending_funding_closeout_root_hashes=base.pending_funding_closeout_root_hashes,
        pending_funding_closeout_source_availability_hashes=(
            base.pending_funding_closeout_source_availability_hashes
        ),
        pending_funding_closeout_carried_liability_hashes=(
            base.pending_funding_closeout_carried_liability_hashes
        ),
        funding_closeout_policy_ledger_hashes=base.funding_closeout_policy_ledger_hashes,
        funding_closeout_sink_claimant_balances_quote=(
            base.funding_closeout_sink_claimant_balances_quote
        ),
        funding_closeout_receiver_claim_balances_quote=(
            base.funding_closeout_receiver_claim_balances_quote
        ),
        funding_closeout_receiver_claim_lots_quote=(
            base.funding_closeout_receiver_claim_lots_quote
        ),
    )

    with pytest.raises(TypeError, match="unsupported exact perps market type"):
        perps_market_locked_quote_e8(derived)


def _fixed_state(*, three_party: bool, net_deposited_e8: int) -> dict[str, object]:
    keys = (
        PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS
        if three_party
        else PERP_CLEARINGHOUSE_2P_STATE_KEYS
    )
    state: dict[str, object] = {key: 0 for key in keys}
    state.update(
        {
            "breaker_active": False,
            "clearing_price_seen": False,
            "oracle_seen": False,
            "liquidated_this_step": False,
            "initial_margin_bps": 1_000,
            "maintenance_margin_bps": 600,
            "liquidation_penalty_bps": 50,
            "max_oracle_move_bps": 500,
            "max_oracle_staleness_epochs": 100,
            "max_position_abs": 1_000_000,
            "net_deposited_e8": net_deposited_e8,
            "collateral_e8_a": net_deposited_e8,
        }
    )
    return state


def test_two_party_projection_uses_closed_system_deposit_total() -> None:
    market = PerpClearinghouse2pMarketState(
        quote_asset=QUOTE_ASSET,
        account_a_pubkey=ACCOUNT_A,
        account_b_pubkey=ACCOUNT_B,
        state=_fixed_state(three_party=False, net_deposited_e8=3 * E8_SCALE),
    )

    assert perps_market_locked_quote_units(market) == 3


def test_three_party_projection_uses_closed_system_deposit_total() -> None:
    market = PerpClearinghouse3pTransferMarketState(
        quote_asset=QUOTE_ASSET,
        account_a_pubkey=ACCOUNT_A,
        account_b_pubkey=ACCOUNT_B,
        account_c_pubkey=ACCOUNT_C,
        state=_fixed_state(three_party=True, net_deposited_e8=4 * E8_SCALE),
    )

    assert perps_market_locked_quote_units(market) == 4


def test_projection_rejects_non_whole_token_e8_total() -> None:
    market = PerpClearinghouse2pMarketState(
        quote_asset=QUOTE_ASSET,
        account_a_pubkey=ACCOUNT_A,
        account_b_pubkey=ACCOUNT_B,
        state=_fixed_state(three_party=False, net_deposited_e8=1),
    )

    with pytest.raises(PerpsTokenAmountNonIntegral):
        perps_market_locked_quote_units(market)

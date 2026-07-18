from __future__ import annotations

import pytest

from src.core.perps import (
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
    PerpAccountState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpClearinghouseNpAccount,
    PerpClearinghouseNpMarketState,
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


def _np_global_state(*, net_deposited_e8: int, insurance_ext_e8: int) -> dict[str, int]:
    return {
        "now_epoch": 0,
        "index_price_e8": 100 * E8_SCALE,
        "fee_pool_e8": 0,
        "insurance_e8": insurance_ext_e8,
        "insurance_ext_e8": insurance_ext_e8,
        "claims_paid_e8": 0,
        "net_deposited_e8": net_deposited_e8,
        "initial_margin_bps": 1_000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 50,
        "max_oracle_move_bps": 500,
        "funding_cap_bps": 100,
        "max_position_abs": 1_000_000,
        "min_notional_for_bounty_e8": 100 * E8_SCALE,
        "clearing_price_seen": 0,
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
    }


def test_n_party_projection_includes_external_insurance_deposits_once() -> None:
    market = PerpClearinghouseNpMarketState(
        quote_asset=QUOTE_ASSET,
        global_state=_np_global_state(
            net_deposited_e8=5 * E8_SCALE,
            insurance_ext_e8=1 * E8_SCALE,
        ),
        accounts=(
            PerpClearinghouseNpAccount(
                pubkey=ACCOUNT_A,
                collateral_e8=5 * E8_SCALE,
            ),
        ),
    )

    assert perps_market_locked_quote_units(market) == 6


def test_projection_rejects_non_whole_token_e8_total() -> None:
    market = PerpClearinghouse2pMarketState(
        quote_asset=QUOTE_ASSET,
        account_a_pubkey=ACCOUNT_A,
        account_b_pubkey=ACCOUNT_B,
        state=_fixed_state(three_party=False, net_deposited_e8=1),
    )

    with pytest.raises(PerpsTokenAmountNonIntegral):
        perps_market_locked_quote_units(market)

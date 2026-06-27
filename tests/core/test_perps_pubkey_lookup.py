from __future__ import annotations

import pytest

from src.core import perps as P
from src.core.perp_np_matching import E8
from src.core.perps import (
    PerpClearinghouse2pMarketState,
    PerpClearinghouseNpAccount,
    PerpClearinghouseNpMarketState,
)
from src.integration import perp_engine as E


def _pk(byte: str) -> str:
    return "0x" + byte * 48


def _np_global_state(net_deposited_e8: int) -> dict[str, int]:
    return {
        "now_epoch": 0,
        "index_price_e8": 100 * E8,
        "clearing_price_seen": 0,
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
        "fee_pool_e8": 0,
        "insurance_e8": 0,
        "insurance_ext_e8": 0,
        "claims_paid_e8": 0,
        "net_deposited_e8": net_deposited_e8,
        "initial_margin_bps": 1000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 50,
        "max_oracle_move_bps": 500,
        "funding_cap_bps": 100,
        "max_position_abs": 1_000_000,
        "min_notional_for_bounty_e8": 100 * E8,
    }


def test_clearinghouse_role_lookup_invalid_pubkey_is_non_member() -> None:
    market = PerpClearinghouse2pMarketState(
        quote_asset="zUSD",
        account_a_pubkey=_pk("aa"),
        account_b_pubkey=_pk("bb"),
        state=E._ch2p_init_state_dict(),
    )

    assert market.role_for_pubkey("not-a-pubkey") is None


def test_np_role_lookup_invalid_pubkey_is_non_member() -> None:
    account = PerpClearinghouseNpAccount(_pk("11"), 0, 100 * E8, 10**15)
    market = PerpClearinghouseNpMarketState(
        quote_asset="zUSD",
        global_state=_np_global_state(10**15),
        accounts=(account,),
    )

    assert market.role_for_pubkey("not-a-pubkey") is None


def test_role_lookup_does_not_suppress_internal_canonicalizer_errors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    market = PerpClearinghouse2pMarketState(
        quote_asset="zUSD",
        account_a_pubkey=_pk("aa"),
        account_b_pubkey=_pk("bb"),
        state=E._ch2p_init_state_dict(),
    )

    def broken_canonicalizer(*_args: object, **_kwargs: object) -> str:
        raise RuntimeError("unexpected canonicalizer bug")

    monkeypatch.setattr(P, "canonical_hex_fixed_allow_0x", broken_canonicalizer)

    with pytest.raises(RuntimeError, match="unexpected canonicalizer bug"):
        market.role_for_pubkey(_pk("aa"))

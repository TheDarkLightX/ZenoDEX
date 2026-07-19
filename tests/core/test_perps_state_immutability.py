"""Retained-alias regressions for persistent perps state.

Mutable dictionaries remain useful as transition-local builders.  Once they
cross a persistent-state constructor, however, the snapshot must own and seal
them so neither a caller alias nor a reference obtained from the snapshot can
change authoritative state.
"""

from __future__ import annotations

from collections.abc import Callable

import pytest

from src.core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
from src.core.perps import (
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
    PERPS_STATE_VERSION_V4,
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpMarketState,
    PerpsState,
)

QUOTE_ASSET = "0x" + "11" * 32
ACCOUNT_A = "0x" + "aa" * 48
ACCOUNT_B = "0x" + "bb" * 48
ACCOUNT_C = "0x" + "cc" * 48


class _BehaviorInt(int):
    """An int lookalike whose projected value can change after validation."""

    def __new__(cls, value: int) -> _BehaviorInt:
        instance = super().__new__(cls, value)
        instance.projected = value
        return instance

    def __int__(self) -> int:
        return self.projected


class _BehaviorStr(str):
    """A str lookalike carrying mutable behavior-bearing state."""

    def __new__(cls, value: str) -> _BehaviorStr:
        instance = super().__new__(cls, value)
        instance.projected = value
        return instance

    def __str__(self) -> str:
        return self.projected


def _isolated_global_state() -> dict[str, bool | int]:
    return {
        "now_epoch": 0,
        "breaker_active": False,
        "breaker_last_trigger_epoch": 0,
        "clearing_price_seen": False,
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
        "mark_price_source_kind": MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
        "oracle_seen": False,
        "oracle_last_update_epoch": 0,
        "index_price_e8": 0,
        "max_oracle_staleness_epochs": 100,
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


def _account() -> PerpAccountState:
    return PerpAccountState(
        position_base=0,
        entry_price_e8=0,
        collateral_quote=10,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )


def _isolated_market() -> PerpMarketState:
    return PerpMarketState(
        quote_asset=QUOTE_ASSET,
        global_state=_isolated_global_state(),
        accounts={ACCOUNT_A: _account()},
    )


def _fixed_state(*, three_party: bool) -> dict[str, bool | int]:
    keys = (
        PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS
        if three_party
        else PERP_CLEARINGHOUSE_2P_STATE_KEYS
    )
    state: dict[str, bool | int] = {key: 0 for key in keys}
    state.update(
        {
            "breaker_active": False,
            "clearing_price_seen": False,
            "oracle_seen": False,
            "liquidated_this_step": False,
            "initial_margin_bps": 1_000,
            "maintenance_margin_bps": 500,
            "liquidation_penalty_bps": 50,
            "max_oracle_move_bps": 500,
            "max_oracle_staleness_epochs": 100,
            "max_position_abs": 1_000_000,
        }
    )
    return state


def test_isolated_market_owns_and_seals_global_and_account_mappings() -> None:
    source_global = _isolated_global_state()
    source_accounts = {ACCOUNT_A: _account()}
    market = PerpMarketState(
        quote_asset=QUOTE_ASSET,
        global_state=source_global,
        accounts=source_accounts,
    )

    source_global["index_price_e8"] = 7
    source_accounts.clear()

    assert market.global_state["index_price_e8"] == 0
    assert market.accounts == {ACCOUNT_A: _account()}
    with pytest.raises(TypeError, match="immutable value cannot be mutated"):
        market.global_state["index_price_e8"] = 7
    with pytest.raises(TypeError, match="immutable value cannot be mutated"):
        market.accounts.clear()


def test_isolated_market_rejects_mutable_account_lookalike() -> None:
    class MutableAccount:
        position_base = 0
        entry_price_e8 = 0
        collateral_quote = 10
        funding_paid_cumulative = 0
        funding_last_applied_epoch = 0
        liquidated_this_step = False

    with pytest.raises(TypeError, match="exact PerpAccountState"):
        PerpMarketState(
            quote_asset=QUOTE_ASSET,
            global_state=_isolated_global_state(),
            accounts={ACCOUNT_A: MutableAccount()},  # type: ignore[dict-item]
        )


def test_isolated_kernel_projection_excludes_shell_only_mark_source() -> None:
    from src.core.perp_v2.state import state_from_dict

    market = _isolated_market()
    account = market.accounts[ACCOUNT_A]

    projected = market.kernel_state_for_account(account)

    assert market.global_state["mark_price_source_kind"] == MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
    assert "mark_price_source_kind" not in projected
    # The projection is accepted by the strict kernel parser without weakening
    # its exact-field rejection rule.
    state_from_dict(projected)


def test_perps_state_owns_and_seals_market_table() -> None:
    market = _isolated_market()
    source_markets = {"BTC-zUSD": market}
    state = PerpsState(version=PERPS_STATE_VERSION_V4, markets=source_markets)

    source_markets.clear()

    assert state.get_market("BTC-zUSD") is market
    with pytest.raises(TypeError, match="immutable value cannot be mutated"):
        state.markets["forged"] = market

    with pytest.raises(TypeError, match="exact persistent market state types"):
        PerpsState(
            version=PERPS_STATE_VERSION_V5,
            markets={"forged": object()},  # type: ignore[dict-item]
        )


@pytest.mark.parametrize(
    "three_party,build_market",
    [
        (
            False,
            lambda state: PerpClearinghouse2pMarketState(
                quote_asset=QUOTE_ASSET,
                account_a_pubkey=ACCOUNT_A,
                account_b_pubkey=ACCOUNT_B,
                state=state,
            ),
        ),
        (
            True,
            lambda state: PerpClearinghouse3pTransferMarketState(
                quote_asset=QUOTE_ASSET,
                account_a_pubkey=ACCOUNT_A,
                account_b_pubkey=ACCOUNT_B,
                account_c_pubkey=ACCOUNT_C,
                state=state,
            ),
        ),
    ],
)
def test_fixed_clearinghouse_owns_and_seals_kernel_state(
    three_party: bool,
    build_market: Callable[
        [dict[str, bool | int]],
        PerpClearinghouse2pMarketState | PerpClearinghouse3pTransferMarketState,
    ],
) -> None:
    source_state = _fixed_state(three_party=three_party)
    market = build_market(source_state)

    source_state["maintenance_margin_bps"] = 1

    assert market.state["maintenance_margin_bps"] == 500
    with pytest.raises(TypeError, match="immutable value cannot be mutated"):
        market.state["maintenance_margin_bps"] = 1


@pytest.mark.parametrize(
    "field_name",
    (
        "position_base",
        "entry_price_e8",
        "collateral_quote",
        "funding_paid_cumulative",
        "funding_last_applied_epoch",
    ),
)
def test_isolated_account_rejects_behavior_changing_int_subclasses(field_name: str) -> None:
    fields: dict[str, object] = {
        "position_base": 0,
        "entry_price_e8": 0,
        "collateral_quote": 10,
        "funding_paid_cumulative": 0,
        "funding_last_applied_epoch": 0,
        "liquidated_this_step": False,
    }
    fields[field_name] = _BehaviorInt(int(fields[field_name]))

    with pytest.raises(TypeError, match="must be an int"):
        PerpAccountState(**fields)  # type: ignore[arg-type]


def test_isolated_market_rejects_behavior_changing_primitive_aliases() -> None:
    global_value = _isolated_global_state()
    global_value["maintenance_margin_bps"] = _BehaviorInt(500)
    with pytest.raises(TypeError, match="maintenance_margin_bps"):
        PerpMarketState(quote_asset=QUOTE_ASSET, global_state=global_value, accounts={})

    global_key = _isolated_global_state()
    value = global_key.pop("maintenance_margin_bps")
    global_key[_BehaviorStr("maintenance_margin_bps")] = value
    with pytest.raises(TypeError, match="global_state keys must be exact strings"):
        PerpMarketState(quote_asset=QUOTE_ASSET, global_state=global_key, accounts={})

    with pytest.raises(TypeError, match="quote_asset"):
        PerpMarketState(
            quote_asset=_BehaviorStr(QUOTE_ASSET),
            global_state=_isolated_global_state(),
            accounts={},
        )


def test_fixed_clearinghouse_rejects_behavior_changing_primitive_aliases() -> None:
    value_state = _fixed_state(three_party=False)
    value_state["maintenance_margin_bps"] = _BehaviorInt(500)
    with pytest.raises(TypeError, match="maintenance_margin_bps"):
        PerpClearinghouse2pMarketState(
            quote_asset=QUOTE_ASSET,
            account_a_pubkey=ACCOUNT_A,
            account_b_pubkey=ACCOUNT_B,
            state=value_state,
        )

    key_state = _fixed_state(three_party=False)
    value = key_state.pop("maintenance_margin_bps")
    key_state[_BehaviorStr("maintenance_margin_bps")] = value
    with pytest.raises(TypeError, match="state keys must be exact strings"):
        PerpClearinghouse2pMarketState(
            quote_asset=QUOTE_ASSET,
            account_a_pubkey=ACCOUNT_A,
            account_b_pubkey=ACCOUNT_B,
            state=key_state,
        )


def test_perps_state_rejects_behavior_changing_version_and_market_keys() -> None:
    market = _isolated_market()
    with pytest.raises(TypeError, match="version must be a positive int"):
        PerpsState(
            version=_BehaviorInt(PERPS_STATE_VERSION_V4),
            markets={"BTC-zUSD": market},
        )

    with pytest.raises(TypeError, match="markets keys must be exact strings"):
        PerpsState(
            version=PERPS_STATE_VERSION_V4,
            markets={_BehaviorStr("BTC-zUSD"): market},
        )

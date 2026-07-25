from __future__ import annotations

from typing import cast

import pytest

from src.core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
from src.core.perps import (
    PERP_CLEARINGHOUSE_2P_BOOL_KEYS,
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpClearinghouseNpAccount,
    PerpClearinghouseNpMarketState,
    PerpClearinghouseNpPendingIntent,
    PerpMarketState,
    PerpsState,
)
from src.state.state_snapshot_values import (
    CommittedPerpClearinghouse2pMarketStateV1,
    CommittedPerpClearinghouse3pTransferMarketStateV1,
    CommittedPerpClearinghouseNpMarketStateV1,
    CommittedPerpMarketStateV1,
    CommittedPerpsStateV1,
)
from src.state.state_snapshots import snapshot_perps

_PUBKEYS = tuple("0x" + f"{index:02x}" * 48 for index in range(1, 8))


def _isolated_global() -> dict[str, int | bool]:
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


def _fixed_state(
    keys: set[str],
    bool_keys: set[str],
    participant_suffixes: tuple[str, ...],
) -> dict[str, int | bool]:
    state: dict[str, int | bool] = {key: 0 for key in keys}
    for key in bool_keys:
        state[key] = False
    state.update(
        {
            "max_oracle_staleness_epochs": 1,
            "max_oracle_move_bps": 500,
            "initial_margin_bps": 1_000,
            "maintenance_margin_bps": 600,
            "liquidation_penalty_bps": 50,
            "max_position_abs": 1_000_000,
            "fee_pool_e8": 10,
            "net_deposited_e8": 10 + 100 * len(participant_suffixes),
        }
    )
    for index, suffix in enumerate(participant_suffixes):
        state[f"position_base_{suffix}"] = 0 if index == 2 else (5 if index == 0 else -5)
        state[f"entry_price_e8_{suffix}"] = 100_000_000
        state[f"collateral_e8_{suffix}"] = 100
    return state


def _np_global() -> dict[str, int]:
    return {
        "now_epoch": 1,
        "index_price_e8": 100_000_000,
        "clearing_price_seen": 0,
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
        "fee_pool_e8": 0,
        "insurance_e8": 0,
        "insurance_ext_e8": 0,
        "claims_paid_e8": 0,
        "net_deposited_e8": 300,
        "initial_margin_bps": 1_000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 50,
        "max_oracle_move_bps": 500,
        "funding_cap_bps": 100,
        "max_position_abs": 1_000_000,
        "min_notional_for_bounty_e8": 100_000_000,
    }


def _legacy_perps() -> PerpsState:
    isolated_accounts = {
        _PUBKEYS[0]: PerpAccountState(
            position_base=5,
            entry_price_e8=100_000_000,
            collateral_quote=200,
            funding_paid_cumulative=0,
            funding_last_applied_epoch=0,
            liquidated_this_step=False,
        )
    }
    np_accounts = (
        PerpClearinghouseNpAccount(_PUBKEYS[1], 5, 100_000_000, 100, 0, 1),
        PerpClearinghouseNpAccount(_PUBKEYS[2], -5, 100_000_000, 200, 0, 2),
    )
    np_intents = (
        PerpClearinghouseNpPendingIntent(_PUBKEYS[1], 0, 2, 100_000_000, 1, 2),
    )
    return PerpsState(
        version=PERPS_STATE_VERSION_V5,
        markets={
            "isolated": PerpMarketState("zUSD", _isolated_global(), isolated_accounts),
            "ch3p": PerpClearinghouse3pTransferMarketState(
                "zUSD",
                _PUBKEYS[3],
                _PUBKEYS[4],
                _PUBKEYS[5],
                _fixed_state(
                    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
                    PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS,
                    ("a", "b", "c"),
                ),
            ),
            "chnp": PerpClearinghouseNpMarketState(
                "zUSD",
                _np_global(),
                np_accounts,
                np_intents,
            ),
            "ch2p": PerpClearinghouse2pMarketState(
                "zUSD",
                _PUBKEYS[3],
                _PUBKEYS[4],
                _fixed_state(
                    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
                    PERP_CLEARINGHOUSE_2P_BOOL_KEYS,
                    ("a", "b"),
                ),
            ),
        },
    )


def _committed_perps() -> CommittedPerpsStateV1:
    committed = snapshot_perps(_legacy_perps())
    assert type(committed) is CommittedPerpsStateV1
    return committed


def test_exact_perps_readers_cover_every_mounted_market_variant() -> None:
    committed = _committed_perps()

    assert tuple(market_id for market_id, _market in committed.market_entries) == (
        "ch2p",
        "ch3p",
        "chnp",
        "isolated",
    )

    ch2p = committed.get_market("ch2p")
    assert type(ch2p) is CommittedPerpClearinghouse2pMarketStateV1
    assert ch2p.state_value("position_base_a") == 5
    assert ch2p.state_entries == ch2p.state.entries

    ch3p = committed.get_market("ch3p")
    assert type(ch3p) is CommittedPerpClearinghouse3pTransferMarketStateV1
    assert ch3p.state_value("position_base_c") == 0
    assert ch3p.state_entries == ch3p.state.entries

    chnp = committed.get_market("chnp")
    assert type(chnp) is CommittedPerpClearinghouseNpMarketStateV1
    assert chnp.global_value("net_deposited_e8") == 300
    assert chnp.get_account(_PUBKEYS[1]) == chnp.accounts[0]
    assert chnp.get_account(_PUBKEYS[6]) is None
    assert chnp.get_pending_intent(_PUBKEYS[1]) == chnp.pending_intents[0]
    assert chnp.get_pending_intent(_PUBKEYS[2]) is None
    assert chnp.global_entries == chnp.global_state.entries

    isolated = committed.get_market("isolated")
    assert type(isolated) is CommittedPerpMarketStateV1
    assert isolated.global_value("index_price_e8") == 100_000_000
    assert isolated.get_account(_PUBKEYS[0]) == isolated.account_entries[0][1]
    assert isolated.get_account(_PUBKEYS[6]) is None
    assert isolated.global_entries == isolated.global_state.entries


def test_exact_perps_readers_reject_behavior_bearing_lookup_keys() -> None:
    committed = _committed_perps()
    isolated = cast(CommittedPerpMarketStateV1, committed.get_market("isolated"))
    ch2p = cast(CommittedPerpClearinghouse2pMarketStateV1, committed.get_market("ch2p"))
    chnp = cast(CommittedPerpClearinghouseNpMarketStateV1, committed.get_market("chnp"))

    class StringSubclass(str):
        pass

    with pytest.raises(TypeError):
        committed.get_market(StringSubclass("isolated"))
    with pytest.raises(TypeError):
        isolated.global_value(StringSubclass("now_epoch"))
    with pytest.raises(TypeError):
        isolated.get_account(StringSubclass(_PUBKEYS[0]))
    with pytest.raises(TypeError):
        ch2p.state_value(StringSubclass("now_epoch"))
    with pytest.raises(TypeError):
        chnp.get_pending_intent(StringSubclass(_PUBKEYS[1]))


def test_exact_perps_reader_results_do_not_retain_legacy_aliases() -> None:
    legacy = _legacy_perps()
    committed = snapshot_perps(legacy)
    assert type(committed) is CommittedPerpsStateV1
    isolated_source = cast(PerpMarketState, legacy.markets["isolated"])

    isolated_source.global_state["index_price_e8"] = 900_000_000
    isolated_source.accounts[_PUBKEYS[0]] = PerpAccountState(
        position_base=0,
        entry_price_e8=0,
        collateral_quote=0,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )
    legacy.markets.clear()

    isolated = committed.get_market("isolated")
    assert type(isolated) is CommittedPerpMarketStateV1
    assert isolated.global_value("index_price_e8") == 100_000_000
    account = isolated.get_account(_PUBKEYS[0])
    assert account is not None
    assert account.position_base == 5
    assert len(committed.market_entries) == 4


def test_exact_perps_readers_preserve_declared_missing_key_behavior() -> None:
    committed = _committed_perps()
    isolated = cast(CommittedPerpMarketStateV1, committed.get_market("isolated"))
    ch2p = cast(CommittedPerpClearinghouse2pMarketStateV1, committed.get_market("ch2p"))
    chnp = cast(CommittedPerpClearinghouseNpMarketStateV1, committed.get_market("chnp"))

    assert committed.get_market("missing") is None
    with pytest.raises(KeyError):
        isolated.global_value("missing")
    with pytest.raises(KeyError):
        ch2p.state_value("missing")
    with pytest.raises(KeyError):
        chnp.global_value("missing")

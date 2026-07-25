from __future__ import annotations

import hashlib
from typing import cast

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

import src.state.committed_dex_snapshot as committed_dex_snapshot
from src.core.dex import DexState
from src.core.domain_limits import DEX_LP_AMOUNT_MAX, DEX_POOL_RESERVE_MAX
from src.core.fees import FeeAccumulatorState
from src.core.oracle import OracleState
from src.core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
from src.core.perps import (
    PERP_CLEARINGHOUSE_2P_BOOL_KEYS,
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
    PERPS_STATE_VERSION_V5,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpClearinghouseNpMarketState,
    PerpMarketState,
    PerpsState,
)
from src.core.vault import VaultState
from src.integration.dex_snapshot import snapshot_from_state
from src.state.balances import BalanceTable
from src.state.committed_dex_snapshot import canonical_snapshot_bytes_from_committed_state_v1
from src.state.dex_snapshot_profile import DEX_SNAPSHOT_SUPPORTED_VERSIONS_V1
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.owned_collections import OwnedMapV1
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedOracleStateV1,
    CommittedPerpsStateV1,
    CommittedPoolStateV1,
    CommittedVaultStateV1,
)
from src.state.state_snapshots import (
    StateAdmissionError,
    snapshot_balance_table,
    snapshot_fee_accumulator,
    snapshot_lp_table,
    snapshot_nonce_table,
    snapshot_oracle,
    snapshot_perps,
    snapshot_pool_map,
    snapshot_vault,
)

_PUBKEYS = tuple("0x" + f"{index:02x}" * 48 for index in range(1, 8))
_ASSET0 = "0x" + "11" * 32
_ASSET1 = "0x" + "22" * 32

LegacySourcesV1 = tuple[
    BalanceTable,
    dict[str, PoolState],
    LPTable,
    NonceTable,
    FeeAccumulatorState,
    VaultState,
    OracleState,
    PerpsState,
]
CommittedSourcesV1 = tuple[
    CommittedBalanceTableV1,
    OwnedMapV1[str, CommittedPoolStateV1],
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedVaultStateV1 | None,
    CommittedOracleStateV1 | None,
    CommittedPerpsStateV1 | None,
]


def _isolated_global() -> dict[str, int | bool]:
    return {
        "now_epoch": 0,
        "epoch_phase": 0,
        "breaker_active": False,
        "breaker_last_trigger_epoch": 0,
        "clearing_price_seen": False,
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
        "mark_price_source_kind": MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
        "oracle_seen": False,
        "oracle_last_update_epoch": 0,
        "index_price_e8": 0,
        "max_oracle_staleness_epochs": 1,
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


def _fixed_state(keys: set[str], bool_keys: set[str]) -> dict[str, int | bool]:
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
        }
    )
    return state


def _np_global() -> dict[str, int]:
    return {
        "now_epoch": 0,
        "index_price_e8": 10_000_000_000,
        "clearing_price_seen": 0,
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
        "fee_pool_e8": 0,
        "insurance_e8": 0,
        "insurance_ext_e8": 0,
        "claims_paid_e8": 0,
        "net_deposited_e8": 0,
        "initial_margin_bps": 1_000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 50,
        "max_oracle_move_bps": 500,
        "funding_cap_bps": 100,
        "max_position_abs": 1_000_000,
        "min_notional_for_bounty_e8": 10_000_000_000,
    }


def _perps() -> PerpsState:
    return PerpsState(
        version=PERPS_STATE_VERSION_V5,
        markets={
            "isolated": PerpMarketState(
                quote_asset="zUSD",
                global_state=_isolated_global(),
                accounts={},
            ),
            "ch2p": PerpClearinghouse2pMarketState(
                quote_asset="zUSD",
                account_a_pubkey=_PUBKEYS[1],
                account_b_pubkey=_PUBKEYS[2],
                state=_fixed_state(
                    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
                    PERP_CLEARINGHOUSE_2P_BOOL_KEYS,
                ),
            ),
            "ch3p": PerpClearinghouse3pTransferMarketState(
                quote_asset="zUSD",
                account_a_pubkey=_PUBKEYS[3],
                account_b_pubkey=_PUBKEYS[4],
                account_c_pubkey=_PUBKEYS[5],
                state=_fixed_state(
                    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
                    PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS,
                ),
            ),
            "chnp": PerpClearinghouseNpMarketState(
                quote_asset="zUSD",
                global_state=_np_global(),
                accounts=(),
                pending_intents=(),
            ),
        },
    )


def _legacy_sources(
    *,
    reserve0: int = 1_000,
    reserve1: int = 2_000,
    lp_amount: int = 100,
    nonce: int = 9,
    dust: int = 4,
) -> LegacySourcesV1:
    balances = BalanceTable()
    balances.set(_PUBKEYS[0], _ASSET0, 7)
    balances.set(_PUBKEYS[1], _ASSET1, 13)
    pool_id = compute_pool_id(_ASSET0, _ASSET1, 30)
    pool = PoolState(
        pool_id=pool_id,
        asset0=_ASSET0,
        asset1=_ASSET1,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=30,
        lp_supply=500,
        status=PoolStatus.FROZEN,
        created_at=7,
    )
    lp = LPTable()
    lp.set(_PUBKEYS[0], pool_id, lp_amount)
    lp.set_last_mint_timestamp(_PUBKEYS[0], pool_id, 3)
    lp.set_last_remove_timestamp(_PUBKEYS[0], pool_id, 5)
    lp.set_churn_tier(_PUBKEYS[0], pool_id, 2)
    lp.set_last_churn_update_timestamp(_PUBKEYS[0], pool_id, 6)
    nonces = NonceTable()
    nonces.set_last(_PUBKEYS[0], nonce)
    return (
        balances,
        {pool_id: pool},
        lp,
        nonces,
        FeeAccumulatorState(dust=dust),
        VaultState(2, 1, 3, 4, 5),
        OracleState(price_timestamp=11, max_staleness_seconds=12),
        _perps(),
    )


def _legacy_bytes(sources: LegacySourcesV1, *, version: int) -> bytes:
    balances, pools, lp, nonces, fees, vault, oracle, perps = sources
    state = DexState(
        balances=balances,
        pools=pools,
        lp_balances=lp,
        nonces=nonces,
        fee_accumulator=fees,
        vault=vault,
        oracle=oracle,
        perps=perps,
    )
    return snapshot_from_state(state, version=version).canonical_bytes()


def _committed_values(sources: LegacySourcesV1) -> CommittedSourcesV1:
    balances, pools, lp, nonces, fees, vault, oracle, perps = sources
    return (
        snapshot_balance_table(balances),
        snapshot_pool_map(pools),
        snapshot_lp_table(lp),
        snapshot_nonce_table(nonces),
        snapshot_fee_accumulator(fees),
        snapshot_vault(vault),
        snapshot_oracle(oracle),
        snapshot_perps(perps),
    )


def _exact_bytes(sources: LegacySourcesV1, *, version: int) -> bytes:
    balances, pools, lp, nonces, fees, vault, oracle, perps = _committed_values(sources)
    return canonical_snapshot_bytes_from_committed_state_v1(
        version=version,
        balances=balances,
        pools=pools,
        lp_balances=lp,
        nonces=nonces,
        fee_accumulator=fees,
        vault=vault,
        oracle=oracle,
        perps=perps,
    )


@pytest.mark.parametrize("version", DEX_SNAPSHOT_SUPPORTED_VERSIONS_V1)
def test_exact_snapshot_bytes_match_legacy_for_every_supported_version(version: int) -> None:
    sources = _legacy_sources()

    exact = _exact_bytes(sources, version=version)

    assert exact == _legacy_bytes(sources, version=version)


@pytest.mark.parametrize("version", (True, 0, 5))
def test_exact_and_legacy_snapshot_encoders_reject_unsupported_versions(
    version: object,
) -> None:
    sources = _legacy_sources()
    committed = _committed_values(sources)

    with pytest.raises(ValueError):
        canonical_snapshot_bytes_from_committed_state_v1(
            version=cast(int, version),
            balances=committed[0],
            pools=committed[1],
            lp_balances=committed[2],
            nonces=committed[3],
            fee_accumulator=committed[4],
            vault=committed[5],
            oracle=committed[6],
            perps=committed[7],
        )
    state = DexState(
        balances=sources[0],
        pools=sources[1],
        lp_balances=sources[2],
        nonces=sources[3],
        fee_accumulator=sources[4],
        vault=sources[5],
        oracle=sources[6],
        perps=sources[7],
    )
    with pytest.raises(ValueError):
        snapshot_from_state(state, version=cast(int, version))


def test_exact_snapshot_all_optional_and_perps_variants_has_pinned_digest() -> None:
    exact = _exact_bytes(_legacy_sources(), version=4)

    assert hashlib.sha256(exact).hexdigest() == (
        "055e72655b657ab866e99c4b5b299337b85cfc40a335d4a303e9df781b969806"
    )


def test_exact_snapshot_is_owned_and_returns_only_canonical_bytes() -> None:
    sources = _legacy_sources()
    committed = _committed_values(sources)
    before = _exact_bytes(sources, version=4)
    balances, pools, lp, nonces, fees, _vault, _oracle, _perps = sources
    balances.set(_PUBKEYS[0], _ASSET0, 999)
    pool_id = next(iter(pools))
    pools[pool_id].reserve0 = 999
    lp.set(_PUBKEYS[0], pool_id, 999)
    nonces.set_last(_PUBKEYS[0], 999)
    object.__setattr__(fees, "dust", 999)

    after = canonical_snapshot_bytes_from_committed_state_v1(
        version=4,
        balances=committed[0],
        pools=committed[1],
        lp_balances=committed[2],
        nonces=committed[3],
        fee_accumulator=committed[4],
        vault=committed[5],
        oracle=committed[6],
        perps=committed[7],
    )
    assert type(after) is bytes
    assert after == before


def test_exact_snapshot_revalidates_corrupted_graph_and_rejects_legacy_types() -> None:
    sources = _legacy_sources()
    committed = _committed_values(sources)
    balances = cast(CommittedBalanceTableV1, committed[0])
    pools = cast(OwnedMapV1[str, CommittedPoolStateV1], committed[1])
    object.__setattr__(pools.entries[0][1], "reserve0", True)

    with pytest.raises(StateAdmissionError):
        canonical_snapshot_bytes_from_committed_state_v1(
            version=4,
            balances=balances,
            pools=pools,
            lp_balances=committed[2],
            nonces=committed[3],
            fee_accumulator=committed[4],
            vault=committed[5],
            oracle=committed[6],
            perps=committed[7],
        )

    with pytest.raises(TypeError, match="exact CommittedBalanceTableV1"):
        canonical_snapshot_bytes_from_committed_state_v1(
            version=4,
            balances=cast(CommittedBalanceTableV1, sources[0]),
            pools=committed[1],
            lp_balances=committed[2],
            nonces=committed[3],
            fee_accumulator=committed[4],
            vault=committed[5],
            oracle=committed[6],
            perps=committed[7],
        )


def test_exact_snapshot_enforces_the_graph_wide_item_budget(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    committed = _committed_values(_legacy_sources())
    monkeypatch.setattr(committed_dex_snapshot, "MAX_ADMISSION_NODES_V1", 1)

    with pytest.raises(ValueError, match="json item count exceeds max_items"):
        canonical_snapshot_bytes_from_committed_state_v1(
            version=4,
            balances=committed[0],
            pools=committed[1],
            lp_balances=committed[2],
            nonces=committed[3],
            fee_accumulator=committed[4],
            vault=committed[5],
            oracle=committed[6],
            perps=committed[7],
        )


@settings(max_examples=50, deadline=None)
@given(
    reserve0=st.integers(min_value=0, max_value=DEX_POOL_RESERVE_MAX),
    reserve1=st.integers(min_value=0, max_value=DEX_POOL_RESERVE_MAX),
    lp_amount=st.integers(min_value=1, max_value=DEX_LP_AMOUNT_MAX),
    nonce=st.integers(min_value=0, max_value=2**32 - 1),
    dust=st.integers(min_value=0, max_value=2**64),
)
def test_exact_snapshot_bytes_match_legacy_over_mounted_machine_domain(
    reserve0: int,
    reserve1: int,
    lp_amount: int,
    nonce: int,
    dust: int,
) -> None:
    sources = _legacy_sources(
        reserve0=reserve0,
        reserve1=reserve1,
        lp_amount=lp_amount,
        nonce=nonce,
        dust=dust,
    )

    assert _exact_bytes(sources, version=4) == _legacy_bytes(sources, version=4)

from __future__ import annotations

from collections.abc import Iterator
from contextlib import contextmanager
from typing import Never, cast

import pytest

from src.core.fees import FeeAccumulatorState
from src.core.oracle import OracleState
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
    PerpClearinghouseNpMarketState,
    PerpMarketState,
    PerpsState,
)
from src.core.vault import VaultState
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.snapshot_combinators import (
    AdmissionLimitsV1,
    AdmitCode,
    AdmitOk,
    AdmitReject,
    ValidatedAdmissionLimitsV1,
    build_admission_limits_v1,
)
from src.state.state_admission_profile import admit
from src.state.state_snapshot_schema import (
    BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1,
    FEE_ACCUMULATOR_ADMISSION_SCHEMA_ID_V1,
    LP_TABLE_ADMISSION_SCHEMA_ID_V1,
    NONCE_TABLE_ADMISSION_SCHEMA_ID_V1,
    ORACLE_ADMISSION_SCHEMA_ID_V1,
    PERPS_ADMISSION_SCHEMA_ID_V1,
    POOL_ADMISSION_SCHEMA_ID_V1,
    POOL_MAP_ADMISSION_SCHEMA_ID_V1,
    VAULT_ADMISSION_SCHEMA_ID_V1,
)
from src.state.state_snapshot_values import (
    FCIS_STATE_SCHEMA_REVISION_V1,
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedOracleStateV1,
    CommittedPerpsStateV1,
    CommittedPoolStateV1,
    CommittedVaultStateV1,
    _BalanceSourceV1,
    _LPSourceV1,
    _NonceSourceV1,
)
from src.state.state_snapshots import (
    FrozenBalanceTable,
    StateAdmissionError,
    freeze_balance_table,
    freeze_lp_table,
    freeze_nonce_table,
    freeze_pool_mapping,
    snapshot_balance_table,
    snapshot_fee_accumulator,
    snapshot_lp_table,
    snapshot_nonce_table,
    snapshot_oracle,
    snapshot_perps,
    snapshot_pool,
    snapshot_pool_map,
    snapshot_vault,
)


@contextmanager
def _propagation_frame() -> Iterator[None]:
    """Exercise traceback attachment performed during exception unwinding."""

    yield


def _limits() -> ValidatedAdmissionLimitsV1:
    limits = build_admission_limits_v1(
        AdmissionLimitsV1(
            max_depth=64,
            max_nodes=200_000,
            max_canonical_bytes=4_000_000,
            max_collection_items=200_000,
        )
    )
    if type(limits) is not ValidatedAdmissionLimitsV1:
        raise AssertionError("test limit profile must be valid")
    return limits


def _admit(schema_id: str, source: object) -> AdmitOk[object] | AdmitReject:
    return admit(FCIS_STATE_SCHEMA_REVISION_V1, schema_id, _limits(), source)


def _pubkey(byte: str) -> str:
    return "0x" + byte * 96


def _pool() -> PoolState:
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    pool_id = compute_pool_id(asset0, asset1, 30)
    return PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=100,
        reserve1=200,
        fee_bps=30,
        lp_supply=50,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


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
    account = PerpAccountState(0, 0, 0, 0, 0, False)
    isolated = PerpMarketState(
        quote_asset="zUSD",
        global_state=_isolated_global(),
        accounts={_pubkey("1"): account},
    )
    ch2p = PerpClearinghouse2pMarketState(
        quote_asset="zUSD",
        account_a_pubkey=_pubkey("2"),
        account_b_pubkey=_pubkey("3"),
        state=_fixed_state(PERP_CLEARINGHOUSE_2P_STATE_KEYS, PERP_CLEARINGHOUSE_2P_BOOL_KEYS),
    )
    ch3p = PerpClearinghouse3pTransferMarketState(
        quote_asset="zUSD",
        account_a_pubkey=_pubkey("4"),
        account_b_pubkey=_pubkey("5"),
        account_c_pubkey=_pubkey("6"),
        state=_fixed_state(
            PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
            PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS,
        ),
    )
    chnp = PerpClearinghouseNpMarketState(
        quote_asset="zUSD",
        global_state=_np_global(),
        accounts=(),
        pending_intents=(),
    )
    return PerpsState(
        version=PERPS_STATE_VERSION_V5,
        markets={
            "isolated": isolated,
            "ch2p": ch2p,
            "ch3p": ch3p,
            "chnp": chnp,
        },
    )


def test_profile_admits_core_sources_to_distinct_owned_values() -> None:
    balance_source = _BalanceSourceV1({("alice", "asset"): 7})
    balance_result = _admit(BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1, balance_source)
    if type(balance_result) is not AdmitOk:
        raise AssertionError(balance_result)
    balances = cast(CommittedBalanceTableV1, balance_result.value)
    assert type(balances) is CommittedBalanceTableV1
    assert balances.get("alice", "asset") == 7

    lp_result = _admit(
        LP_TABLE_ADMISSION_SCHEMA_ID_V1,
        _LPSourceV1(
            {("alice", "pool"): 5},
            {("alice", "pool"): 1},
            {("alice", "pool"): 2},
            {("alice", "pool"): 3},
            {("alice", "pool"): 4},
        ),
    )
    if type(lp_result) is not AdmitOk:
        raise AssertionError(lp_result)
    assert type(lp_result.value) is CommittedLPTableV1

    nonce_result = _admit(
        NONCE_TABLE_ADMISSION_SCHEMA_ID_V1,
        _NonceSourceV1({_pubkey("7"): 3}),
    )
    if type(nonce_result) is not AdmitOk:
        raise AssertionError(nonce_result)
    assert type(nonce_result.value) is CommittedNonceTableV1

    pool_result = _admit(POOL_ADMISSION_SCHEMA_ID_V1, _pool())
    if type(pool_result) is not AdmitOk:
        raise AssertionError(pool_result)
    assert type(pool_result.value) is CommittedPoolStateV1

    pool = _pool()
    pool_map_result = _admit(POOL_MAP_ADMISSION_SCHEMA_ID_V1, {pool.pool_id: pool})
    if type(pool_map_result) is not AdmitOk:
        raise AssertionError(pool_map_result)


def test_pool_map_key_must_bind_the_committed_pool() -> None:
    result = _admit(POOL_MAP_ADMISSION_SCHEMA_ID_V1, {"wrong": _pool()})
    assert result == AdmitReject(AdmitCode.DOMAIN_INVARIANT, ())


@pytest.mark.parametrize(
    ("schema_id", "source", "owned_type"),
    [
        (VAULT_ADMISSION_SCHEMA_ID_V1, VaultState(2, 1, 0, 0, 0), CommittedVaultStateV1),
        (ORACLE_ADMISSION_SCHEMA_ID_V1, OracleState(0, 1), CommittedOracleStateV1),
        (FEE_ACCUMULATOR_ADMISSION_SCHEMA_ID_V1, FeeAccumulatorState(0), object),
        (PERPS_ADMISSION_SCHEMA_ID_V1, _perps(), CommittedPerpsStateV1),
    ],
)
def test_profile_admits_optional_and_perps_sources(
    schema_id: str,
    source: object,
    owned_type: type[object],
) -> None:
    result = _admit(schema_id, source)
    if type(result) is not AdmitOk:
        raise AssertionError(result)
    assert type(result.value) is owned_type or owned_type is object


@pytest.mark.parametrize(
    "schema_id",
    [VAULT_ADMISSION_SCHEMA_ID_V1, ORACLE_ADMISSION_SCHEMA_ID_V1, PERPS_ADMISSION_SCHEMA_ID_V1],
)
def test_optional_schemas_admit_none(schema_id: str) -> None:
    assert _admit(schema_id, None) == AdmitOk(None)


def test_admission_owns_source_aliases_and_re_admits_committed_values() -> None:
    raw = {("alice", "asset"): 7}
    first = _admit(BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1, _BalanceSourceV1(raw))
    if type(first) is not AdmitOk:
        raise AssertionError(first)
    committed = cast(CommittedBalanceTableV1, first.value)
    raw[("alice", "asset")] = 999
    raw[("mallory", "asset")] = 1
    assert committed.entries == ((("alice", "asset"), 7),)

    second = _admit(BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1, committed)
    if type(second) is not AdmitOk:
        raise AssertionError(second)
    assert second.value == committed
    assert second.value is not committed


def test_balance_snapshot_facade_owns_aliases_and_revalidates_committed_input() -> None:
    source = BalanceTable()
    source.set("alice", "asset", 7)

    committed = snapshot_balance_table(source)
    source.set("alice", "asset", 999)
    source.set("mallory", "asset", 1)

    assert type(committed) is CommittedBalanceTableV1
    assert committed.entries == ((("alice", "asset"), 7),)

    readmitted = snapshot_balance_table(committed)
    assert readmitted == committed
    assert readmitted is not committed


def test_snapshot_facades_bridge_exact_repository_owned_legacy_snapshots() -> None:
    balances = BalanceTable()
    balances.set("alice", "asset", 7)
    frozen_balances = freeze_balance_table(balances)

    lp_source = LPTable()
    lp_source.set("alice", _pool().pool_id, 5)
    frozen_lp = freeze_lp_table(lp_source)

    pool = _pool()
    frozen_pools = freeze_pool_mapping({pool.pool_id: pool})

    assert snapshot_balance_table(frozen_balances).entries == ((("alice", "asset"), 7),)
    assert snapshot_lp_table(frozen_lp).get("alice", pool.pool_id) == 5
    assert snapshot_pool_map(frozen_pools).entries[0][1].reserve0 == pool.reserve0


def test_snapshot_facade_rejects_caller_defined_frozen_subclass() -> None:
    class CallerFrozenBalance(FrozenBalanceTable):
        pass

    source = BalanceTable()
    source.set("alice", "asset", 7)

    with pytest.raises(StateAdmissionError) as captured:
        snapshot_balance_table(CallerFrozenBalance(source))

    assert captured.value.code is AdmitCode.WRONG_EXACT_TYPE
    assert captured.value.path == ()


def test_balance_snapshot_facade_rejects_raw_corruption_before_source_hooks() -> None:
    class HostileDict(dict[tuple[str, str], int]):
        iterated = False

        def items(self) -> Never:
            self.iterated = True
            raise AssertionError("hostile source hook must not execute")

    hostile = HostileDict({("alice", "asset"): 7})
    source = BalanceTable()
    object.__setattr__(source, "_balances", hostile)

    with pytest.raises(StateAdmissionError) as captured:
        snapshot_balance_table(source)

    assert captured.value.code is AdmitCode.WRONG_CONTAINER
    assert captured.value.path == ("_balances",)
    assert hostile.iterated is False


@pytest.mark.parametrize(
    ("key", "amount", "code"),
    [
        (("alice", "asset"), True, AdmitCode.WRONG_EXACT_TYPE),
        (("alice", "asset"), 0, AdmitCode.DOMAIN_INVARIANT),
        (("alice", 1), 7, AdmitCode.WRONG_KEY_TYPE),
        (("", "asset"), 7, AdmitCode.NONCANONICAL_SCALAR),
    ],
)
def test_balance_snapshot_facade_rejects_noncanonical_raw_entries(
    key: object,
    amount: object,
    code: AdmitCode,
) -> None:
    source = BalanceTable()
    raw = object.__getattribute__(source, "_balances")
    raw[key] = amount

    with pytest.raises(StateAdmissionError) as captured:
        snapshot_balance_table(source)

    assert captured.value.code is code


def test_balance_snapshot_facade_rejects_corrupted_owned_value() -> None:
    source = BalanceTable()
    source.set("alice", "asset", 7)
    committed = snapshot_balance_table(source)
    owned_map = object.__getattribute__(committed, "_balances")
    object.__setattr__(owned_map, "_entries", ((("alice", "asset"), True),))

    with pytest.raises(StateAdmissionError) as captured:
        snapshot_balance_table(committed)

    assert captured.value.code is AdmitCode.REGISTRY_DRIFT
    assert captured.value.path == ("_balances",)


def test_balance_snapshot_has_no_legacy_mutable_base_route() -> None:
    source = BalanceTable()
    source.set("alice", "asset", 7)
    committed = snapshot_balance_table(source)
    before = committed.entries

    assert not isinstance(committed, BalanceTable)
    with pytest.raises((AttributeError, TypeError)):
        BalanceTable.__init__(committed)
    with pytest.raises(TypeError):
        BalanceTable.set(committed, "alice", "asset", 9)

    assert committed.entries == before


def test_state_snapshot_facades_mount_every_declared_state_family() -> None:
    lp_source = LPTable()
    lp_source.set("alice", "pool", 5)
    lp_source.set_last_mint_timestamp("alice", "pool", 1)
    lp_source.set_last_remove_timestamp("alice", "pool", 2)
    lp_source.set_churn_tier("alice", "pool", 3)
    lp_source.set_last_churn_update_timestamp("alice", "pool", 4)
    lp = snapshot_lp_table(lp_source)

    nonce_source = NonceTable()
    nonce_source.set_last(_pubkey("7"), 3)
    nonces = snapshot_nonce_table(nonce_source)

    pool_source = _pool()
    pool = snapshot_pool(pool_source)
    pools = snapshot_pool_map({pool_source.pool_id: pool_source})
    vault = snapshot_vault(VaultState(2, 1, 0, 0, 0))
    oracle = snapshot_oracle(OracleState(0, 1))
    fees = snapshot_fee_accumulator(FeeAccumulatorState(0))
    perps = snapshot_perps(_perps())

    lp_source.set("alice", "pool", 999)
    nonce_source.set_last(_pubkey("7"), 4)
    pool_source.reserve0 = 999

    assert type(lp) is CommittedLPTableV1
    assert lp.get("alice", "pool") == 5
    assert lp.get_last_mint_timestamp("alice", "pool") == 1
    assert type(nonces) is CommittedNonceTableV1
    assert nonces.get_last(_pubkey("7")) == 3
    assert type(pool) is CommittedPoolStateV1
    assert pool.reserve0 == 100
    assert pools.entries == ((pool.pool_id, pool),)
    assert type(vault) is CommittedVaultStateV1
    assert type(oracle) is CommittedOracleStateV1
    assert type(fees) is CommittedFeeAccumulatorStateV1
    assert type(perps) is CommittedPerpsStateV1


def test_nonce_snapshot_facade_admits_the_mounted_frozen_nonce_table() -> None:
    source = NonceTable()
    source.set_last(_pubkey("7"), 3)
    mounted = freeze_nonce_table(source)

    committed = snapshot_nonce_table(mounted)
    source.set_last(_pubkey("7"), 4)

    assert type(committed) is CommittedNonceTableV1
    assert committed.get_last(_pubkey("7")) == 3


def test_lp_and_nonce_snapshot_facades_reject_hostile_raw_containers_before_hooks() -> None:
    class HostileDict(dict[object, object]):
        iterated = False

        def items(self) -> Never:
            self.iterated = True
            raise AssertionError("hostile source hook must not execute")

    lp_hostile = HostileDict()
    lp_source = LPTable()
    object.__setattr__(lp_source, "_balances", lp_hostile)
    with pytest.raises(StateAdmissionError) as lp_error:
        snapshot_lp_table(lp_source)
    assert lp_error.value == StateAdmissionError(AdmitCode.WRONG_CONTAINER, ("_balances",))
    assert lp_hostile.iterated is False

    nonce_hostile = HostileDict()
    nonce_source = NonceTable()
    object.__setattr__(nonce_source, "_last", nonce_hostile)
    with pytest.raises(StateAdmissionError) as nonce_error:
        snapshot_nonce_table(nonce_source)
    assert nonce_error.value == StateAdmissionError(AdmitCode.WRONG_CONTAINER, ("_last",))
    assert nonce_hostile.iterated is False


def test_explicit_optional_snapshot_families_reject_unregistered_values() -> None:
    for snapshot in (
        snapshot_vault,
        snapshot_oracle,
        snapshot_fee_accumulator,
        snapshot_perps,
    ):
        with pytest.raises(StateAdmissionError) as captured:
            snapshot(object())
        assert captured.value == StateAdmissionError(AdmitCode.WRONG_EXACT_TYPE, ())


def test_state_admission_error_allows_traceback_attachment_during_unwinding() -> None:
    with pytest.raises(StateAdmissionError) as captured:
        with _propagation_frame():
            snapshot_fee_accumulator(object())

    assert captured.value == StateAdmissionError(AdmitCode.WRONG_EXACT_TYPE, ())


def test_domain_invariant_rejects_without_partial_owned_value() -> None:
    result = _admit(
        BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1,
        _BalanceSourceV1({("alice", "asset"): 0}),
    )
    assert result == AdmitReject(AdmitCode.DOMAIN_INVARIANT, ())


def test_wrong_exact_types_reject_before_source_behavior() -> None:
    class HostileDict(dict[tuple[str, str], int]):
        iterated = False

        def items(self) -> Never:
            self.iterated = True
            raise AssertionError("hostile override must not execute")

    hostile = HostileDict({("alice", "asset"): 7})
    result = _admit(BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1, _BalanceSourceV1(hostile))
    assert result == AdmitReject(AdmitCode.WRONG_CONTAINER, ("_balances",))
    assert hostile.iterated is False


def test_unknown_revision_and_schema_fail_closed() -> None:
    source = _BalanceSourceV1({("alice", "asset"): 7})
    assert admit("wrong", BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1, _limits(), source) == AdmitReject(
        AdmitCode.UNSUPPORTED_VARIANT,
        (),
    )
    assert admit(FCIS_STATE_SCHEMA_REVISION_V1, "unknown", _limits(), source) == AdmitReject(
        AdmitCode.UNSUPPORTED_VARIANT,
        (),
    )

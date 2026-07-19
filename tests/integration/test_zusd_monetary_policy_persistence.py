from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.dex import DexState
from src.core.perps import PERPS_STATE_VERSION_V5, PerpsState
from src.core.zusd import E8
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    apply_zusd_monetary_ops,
    init_monetary_state,
    zusd_monetary_state_from_obj,
    zusd_monetary_state_to_obj,
)
from src.state.balances import NATIVE_ASSET, BalanceTable
from src.state.lp import LPTable, copy_lp_table
from src.state.pools import PoolState, PoolStatus, copy_pool_state

ACTOR = "0x" + "41" * 48
ASSET_A = "0x" + "51" * 32
ASSET_B = "0x" + "52" * 32
STAKE_A = "0x" + "61" * 32
STAKE_B = "0x" + "62" * 32


def _config(**changes: object) -> ZUSDMonetaryConfig:
    fields: dict[str, object] = {
        "chain_id": "tau-policy-binding",
        "asset_id": ASSET_A,
        "fee_stake_asset_id": STAKE_A,
        "liquidation_gas_comp_fixed_collateral_e8": 7,
        "liquidation_gas_comp_bps": 20,
        "borrow_fee_floor_bps": 10,
        "borrow_fee_max_bps": 100,
        "host_protocol_fee_share_bps": 30,
        "staking_activation_delay_epochs": 2,
    }
    fields.update(changes)
    return ZUSDMonetaryConfig(**fields)  # type: ignore[arg-type]


def _dex_state(*, native_balance: int = 0) -> DexState:
    balances = BalanceTable()
    if native_balance:
        balances.set(ACTOR, NATIVE_ASSET, native_balance)
    return DexState(balances=balances, pools={}, lp_balances=LPTable())


def test_v2_roundtrip_preserves_exact_committed_policy() -> None:
    state = init_monetary_state(_config())

    encoded = zusd_monetary_state_to_obj(state)
    decoded = zusd_monetary_state_from_obj(encoded)

    assert encoded["schema"] == "zenodex/zusd_monetary_state/v2"
    assert encoded["version"] == 2
    assert decoded == state
    assert decoded.policy_binding == state.policy_binding


def test_v2_core_schema_registry_matches_runtime_state_fields() -> None:
    state = init_monetary_state(_config())
    encoded = zusd_monetary_state_to_obj(state)

    assert tuple(encoded["core"]) == tuple(state.core.__dict__)


def test_v2_decoder_rejects_legacy_unbound_state() -> None:
    encoded = zusd_monetary_state_to_obj(init_monetary_state(_config()))
    encoded["schema"] = "zenodex/zusd_monetary_state/v1"
    encoded["version"] = 1
    encoded.pop("policy_binding")

    with pytest.raises(ValueError, match="explicit governed migration"):
        zusd_monetary_state_from_obj(encoded)


@pytest.mark.parametrize("missing_field", ("oracle_pubkey", "fee_stake_asset_id"))
def test_v2_decoder_requires_nullable_policy_fields_explicitly(
    missing_field: str,
) -> None:
    encoded = zusd_monetary_state_to_obj(init_monetary_state(_config()))
    policy = dict(encoded["policy_binding"])
    policy.pop(missing_field)
    encoded["policy_binding"] = policy

    with pytest.raises(ValueError, match="fields must match the v1 schema exactly"):
        zusd_monetary_state_from_obj(encoded)


def test_v2_decoder_rejects_unknown_policy_and_state_fields() -> None:
    state_obj = zusd_monetary_state_to_obj(init_monetary_state(_config()))
    policy_obj = dict(state_obj["policy_binding"])
    policy_obj["future_policy"] = 1
    state_obj["policy_binding"] = policy_obj

    with pytest.raises(ValueError, match="fields must match the v1 schema exactly"):
        zusd_monetary_state_from_obj(state_obj)

    state_obj = zusd_monetary_state_to_obj(init_monetary_state(_config()))
    state_obj["future_state"] = 1
    with pytest.raises(ValueError, match="fields must match the v2 schema exactly"):
        zusd_monetary_state_from_obj(state_obj)


@pytest.mark.parametrize("mutation", ("missing", "unknown"))
def test_v2_decoder_requires_exact_core_field_set(mutation: str) -> None:
    state_obj = zusd_monetary_state_to_obj(init_monetary_state(_config()))
    core_obj = dict(state_obj["core"])
    if mutation == "missing":
        core_obj.pop("collateral_e8")
    else:
        core_obj["future_core_field"] = 0
    state_obj["core"] = core_obj

    with pytest.raises(
        ValueError,
        match="zusd_monetary.core fields must match the v2 schema exactly",
    ):
        zusd_monetary_state_from_obj(state_obj)


@pytest.mark.parametrize(
    ("field_name", "entry"),
    (
        (
            "active_fee_stakes",
            {"pubkey": ACTOR, "amount": 1, "unbound_policy_override": 1},
        ),
        (
            "pending_fee_stakes",
            {
                "pubkey": ACTOR,
                "amount": 1,
                "activation_epoch": 2,
                "ignored": True,
            },
        ),
    ),
)
def test_v2_decoder_rejects_unknown_nested_record_fields(
    field_name: str,
    entry: dict[str, object],
) -> None:
    state_obj = zusd_monetary_state_to_obj(init_monetary_state(_config()))
    state_obj[field_name] = [entry]

    with pytest.raises(ValueError, match="fields must match the v2 schema exactly"):
        zusd_monetary_state_from_obj(state_obj)


@pytest.mark.parametrize("field_name", ("sp_deposits", "pending_fee_stakes"))
def test_v2_decoder_rejects_null_nested_tables(field_name: str) -> None:
    state_obj = zusd_monetary_state_to_obj(init_monetary_state(_config()))
    state_obj[field_name] = None

    with pytest.raises(TypeError, match="must be a list"):
        zusd_monetary_state_from_obj(state_obj)


def test_v2_decoder_rejects_zero_and_unsorted_account_records() -> None:
    state_obj = zusd_monetary_state_to_obj(init_monetary_state(_config()))
    state_obj["active_fee_stakes"] = [{"pubkey": ACTOR, "amount": 0}]
    with pytest.raises(ValueError, match="amount must be positive"):
        zusd_monetary_state_from_obj(state_obj)

    state_obj = zusd_monetary_state_to_obj(init_monetary_state(_config()))
    state_obj["active_fee_stakes"] = [
        {"pubkey": "0x" + "42" * 48, "amount": 1},
        {"pubkey": ACTOR, "amount": 1},
    ]
    with pytest.raises(ValueError, match="strictly sorted by pubkey"):
        zusd_monetary_state_from_obj(state_obj)


@pytest.mark.parametrize(
    ("field_name", "invalid_value"),
    (
        ("collateral_e8", True),
        ("collateral_e8", "0"),
        ("collateral_e8", 0.0),
        ("oracle_seen", 1),
    ),
)
def test_v2_decoder_rejects_core_numeric_coercions(
    field_name: str,
    invalid_value: object,
) -> None:
    state_obj = zusd_monetary_state_to_obj(init_monetary_state(_config()))
    core_obj = dict(state_obj["core"])
    core_obj[field_name] = invalid_value
    state_obj["core"] = core_obj

    with pytest.raises(TypeError, match=rf"zusd_monetary.core.{field_name}"):
        zusd_monetary_state_from_obj(state_obj)


def test_core_policy_duplication_cannot_disagree_at_construction() -> None:
    state = init_monetary_state(_config())

    with pytest.raises(
        ValueError,
        match="core policy field does not match committed binding: borrow_fee_floor_bps",
    ):
        replace(
            state,
            core=replace(state.core, borrow_fee_floor_bps=11),
        )


def test_committed_maps_defensively_copy_and_reject_retained_alias_mutation() -> None:
    deposits = {ACTOR: E8}
    base = init_monetary_state(_config())
    state = replace(base, sp_deposits_e8=deposits)

    deposits[ACTOR] = 2 * E8

    assert state.sp_deposits_e8 == {ACTOR: E8}
    with pytest.raises(TypeError):
        state.sp_deposits_e8[ACTOR] = 3 * E8  # type: ignore[index]


@pytest.mark.parametrize(
    ("changes", "field_name"),
    (
        ({"asset_id": ASSET_B}, "canonical_zusd_asset"),
        ({"fee_stake_asset_id": STAKE_B}, "fee_stake_asset_id"),
    ),
)
def test_runtime_configuration_rebinding_rejects_without_state_change(
    changes: dict[str, object],
    field_name: str,
) -> None:
    committed_config = _config()
    state = _dex_state()
    monetary = init_monetary_state(committed_config)

    result = apply_zusd_monetary_ops(
        config=_config(**changes),
        state=state,
        zusd_state=monetary,
        operations=[],
        tx_sender_pubkey=ACTOR,
        block_timestamp=0,
    )

    assert result.ok is False
    assert result.state is None
    assert result.zusd_state is None
    assert result.effects is None
    assert result.error == f"zUSD monetary policy binding mismatch: {field_name}"
    assert state.balances.get_all_balances() == {}
    assert monetary == init_monetary_state(committed_config)


def test_accepted_transition_preserves_committed_policy_identity() -> None:
    config = _config()
    monetary = init_monetary_state(config)
    state = _dex_state(native_balance=2 * E8)

    result = apply_zusd_monetary_ops(
        config=config,
        state=state,
        zusd_state=monetary,
        operations=[
            {
                "module": "ZUSDFinance",
                "version": "0.1",
                "action": "deposit_collateral",
                "owner_pubkey": ACTOR,
                "amount_e8": E8,
                "nonce": 1,
                "deadline": 100,
            }
        ],
        tx_sender_pubkey=ACTOR,
        block_timestamp=0,
    )

    assert result.ok is True, result.error
    assert result.zusd_state is not None
    assert result.zusd_state.policy_binding is monetary.policy_binding
    assert result.zusd_state.core.collateral_e8 == E8


def test_first_fee_stake_activation_uses_sparse_zero_reward_debt() -> None:
    config = _config(staking_activation_delay_epochs=1)
    balances = BalanceTable()
    balances.set(ACTOR, STAKE_A, 2)
    prestate = DexState(balances=balances, pools={}, lp_balances=LPTable())

    result = apply_zusd_monetary_ops(
        config=config,
        state=prestate,
        zusd_state=init_monetary_state(config),
        operations=[
            {
                "module": "ZUSDFinance",
                "version": "0.1",
                "action": "stake_fee_shares",
                "amount": 2,
                "nonce": 1,
                "deadline": 100,
            },
            {
                "module": "ZUSDFinance",
                "version": "0.1",
                "action": "advance_epoch",
                "delta": 1,
                "nonce": 2,
                "deadline": 100,
            },
        ],
        tx_sender_pubkey=ACTOR,
        block_timestamp=0,
    )

    assert result.ok is True, result.error
    assert result.state is not None
    assert result.zusd_state is not None
    assert result.state.balances.get(ACTOR, STAKE_A) == 0
    assert result.zusd_state.active_fee_stakes == {ACTOR: 2}
    assert result.zusd_state.pending_fee_stakes == {}
    assert result.zusd_state.fee_stake_reward_debt_e8 == {}
    explicit_zero = replace(
        result.zusd_state,
        fee_stake_reward_debt_e8={ACTOR: 0},
    )
    assert explicit_zero.fee_stake_reward_debt_e8 == {}
    assert (
        zusd_monetary_state_from_obj(
            zusd_monetary_state_to_obj(result.zusd_state)
        )
        == result.zusd_state
    )


def test_partial_unstake_preserves_sparse_zero_reward_debt() -> None:
    config = _config(staking_activation_delay_epochs=0)
    balances = BalanceTable()
    balances.set(ACTOR, STAKE_A, 2)
    prestate = DexState(balances=balances, pools={}, lp_balances=LPTable())

    result = apply_zusd_monetary_ops(
        config=config,
        state=prestate,
        zusd_state=init_monetary_state(config),
        operations=[
            {
                "module": "ZUSDFinance",
                "version": "0.1",
                "action": "stake_fee_shares",
                "amount": 2,
                "nonce": 1,
                "deadline": 100,
            },
            {
                "module": "ZUSDFinance",
                "version": "0.1",
                "action": "advance_epoch",
                "delta": 1,
                "nonce": 2,
                "deadline": 100,
            },
            {
                "module": "ZUSDFinance",
                "version": "0.1",
                "action": "unstake_fee_shares",
                "amount": 1,
                "nonce": 3,
                "deadline": 100,
            },
        ],
        tx_sender_pubkey=ACTOR,
        block_timestamp=0,
    )

    assert result.ok is True, result.error
    assert result.state is not None
    assert result.zusd_state is not None
    assert result.state.balances.get(ACTOR, STAKE_A) == 1
    assert result.zusd_state.active_fee_stakes == {ACTOR: 1}
    assert result.zusd_state.fee_stake_reward_debt_e8 == {}


def test_accepted_result_effects_are_transitively_immutable() -> None:
    config = _config()
    monetary = init_monetary_state(config)
    state = _dex_state(native_balance=2 * E8)

    result = apply_zusd_monetary_ops(
        config=config,
        state=state,
        zusd_state=monetary,
        operations=[
            {
                "module": "ZUSDFinance",
                "version": "0.1",
                "action": "deposit_collateral",
                "owner_pubkey": ACTOR,
                "amount_e8": E8,
                "nonce": 1,
                "deadline": 100,
            }
        ],
        tx_sender_pubkey=ACTOR,
        block_timestamp=0,
    )

    assert result.ok is True
    assert result.effects is not None
    assert isinstance(result.effects, tuple)
    rendered = result.effects[0].to_obj()
    rendered["action"] = "forged"
    rendered["effects"]["amount_e8"] = 999
    assert result.effects[0].to_obj()["action"] == "deposit_collateral"
    assert result.effects[0].to_obj()["effects"]["amount_e8"] == E8


def test_accepted_result_detaches_mutable_dex_children_from_prestate() -> None:
    pool = PoolState(
        pool_id="pool-a",
        asset0=ASSET_B,
        asset1=STAKE_A,
        reserve0=10,
        reserve1=20,
        fee_bps=30,
        lp_supply=5,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(ACTOR, NATIVE_ASSET, 2 * E8)
    lp_balances = LPTable()
    lp_balances.set(ACTOR, pool.pool_id, 3)
    perps = PerpsState(version=PERPS_STATE_VERSION_V5, markets={})
    prestate = DexState(
        balances=balances,
        pools={pool.pool_id: pool},
        lp_balances=lp_balances,
        perps=perps,
    )

    result = apply_zusd_monetary_ops(
        config=_config(),
        state=prestate,
        zusd_state=init_monetary_state(_config()),
        operations=[
            {
                "module": "ZUSDFinance",
                "version": "0.1",
                "action": "deposit_collateral",
                "owner_pubkey": ACTOR,
                "amount_e8": E8,
                "nonce": 1,
                "deadline": 100,
            }
        ],
        tx_sender_pubkey=ACTOR,
        block_timestamp=0,
    )

    assert result.ok is True
    assert result.state is not None
    assert result.state.pools is not prestate.pools
    assert result.state.pools[pool.pool_id] is not prestate.pools[pool.pool_id]
    assert result.state.lp_balances is not prestate.lp_balances
    # PerpsState is sealed and may be structurally shared unchanged.
    assert result.state.perps is prestate.perps
    assert result.state.perps is not None
    # Sealed mappings are safe to structurally share across committed snapshots.
    assert result.state.perps.markets is prestate.perps.markets

    with pytest.raises(TypeError, match="FrozenPoolState cannot be mutated"):
        result.state.pools[pool.pool_id].reserve0 = 999
    with pytest.raises(TypeError, match="FrozenLPTable cannot be mutated"):
        result.state.lp_balances.set(ACTOR, pool.pool_id, 99)
    with pytest.raises(TypeError, match="immutable value cannot be mutated"):
        result.state.perps.markets["forged"] = "invalid-market"  # type: ignore[index]

    pool_builder = copy_pool_state(result.state.pools[pool.pool_id])
    pool_builder.reserve0 = 999
    pool_builders = dict(result.state.pools)
    pool_builders[pool.pool_id] = pool_builder
    lp_builder = copy_lp_table(result.state.lp_balances)
    lp_builder.set(ACTOR, pool.pool_id, 99)
    forked_state = replace(
        result.state,
        pools=pool_builders,
        lp_balances=lp_builder,
    )

    assert forked_state.pools[pool.pool_id].reserve0 == 999
    assert forked_state.lp_balances.get(ACTOR, pool.pool_id) == 99
    with pytest.raises(TypeError, match="exact persistent market state types"):
        replace(result.state.perps, markets={"forged": "invalid-market"})  # type: ignore[dict-item]

    assert result.state.pools[pool.pool_id].reserve0 == 10
    assert result.state.lp_balances.get(ACTOR, pool.pool_id) == 3
    assert result.state.perps.markets == {}
    assert prestate.pools[pool.pool_id].reserve0 == 10
    assert prestate.lp_balances.get(ACTOR, pool.pool_id) == 3
    assert prestate.perps.markets == {}

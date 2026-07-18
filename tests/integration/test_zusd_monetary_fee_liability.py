from __future__ import annotations

from dataclasses import replace

from src.core.dex import DexState
from src.core.zusd import E8
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    ZUSDMonetaryState,
    ZUSDMonetaryTxResult,
    apply_zusd_monetary_ops,
    init_monetary_state,
)
from src.state.balances import NATIVE_ASSET, BalanceTable
from src.state.lp import LPTable
from tests.consensus_clock import execution_clock_v1

ORACLE = "0x" + "01" * 48
ALICE = "0x" + "02" * 48
PROTOCOL = "0x" + "03" * 48
STAKER = "0x" + "04" * 48
STAKE_ASSET = "0x" + "aa" * 32


def _state(*, alice_native_e8: int = 100 * E8, stake_units: int = 0) -> DexState:
    balances = BalanceTable()
    balances.set(ALICE, NATIVE_ASSET, alice_native_e8)
    if stake_units:
        balances.set(STAKER, STAKE_ASSET, stake_units)
    return DexState(balances=balances, pools={}, lp_balances=LPTable())


def _apply(
    *,
    config: ZUSDMonetaryConfig,
    state: DexState,
    monetary: ZUSDMonetaryState,
    sender: str,
    height: int,
    operations: list[dict[str, object]],
) -> ZUSDMonetaryTxResult:
    return apply_zusd_monetary_ops(
        config=config,
        state=state,
        zusd_state=monetary,
        operations=operations,
        tx_sender_pubkey=sender,
        block_timestamp=height,
        execution_clock=execution_clock_v1(
            chain_id=config.chain_id,
            height=height,
        ),
    )


def _accepted(result: ZUSDMonetaryTxResult) -> tuple[DexState, ZUSDMonetaryState]:
    assert result.ok is True, result.error
    assert result.state is not None
    assert result.zusd_state is not None
    return result.state, result.zusd_state


def _bootstrap_and_deposit(
    config: ZUSDMonetaryConfig,
    *,
    state: DexState,
) -> tuple[DexState, ZUSDMonetaryState]:
    monetary = init_monetary_state(config)
    state, monetary = _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=ORACLE,
            height=0,
            operations=[
                {
                    "action": "bootstrap_oracle",
                    "price_e8": 100 * E8,
                    "nonce": 1,
                }
            ],
        )
    )
    return _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=ALICE,
            height=0,
            operations=[
                {
                    "action": "deposit_collateral",
                    "owner_pubkey": ALICE,
                    "amount_e8": 20 * E8,
                    "nonce": 1,
                }
            ],
        )
    )


def _assert_reject_has_no_state_or_effects(result: ZUSDMonetaryTxResult) -> None:
    assert result.ok is False
    assert result.state is None
    assert result.zusd_state is None
    assert result.effects is None


def _transfer_zusd(
    state: DexState,
    *,
    asset: str,
    sender: str,
    recipient: str,
    units: int,
) -> DexState:
    balances = BalanceTable()
    for (pubkey, current_asset), amount in state.balances.get_all_balances().items():
        balances.set(pubkey, current_asset, amount)
    balances.subtract(sender, asset, units)
    balances.add(recipient, asset, units)
    return replace(state, balances=balances)


def test_protocol_fee_requires_committed_claimant_before_mint_mutates() -> None:
    config = ZUSDMonetaryConfig(
        chain_id="fee-liability-missing-claimant",
        oracle_pubkey=ORACLE,
        borrow_fee_floor_bps=50,
        borrow_fee_max_bps=500,
    )
    state, monetary = _bootstrap_and_deposit(config, state=_state())
    balances_before = state.balances.get_all_balances()
    nonces_before = state.nonces.get_all()

    result = _apply(
        config=config,
        state=state,
        monetary=monetary,
        sender=ALICE,
        height=1,
        operations=[
            {
                "action": "mint_zusd",
                "owner_pubkey": ALICE,
                "amount_e8": 1_000 * E8,
                "nonce": 2,
            }
        ],
    )

    _assert_reject_has_no_state_or_effects(result)
    assert result.error == "zusd op[0] protocol fee recipient not configured"
    assert state.balances.get_all_balances() == balances_before
    assert state.nonces.get_all() == nonces_before
    assert monetary.core.debt_e8 == 0


def test_protocol_claimant_can_drain_reserve_and_enable_full_repay() -> None:
    config = ZUSDMonetaryConfig(
        chain_id="fee-liability-claim",
        oracle_pubkey=ORACLE,
        protocol_fee_recipient_pubkey=PROTOCOL,
        borrow_fee_floor_bps=50,
        borrow_fee_max_bps=500,
    )
    state, monetary = _bootstrap_and_deposit(config, state=_state())
    state, monetary = _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=ALICE,
            height=1,
            operations=[
                {
                    "action": "mint_zusd",
                    "owner_pubkey": ALICE,
                    "amount_e8": 1_000 * E8,
                    "nonce": 2,
                }
            ],
        )
    )
    assert monetary.core.debt_e8 == 1_005 * E8
    assert monetary.protocol_zusd_fee_reserve_e8 == 5 * E8
    assert state.balances.get(ALICE, config.zusd_asset) == 1_000

    balances_before = state.balances.get_all_balances()
    nonces_before = state.nonces.get_all()
    monetary_before = monetary
    unauthorized = _apply(
        config=config,
        state=state,
        monetary=monetary,
        sender=STAKER,
        height=2,
        operations=[{"action": "claim_protocol_fees", "nonce": 1}],
    )
    _assert_reject_has_no_state_or_effects(unauthorized)
    assert unauthorized.error == "zusd op[0] claim_protocol_fees recipient only"
    assert state.balances.get_all_balances() == balances_before
    assert state.nonces.get_all() == nonces_before
    assert monetary == monetary_before

    state, monetary = _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=PROTOCOL,
            height=2,
            operations=[{"action": "claim_protocol_fees", "nonce": 1}],
        )
    )
    assert monetary.protocol_zusd_fee_reserve_e8 == 0
    assert state.balances.get(PROTOCOL, config.zusd_asset) == 5

    state = _transfer_zusd(
        state,
        asset=config.zusd_asset,
        sender=PROTOCOL,
        recipient=ALICE,
        units=5,
    )
    state, monetary = _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=ALICE,
            height=3,
            operations=[
                {
                    "action": "repay_zusd",
                    "owner_pubkey": ALICE,
                    "amount_e8": 1_005 * E8,
                    "nonce": 3,
                }
            ],
        )
    )
    assert monetary.core.debt_e8 == 0
    assert monetary.core.free_debt_e8 == 0
    assert state.balances.get(ALICE, config.zusd_asset) == 0


def test_fractional_fee_cannot_create_unclosable_whole_token_debt() -> None:
    config = ZUSDMonetaryConfig(
        chain_id="fee-liability-fractional",
        oracle_pubkey=ORACLE,
        protocol_fee_recipient_pubkey=PROTOCOL,
        borrow_fee_floor_bps=50,
        borrow_fee_max_bps=500,
    )
    state, monetary = _bootstrap_and_deposit(config, state=_state())
    balances_before = state.balances.get_all_balances()
    nonces_before = state.nonces.get_all()

    result = _apply(
        config=config,
        state=state,
        monetary=monetary,
        sender=ALICE,
        height=1,
        operations=[
            {
                "action": "mint_zusd",
                "owner_pubkey": ALICE,
                "amount_e8": 100 * E8,
                "nonce": 2,
            }
        ],
    )

    _assert_reject_has_no_state_or_effects(result)
    assert result.error == ("zusd op[0] mint fee is not representable by whole-zUSD transport")
    assert state.balances.get_all_balances() == balances_before
    assert state.nonces.get_all() == nonces_before
    assert monetary.core.debt_e8 == 0


def test_accumulator_residue_rejects_before_stake_or_debt_can_lock() -> None:
    config = ZUSDMonetaryConfig(
        chain_id="fee-liability-residue",
        oracle_pubkey=ORACLE,
        protocol_fee_recipient_pubkey=PROTOCOL,
        fee_stake_asset_id=STAKE_ASSET,
        borrow_fee_floor_bps=50,
        borrow_fee_max_bps=500,
        staking_activation_delay_epochs=1,
    )
    state, monetary = _bootstrap_and_deposit(
        config,
        state=_state(stake_units=3),
    )
    state, monetary = _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=STAKER,
            height=0,
            operations=[
                {
                    "action": "stake_fee_shares",
                    "amount": 3,
                    "nonce": 1,
                }
            ],
        )
    )
    state, monetary = _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=STAKER,
            height=1,
            operations=[],
        )
    )
    assert monetary.active_fee_stakes == {STAKER: 3}
    balances_before = state.balances.get_all_balances()
    nonces_before = state.nonces.get_all()

    result = _apply(
        config=config,
        state=state,
        monetary=monetary,
        sender=ALICE,
        height=1,
        operations=[
            {
                "action": "mint_zusd",
                "owner_pubkey": ALICE,
                "amount_e8": 200 * E8,
                "nonce": 2,
            }
        ],
    )

    _assert_reject_has_no_state_or_effects(result)
    assert result.error == ("zusd op[0] staking fee accumulator would create unattributed residue")
    assert state.balances.get_all_balances() == balances_before
    assert state.nonces.get_all() == nonces_before
    assert monetary.staking_zusd_fee_pool_e8 == 0
    assert monetary.core.debt_e8 == 0


def test_active_stake_top_up_preserves_claimable_across_floor_boundary() -> None:
    config = ZUSDMonetaryConfig(
        chain_id="fee-liability-top-up-rounding",
        oracle_pubkey=ORACLE,
        protocol_fee_recipient_pubkey=PROTOCOL,
        fee_stake_asset_id=STAKE_ASSET,
        borrow_fee_floor_bps=50,
        borrow_fee_max_bps=500,
        staking_activation_delay_epochs=1,
    )
    state, monetary = _bootstrap_and_deposit(
        config,
        state=_state(stake_units=200_000_001),
    )
    state, monetary = _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=STAKER,
            height=0,
            operations=[
                {
                    "action": "stake_fee_shares",
                    "amount": 200_000_000,
                    "nonce": 1,
                }
            ],
        )
    )
    state, monetary = _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=STAKER,
            height=1,
            operations=[],
        )
    )
    state, monetary = _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=ALICE,
            height=1,
            operations=[
                {
                    "action": "mint_zusd",
                    "owner_pubkey": ALICE,
                    "amount_e8": 200 * E8,
                    "nonce": 2,
                }
            ],
        )
    )
    assert monetary.staking_zusd_fee_acc_per_share_e8 == 500_000
    assert monetary.staking_zusd_fee_pool_e8 == E8
    state, monetary = _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=STAKER,
            height=1,
            operations=[
                {"action": "claim_staking_fees", "nonce": 2},
                {
                    "action": "unstake_fee_shares",
                    "amount": 199_999_999,
                    "nonce": 3,
                },
                {
                    "action": "stake_fee_shares",
                    "amount": 1,
                    "nonce": 4,
                },
            ],
        )
    )
    assert monetary.active_fee_stakes == {STAKER: 1}
    assert monetary.pending_fee_stakes == {STAKER: 1}
    assert monetary.staking_zusd_fee_pool_e8 == 0

    state, monetary = _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=STAKER,
            height=2,
            operations=[],
        )
    )

    assert monetary.active_fee_stakes == {STAKER: 2}
    assert monetary.pending_fee_stakes == {}
    assert monetary.fee_stake_reward_debt_e8 == {STAKER: 1}
    assert monetary.staking_zusd_fee_pool_e8 == 0


def test_same_batch_stake_remains_pending_and_cannot_capture_borrow_fee() -> None:
    config = ZUSDMonetaryConfig(
        chain_id="fee-liability-no-flash-stake",
        oracle_pubkey=ORACLE,
        protocol_fee_recipient_pubkey=PROTOCOL,
        fee_stake_asset_id=STAKE_ASSET,
        borrow_fee_floor_bps=50,
        borrow_fee_max_bps=500,
        staking_activation_delay_epochs=1,
    )
    state = _state(stake_units=0)
    balances = BalanceTable()
    for (pubkey, asset), amount in state.balances.get_all_balances().items():
        balances.set(pubkey, asset, amount)
    balances.set(ALICE, STAKE_ASSET, 1)
    state = replace(state, balances=balances)
    state, monetary = _bootstrap_and_deposit(config, state=state)

    state, monetary = _accepted(
        _apply(
            config=config,
            state=state,
            monetary=monetary,
            sender=ALICE,
            height=0,
            operations=[
                {
                    "action": "stake_fee_shares",
                    "amount": 1,
                    "nonce": 2,
                },
                {
                    "action": "mint_zusd",
                    "owner_pubkey": ALICE,
                    "amount_e8": 1_000 * E8,
                    "nonce": 3,
                },
            ],
        )
    )

    assert monetary.pending_fee_stakes == {ALICE: 1}
    assert monetary.active_fee_stakes == {}
    assert monetary.staking_zusd_fee_pool_e8 == 0
    assert monetary.protocol_zusd_fee_reserve_e8 == 5 * E8
    assert state.balances.get(ALICE, STAKE_ASSET) == 0

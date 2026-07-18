from __future__ import annotations

import pytest

from src.core.consensus_time import (
    U64_MAX,
    ClockAuthorityProfileV1,
    ClockPolicyScheduleV1,
    ClockPolicyV1,
    clock_policy_hash_v1,
    clock_policy_schedule_hash_v1,
    verify_execution_clock_v1,
)
from src.core.dex import DexState
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    apply_zusd_monetary_ops,
    init_monetary_state,
)
from src.state import BalanceTable, LPTable

SENDER = "0x" + "11" * 48


def _policy(*, blocks_per_epoch: int = 5) -> ClockPolicyV1:
    return ClockPolicyV1(
        clock_policy_id="HEIGHT_ONLY_V1",
        clock_policy_version=1,
        chain_id="zenodex-testnet-1",
        deployment_profile=(ClockAuthorityProfileV1.ZENO_LEDGER_TAU_CHECKPOINTED_V1),
        consensus_domain_id="zeno-ledger:testnet-1",
        activation_height=10,
        epoch_base=7,
        blocks_per_epoch=blocks_per_epoch,
    )


def _clock(*, height: int):
    schedule = ClockPolicyScheduleV1(policies=(_policy(),))
    return verify_execution_clock_v1(
        chain_id="zenodex-testnet-1",
        height=height,
        schedule=schedule,
        expected_schedule_hash=clock_policy_schedule_hash_v1(schedule),
    )


def _config() -> ZUSDMonetaryConfig:
    return ZUSDMonetaryConfig(
        chain_id="zenodex-testnet-1",
        clock_policy_hash=clock_policy_hash_v1(_policy()),
        oracle_pubkey=SENDER,
    )


def _state() -> DexState:
    return DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
    )


def test_mounted_zusd_rejects_missing_verified_execution_clock() -> None:
    config = _config()
    monetary = init_monetary_state(config)

    result = apply_zusd_monetary_ops(
        config=config,
        state=_state(),
        zusd_state=monetary,
        operations=[],
        tx_sender_pubkey=SENDER,
        block_timestamp=15,
        execution_clock=None,
    )

    assert result.ok is False
    assert result.error == "verified execution clock is required"
    assert result.zusd_state is None
    assert monetary.core.now_epoch == 0


def test_consensus_height_advances_epoch_even_without_user_operations() -> None:
    config = _config()
    monetary = init_monetary_state(config)
    clock = _clock(height=15)

    result = apply_zusd_monetary_ops(
        config=config,
        state=_state(),
        zusd_state=monetary,
        operations=[],
        tx_sender_pubkey=SENDER,
        block_timestamp=clock.height,
        execution_clock=clock,
    )

    assert result.ok is True, result.error
    assert result.zusd_state is not None
    assert result.zusd_state.core.now_epoch == 8
    assert monetary.core.now_epoch == 0
    assert result.effects == ()


def test_public_advance_epoch_is_rejected_without_mutating_prestate() -> None:
    config = _config()
    monetary = init_monetary_state(config)
    state = _state()
    clock = _clock(height=10)

    result = apply_zusd_monetary_ops(
        config=config,
        state=state,
        zusd_state=monetary,
        operations=[{"action": "advance_epoch", "delta": 1, "nonce": 1}],
        tx_sender_pubkey=SENDER,
        block_timestamp=clock.height,
        execution_clock=clock,
    )

    assert result.ok is False
    assert result.error == "zusd op[0] action unsupported: 'advance_epoch'"
    assert result.state is None
    assert result.zusd_state is None
    assert state.nonces.get_all() == {}
    assert monetary.core.now_epoch == 0


def test_raw_timestamp_cannot_disagree_with_verified_height() -> None:
    config = _config()
    clock = _clock(height=10)

    result = apply_zusd_monetary_ops(
        config=config,
        state=_state(),
        zusd_state=init_monetary_state(config),
        operations=[],
        tx_sender_pubkey=SENDER,
        block_timestamp=11,
        execution_clock=clock,
    )

    assert result.ok is False
    assert result.error == "block_timestamp must equal verified consensus height"


@pytest.mark.parametrize("legacy_height", [True, "10", 10.0])
def test_raw_timestamp_compatibility_field_rejects_noncanonical_integer_types(
    legacy_height: object,
) -> None:
    config = _config()
    clock = _clock(height=10)

    result = apply_zusd_monetary_ops(
        config=config,
        state=_state(),
        zusd_state=init_monetary_state(config),
        operations=[],
        tx_sender_pubkey=SENDER,
        block_timestamp=legacy_height,  # type: ignore[arg-type]
        execution_clock=clock,
    )

    assert result.ok is False
    assert result.error == "block_timestamp must be an int"


def test_height_deadline_remains_representable_above_u32_boundary() -> None:
    config = _config()
    height = 1 << 32
    clock = _clock(height=height)

    result = apply_zusd_monetary_ops(
        config=config,
        state=_state(),
        zusd_state=init_monetary_state(config),
        operations=[
            {
                "action": "bootstrap_oracle",
                "price_e8": 100_000_000,
                "nonce": 1,
                "deadline": U64_MAX,
            }
        ],
        tx_sender_pubkey=SENDER,
        block_timestamp=height,
        execution_clock=clock,
    )

    assert result.ok is True, result.error
    assert result.zusd_state is not None
    assert result.zusd_state.core.now_epoch == clock.derived_epoch


@pytest.mark.parametrize("deadline", [True, U64_MAX + 1])
def test_height_deadline_rejects_bool_and_u64_overflow(deadline: object) -> None:
    config = _config()
    clock = _clock(height=10)
    monetary = init_monetary_state(config)

    result = apply_zusd_monetary_ops(
        config=config,
        state=_state(),
        zusd_state=monetary,
        operations=[
            {
                "action": "bootstrap_oracle",
                "price_e8": 100_000_000,
                "nonce": 1,
                "deadline": deadline,
            }
        ],
        tx_sender_pubkey=SENDER,
        block_timestamp=clock.height,
        execution_clock=clock,
    )

    assert result.ok is False
    assert result.state is None
    assert result.zusd_state is None
    assert monetary.core.now_epoch == 0

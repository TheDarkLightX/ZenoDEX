from __future__ import annotations

from typing import cast

import pytest

from src.core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
from src.core.perp_epoch import perp_epoch_isolated_default_apply
from src.core.perps import (
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpMarketState,
    PerpsState,
)
from src.state.perps_liquidation_transitions import (
    IsolatedPartialLiquidationTransitionOkV1,
    apply_isolated_partial_liquidate_v1,
)
from src.state.perps_state_transitions import (
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
)
from src.state.state_snapshot_values import (
    CommittedPerpAccountStateV1,
    CommittedPerpMarketStateV1,
)
from src.state.state_snapshots import snapshot_perps

_ALICE = "0x" + "11" * 48
_BOB = "0x" + "22" * 48


def _global(
    *,
    now_epoch: int = 1,
    oracle_last_update_epoch: int = 0,
    min_notional_for_bounty: int = 200,
) -> dict[str, int | bool]:
    return {
        "now_epoch": now_epoch,
        "epoch_phase": 0,
        "breaker_active": False,
        "breaker_last_trigger_epoch": 0,
        "clearing_price_seen": False,
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
        "mark_price_source_kind": MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
        "oracle_seen": True,
        "oracle_last_update_epoch": oracle_last_update_epoch,
        "index_price_e8": 100_000_000,
        "max_oracle_staleness_epochs": 2,
        "max_oracle_move_bps": 500,
        "initial_margin_bps": 1_000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 50,
        "max_position_abs": 1_000_000,
        "fee_pool_quote": 10,
        "funding_rate_bps": 0,
        "funding_cap_bps": 100,
        "insurance_balance": 110,
        "initial_insurance": 100,
        "fee_income": 10,
        "claims_paid": 0,
        "min_notional_for_bounty": min_notional_for_bounty,
    }


def _legacy_account(
    *,
    position_base: int = 1_000_000,
    collateral_quote: int = 50_000,
) -> PerpAccountState:
    return PerpAccountState(
        position_base=position_base,
        entry_price_e8=100_000_000,
        collateral_quote=collateral_quote,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )


def _exact_market(
    account: PerpAccountState,
    *,
    global_state: dict[str, int | bool] | None = None,
) -> CommittedPerpMarketStateV1:
    committed = snapshot_perps(
        PerpsState(
            version=PERPS_STATE_VERSION_V5,
            markets={
                "perp:test": PerpMarketState(
                    quote_asset="zUSD",
                    global_state=_global() if global_state is None else global_state,
                    accounts={_ALICE: account},
                )
            },
        )
    )
    assert committed is not None
    market = committed.get_market("perp:test")
    assert type(market) is CommittedPerpMarketStateV1
    return market


def _kernel_state(
    market: CommittedPerpMarketStateV1,
    account: CommittedPerpAccountStateV1,
) -> dict[str, int | bool]:
    return {
        **dict(market.global_entries),
        "position_base": account.position_base,
        "entry_price_e8": account.entry_price_e8,
        "collateral_quote": account.collateral_quote,
        "funding_paid_cumulative": account.funding_paid_cumulative,
        "funding_last_applied_epoch": account.funding_last_applied_epoch,
        "liquidated_this_step": account.liquidated_this_step,
    }


@pytest.mark.parametrize("position_base", (1_000_000, -1_000_000))
def test_partial_liquidation_matches_kernel_and_freezes_one_combined_candidate(
    position_base: int,
) -> None:
    pre = _exact_market(_legacy_account(position_base=position_base))
    pre_account = pre.get_account(_ALICE)
    assert pre_account is not None
    reference = perp_epoch_isolated_default_apply(
        state=_kernel_state(pre, pre_account),
        action="partial_liquidate",
        params={"fraction_bps": 0, "auth_ok": True},
    )
    assert reference.ok is True
    assert reference.state is not None

    result = apply_isolated_partial_liquidate_v1(
        pre,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
    )

    assert type(result) is IsolatedPartialLiquidationTransitionOkV1
    post_account = result.market.get_account(_ALICE)
    assert post_account is not None
    for field in (
        "position_base",
        "entry_price_e8",
        "collateral_quote",
        "funding_paid_cumulative",
        "funding_last_applied_epoch",
        "liquidated_this_step",
    ):
        assert getattr(post_account, field) == reference.state[field]
    for field, value in result.market.global_entries:
        expected = (
            MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
            if field == "mark_price_source_kind"
            else reference.state[field]
        )
        assert value == expected

    assert result.account_patch.writes[0].expected is pre_account
    assert result.account_patch.writes[0].replacement is post_account
    assert result.global_patch is not None
    assert tuple(write.field for write in result.global_patch.writes) == (
        "fee_income",
        "fee_pool_quote",
        "insurance_balance",
    )
    assert pre.get_account(_ALICE) is pre_account
    assert pre.global_value("fee_pool_quote") == 10


def test_combined_patches_replay_to_the_exact_candidate() -> None:
    pre = _exact_market(_legacy_account())
    result = apply_isolated_partial_liquidate_v1(
        pre,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        fraction_bps=5_000,
    )

    assert type(result) is IsolatedPartialLiquidationTransitionOkV1
    replayed_globals = dict(pre.global_entries)
    assert result.global_patch is not None
    for global_write in result.global_patch.writes:
        assert replayed_globals[global_write.field] == global_write.expected
        replayed_globals[global_write.field] = global_write.replacement
    assert replayed_globals == dict(result.market.global_entries)

    replayed_accounts = dict(pre.account_entries)
    for account_write in result.account_patch.writes:
        assert replayed_accounts.get(account_write.account_pubkey) is account_write.expected
        replayed_accounts[account_write.account_pubkey] = account_write.replacement
    assert tuple(sorted(replayed_accounts.items())) == result.market.account_entries


def test_zero_penalty_liquidation_reuses_globals_inside_combined_candidate() -> None:
    pre = _exact_market(
        _legacy_account(),
        global_state=_global(min_notional_for_bounty=100_000_000),
    )

    result = apply_isolated_partial_liquidate_v1(
        pre,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        fraction_bps=10_000,
    )

    assert type(result) is IsolatedPartialLiquidationTransitionOkV1
    assert result.global_patch is None
    assert result.market.global_entries == pre.global_entries
    post_account = result.market.get_account(_ALICE)
    assert post_account is not None
    assert post_account.position_base == 0


def test_sender_binding_precedes_fraction_typing_and_returns_no_candidate() -> None:
    pre = _exact_market(_legacy_account())

    result = apply_isolated_partial_liquidate_v1(
        pre,
        account_pubkey=_ALICE,
        sender_pubkey=_BOB,
        fraction_bps=cast(int, True),
    )

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
        ("gate",),
        "SenderBindingInvalid",
    )
    assert not hasattr(result, "market")


def test_fraction_domain_and_healthy_account_reject_without_partial_output() -> None:
    underwater = _exact_market(_legacy_account())
    healthy = _exact_market(_legacy_account(collateral_quote=100_000))

    wrong_type = apply_isolated_partial_liquidate_v1(
        underwater,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        fraction_bps=cast(int, True),
    )
    out_of_domain = apply_isolated_partial_liquidate_v1(
        underwater,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        fraction_bps=10_001,
    )
    not_liquidatable = apply_isolated_partial_liquidate_v1(
        healthy,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        fraction_bps=10_000,
    )

    assert wrong_type == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
        ("fraction_bps",),
    )
    assert out_of_domain == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
        ("kernel",),
        "param_domain:fraction_bps",
    )
    assert not_liquidatable == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
        ("kernel",),
        "guard",
    )
    for rejected in (wrong_type, out_of_domain, not_liquidatable):
        assert not hasattr(rejected, "market")


def test_stale_oracle_and_corrupted_prestate_fail_closed() -> None:
    stale = _exact_market(
        _legacy_account(),
        global_state=_global(now_epoch=3, oracle_last_update_epoch=0),
    )
    stale_result = apply_isolated_partial_liquidate_v1(
        stale,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        fraction_bps=10_000,
    )
    object.__setattr__(stale.accounts, "_schema_id", "corrupted")
    corrupted_result = apply_isolated_partial_liquidate_v1(
        stale,
        account_pubkey=_ALICE,
        sender_pubkey=_BOB,
        fraction_bps=cast(int, True),
    )

    assert stale_result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
        ("kernel",),
        "guard",
    )
    assert corrupted_result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.INVALID_PRESTATE,
        ("state",),
    )

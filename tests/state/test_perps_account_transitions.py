from __future__ import annotations

from typing import cast

from src.core.domain_limits import PERP_POSITION_MAX
from src.core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
from src.core.perp_epoch import perp_epoch_isolated_default_apply
from src.core.perps import (
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpMarketState,
    PerpsState,
)
from src.state.perps_account_transitions import (
    CanonicalIsolatedAccountPatchV1,
    IsolatedAccountTransitionOkV1,
    apply_isolated_set_position_v1,
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


def _global() -> dict[str, int | bool]:
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


def _legacy_account(*, collateral_quote: int = 1_000_000) -> PerpAccountState:
    return PerpAccountState(
        position_base=0,
        entry_price_e8=0,
        collateral_quote=collateral_quote,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )


def _exact_market(
    accounts: dict[str, PerpAccountState],
) -> CommittedPerpMarketStateV1:
    source = PerpsState(
        version=PERPS_STATE_VERSION_V5,
        markets={
            "perp:test": PerpMarketState(
                quote_asset="zUSD",
                global_state=_global(),
                accounts=accounts,
            )
        },
    )
    committed = snapshot_perps(source)
    assert committed is not None
    market = committed.get_market("perp:test")
    assert type(market) is CommittedPerpMarketStateV1
    return market


def _kernel_account(
    pre: CommittedPerpMarketStateV1,
    account: CommittedPerpAccountStateV1,
    *,
    new_position_base: int,
) -> dict[str, int | bool]:
    state = {
        **dict(pre.global_entries),
        "position_base": account.position_base,
        "entry_price_e8": account.entry_price_e8,
        "collateral_quote": account.collateral_quote,
        "funding_paid_cumulative": account.funding_paid_cumulative,
        "funding_last_applied_epoch": account.funding_last_applied_epoch,
        "liquidated_this_step": account.liquidated_this_step,
    }
    result = perp_epoch_isolated_default_apply(
        state=state,
        action="set_position",
        params={"new_position_base": new_position_base, "auth_ok": True},
    )
    assert result.ok is True
    assert result.state is not None
    return {
        key: result.state[key]
        for key in (
            "position_base",
            "entry_price_e8",
            "collateral_quote",
            "funding_paid_cumulative",
            "funding_last_applied_epoch",
            "liquidated_this_step",
        )
    }


def test_set_position_matches_kernel_and_returns_one_account_patch() -> None:
    pre = _exact_market({_ALICE: _legacy_account()})
    pre_account = pre.get_account(_ALICE)
    assert pre_account is not None

    result = apply_isolated_set_position_v1(
        pre,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        new_position_base=500,
    )

    assert type(result) is IsolatedAccountTransitionOkV1
    assert result.market.global_state is pre.global_state
    assert type(result.account_patch) is CanonicalIsolatedAccountPatchV1
    assert len(result.account_patch.writes) == 1
    write = result.account_patch.writes[0]
    assert write.account_pubkey == _ALICE
    assert write.expected is pre_account
    assert write.replacement is result.market.get_account(_ALICE)
    expected = _kernel_account(pre, pre_account, new_position_base=500)
    post_account = result.market.get_account(_ALICE)
    assert post_account is not None
    assert {field: getattr(post_account, field) for field in expected} == expected


def test_set_position_inserts_an_absent_flat_account_canonically() -> None:
    pre = _exact_market({})

    result = apply_isolated_set_position_v1(
        pre,
        account_pubkey=_BOB,
        sender_pubkey=_BOB,
        new_position_base=0,
    )

    assert type(result) is IsolatedAccountTransitionOkV1
    assert result.account_patch is not None
    assert result.account_patch.writes[0].expected is None
    assert tuple(key for key, _account in result.market.account_entries) == (_BOB,)


def test_set_position_semantic_noop_reuses_the_exact_prestate() -> None:
    pre = _exact_market({_ALICE: _legacy_account()})

    result = apply_isolated_set_position_v1(
        pre,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        new_position_base=0,
    )

    assert result == IsolatedAccountTransitionOkV1(pre, None)
    assert result.market is pre


def test_sender_binding_precedes_position_parameter_validation() -> None:
    pre = _exact_market({_ALICE: _legacy_account()})

    result = apply_isolated_set_position_v1(
        pre,
        account_pubkey=_ALICE,
        sender_pubkey=_BOB,
        new_position_base=cast(int, True),
    )

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
        ("gate",),
        "SenderBindingInvalid",
    )
    assert not hasattr(result, "market")


def test_noncanonical_authority_keys_reject_without_candidate() -> None:
    pre = _exact_market({_ALICE: _legacy_account()})

    account_result = apply_isolated_set_position_v1(
        pre,
        account_pubkey=_ALICE.upper(),
        sender_pubkey=_ALICE,
        new_position_base=0,
    )
    sender_result = apply_isolated_set_position_v1(
        pre,
        account_pubkey=_ALICE,
        sender_pubkey="alice",
        new_position_base=0,
    )

    assert account_result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.NONCANONICAL_ACCOUNT,
        ("account_pubkey",),
    )
    assert sender_result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.NONCANONICAL_ACCOUNT,
        ("sender_pubkey",),
    )


def test_position_domain_and_margin_rejections_are_kernel_typed() -> None:
    funded = _exact_market({_ALICE: _legacy_account()})
    empty = _exact_market({_ALICE: _legacy_account(collateral_quote=0)})

    out_of_domain = apply_isolated_set_position_v1(
        funded,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        new_position_base=PERP_POSITION_MAX + 1,
    )
    below_margin = apply_isolated_set_position_v1(
        empty,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        new_position_base=500,
    )

    assert out_of_domain == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
        ("kernel",),
        "param_domain:new_position_base",
    )
    assert below_margin == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
        ("kernel",),
        "guard",
    )


def test_wrong_or_corrupted_prestate_rejects_before_account_work() -> None:
    wrong = apply_isolated_set_position_v1(
        cast(CommittedPerpMarketStateV1, object()),
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        new_position_base=0,
    )
    pre = _exact_market({_ALICE: _legacy_account()})
    object.__setattr__(pre.accounts, "_schema_id", "corrupted")
    corrupted = apply_isolated_set_position_v1(
        pre,
        account_pubkey=_ALICE,
        sender_pubkey=_ALICE,
        new_position_base=0,
    )

    assert wrong == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
        ("state",),
    )
    assert corrupted == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.INVALID_PRESTATE,
        ("state",),
    )

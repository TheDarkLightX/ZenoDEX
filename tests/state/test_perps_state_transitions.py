from __future__ import annotations

from typing import cast

import pytest

import src.core.perps as perps_module
from src.core.domain_limits import PERP_ADVANCE_EPOCH_DELTA_MAX
from src.core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
from src.core.perp_epoch import perp_epoch_isolated_default_apply
from src.core.perps import (
    PERP_ACCOUNT_KEYS,
    PERP_GLOBAL_KEYS,
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpMarketState,
    PerpsState,
)
from src.state.perps_state_transitions import (
    IsolatedGlobalWriteV1,
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionOkV1,
    IsolatedPerpTransitionRejectV1,
    apply_isolated_advance_epoch_v1,
    apply_isolated_clear_breaker_v1,
    apply_isolated_publish_clearing_price_v1,
)
from src.state.state_snapshot_schema import ISOLATED_GLOBAL_FIELD_NAMES_V1
from src.state.state_snapshot_values import CommittedPerpMarketStateV1
from src.state.state_snapshots import snapshot_perps

_ACCOUNT = "0x" + "11" * 48


def _global(
    *,
    phase: int = 0,
    now_epoch: int = 1,
    settled: bool = False,
    breaker_active: bool = False,
) -> dict[str, int | bool]:
    clearing_seen = phase in {1, 2}
    oracle_seen = True
    return {
        "now_epoch": now_epoch,
        "epoch_phase": phase,
        "breaker_active": breaker_active,
        "breaker_last_trigger_epoch": now_epoch if breaker_active else 0,
        "clearing_price_seen": clearing_seen,
        "clearing_price_epoch": now_epoch if clearing_seen else 0,
        "clearing_price_e8": 105_000_000 if clearing_seen else 0,
        "mark_price_source_kind": MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
        "oracle_seen": oracle_seen,
        "oracle_last_update_epoch": now_epoch if settled else 0,
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


def _exact_market(
    global_state: dict[str, int | bool],
    *,
    accounts: dict[str, PerpAccountState] | None = None,
) -> CommittedPerpMarketStateV1:
    legacy = PerpsState(
        version=PERPS_STATE_VERSION_V5,
        markets={
            "perp:test": PerpMarketState(
                quote_asset="zUSD",
                global_state=global_state,
                accounts={} if accounts is None else accounts,
            )
        },
    )
    committed = snapshot_perps(legacy)
    assert committed is not None
    market = committed.get_market("perp:test")
    assert type(market) is CommittedPerpMarketStateV1
    return market


def _flat_kernel_account() -> dict[str, int | bool]:
    return {
        "position_base": 0,
        "entry_price_e8": 0,
        "collateral_quote": 0,
        "funding_paid_cumulative": 0,
        "funding_last_applied_epoch": 0,
        "liquidated_this_step": False,
    }


def _reference_market(
    pre: CommittedPerpMarketStateV1,
    *,
    action: str,
    params: dict[str, int | bool],
    mark_price_source_kind: int,
) -> CommittedPerpMarketStateV1:
    state = {**dict(pre.global_entries), **_flat_kernel_account()}
    result = perp_epoch_isolated_default_apply(state=state, action=action, params=params)
    assert result.ok is True
    assert result.state is not None
    post_global = {
        key: (mark_price_source_kind if key == "mark_price_source_kind" else result.state[key])
        for key in sorted(PERP_GLOBAL_KEYS)
    }
    return _exact_market(post_global)


def _assert_patch_replays(
    result: IsolatedPerpTransitionOkV1,
    pre: CommittedPerpMarketStateV1,
) -> None:
    replayed = dict(pre.global_entries)
    assert tuple(write.field for write in result.patch.writes) == tuple(
        sorted(write.field for write in result.patch.writes)
    )
    for write in result.patch.writes:
        assert replayed[write.field] == write.expected
        replayed[write.field] = write.replacement
    assert replayed == dict(result.market.global_entries)
    assert result.market.accounts is pre.accounts


def test_global_write_registry_is_detached_from_mutable_legacy_key_set() -> None:
    attacker_field = "attacker_controlled_field"
    legacy_keys = perps_module.PERP_ISOLATED_GLOBAL_KEYS
    legacy_keys.add(attacker_field)
    try:
        assert attacker_field not in ISOLATED_GLOBAL_FIELD_NAMES_V1
        with pytest.raises(ValueError, match="field is not declared"):
            IsolatedGlobalWriteV1(attacker_field, 0, 1)
    finally:
        legacy_keys.discard(attacker_field)


def test_advance_epoch_matches_the_mounted_kernel_and_returns_one_patch() -> None:
    pre = _exact_market(_global(phase=2, settled=True))

    result = apply_isolated_advance_epoch_v1(
        pre,
        delta=1,
        operator_authorized=True,
    )

    assert type(result) is IsolatedPerpTransitionOkV1
    expected = _reference_market(
        pre,
        action="advance_epoch",
        params={"delta": 1},
        mark_price_source_kind=MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
    )
    assert result.market == expected
    _assert_patch_replays(result, pre)


def test_publish_price_matches_kernel_and_binds_mark_source_in_same_candidate() -> None:
    pre = _exact_market(_global())

    result = apply_isolated_publish_clearing_price_v1(
        pre,
        price_e8=105_000_000,
        mark_price_source_kind=MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
        operator_authorized=True,
    )

    assert type(result) is IsolatedPerpTransitionOkV1
    expected = _reference_market(
        pre,
        action="publish_clearing_price",
        params={"price_e8": 105_000_000},
        mark_price_source_kind=MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
    )
    assert result.market == expected
    assert result.market.global_value("epoch_phase") == 1
    assert result.market.global_value("mark_price_source_kind") == (
        MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
    )
    _assert_patch_replays(result, pre)


def test_clear_breaker_matches_kernel_and_preserves_account_table() -> None:
    pre = _exact_market(_global(breaker_active=True))

    result = apply_isolated_clear_breaker_v1(pre, operator_authorized=True)

    assert type(result) is IsolatedPerpTransitionOkV1
    expected = _reference_market(
        pre,
        action="clear_breaker",
        params={"auth_ok": True},
        mark_price_source_kind=MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
    )
    assert result.market == expected
    assert result.market.global_value("breaker_active") is False
    assert result.market.global_value("breaker_last_trigger_epoch") == 0
    _assert_patch_replays(result, pre)


@pytest.mark.parametrize(
    ("call", "reason"),
    (
        (
            lambda market: apply_isolated_advance_epoch_v1(
                market,
                delta=1,
                operator_authorized=False,
            ),
            "OperatorOnly",
        ),
        (
            lambda market: apply_isolated_advance_epoch_v1(
                market,
                delta=1,
                operator_authorized=True,
            ),
            "EpochNotSettled",
        ),
        (
            lambda market: apply_isolated_publish_clearing_price_v1(
                market,
                price_e8=0,
                mark_price_source_kind=MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
                operator_authorized=True,
            ),
            "PriceInvalid",
        ),
    ),
)
def test_runtime_gate_rejections_return_no_candidate(call: object, reason: str) -> None:
    pre = _exact_market(_global())
    result = call(pre)  # type: ignore[operator]

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
        ("gate",),
        reason,
    )
    assert not hasattr(result, "market")


def test_exact_parameter_and_kernel_rejections_are_typed_no_output() -> None:
    settled = _exact_market(_global(phase=2, settled=True))

    wrong_type = apply_isolated_advance_epoch_v1(
        settled,
        delta=cast(int, True),
        operator_authorized=True,
    )
    out_of_domain = apply_isolated_advance_epoch_v1(
        settled,
        delta=PERP_ADVANCE_EPOCH_DELTA_MAX + 1,
        operator_authorized=True,
    )

    assert wrong_type == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
        ("delta",),
    )
    assert out_of_domain == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
        ("kernel",),
        "param_domain:delta",
    )
    assert not hasattr(wrong_type, "market")
    assert not hasattr(out_of_domain, "market")


def test_publish_rejects_an_unsafe_mark_source_without_candidate() -> None:
    pre = _exact_market(_global())

    result = apply_isolated_publish_clearing_price_v1(
        pre,
        price_e8=105_000_000,
        mark_price_source_kind=0,
        operator_authorized=True,
    )

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.MARK_PRICE_SOURCE,
        ("mark_price_source_kind",),
    )
    assert not hasattr(result, "market")


def test_publish_preserves_operator_first_rejection_precedence() -> None:
    pre = _exact_market(_global())

    result = apply_isolated_publish_clearing_price_v1(
        pre,
        price_e8=cast(int, True),
        mark_price_source_kind=0,
        operator_authorized=False,
    )

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
        ("gate",),
        "OperatorOnly",
    )


def test_publish_preserves_mark_source_before_price_rejection_precedence() -> None:
    pre = _exact_market(_global())

    result = apply_isolated_publish_clearing_price_v1(
        pre,
        price_e8=0,
        mark_price_source_kind=0,
        operator_authorized=True,
    )

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.MARK_PRICE_SOURCE,
        ("mark_price_source_kind",),
    )


def test_clear_breaker_rejects_open_positions_before_kernel_evaluation() -> None:
    account = PerpAccountState(
        position_base=5,
        entry_price_e8=100_000_000,
        collateral_quote=1_000,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )
    pre = _exact_market(
        _global(breaker_active=True),
        accounts={_ACCOUNT: account},
    )

    result = apply_isolated_clear_breaker_v1(pre, operator_authorized=True)

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
        ("gate",),
        "PositionsOpen",
    )


def test_corrupted_or_wrong_prestate_rejects_before_transition_work() -> None:
    wrong = apply_isolated_clear_breaker_v1(
        cast(CommittedPerpMarketStateV1, object()),
        operator_authorized=True,
    )
    pre = _exact_market(_global(breaker_active=True))
    object.__setattr__(pre.global_state, "_schema_id", "corrupted")
    corrupted = apply_isolated_clear_breaker_v1(pre, operator_authorized=True)

    assert wrong == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
        ("state",),
    )
    assert corrupted == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.INVALID_PRESTATE,
        ("state",),
    )


def test_kernel_reference_uses_only_the_declared_account_fields() -> None:
    assert set(_flat_kernel_account()) == PERP_ACCOUNT_KEYS

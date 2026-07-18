from __future__ import annotations

from dataclasses import replace

from src.core.dex import DexState
from src.core.generic_token_authority import (
    U32_MAX,
    GenericTokenAssetAuthority,
    GenericTokenAuthorityState,
)
from src.integration.generic_token_accounting import (
    GenericTokenAccountingRejectCode,
    evaluate_generic_token_accounting,
)
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    init_monetary_state,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

ASSET_A = "0x" + "11" * 32
ASSET_B = "0x" + "22" * 32
ZUSD = "0x" + "99" * 32
ACTOR = "0x" + "aa" * 48
ALICE = "0x" + "01" * 48


def _authority(*, supply: int) -> GenericTokenAuthorityState:
    return GenericTokenAuthorityState(
        assets=(GenericTokenAssetAuthority(ASSET_A, supply, ACTOR),)
    )


def _state(*, wallet_units: int, pool_units: int = 0) -> DexState:
    balances = BalanceTable()
    balances.set(ALICE, ASSET_A, wallet_units)
    pools = {}
    if pool_units:
        pool = PoolState(
            pool_id="pool-a-b",
            asset0=ASSET_A,
            asset1=ZUSD,
            reserve0=pool_units,
            reserve1=1,
            fee_bps=30,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=1,
        )
        pools[pool.pool_id] = pool
    return DexState(balances=balances, pools=pools, lp_balances=LPTable())


def _monetary_state():
    return init_monetary_state(ZUSDMonetaryConfig(asset_id=ZUSD))


def test_projection_sums_wallet_and_pool_locations_exactly_once() -> None:
    decision = evaluate_generic_token_accounting(
        authority_state=_authority(supply=10),
        dex_state=_state(wallet_units=4, pool_units=6),
        monetary_state=_monetary_state(),
        canonical_zusd_asset=ZUSD,
    )

    assert decision.accepted is True
    assert decision.projection is not None
    accounted = decision.projection.get_asset(ASSET_A)
    assert accounted is not None
    assert accounted.wallet_units == 4
    assert accounted.pool_locked_units == 6
    assert accounted.total_units == 10


def test_existing_u32_max_units_cannot_be_hidden_by_an_empty_authority() -> None:
    decision = evaluate_generic_token_accounting(
        authority_state=GenericTokenAuthorityState(),
        dex_state=_state(wallet_units=U32_MAX),
        monetary_state=_monetary_state(),
        canonical_zusd_asset=ZUSD,
    )

    assert decision.accepted is False
    assert decision.violation is not None
    assert (
        decision.violation.code
        is GenericTokenAccountingRejectCode.UNREGISTERED_ACCOUNTED_ASSET
    )


def test_supply_mismatch_and_accounted_overflow_are_distinct() -> None:
    mismatch = evaluate_generic_token_accounting(
        authority_state=_authority(supply=2),
        dex_state=_state(wallet_units=1),
        monetary_state=_monetary_state(),
        canonical_zusd_asset=ZUSD,
    )
    overflow = evaluate_generic_token_accounting(
        authority_state=_authority(supply=U32_MAX),
        dex_state=_state(wallet_units=U32_MAX, pool_units=1),
        monetary_state=_monetary_state(),
        canonical_zusd_asset=ZUSD,
    )

    assert mismatch.violation is not None
    assert mismatch.violation.code is GenericTokenAccountingRejectCode.SUPPLY_ACCOUNTING_MISMATCH
    assert overflow.violation is not None
    assert overflow.violation.code is GenericTokenAccountingRejectCode.ACCOUNTED_UNITS_OVERFLOW


def test_canonical_zusd_cannot_be_registered_as_a_generic_asset() -> None:
    authority = GenericTokenAuthorityState(
        assets=(GenericTokenAssetAuthority(ZUSD, 0, ACTOR),)
    )
    decision = evaluate_generic_token_accounting(
        authority_state=authority,
        dex_state=_state(wallet_units=0),
        monetary_state=_monetary_state(),
        canonical_zusd_asset=ZUSD,
    )

    assert decision.violation is not None
    assert decision.violation.code is GenericTokenAccountingRejectCode.CANONICAL_ZUSD_REGISTERED


def test_unused_configured_stake_asset_does_not_require_registration() -> None:
    monetary = init_monetary_state(
        ZUSDMonetaryConfig(
            asset_id=ZUSD,
            fee_stake_asset_id=ASSET_A,
        )
    )

    decision = evaluate_generic_token_accounting(
        authority_state=GenericTokenAuthorityState(),
        dex_state=_state(wallet_units=0),
        monetary_state=monetary,
        canonical_zusd_asset=ZUSD,
    )

    assert decision.accepted is True
    assert decision.projection is not None
    assert decision.projection.assets == ()


def test_projection_sums_active_and_pending_fee_stakes_exactly_once() -> None:
    monetary = init_monetary_state(
        ZUSDMonetaryConfig(
            asset_id=ZUSD,
            fee_stake_asset_id=ASSET_A,
        )
    )
    monetary = replace(
        monetary,
        active_fee_stakes={ALICE: 2},
        pending_fee_stakes={ACTOR: 3},
        pending_fee_stake_activation_epochs={ACTOR: 1},
    )

    decision = evaluate_generic_token_accounting(
        authority_state=_authority(supply=5),
        dex_state=_state(wallet_units=0),
        monetary_state=monetary,
        canonical_zusd_asset=ZUSD,
    )

    assert decision.accepted is True
    assert decision.projection is not None
    accounted = decision.projection.get_asset(ASSET_A)
    assert accounted is not None
    assert accounted.stake_locked_units == 5
    assert accounted.total_units == 5


def test_nonzero_fee_stakes_require_explicit_stake_asset() -> None:
    monetary = replace(
        _monetary_state(),
        active_fee_stakes={ALICE: 1},
    )

    decision = evaluate_generic_token_accounting(
        authority_state=GenericTokenAuthorityState(),
        dex_state=_state(wallet_units=0),
        monetary_state=monetary,
        canonical_zusd_asset=ZUSD,
    )

    assert decision.violation is not None
    assert decision.violation.code is GenericTokenAccountingRejectCode.STAKE_ASSET_MISSING

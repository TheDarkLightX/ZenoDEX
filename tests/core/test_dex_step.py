# [TESTER] v1

from __future__ import annotations

from src.core import DexConfig, DexState, FeeSplitParams, dex_step
from src.core.liquidity import create_pool
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _dex_step_intents(
    *,
    pk: str,
    pool_id: str,
    asset0: str,
    asset1: str,
    include_nonces: bool,
) -> list[Intent]:
    def fields(base: dict[str, object], nonce: int) -> dict[str, object]:
        if include_nonces:
            return {**base, "nonce": nonce}
        return base

    return [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id=_iid(1),
            sender_pubkey=pk,
            deadline=9999999999,
            fields=fields(
                {
                    "asset0": asset0,
                    "asset1": asset1,
                    "fee_bps": 30,
                    "amount0": 2_000_000,
                    "amount1": 2_000_000,
                },
                1,
            ),
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(2),
            sender_pubkey=pk,
            deadline=9999999999,
            fields=fields(
                {
                    "pool_id": pool_id,
                    "asset_in": asset0,
                    "asset_out": asset1,
                    "amount_in": 1000,
                    "min_amount_out": 1,
                },
                2,
            ),
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_OUT,
            intent_id=_iid(5),
            sender_pubkey=pk,
            deadline=9999999999,
            fields=fields(
                {
                    "pool_id": pool_id,
                    "asset_in": asset1,
                    "asset_out": asset0,
                    "amount_out": 500,
                    "max_amount_in": 10_000_000,
                },
                3,
            ),
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.ADD_LIQUIDITY,
            intent_id=_iid(3),
            sender_pubkey=pk,
            deadline=9999999999,
            fields=fields(
                {
                    "pool_id": pool_id,
                    "amount0_desired": 100_000,
                    "amount1_desired": 100_000,
                    "amount0_min": 0,
                    "amount1_min": 0,
                },
                4,
            ),
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.REMOVE_LIQUIDITY,
            intent_id=_iid(4),
            sender_pubkey=pk,
            deadline=9999999999,
            fields=fields(
                {
                    "pool_id": pool_id,
                    "lp_amount": 1000,
                    "amount0_min": 0,
                    "amount1_min": 0,
                },
                5,
            ),
        ),
    ]


def test_dex_step_end_to_end_create_swap_lp() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    # Pool id is deterministic from (asset0, asset1, fee_bps).
    pool_id, _, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    lp_balances = LPTable()

    state = DexState(balances=balances, pools={}, lp_balances=lp_balances)
    config = DexConfig(fee_split_params=FeeSplitParams(buyback_bps=3000, treasury_bps=3000, rewards_bps=4000))

    intents = _dex_step_intents(
        pk=pk,
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        include_nonces=True,
    )

    res = dex_step(config, state, intents)
    assert res.ok, res.error
    assert res.state is not None
    assert res.effects is not None

    next_state = res.state
    settlement = res.effects["settlement"]
    assert settlement.module == "TauSwap"
    assert pool_id in next_state.pools

    # LP balances exist for the user and the lock address after pool creation.
    assert next_state.lp_balances.get(pk, pool_id) > 0
    assert next_state.lp_balances.get("0x" + "00" * 48, pool_id) > 0

    # Fee split is computed when configured.
    assert int(res.effects["total_swap_fees"]) >= 0
    assert res.effects["fee_split"] is not None


def test_dex_step_default_rejects_nonce_free_batch() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, _, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    intents = _dex_step_intents(
        pk=pk,
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        include_nonces=False,
    )

    res = dex_step(DexConfig(), state, intents)
    assert res.ok is False
    assert res.error == "Missing/invalid nonce"


def test_dex_step_legacy_config_allows_nonce_free_fixture() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, _, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())
    intents = _dex_step_intents(
        pk=pk,
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        include_nonces=False,
    )

    res = dex_step(
        DexConfig(
            require_all_nonces=False,
            allow_legacy_nonce_free_steps=True,
        ),
        state,
        intents,
    )
    assert res.ok, res.error


def test_dex_step_rejects_nonce_free_compat_without_explicit_legacy_flag() -> None:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    res = dex_step(DexConfig(require_all_nonces=False), state, [])
    assert res.ok is False
    assert res.error == "require_all_nonces=False requires allow_legacy_nonce_free_steps=True"

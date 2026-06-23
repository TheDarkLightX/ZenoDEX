# [TESTER] v1

from __future__ import annotations

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexConfig, DexState, step, step_with_candidate_settlement
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _nonce_free_create_pool_setup() -> tuple[DexState, list[Intent]]:
    sender = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    balances = BalanceTable()
    balances.set(sender, asset0, 10_000_000)
    balances.set(sender, asset1, 10_000_000)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(1),
        sender_pubkey=sender,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 30,
            "amount0": 2_000_000,
            "amount1": 2_000_000,
        },
    )
    return DexState(balances=balances, pools={}, lp_balances=LPTable()), [intent]


def _legacy_nonce_free_config() -> DexConfig:
    return DexConfig(
        require_all_nonces=False,
        allow_legacy_nonce_free_steps=True,
    )


def test_step_rejects_nonce_free_intent_by_default() -> None:
    state, intents = _nonce_free_create_pool_setup()

    result = step(DexConfig(), state, intents)

    assert not result.ok
    assert result.error == "Missing/invalid nonce"
    assert state.nonces.get_last(intents[0].sender_pubkey) == 0


def test_candidate_settlement_rejects_nonce_free_intent_by_default() -> None:
    state, intents = _nonce_free_create_pool_setup()
    candidate = compute_settlement(
        intents=intents,
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
    )

    result = step_with_candidate_settlement(
        DexConfig(),
        state,
        intents,
        candidate_settlement=candidate,
    )

    assert not result.ok
    assert result.error == "Missing/invalid nonce"
    assert state.nonces.get_last(intents[0].sender_pubkey) == 0


def test_legacy_nonce_free_compatibility_requires_explicit_dual_opt_in() -> None:
    state, intents = _nonce_free_create_pool_setup()

    ambiguous = step(DexConfig(require_all_nonces=False), state, intents)
    legacy = step(_legacy_nonce_free_config(), state, intents)

    assert not ambiguous.ok
    assert ambiguous.error == "Missing/invalid nonce"
    assert legacy.ok, legacy.error
    assert legacy.state is not None
    assert legacy.state.nonces.get_last(intents[0].sender_pubkey) == 0

from __future__ import annotations

from dataclasses import replace

import src.integration.zusd_monetary_bridge as bridge
from src.core.dex import DexState
from src.core.zusd import E8, ZUSDState, ZUSDStepResult
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    ZUSDMonetaryState,
    apply_zusd_monetary_ops,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable

ALICE = "0x" + "11" * 48


def _dex_state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())


def _fee_ready_state(*, fee_bps: int = 100) -> ZUSDMonetaryState:
    core = ZUSDState(
        oracle_seen=True,
        oracle_last_update_epoch=0,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        collateral_e8=2 * E8,
        borrow_fee_floor_bps=fee_bps,
    )
    return ZUSDMonetaryState(
        core=core,
        vault_owner_pubkey=ALICE,
        sp_deposits_e8={},
        sp_collateral_claims_e8={},
    )


def _mint_op() -> dict[str, object]:
    return {
        "module": "ZUSDFinance",
        "version": "0.1",
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount_e8": 100 * E8,
        "nonce": 1,
        "deadline": 10,
    }


def test_bridge_emits_zero_fee_supply_delta_certificate() -> None:
    result = apply_zusd_monetary_ops(
        config=ZUSDMonetaryConfig(chain_id="tau-test-supply-delta"),
        state=_dex_state(),
        zusd_state=_fee_ready_state(fee_bps=0),
        operations=[_mint_op()],
        tx_sender_pubkey=ALICE,
        block_timestamp=1,
    )

    assert result.ok is True, result.error
    assert result.zusd_state is not None
    assert result.effects is not None
    certificate = result.effects[0]["supply_delta_certificate"]
    assert certificate["debt_delta_e8"] == 100 * E8
    assert certificate["ledger_supply_delta_e8"] == 100 * E8
    assert certificate["protocol_fee_accrual_delta_e8"] == 0
    assert result.zusd_state.core.protocol_revenue_zusd_cum_e8 == 0


def test_bridge_rejects_fee_bearing_mint_until_claim_settlement_exists() -> None:
    for fee_bps in (50, 100):
        result = apply_zusd_monetary_ops(
            config=ZUSDMonetaryConfig(chain_id="tau-test-supply-delta"),
            state=_dex_state(),
            zusd_state=_fee_ready_state(fee_bps=fee_bps),
            operations=[_mint_op()],
            tx_sender_pubkey=ALICE,
            block_timestamp=1,
        )

        assert result.ok is False
        assert result.state is None
        assert result.zusd_state is None
        assert result.effects is None
        assert result.error is not None
        assert "borrowing fee claim settlement is not mounted" in result.error


def test_bridge_fails_closed_when_core_debt_omits_matching_fee_accrual(monkeypatch) -> None:
    real_step = bridge.step

    def mutated_step(state: ZUSDState, command: object) -> ZUSDStepResult:
        result = real_step(state, command)  # type: ignore[arg-type]
        if getattr(command, "tag", None) != "mint_zusd" or not result.ok or result.state is None:
            return result
        bad_state = replace(
            result.state,
            debt_e8=result.state.debt_e8 + E8,
            free_debt_e8=result.state.free_debt_e8 + E8,
        )
        return ZUSDStepResult(ok=True, state=bad_state, effects=result.effects)

    monkeypatch.setattr(bridge, "step", mutated_step)
    pre_state = _dex_state()
    result = apply_zusd_monetary_ops(
        config=ZUSDMonetaryConfig(chain_id="tau-test-supply-delta"),
        state=pre_state,
        zusd_state=_fee_ready_state(fee_bps=0),
        operations=[_mint_op()],
        tx_sender_pubkey=ALICE,
        block_timestamp=1,
    )

    assert result.ok is False
    assert result.state is None
    assert result.zusd_state is None
    assert result.effects is None
    assert result.error is not None
    assert "delta_identity_mismatch" in result.error
    assert (
        pre_state.balances.get(
            ALICE, ZUSDMonetaryConfig(chain_id="tau-test-supply-delta").zusd_asset
        )
        == 0
    )

"""
Unit tests for batch clearing algorithm.
"""

import pytest

from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus
from src.state.balances import BalanceTable
from src.core.batch_clearing import (
    compute_settlement,
    validate_settlement,
    apply_settlement,
)
from src.core.settlement import FillAction


class TestBatchClearing:
    """Test batch clearing algorithm."""
    
    def test_single_swap_intent(self):
        """Test clearing a single swap intent."""
        # Create pool
        pool_id = "0x" + "12" * 32
        pool = PoolState(
            pool_id=pool_id,
            asset0="0x" + "00" * 32,
            asset1="0x" + "11" * 32,
            reserve0=1000000,
            reserve1=1000000,
            fee_bps=30,
            lp_supply=1000000,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
        
        # Create intent
        intent = Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id="0x" + "aa" * 32,
            sender_pubkey="0x" + "bb" * 96,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": pool.asset0,
                "asset_out": pool.asset1,
                "amount_in": 10000,
                "min_amount_out": 9800,  # Realistic slippage tolerance
                "recipient": "0x" + "bb" * 96,
            },
        )
        
        # Compute settlement
        balances = BalanceTable()
        pools = {pool_id: pool}
        settlement = compute_settlement([intent], pools, balances)
        
        # Check that intent was included
        assert len(settlement.included_intents) == 1
        assert settlement.included_intents[0][0] == intent.intent_id
        
        # Check that fill exists
        assert len(settlement.fills) == 1
        fill = settlement.fills[0]
        assert fill.intent_id == intent.intent_id
        assert fill.action == FillAction.FILL
        assert fill.amount_in_filled == 10000
        assert fill.amount_out_filled is not None
        assert fill.amount_out_filled >= 9800  # Realistic expectation
    
    def test_multiple_swaps_same_pool(self):
        """Test clearing multiple swaps for the same pool."""
        pool_id = "0x" + "12" * 32
        pool = PoolState(
            pool_id=pool_id,
            asset0="0x" + "00" * 32,
            asset1="0x" + "11" * 32,
            reserve0=1000000,
            reserve1=1000000,
            fee_bps=30,
            lp_supply=1000000,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
        
        # Create multiple intents
        intents = []
        for i in range(3):
            intent = Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=f"0x{i:064x}",
                sender_pubkey="0x" + "bb" * 96,
                deadline=9999999999,
                fields={
                    "pool_id": pool_id,
                    "asset_in": pool.asset0,
                    "asset_out": pool.asset1,
                    "amount_in": 10000,
                    "min_amount_out": 9800,
                    "recipient": "0x" + "bb" * 96,
                },
            )
            intents.append(intent)
        
        # Compute settlement
        balances = BalanceTable()
        pools = {pool_id: pool}
        settlement = compute_settlement(intents, pools, balances)
        
        # All intents should be included
        assert len(settlement.included_intents) == 3
        assert len(settlement.fills) == 3
    
    def test_swap_slippage_rejection(self):
        """Test that swaps failing slippage are rejected."""
        pool_id = "0x" + "12" * 32
        pool = PoolState(
            pool_id=pool_id,
            asset0="0x" + "00" * 32,
            asset1="0x" + "11" * 32,
            reserve0=1000000,
            reserve1=1000000,
            fee_bps=30,
            lp_supply=1000000,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
        
        # Create intent with unrealistic slippage tolerance
        intent = Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id="0x" + "aa" * 32,
            sender_pubkey="0x" + "bb" * 96,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": pool.asset0,
                "asset_out": pool.asset1,
                "amount_in": 10000,
                "min_amount_out": 999999,  # Unrealistic
                "recipient": "0x" + "bb" * 96,
            },
        )
        
        # Compute settlement
        balances = BalanceTable()
        pools = {pool_id: pool}
        settlement = compute_settlement([intent], pools, balances)
        
        # Intent should be rejected
        fill = settlement.fills[0]
        assert fill.action == FillAction.REJECT
        assert "SLIPPAGE" in fill.reason


class TestSettlementValidation:
    """Test settlement validation."""
    
    def test_validate_valid_settlement(self):
        """Test validation of a valid settlement."""
        from src.core.settlement import Settlement, Fill, BalanceDelta, ReserveDelta
        
        pool_id = "0x" + "12" * 32
        pool = PoolState(
            pool_id=pool_id,
            asset0="0x" + "00" * 32,
            asset1="0x" + "11" * 32,
            reserve0=1000000,
            reserve1=1000000,
            fee_bps=30,
            lp_supply=1000000,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
        
        # Create valid settlement
        settlement = Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="test",
            included_intents=[("0x" + "aa" * 32, FillAction.FILL)],
            fills=[
                Fill(
                    intent_id="0x" + "aa" * 32,
                    action=FillAction.FILL,
                    amount_in_filled=10000,
                    amount_out_filled=9900,
                )
            ],
            balance_deltas=[
                BalanceDelta(
                    pubkey="0x" + "bb" * 96,
                    asset="0x" + "00" * 32,
                    delta_add=0,
                    delta_sub=10000,
                ),
                BalanceDelta(
                    pubkey="0x" + "bb" * 96,
                    asset="0x" + "11" * 32,
                    delta_add=9900,
                    delta_sub=0,
                ),
            ],
            reserve_deltas=[
                ReserveDelta(
                    pool_id=pool_id,
                    asset="0x" + "00" * 32,
                    delta_add=10000,
                    delta_sub=0,
                ),
                ReserveDelta(
                    pool_id=pool_id,
                    asset="0x" + "11" * 32,
                    delta_add=0,
                    delta_sub=9900,
                ),
            ],
            lp_deltas=[],
        )
        
        # Pre-state: user has enough balance
        balances = BalanceTable()
        balances.set("0x" + "bb" * 96, "0x" + "00" * 32, 20000)
        
        pools = {pool_id: pool}
        
        # Validate
        is_valid, error = validate_settlement(settlement, balances, pools)
        assert is_valid, error
    
    def test_validate_negative_balance(self):
        """Test that negative balances are rejected."""
        from src.core.settlement import Settlement, Fill, BalanceDelta
        
        settlement = Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="test",
            included_intents=[("0x" + "aa" * 32, FillAction.FILL)],
            fills=[Fill(intent_id="0x" + "aa" * 32, action=FillAction.FILL)],
            balance_deltas=[
                BalanceDelta(
                    pubkey="0x" + "bb" * 96,
                    asset="0x" + "00" * 32,
                    delta_add=0,
                    delta_sub=10000,  # Would make balance negative
                ),
            ],
            reserve_deltas=[],
            lp_deltas=[],
        )
        
        balances = BalanceTable()
        balances.set("0x" + "bb" * 96, "0x" + "00" * 32, 5000)  # Not enough
        
        pools = {}
        
        # Validate should fail
        is_valid, error = validate_settlement(settlement, balances, pools)
        assert not is_valid
        assert "Negative balance" in error


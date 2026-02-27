"""
Integration tests for end-to-end settlement.
"""

import pytest

from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus
from src.state.balances import BalanceTable
from src.core.batch_clearing import compute_settlement, validate_settlement, apply_settlement
from src.core.settlement import FillAction


class TestEndToEndSettlement:
    """Test end-to-end settlement flow."""
    
    def test_complete_swap_settlement(self):
        """Test complete swap settlement from intent to state update."""
        # Setup: Create pool
        pool_id = "0x" + "12" * 32
        asset0 = "0x" + "00" * 32
        asset1 = "0x" + "11" * 32
        
        pool = PoolState(
            pool_id=pool_id,
            asset0=asset0,
            asset1=asset1,
            reserve0=1000000,
            reserve1=1000000,
            fee_bps=30,
            lp_supply=1000000,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
        
        # Setup: User has balance
        user_pubkey = "0x" + "bb" * 96
        balances = BalanceTable()
        balances.set(user_pubkey, asset0, 50000)
        
        # Create swap intent
        intent = Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id="0x" + "aa" * 32,
            sender_pubkey=user_pubkey,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 10000,
                "min_amount_out": 9800,
                "recipient": user_pubkey,
            },
        )
        
        # Compute settlement
        pools = {pool_id: pool}
        settlement = compute_settlement([intent], pools, balances)
        
        # Validate settlement
        is_valid, error = validate_settlement(settlement, balances, pools)
        assert is_valid, error
        
        # Apply settlement
        apply_settlement(settlement, balances, pools)
        
        # Verify state updates
        # User should have less asset0, more asset1
        new_balance0 = balances.get(user_pubkey, asset0)
        new_balance1 = balances.get(user_pubkey, asset1)
        
        assert new_balance0 == 40000  # 50000 - 10000
        assert new_balance1 >= 9800  # 0 + amount_out (approximately 9871)
        
        # Pool reserves should be updated
        assert pool.reserve0 > 1000000  # Increased by amount_in
        assert pool.reserve1 < 1000000  # Decreased by amount_out
    
    def test_multiple_swaps_batch(self):
        """Test batch settlement with multiple swaps."""
        pool_id = "0x" + "12" * 32
        asset0 = "0x" + "00" * 32
        asset1 = "0x" + "11" * 32
        
        pool = PoolState(
            pool_id=pool_id,
            asset0=asset0,
            asset1=asset1,
            reserve0=1000000,
            reserve1=1000000,
            fee_bps=30,
            lp_supply=1000000,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
        
        # Create multiple intents from different users
        intents = []
        balances = BalanceTable()
        
        for i in range(3):
            user_pubkey = f"0x{i:096x}"
            balances.set(user_pubkey, asset0, 20000)
            
            intent = Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=f"0x{i:064x}",
                sender_pubkey=user_pubkey,
                deadline=9999999999,
                fields={
                    "pool_id": pool_id,
                    "asset_in": asset0,
                    "asset_out": asset1,
                    "amount_in": 5000,
                    "min_amount_out": 4800,
                    "recipient": user_pubkey,
                },
            )
            intents.append(intent)
        
        # Compute and validate settlement
        pools = {pool_id: pool}
        settlement = compute_settlement(intents, pools, balances)
        
        is_valid, error = validate_settlement(settlement, balances, pools)
        assert is_valid, error
        
        # Apply settlement
        apply_settlement(settlement, balances, pools)
        
        # Verify all users got their swaps
        for i in range(3):
            user_pubkey = f"0x{i:096x}"
            balance0 = balances.get(user_pubkey, asset0)
            balance1 = balances.get(user_pubkey, asset1)
            
            assert balance0 == 15000  # 20000 - 5000
            assert balance1 > 0  # Received asset1


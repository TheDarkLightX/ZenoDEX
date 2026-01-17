"""
Pool state management for CPMM pools.
"""

from dataclasses import dataclass
from enum import Enum
from typing import Tuple

import hashlib

from .balances import AssetId, Amount


class PoolStatus(Enum):
    """Pool status enumeration."""
    ACTIVE = "ACTIVE"
    FROZEN = "FROZEN"
    DISABLED = "DISABLED"


def compute_pool_id(
    asset0: AssetId,
    asset1: AssetId,
    fee_bps: int,
    *,
    curve_tag: str = "CPMM",
    curve_params: str = "",
) -> str:
    """
    Deterministically compute a pool_id for the given pool parameters.

    Matches the formula described in `src/core/liquidity.py`.
    """
    if asset0 >= asset1:
        raise ValueError(f"Assets must be in canonical order: {asset0} < {asset1}")
    if not (0 <= fee_bps <= 10000):
        raise ValueError(f"fee_bps must be in [0, 10000]: {fee_bps}")
    if not isinstance(curve_tag, str) or not curve_tag:
        raise ValueError("curve_tag must be a non-empty string")
    if not isinstance(curve_params, str):
        raise ValueError("curve_params must be a string")

    pool_id_data = (
        b"TauSwapPool"
        + asset0.encode("utf-8")
        + asset1.encode("utf-8")
        + str(int(fee_bps)).encode("utf-8")
        + curve_tag.encode("utf-8")
        + curve_params.encode("utf-8")
    )
    return "0x" + hashlib.sha256(pool_id_data).hexdigest()


@dataclass
class PoolState:
    """
    State of a CPMM liquidity pool.
    
    Attributes:
        pool_id: 32-byte pool identifier (hex string)
        asset0: First asset identifier (must be < asset1 lexicographically)
        asset1: Second asset identifier
        reserve0: Reserve amount for asset0
        reserve1: Reserve amount for asset1
        fee_bps: Fee in basis points (0-10000)
        lp_supply: Total LP token supply
        status: Pool status
        created_at: Block height or timestamp when pool was created
    """
    pool_id: str
    asset0: AssetId
    asset1: AssetId
    reserve0: Amount
    reserve1: Amount
    fee_bps: int
    lp_supply: Amount
    status: PoolStatus
    created_at: int
    
    def __post_init__(self):
        """Validate pool state invariants."""
        # Ensure canonical ordering
        if self.asset0 >= self.asset1:
            raise ValueError(
                f"Assets must be in canonical order: {self.asset0} < {self.asset1}"
            )
        
        # Validate fee_bps
        if not (0 <= self.fee_bps <= 10000):
            raise ValueError(f"fee_bps must be in [0, 10000]: {self.fee_bps}")
        
        # Validate non-negative reserves
        if self.reserve0 < 0 or self.reserve1 < 0:
            raise ValueError(
                f"Reserves must be non-negative: ({self.reserve0}, {self.reserve1})"
            )
        
        # Validate non-negative LP supply
        if self.lp_supply < 0:
            raise ValueError(f"LP supply must be non-negative: {self.lp_supply}")
    
    def get_reserve(self, asset: AssetId) -> Amount:
        """
        Get reserve for a specific asset.
        
        Args:
            asset: Asset identifier
            
        Returns:
            Reserve amount
            
        Raises:
            ValueError: If asset is not in this pool
        """
        if asset == self.asset0:
            return self.reserve0
        elif asset == self.asset1:
            return self.reserve1
        else:
            raise ValueError(f"Asset {asset} not in pool {self.pool_id}")
    
    def get_constant_product(self) -> int:
        """
        Compute k = reserve0 * reserve1 (CPMM constant).
        
        Returns:
            Constant product k
        """
        return self.reserve0 * self.reserve1
    
    def verify_invariant(self, min_k: int = 0) -> bool:
        """
        Verify CPMM invariant: reserve0 * reserve1 >= min_k.
        
        Args:
            min_k: Minimum allowed constant product
            
        Returns:
            True if invariant holds
        """
        k = self.get_constant_product()
        return k >= min_k
    
    def __repr__(self) -> str:
        return (
            f"PoolState(pool_id={self.pool_id[:16]}..., "
            f"assets=({self.asset0[:8]}..., {self.asset1[:8]}...), "
            f"reserves=({self.reserve0}, {self.reserve1}), "
            f"lp_supply={self.lp_supply}, status={self.status.value})"
        )

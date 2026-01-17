"""
Tau validation bridge for TauSwap operations.

This module bridges between Python operations and Tau Language validation.
In production, this would call the Tau Docker container to validate operations.
"""

from __future__ import annotations

from typing import List, Dict, Any, Tuple, Optional, TYPE_CHECKING

from ..state.intents import Intent
from ..core.settlement import Settlement
from ..state.balances import BalanceTable
from ..state.pools import PoolState
from ..state.lp import LPTable
from ..core.batch_clearing import validate_settlement, apply_settlement

if TYPE_CHECKING:
    from .tau_gate import TauGateConfig


def validate_operations(
    intents: List[Intent],
    settlement: Optional[Settlement],
    balances: BalanceTable,
    pools: Dict[str, PoolState],
    lp_balances: Optional[LPTable],
    block_timestamp: int,
    *,
    tau_gate_config: Optional["TauGateConfig"] = None,
) -> Tuple[bool, Optional[str]]:
    """
    Validate TauSwap operations using Tau Language validation.
    
    In production, this would:
    1. Serialize state and operations to Tau Language format
    2. Call Tau Docker container with validation spec
    3. Parse validation result
    
    For now, this performs Python-side validation as a placeholder.
    
    Args:
        intents: List of intents from operations["2"]
        settlement: Settlement from operations["3"] (if present)
        balances: Current balance table
        pools: Current pool states
        block_timestamp: Current block timestamp
        
    Returns:
        Tuple of (is_valid, error_message)
    """
    if settlement and not intents:
        return False, "Settlement provided without intents"

    # Check that if intents exist, settlement exists
    if intents and not settlement:
        return False, "Settlement required when intents are present"
    
    # Check that settlement covers all intents
    if settlement:
        intent_ids = {intent.intent_id for intent in intents}
        settlement_intent_ids = {
            intent_id for intent_id, _ in settlement.included_intents
        }
        
        if intent_ids != settlement_intent_ids:
            missing = intent_ids - settlement_intent_ids
            extra = settlement_intent_ids - intent_ids
            return False, (
                f"Intent coverage mismatch: missing {missing}, extra {extra}"
            )
        
        # Validate settlement
        is_valid, error = validate_settlement(settlement, balances, pools, lp_balances)
        if not is_valid:
            return False, error

        # Optional fail-closed Tau gate (swap transition checks).
        if tau_gate_config and tau_gate_config.enabled:
            try:
                from .tau_gate import validate_settlement_swaps
            except Exception as exc:
                return False, f"Tau gate unavailable: {type(exc).__name__}"
            try:
                tau_ok, tau_err = validate_settlement_swaps(
                    intents=intents,
                    settlement_fills=settlement.fills,
                    pre_pools=pools,
                    config=tau_gate_config,
                )
            except Exception as exc:
                detail = str(exc).strip()
                if detail:
                    return False, f"Tau gate crashed: {type(exc).__name__}: {detail[:200]}"
                return False, f"Tau gate crashed: {type(exc).__name__}"
            if not tau_ok:
                detail = (tau_err or "unknown error").strip()
                if "\n" in detail or "\r" in detail:
                    detail = " ".join(detail.split())
                if len(detail) > 200:
                    detail = detail[:200]
                return False, f"Tau gate rejected settlement: {detail}"
        
        # Validate intent constraints
        for intent in intents:
            # Check expiration
            if intent.deadline < block_timestamp:
                return False, f"Intent expired: {intent.intent_id}"
            
            # Check authorization (would be done by transaction signature in real system)
            # For now, we assume it's validated at transaction level
    
    return True, None


def apply_operations(
    settlement: Settlement,
    balances: BalanceTable,
    pools: Dict[str, PoolState],
    lp_balances: Optional[LPTable] = None,
) -> None:
    """
    Apply validated operations to state.
    
    Args:
        settlement: Validated settlement
        balances: Balance table to update
        pools: Pool states to update
        
    Raises:
        ValueError: If settlement is invalid
    """
    apply_settlement(settlement, balances, pools, lp_balances)

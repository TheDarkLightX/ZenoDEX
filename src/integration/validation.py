"""
Tau validation bridge for ZenoDEX operations.

This module bridges between Python operations and Tau Language validation.
In production, this would call the Tau Docker container to validate operations.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Dict, List, Optional, Tuple

from ..core.batch_clearing import apply_settlement
from ..core.settlement import Settlement
from ..core.settlement_strong_validator import validate_settlement_strong
from ..core.uniform_batch_clearing import (
    UniformBatchCertificateV1,
    validate_uniform_batch_settlement_v1,
)
from ..state.balances import BalanceTable
from ..state.intents import Intent
from ..state.lp import LPTable
from ..state.pools import PoolState
from .settlement_end_to_end_certificate_packet import (
    SettlementEndToEndCertificateInputs,
    enforce_settlement_end_to_end_certificate,
)
from .settlement_strong_certificate import (
    SettlementProofFlags,
)

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
    settlement_validation: str = "strong_proof_carrying",
    swap_ordering: str = "greedy_ab_refined",
    quote_bindings_validated: bool = False,
    require_settlement_certificate: bool = False,
    settlement_proof_flags: Optional[SettlementProofFlags] = None,
    settlement_price_history: Optional[Tuple[int, int, int]] = None,
    require_settlement_end_to_end_certificate: bool = False,
    settlement_end_to_end_certificate_inputs: Optional[SettlementEndToEndCertificateInputs] = None,
    uniform_batch_certificate: Optional[Dict[str, object]] = None,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[str] = None,
) -> Tuple[bool, Optional[str]]:
    """
    Validate ZenoDEX operations using Tau Language validation.
    
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
        allow_cow_netting = str(swap_ordering) == "cow_pair_netting_v1"
        use_end_to_end_certificate = bool(
            require_settlement_end_to_end_certificate or require_settlement_certificate
        )
        if uniform_batch_certificate is not None and use_end_to_end_certificate:
            return False, "uniform batch certificate cannot be combined with settlement end-to-end certificate"
        if uniform_batch_certificate is not None:
            if protocol_fee_share_bps > 0:
                return False, "uniform batch certificate cannot be used when protocol fees are enabled"
            try:
                cert = UniformBatchCertificateV1.from_obj(uniform_batch_certificate)
            except Exception as exc:
                return False, f"invalid uniform batch certificate: {exc}"
            pool = pools.get(cert.pool_id)
            if pool is None:
                return False, f"uniform batch certificate pool not found: {cert.pool_id}"
            is_valid, error = validate_uniform_batch_settlement_v1(
                intents=intents,
                pool=pool,
                balances=balances,
                certificate=cert,
                settlement=settlement,
            )
        elif use_end_to_end_certificate:
            if settlement_end_to_end_certificate_inputs is None:
                return False, "settlement certificate required but settlement_end_to_end_certificate_inputs missing"
            try:
                is_valid, error, _packet = enforce_settlement_end_to_end_certificate(
                    settlement=settlement,
                    certificate_inputs=settlement_end_to_end_certificate_inputs,
                    intents=intents,
                    pre_balances=balances,
                    pre_pools=pools,
                    pre_lp_balances=lp_balances,
                    mode=str(settlement_validation),
                    allow_cow_netting=bool(allow_cow_netting),
                    allow_snapshot_bound_quote_bindings=bool(quote_bindings_validated),
                    protocol_fee_share_bps=protocol_fee_share_bps,
                    protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
                )
            except Exception as exc:
                return False, f"invalid settlement end-to-end certificate inputs: {exc}"
        else:
            # Validate settlement (fail-closed): bind deltas to intents + kernel-backed swap math.
            is_valid, error = validate_settlement_strong(
                settlement=settlement,
                intents=intents,
                pre_balances=balances,
                pre_pools=pools,
                pre_lp_balances=lp_balances,
                mode=str(settlement_validation),
                allow_cow_netting=bool(allow_cow_netting),
                allow_snapshot_bound_quote_bindings=bool(quote_bindings_validated),
                protocol_fee_share_bps=protocol_fee_share_bps,
                protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
            )
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
                    settlement=settlement,
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

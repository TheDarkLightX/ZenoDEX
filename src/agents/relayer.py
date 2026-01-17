"""
Intent batching and relay for autonomous agents.
"""

from typing import List, Dict, Any
from collections import defaultdict

from ..state.intents import SignedIntent, Intent


def batch_intents(
    signed_intents: List[SignedIntent],
    max_batch_size: int = 100,
) -> List[List[SignedIntent]]:
    """
    Group intents into batches.
    
    Groups by pool_id to optimize batch clearing.
    
    Args:
        signed_intents: List of signed intents
        max_batch_size: Maximum intents per batch
        
    Returns:
        List of batches (each batch is a list of signed intents)
    """
    # Group by pool_id
    intents_by_pool: Dict[str, List[SignedIntent]] = defaultdict(list)
    non_pool_intents: List[SignedIntent] = []
    
    for signed_intent in signed_intents:
        pool_id = signed_intent.intent.get_field("pool_id")
        if pool_id:
            intents_by_pool[pool_id].append(signed_intent)
        else:
            non_pool_intents.append(signed_intent)
    
    # Create batches
    batches: List[List[SignedIntent]] = []
    
    # Add pool-specific batches
    for pool_id, pool_intents in intents_by_pool.items():
        # Split large pools into multiple batches
        for i in range(0, len(pool_intents), max_batch_size):
            batches.append(pool_intents[i:i + max_batch_size])
    
    # Add non-pool intents as separate batch
    if non_pool_intents:
        batches.append(non_pool_intents)
    
    return batches


def create_batch(
    signed_intents: List[SignedIntent],
    batch_ref: str = "",
) -> Dict[str, Any]:
    """
    Create a batch object for submission.
    
    Args:
        signed_intents: List of signed intents
        batch_ref: Reference to block height/hash
        
    Returns:
        Batch dictionary ready for JSON serialization
    """
    # Extract intents (without signatures for now; signatures verified separately)
    intents = [signed_intent.intent for signed_intent in signed_intents]
    
    # Create batch structure
    batch = {
        "module": "TauSwap",
        "version": "0.1",
        "batch_ref": batch_ref,
        "intents": [
            _intent_to_dict(intent) for intent in intents
        ],
    }
    
    return batch


def _intent_to_dict(intent: Intent) -> Dict[str, Any]:
    """
    Convert intent to dictionary for JSON serialization.
    
    Args:
        intent: Intent object
        
    Returns:
        Dictionary representation
    """
    intent_dict = {
        "module": intent.module,
        "version": intent.version,
        "kind": intent.kind.value,
        "intent_id": intent.intent_id,
        "sender_pubkey": intent.sender_pubkey,
        "deadline": intent.deadline,
    }
    
    if intent.salt:
        intent_dict["salt"] = intent.salt
    
    if intent.fields:
        intent_dict.update(intent.fields)
    
    return intent_dict


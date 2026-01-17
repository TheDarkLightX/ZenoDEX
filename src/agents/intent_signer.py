"""
Intent creation and signing for autonomous agents.
"""

import hashlib
import json
from typing import Dict, Any, Optional

from ..state.intents import Intent, IntentKind, SignedIntent
from ..state.balances import AssetId, Amount, PubKey

# For BLS12-381 signing (same as tau-testnet)
try:
    from py_ecc import bls12_381 as bls
except ImportError:
    # Fallback for development (signatures won't be valid)
    bls = None


def create_swap_intent(
    pool_id: str,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    min_amount_out: Amount,
    deadline: int,
    sender_pubkey: PubKey,
    exact_out: bool = False,
    amount_out: Optional[Amount] = None,
    max_amount_in: Optional[Amount] = None,
    recipient: Optional[PubKey] = None,
    salt: Optional[str] = None,
) -> Intent:
    """
    Create a swap intent.
    
    Args:
        pool_id: Pool identifier
        asset_in: Input asset
        asset_out: Output asset
        amount_in: Input amount (for exact-in)
        min_amount_out: Minimum output (for exact-in)
        deadline: Expiration timestamp
        sender_pubkey: Public key of sender
        exact_out: If True, create exact-out intent
        amount_out: Output amount (for exact-out)
        max_amount_in: Maximum input (for exact-out)
        recipient: Recipient pubkey (defaults to sender)
        salt: Optional salt for uniqueness
        
    Returns:
        Intent object
    """
    if exact_out:
        if amount_out is None or amount_out <= 0:
            raise ValueError("amount_out must be positive for exact-out")
        if max_amount_in is None or max_amount_in < 0:
            raise ValueError("max_amount_in must be non-negative for exact-out")
        
        kind = IntentKind.SWAP_EXACT_OUT
        fields = {
            "pool_id": pool_id,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_out": amount_out,
            "max_amount_in": max_amount_in,
            "recipient": recipient or sender_pubkey,
        }
    else:
        if amount_in <= 0:
            raise ValueError("amount_in must be positive")
        if min_amount_out < 0:
            raise ValueError("min_amount_out must be non-negative")
        
        kind = IntentKind.SWAP_EXACT_IN
        fields = {
            "pool_id": pool_id,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
            "recipient": recipient or sender_pubkey,
        }
    
    # Generate intent_id
    intent_id = _generate_intent_id(
        sender_pubkey, deadline, kind.value, fields, salt
    )
    
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id=intent_id,
        sender_pubkey=sender_pubkey,
        deadline=deadline,
        salt=salt,
        fields=fields,
    )
    
    return intent


def _generate_intent_id(
    sender: PubKey,
    deadline: int,
    kind: str,
    fields: Dict[str, Any],
    salt: Optional[str],
) -> str:
    """
    Generate deterministic intent ID.
    
    Formula: H(sender || deadline || kind || canonical_json(fields) || salt)
    
    Args:
        sender: Sender public key
        deadline: Deadline timestamp
        kind: Intent kind
        fields: Intent fields
        salt: Optional salt
        
    Returns:
        32-byte hex string (0x...)
    """
    # Canonical JSON encoding (sorted keys, no whitespace)
    canonical_json = json.dumps(fields, sort_keys=True, separators=(',', ':'))
    
    # Hash components
    data = (
        sender.encode('utf-8')
        + str(deadline).encode('utf-8')
        + kind.encode('utf-8')
        + canonical_json.encode('utf-8')
    )
    
    if salt:
        data += salt.encode('utf-8')
    
    intent_id_hash = hashlib.sha256(data).hexdigest()
    return "0x" + intent_id_hash


def sign_intent(intent: Intent, private_key: bytes) -> SignedIntent:
    """
    Sign an intent with BLS12-381 signature.
    
    Args:
        intent: Intent to sign
        private_key: BLS12-381 private key (bytes)
        
    Returns:
        SignedIntent object
        
    Raises:
        ImportError: If py_ecc is not available
    """
    if bls is None:
        raise ImportError(
            "py_ecc not available. Install with: pip install py-ecc"
        )
    
    # Create canonical message for signing
    message = _create_canonical_message(intent)
    
    # Sign with BLS12-381
    # Note: This is a simplified version; full implementation would
    # use proper BLS12-381 signing as per tau-testnet
    signature_bytes = bls.sign(message, private_key)
    signature = "0x" + signature_bytes.hex()
    
    return SignedIntent(intent=intent, signature=signature)


def _create_canonical_message(intent: Intent) -> bytes:
    """
    Create canonical message for intent signing.
    
    Uses canonical JSON encoding consistent with tau-testnet.
    
    Args:
        intent: Intent to encode
        
    Returns:
        Canonical message bytes
    """
    # Create canonical JSON representation
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
    
    # Canonical JSON (sorted keys, no whitespace)
    canonical_json = json.dumps(intent_dict, sort_keys=True, separators=(',', ':'))
    
    return canonical_json.encode('utf-8')


def verify_intent_signature(signed_intent: SignedIntent) -> bool:
    """
    Verify intent signature.
    
    Args:
        signed_intent: Signed intent to verify
        
    Returns:
        True if signature is valid
        
    Raises:
        ImportError: If py_ecc is not available
    """
    if bls is None:
        raise ImportError(
            "py_ecc not available. Install with: pip install py-ecc"
        )
    
    # Create canonical message
    message = _create_canonical_message(signed_intent.intent)
    
    # Verify signature
    # Note: This is a simplified version; full implementation would
    # use proper BLS12-381 verification as per tau-testnet
    try:
        pubkey_bytes = bytes.fromhex(signed_intent.intent.sender_pubkey[2:])
        signature_bytes = bytes.fromhex(signed_intent.signature[2:])
        return bls.verify(message, signature_bytes, pubkey_bytes)
    except Exception:
        return False


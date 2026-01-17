"""
Operation group handlers for Tau Testnet Alpha.

Handles operation groups "2" (DEX intents) and "3" (DEX settlement).
"""

from collections.abc import Mapping
from dataclasses import dataclass
from typing import List, Dict, Any, Optional

from ..state.intents import Intent, IntentKind
from ..core.settlement import Settlement, FillAction


def _require_str(value: Any, *, name: str, non_empty: bool = True, max_len: int = 4096) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a string")
    if non_empty and not value:
        raise ValueError(f"{name} must be non-empty")
    if max_len > 0 and len(value) > max_len:
        raise ValueError(f"{name} too large")
    return value


def _require_int(value: Any, *, name: str, non_negative: bool = False) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    if non_negative and value < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def _optional_int(value: Any, *, name: str, non_negative: bool = False) -> Optional[int]:
    if value is None:
        return None
    return _require_int(value, name=name, non_negative=non_negative)


def _require_dict_str_keys(value: Any, *, name: str) -> Dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError(f"{name} must be an object")
    for k in value.keys():
        if not isinstance(k, str):
            raise ValueError(f"{name} keys must be strings")
    return value


@dataclass(frozen=True)
class SignedIntentEnvelope:
    """
    Parsed intent with optional per-intent signature.

    Note: the transaction itself is signed by `sender_pubkey` at the Tau Net layer,
    but batch settlement requires each included intent to carry its own signature.
    """

    intent: Intent
    signature: Optional[str] = None


@dataclass(frozen=True)
class SettlementEnvelope:
    settlement: Settlement
    proof: Optional[Dict[str, Any]] = None


def parse_intents(operations: Dict[str, Any]) -> List[Intent]:
    """
    Parse intents from transaction operations["2"].
    
    Args:
        operations: Transaction operations dictionary
        
    Returns:
        List of Intent objects
        
    Raises:
        ValueError: If operations structure is invalid
    """
    if not isinstance(operations, Mapping):
        raise ValueError(f"operations must be an object, got {type(operations)}")

    if "2" not in operations:
        return []
    
    intents_data = operations["2"]
    if not isinstance(intents_data, list):
        raise ValueError(f"operations['2'] must be a list, got {type(intents_data)}")
    
    intents = []
    for i, intent_data in enumerate(intents_data):
        try:
            intent = _parse_intent(intent_data)
            intents.append(intent)
        except Exception as e:
            raise ValueError(f"Failed to parse intent {i}: {e}") from e
    
    return intents


def parse_signed_intents(operations: Dict[str, Any]) -> List[SignedIntentEnvelope]:
    """
    Parse intents from operations["2"] allowing optional per-intent signatures.

    Accepted formats for each entry:
    1) intent dict with optional "signature" field
    2) [intent_dict, signature_hex]
    """
    if not isinstance(operations, Mapping):
        raise ValueError(f"operations must be an object, got {type(operations)}")

    if "2" not in operations:
        return []

    intents_data = operations["2"]
    if not isinstance(intents_data, list):
        raise ValueError(f"operations['2'] must be a list, got {type(intents_data)}")

    out: List[SignedIntentEnvelope] = []
    for i, entry in enumerate(intents_data):
        try:
            signature = None
            signature_in_dict = None

            if isinstance(entry, list):
                if len(entry) not in (1, 2):
                    raise ValueError("intent list entry must have length 1 or 2")
                intent_data = entry[0]
                if len(entry) == 2:
                    signature = entry[1]
            else:
                intent_data = entry

            if not isinstance(intent_data, dict):
                raise ValueError(f"intent entry must be a dict, got {type(intent_data)}")

            # Never allow "signature" to leak into intent-specific fields.
            if "signature" in intent_data:
                signature_in_dict = intent_data.get("signature")
                intent_data = {k: v for k, v in intent_data.items() if k != "signature"}

            # If both envelope and dict provide signatures, reject ambiguity.
            if signature is not None and signature_in_dict is not None:
                if signature != signature_in_dict:
                    raise ValueError("signature provided twice (envelope + field) and differs")
                raise ValueError("signature provided twice (envelope + field)")

            if signature is None:
                signature = signature_in_dict

            intent = _parse_intent(intent_data)
            if signature is not None and not isinstance(signature, str):
                raise ValueError("signature must be a string")
            if isinstance(signature, str) and len(signature) > 4096:
                raise ValueError("signature too large")
            out.append(SignedIntentEnvelope(intent=intent, signature=signature))
        except Exception as e:
            raise ValueError(f"Failed to parse signed intent {i}: {e}") from e
    return out


def _parse_intent(intent_data: Dict[str, Any]) -> Intent:
    """
    Parse a single intent from JSON data.
    
    Args:
        intent_data: Intent dictionary
        
    Returns:
        Intent object
    """
    intent_data = _require_dict_str_keys(intent_data, name="intent")

    # Validate required fields
    required_fields = ["module", "version", "kind", "intent_id", "sender_pubkey", "deadline"]
    for field in required_fields:
        if field not in intent_data:
            raise ValueError(f"Missing required field: {field}")

    module = _require_str(intent_data.get("module"), name="intent.module", non_empty=True, max_len=64)
    if module != "TauSwap":
        raise ValueError(f"Invalid module: {module}")

    version = _require_str(intent_data.get("version"), name="intent.version", non_empty=True, max_len=64)
    if version != "0.1":
        raise ValueError(f"Invalid version: {version}")

    kind_raw = _require_str(intent_data.get("kind"), name="intent.kind", non_empty=True, max_len=64)
    intent_id = _require_str(intent_data.get("intent_id"), name="intent.intent_id", non_empty=True, max_len=256)
    sender_pubkey = _require_str(intent_data.get("sender_pubkey"), name="intent.sender_pubkey", non_empty=True, max_len=512)
    deadline = _require_int(intent_data.get("deadline"), name="intent.deadline", non_negative=True)
    salt = intent_data.get("salt")
    if salt is not None:
        salt = _require_str(salt, name="intent.salt", non_empty=True, max_len=4096)
    
    # Parse kind
    try:
        kind = IntentKind(kind_raw)
    except ValueError as e:
        raise ValueError(f"Invalid intent kind: {kind_raw}") from e
    
    # Extract fields (everything except common fields)
    common_fields = {"module", "version", "kind", "intent_id", "sender_pubkey", "deadline", "salt"}
    fields = {
        k: v for k, v in intent_data.items()
        if k not in common_fields
    }
    
    intent = Intent(
        module=module,
        version=version,
        kind=kind,
        intent_id=intent_id,
        sender_pubkey=sender_pubkey,
        deadline=deadline,
        salt=salt,
        fields=fields,
    )
    
    return intent


def parse_settlement(operations: Dict[str, Any]) -> Optional[Settlement]:
    """
    Parse settlement from transaction operations["3"].
    
    Args:
        operations: Transaction operations dictionary
        
    Returns:
        Settlement object or None if not present
        
    Raises:
        ValueError: If operations structure is invalid
    """
    if not isinstance(operations, Mapping):
        raise ValueError(f"operations must be an object, got {type(operations)}")

    if "3" not in operations:
        return None
    
    settlement_data = operations["3"]
    if not isinstance(settlement_data, dict):
        raise ValueError(f"operations['3'] must be a dict, got {type(settlement_data)}")
    
    return _parse_settlement(settlement_data)


def parse_settlement_envelope(operations: Dict[str, Any]) -> Optional[SettlementEnvelope]:
    """
    Parse settlement and optional proof payload from operations["3"].

    Proof payload is passed through as an opaque JSON object under either:
    - settlement_data["proof"] (preferred: object)
    - settlement_data["zk_proof"] (legacy/alt: object)
    """
    if not isinstance(operations, Mapping):
        raise ValueError(f"operations must be an object, got {type(operations)}")

    if "3" not in operations:
        return None

    settlement_data = operations["3"]
    if not isinstance(settlement_data, dict):
        raise ValueError(f"operations['3'] must be a dict, got {type(settlement_data)}")

    if "proof" in settlement_data and "zk_proof" in settlement_data:
        raise ValueError("settlement proof provided twice (proof + zk_proof)")

    proof = None
    raw_proof = settlement_data.get("proof")
    if raw_proof is None:
        raw_proof = settlement_data.get("zk_proof")
    if raw_proof is not None:
        if not isinstance(raw_proof, dict):
            raise ValueError("settlement proof must be an object")
        proof = raw_proof

    settlement_data_no_proof = {k: v for k, v in settlement_data.items() if k not in ("proof", "zk_proof")}
    settlement = _parse_settlement(settlement_data_no_proof)
    return SettlementEnvelope(settlement=settlement, proof=proof)


def _parse_settlement(settlement_data: Dict[str, Any]) -> Settlement:
    """
    Parse settlement from dictionary.
    
    Args:
        settlement_data: Settlement dictionary
        
    Returns:
        Settlement object
    """
    from ..core.settlement import (
        Fill, BalanceDelta, ReserveDelta, LPDelta
    )
    
    settlement_data = _require_dict_str_keys(settlement_data, name="settlement")

    module = _require_str(settlement_data.get("module"), name="settlement.module", non_empty=True, max_len=64)
    if module != "TauSwap":
        raise ValueError(f"Invalid module: {module}")

    version = _require_str(settlement_data.get("version"), name="settlement.version", non_empty=True, max_len=64)
    if version != "0.1":
        raise ValueError(f"Invalid version: {version}")

    # Parse included_intents
    included_intents_raw = settlement_data.get("included_intents", [])
    if included_intents_raw is None:
        included_intents_raw = []
    if not isinstance(included_intents_raw, list):
        raise ValueError("settlement.included_intents must be a list")
    included_intents: list[tuple[str, FillAction]] = []
    for entry in included_intents_raw:
        if not isinstance(entry, (list, tuple)) or len(entry) != 2:
            raise ValueError("included_intents entries must be [intent_id, action]")
        intent_id, action_str = entry[0], entry[1]
        intent_id_s = _require_str(intent_id, name="included_intents.intent_id", non_empty=True, max_len=256)
        action_s = _require_str(action_str, name="included_intents.action", non_empty=True, max_len=64)
        try:
            action = FillAction(action_s)
        except ValueError as exc:
            raise ValueError(f"Invalid action: {action_s}") from exc
        included_intents.append((intent_id_s, action))
    
    # Parse fills
    fills_raw = settlement_data.get("fills", [])
    if fills_raw is None:
        fills_raw = []
    if not isinstance(fills_raw, list):
        raise ValueError("settlement.fills must be a list")
    fills: list[Fill] = []
    for fill_data in fills_raw:
        if not isinstance(fill_data, dict):
            raise ValueError("fills entries must be objects")

        action_s = _require_str(fill_data.get("action"), name="fill.action", non_empty=True, max_len=64)
        try:
            action = FillAction(action_s)
        except ValueError as exc:
            raise ValueError(f"Invalid fill action: {action_s}") from exc

        intent_id_s = _require_str(fill_data.get("intent_id"), name="fill.intent_id", non_empty=True, max_len=256)
        reason = fill_data.get("reason")
        if reason is not None:
            reason = _require_str(reason, name="fill.reason", non_empty=False, max_len=4096)

        fill = Fill(
            intent_id=intent_id_s,
            action=action,
            reason=reason,
            amount_in_filled=_optional_int(fill_data.get("amount_in_filled"), name="fill.amount_in_filled", non_negative=True),
            amount_out_filled=_optional_int(
                fill_data.get("amount_out_filled"), name="fill.amount_out_filled", non_negative=True
            ),
            fee_paid=_optional_int(fill_data.get("fee_paid"), name="fill.fee_paid", non_negative=True),
            amount0_used=_optional_int(fill_data.get("amount0_used"), name="fill.amount0_used", non_negative=True),
            amount1_used=_optional_int(fill_data.get("amount1_used"), name="fill.amount1_used", non_negative=True),
            lp_minted=_optional_int(fill_data.get("lp_minted"), name="fill.lp_minted", non_negative=True),
            amount0_out=_optional_int(fill_data.get("amount0_out"), name="fill.amount0_out", non_negative=True),
            amount1_out=_optional_int(fill_data.get("amount1_out"), name="fill.amount1_out", non_negative=True),
            lp_burned=_optional_int(fill_data.get("lp_burned"), name="fill.lp_burned", non_negative=True),
        )
        fills.append(fill)
    
    # Parse deltas
    balance_deltas_raw = settlement_data.get("balance_deltas", [])
    if balance_deltas_raw is None:
        balance_deltas_raw = []
    if not isinstance(balance_deltas_raw, list):
        raise ValueError("settlement.balance_deltas must be a list")
    balance_deltas: list[BalanceDelta] = []
    for d in balance_deltas_raw:
        if not isinstance(d, dict):
            raise ValueError("balance_deltas entries must be objects")
        pubkey = _require_str(d.get("pubkey"), name="balance_delta.pubkey", non_empty=True, max_len=512)
        asset = _require_str(d.get("asset"), name="balance_delta.asset", non_empty=True, max_len=256)
        delta_add = _require_int(d.get("delta_add", 0), name="balance_delta.delta_add", non_negative=True)
        delta_sub = _require_int(d.get("delta_sub", 0), name="balance_delta.delta_sub", non_negative=True)
        balance_deltas.append(BalanceDelta(pubkey=pubkey, asset=asset, delta_add=delta_add, delta_sub=delta_sub))

    reserve_deltas_raw = settlement_data.get("reserve_deltas", [])
    if reserve_deltas_raw is None:
        reserve_deltas_raw = []
    if not isinstance(reserve_deltas_raw, list):
        raise ValueError("settlement.reserve_deltas must be a list")
    reserve_deltas: list[ReserveDelta] = []
    for d in reserve_deltas_raw:
        if not isinstance(d, dict):
            raise ValueError("reserve_deltas entries must be objects")
        pool_id = _require_str(d.get("pool_id"), name="reserve_delta.pool_id", non_empty=True, max_len=256)
        asset = _require_str(d.get("asset"), name="reserve_delta.asset", non_empty=True, max_len=256)
        delta_add = _require_int(d.get("delta_add", 0), name="reserve_delta.delta_add", non_negative=True)
        delta_sub = _require_int(d.get("delta_sub", 0), name="reserve_delta.delta_sub", non_negative=True)
        reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset, delta_add=delta_add, delta_sub=delta_sub))

    lp_deltas_raw = settlement_data.get("lp_deltas", [])
    if lp_deltas_raw is None:
        lp_deltas_raw = []
    if not isinstance(lp_deltas_raw, list):
        raise ValueError("settlement.lp_deltas must be a list")
    lp_deltas: list[LPDelta] = []
    for d in lp_deltas_raw:
        if not isinstance(d, dict):
            raise ValueError("lp_deltas entries must be objects")
        pubkey = _require_str(d.get("pubkey"), name="lp_delta.pubkey", non_empty=True, max_len=512)
        pool_id = _require_str(d.get("pool_id"), name="lp_delta.pool_id", non_empty=True, max_len=256)
        delta_add = _require_int(d.get("delta_add", 0), name="lp_delta.delta_add", non_negative=True)
        delta_sub = _require_int(d.get("delta_sub", 0), name="lp_delta.delta_sub", non_negative=True)
        lp_deltas.append(LPDelta(pubkey=pubkey, pool_id=pool_id, delta_add=delta_add, delta_sub=delta_sub))

    batch_ref = settlement_data.get("batch_ref", "")
    if batch_ref is None:
        batch_ref = ""
    if not isinstance(batch_ref, str):
        raise ValueError("settlement.batch_ref must be a string")

    events = settlement_data.get("events")
    if events is not None:
        if not isinstance(events, list):
            raise ValueError("settlement.events must be a list")
        for e in events:
            if not isinstance(e, dict):
                raise ValueError("settlement.events entries must be objects")
    
    try:
        settlement = Settlement(
            module=module,
            version=version,
            batch_ref=batch_ref,
            included_intents=included_intents,
            fills=fills,
            balance_deltas=balance_deltas,
            reserve_deltas=reserve_deltas,
            lp_deltas=lp_deltas,
            events=events,
        )
    except Exception as exc:
        raise ValueError(f"Invalid settlement: {exc}") from exc
    
    return settlement


def create_intent_operation(intents: List[Intent]) -> Dict[str, Any]:
    """
    Create operations["2"] structure from intents.
    
    Args:
        intents: List of Intent objects
        
    Returns:
        Dictionary for operations["2"]
    """
    reserved_keys = {"module", "version", "kind", "intent_id", "sender_pubkey", "deadline", "salt", "signature"}

    intents_data = []
    for intent in intents:
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
            for k, v in intent.fields.items():
                if k in reserved_keys:
                    raise ValueError(f"intent.fields contains reserved key: {k}")
                intent_dict[k] = v
        
        intents_data.append(intent_dict)
    
    return {"2": intents_data}


def create_settlement_operation(settlement: Settlement) -> Dict[str, Any]:
    """
    Create operations["3"] structure from settlement.
    
    Args:
        settlement: Settlement object
        
    Returns:
        Dictionary for operations["3"]
    """
    settlement_data = {
        "module": settlement.module,
        "version": settlement.version,
        "batch_ref": settlement.batch_ref,
        "included_intents": [
            [intent_id, action.value]
            for intent_id, action in settlement.included_intents
        ],
        "fills": [
            {
                "intent_id": fill.intent_id,
                "action": fill.action.value,
                "reason": fill.reason,
                "amount_in_filled": fill.amount_in_filled,
                "amount_out_filled": fill.amount_out_filled,
                "fee_paid": fill.fee_paid,
                "amount0_used": fill.amount0_used,
                "amount1_used": fill.amount1_used,
                "lp_minted": fill.lp_minted,
                "amount0_out": fill.amount0_out,
                "amount1_out": fill.amount1_out,
                "lp_burned": fill.lp_burned,
            }
            for fill in settlement.fills
        ],
        "balance_deltas": [
            {
                "pubkey": delta.pubkey,
                "asset": delta.asset,
                "delta_add": delta.delta_add,
                "delta_sub": delta.delta_sub,
            }
            for delta in settlement.balance_deltas
        ],
        "reserve_deltas": [
            {
                "pool_id": delta.pool_id,
                "asset": delta.asset,
                "delta_add": delta.delta_add,
                "delta_sub": delta.delta_sub,
            }
            for delta in settlement.reserve_deltas
        ],
        "lp_deltas": [
            {
                "pubkey": delta.pubkey,
                "pool_id": delta.pool_id,
                "delta_add": delta.delta_add,
                "delta_sub": delta.delta_sub,
            }
            for delta in settlement.lp_deltas
        ],
    }
    
    if settlement.events:
        settlement_data["events"] = settlement.events
    
    return {"3": settlement_data}

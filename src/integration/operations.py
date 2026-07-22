"""
Operation group handlers for Tau Testnet Alpha.

Handles operation groups "2" (DEX intents) and "3" (DEX settlement).
"""

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any, Dict, List, Optional

from ..core.dex_intent_auth_message import canonicalize_dex_intent_identifier_if_decodable
from ..core.domain_limits import (
    DEX_LP_AMOUNT_MAX,
    DEX_LP_SUPPLY_MAX,
    DEX_POOL_RESERVE_MAX,
    DEX_SWAP_AMOUNT_MAX,
)
from ..core.settlement import (
    BalanceDelta,
    Fill,
    FillAction,
    LPDelta,
    ReserveDelta,
    Settlement,
)
from ..state.immutable_collections import deep_freeze, deep_thaw_json
from ..state.intents import Intent, IntentKind
from ..state.pools import normalize_curve_config, normalize_pool_asset_pair

POOL_FEE_BPS_MIN = 0
POOL_FEE_BPS_MAX = 10_000

_CANONICAL_INTENT_FIELD_IDENTIFIERS = (
    "recipient",
    "asset0",
    "asset1",
    "asset_in",
    "asset_out",
    "pool_id",
)


def _canonicalize_decodable_intent_identifiers(intent: Intent) -> None:
    """Normalize parser-admitted identifiers to match DEX intent auth hashing.

    Design by Contract:
    - Precondition: ``intent.fields`` is a mutable parser-owned dictionary.
    - Invariant: State transitions consume the same canonical fixed-width hex
      spellings that signature verification hashes.
    - Postcondition: Non-decodable symbolic identifiers remain unchanged.
    """
    intent.sender_pubkey = canonicalize_dex_intent_identifier_if_decodable(
        intent.sender_pubkey,
        key="sender_pubkey",
    )
    fields = intent.fields or {}
    for key in _CANONICAL_INTENT_FIELD_IDENTIFIERS:
        if key in fields:
            fields[key] = canonicalize_dex_intent_identifier_if_decodable(fields[key], key=key)


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


def _require_int_range(
    value: Any,
    *,
    name: str,
    minimum: int | None = None,
    maximum: int | None = None,
) -> int:
    value_int = _require_int(value, name=name)
    if minimum is not None and value_int < minimum:
        raise ValueError(f"{name} must be >= {minimum}")
    if maximum is not None and value_int > maximum:
        raise ValueError(f"{name} must be <= {maximum}")
    return value_int


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


def _parse_quote_receipt_transport(value: Any, *, name: str) -> Dict[str, Any]:
    receipt = _require_dict_str_keys(value, name=name)
    body = receipt.get("body")
    receipt_hash = receipt.get("receipt_hash")
    if not isinstance(body, dict):
        raise ValueError(f"{name}.body must be an object")
    if not isinstance(receipt_hash, str) or not receipt_hash:
        raise ValueError(f"{name}.receipt_hash must be a non-empty string")
    return receipt


@dataclass(frozen=True, slots=True)
class SignedIntentEnvelope:
    """
    Parsed intent with optional per-intent signature.

    Note: the transaction itself is signed by `sender_pubkey` at the Tau Net layer,
    but batch settlement requires each included intent to carry its own signature.
    """

    intent: Intent
    signature: Optional[str] = None
    quote_receipt: Optional[Mapping[str, Any]] = None

    def __post_init__(self) -> None:
        if not isinstance(self.intent, Intent):
            raise TypeError("intent must be an Intent")

        # Bind signature verification and quote validation to one detached
        # payload even if the caller retains and mutates its builder.
        from ..state.intent_snapshots import freeze_intent

        object.__setattr__(self, "intent", freeze_intent(self.intent))
        if self.quote_receipt is not None:
            if not isinstance(self.quote_receipt, Mapping):
                raise TypeError("quote_receipt must be a mapping or None")
            object.__setattr__(self, "quote_receipt", deep_freeze(self.quote_receipt))


@dataclass
class ValidatedIntent(Intent):
    """
    Intent admitted through the operations parser normal-form boundary.

    The state-layer `Intent` type remains generic for generated fixtures and
    internal proof/test construction. User-supplied operations cross this
    boundary only after common fields, kind-specific fields, and unknown fields
    have been validated.
    """


@dataclass(frozen=True)
class SettlementEnvelope:
    settlement: Settlement
    proof: Optional[Dict[str, Any]] = None
    oracle_authorization: Optional[Dict[str, Any]] = None
    uniform_batch_certificate: Optional[Dict[str, Any]] = None
    uniform_batch_optimality_certificate: Optional[Dict[str, Any]] = None
    uniform_batch_v2_bounded_grid: Optional[Dict[str, Any]] = None
    uniform_batch_v3_exact_out_grid: Optional[Dict[str, Any]] = None


def _require_list_or_empty(value: Any, *, name: str) -> list[Any]:
    if value is None:
        return []
    if not isinstance(value, list):
        raise ValueError(f"{name} must be a list")
    return list(value)


def _parse_fill_action(value: Any, *, name: str, error_prefix: str) -> FillAction:
    action_s = _require_str(value, name=name, non_empty=True, max_len=64)
    try:
        return FillAction(action_s)
    except ValueError as exc:
        raise ValueError(f"{error_prefix}: {action_s}") from exc


def _parse_included_intent_entry(entry: Any) -> tuple[str, FillAction]:
    if not isinstance(entry, (list, tuple)) or len(entry) != 2:
        raise ValueError("included_intents entries must be [intent_id, action]")
    intent_id_s = _require_str(entry[0], name="included_intents.intent_id", non_empty=True, max_len=256)
    action = _parse_fill_action(
        entry[1],
        name="included_intents.action",
        error_prefix="Invalid action",
    )
    return intent_id_s, action


def _parse_included_intents(value: Any) -> list[tuple[str, FillAction]]:
    return [_parse_included_intent_entry(entry) for entry in _require_list_or_empty(value, name="settlement.included_intents")]


def _parse_fill(fill_data: Any) -> Fill:
    if not isinstance(fill_data, dict):
        raise ValueError("fills entries must be objects")

    action = _parse_fill_action(
        fill_data.get("action"),
        name="fill.action",
        error_prefix="Invalid fill action",
    )
    intent_id_s = _require_str(fill_data.get("intent_id"), name="fill.intent_id", non_empty=True, max_len=256)
    reason = fill_data.get("reason")
    if reason is not None:
        reason = _require_str(reason, name="fill.reason", non_empty=False, max_len=4096)

    return Fill(
        intent_id=intent_id_s,
        action=action,
        reason=reason,
        amount_in_filled=_optional_int(fill_data.get("amount_in_filled"), name="fill.amount_in_filled", non_negative=True),
        amount_out_filled=_optional_int(
            fill_data.get("amount_out_filled"), name="fill.amount_out_filled", non_negative=True
        ),
        fee_paid=_optional_int(fill_data.get("fee_paid"), name="fill.fee_paid", non_negative=True),
        protocol_fee_paid=_optional_int(
            fill_data.get("protocol_fee_paid"),
            name="fill.protocol_fee_paid",
            non_negative=True,
        ),
        amount0_used=_optional_int(fill_data.get("amount0_used"), name="fill.amount0_used", non_negative=True),
        amount1_used=_optional_int(fill_data.get("amount1_used"), name="fill.amount1_used", non_negative=True),
        lp_minted=_optional_int(fill_data.get("lp_minted"), name="fill.lp_minted", non_negative=True),
        amount0_out=_optional_int(fill_data.get("amount0_out"), name="fill.amount0_out", non_negative=True),
        amount1_out=_optional_int(fill_data.get("amount1_out"), name="fill.amount1_out", non_negative=True),
        lp_burned=_optional_int(fill_data.get("lp_burned"), name="fill.lp_burned", non_negative=True),
        reserve_in_before=_optional_int(
            fill_data.get("reserve_in_before"),
            name="fill.reserve_in_before",
            non_negative=True,
        ),
        reserve_out_before=_optional_int(
            fill_data.get("reserve_out_before"),
            name="fill.reserve_out_before",
            non_negative=True,
        ),
    )


def _parse_balance_delta(value: Any) -> BalanceDelta:
    if not isinstance(value, dict):
        raise ValueError("balance_deltas entries must be objects")
    return BalanceDelta(
        pubkey=_require_str(value.get("pubkey"), name="balance_delta.pubkey", non_empty=True, max_len=512),
        asset=_require_str(value.get("asset"), name="balance_delta.asset", non_empty=True, max_len=256),
        delta_add=_require_int(value.get("delta_add", 0), name="balance_delta.delta_add", non_negative=True),
        delta_sub=_require_int(value.get("delta_sub", 0), name="balance_delta.delta_sub", non_negative=True),
    )


def _parse_reserve_delta(value: Any) -> ReserveDelta:
    if not isinstance(value, dict):
        raise ValueError("reserve_deltas entries must be objects")
    return ReserveDelta(
        pool_id=_require_str(value.get("pool_id"), name="reserve_delta.pool_id", non_empty=True, max_len=256),
        asset=_require_str(value.get("asset"), name="reserve_delta.asset", non_empty=True, max_len=256),
        delta_add=_require_int(value.get("delta_add", 0), name="reserve_delta.delta_add", non_negative=True),
        delta_sub=_require_int(value.get("delta_sub", 0), name="reserve_delta.delta_sub", non_negative=True),
    )


def _parse_lp_delta(value: Any) -> LPDelta:
    if not isinstance(value, dict):
        raise ValueError("lp_deltas entries must be objects")
    return LPDelta(
        pubkey=_require_str(value.get("pubkey"), name="lp_delta.pubkey", non_empty=True, max_len=512),
        pool_id=_require_str(value.get("pool_id"), name="lp_delta.pool_id", non_empty=True, max_len=256),
        delta_add=_require_int(value.get("delta_add", 0), name="lp_delta.delta_add", non_negative=True),
        delta_sub=_require_int(value.get("delta_sub", 0), name="lp_delta.delta_sub", non_negative=True),
    )


def _parse_events(value: Any) -> Optional[list[dict[str, Any]]]:
    if value is None:
        return None
    if not isinstance(value, list):
        raise ValueError("settlement.events must be a list")
    for entry in value:
        if not isinstance(entry, dict):
            raise ValueError("settlement.events entries must be objects")
    return value


def parse_intents(operations: Dict[str, Any]) -> List[ValidatedIntent]:
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
    
    intents: list[ValidatedIntent] = []
    for i, intent_data in enumerate(intents_data):
        try:
            intent = _parse_intent(intent_data)
            intents.append(intent)
        except Exception as e:
            raise ValueError(f"Failed to parse intent {i}: {e}") from e
    
    return intents


def _unpack_signed_intent_entry(entry: Any) -> tuple[Dict[str, Any], Optional[str], Optional[Dict[str, Any]]]:
    signature = None
    signature_in_dict = None
    quote_receipt = None
    quote_receipt_in_dict = None

    if isinstance(entry, list):
        if len(entry) not in (1, 2, 3):
            raise ValueError("intent list entry must have length 1, 2, or 3")
        intent_data = entry[0]
        if len(entry) == 2:
            if isinstance(entry[1], dict):
                quote_receipt = entry[1]
            else:
                signature = entry[1]
        if len(entry) == 3:
            signature = entry[1]
            quote_receipt = entry[2]
    else:
        intent_data = entry

    if not isinstance(intent_data, dict):
        raise ValueError(f"intent entry must be a dict, got {type(intent_data)}")

    # Never allow "signature" to leak into intent-specific fields.
    if "signature" in intent_data:
        signature_in_dict = intent_data.get("signature")
        intent_data = {k: v for k, v in intent_data.items() if k != "signature"}
    if "quote_receipt" in intent_data:
        quote_receipt_in_dict = intent_data.get("quote_receipt")
        intent_data = {k: v for k, v in intent_data.items() if k != "quote_receipt"}

    # If both envelope and dict provide signatures, reject ambiguity.
    if signature is not None and signature_in_dict is not None:
        if signature != signature_in_dict:
            raise ValueError("signature provided twice (envelope + field) and differs")
        raise ValueError("signature provided twice (envelope + field)")

    if signature is None:
        signature = signature_in_dict

    if signature is not None:
        signature = _require_str(signature, name="signature", non_empty=True, max_len=4096)

    if quote_receipt is not None and quote_receipt_in_dict is not None:
        raise ValueError("quote_receipt provided twice (envelope + field)")
    if quote_receipt is None:
        quote_receipt = quote_receipt_in_dict
    if quote_receipt is not None:
        quote_receipt = _parse_quote_receipt_transport(quote_receipt, name="quote_receipt")
    return intent_data, signature, quote_receipt


def parse_signed_intents(operations: Dict[str, Any]) -> List[SignedIntentEnvelope]:
    """
    Parse intents from operations["2"] allowing optional per-intent signatures.

    Accepted formats for each entry:
    1) intent dict with optional "signature" and/or "quote_receipt" fields
    2) [intent_dict, signature_hex]
    3) [intent_dict, quote_receipt_obj]
    4) [intent_dict, signature_hex, quote_receipt_obj]
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
            intent_data, signature, quote_receipt = _unpack_signed_intent_entry(entry)
            intent = _parse_intent(intent_data)
            out.append(SignedIntentEnvelope(intent=intent, signature=signature, quote_receipt=quote_receipt))
        except Exception as e:
            raise ValueError(f"Failed to parse signed intent {i}: {e}") from e
    return out


def _parse_intent(intent_data: Dict[str, Any]) -> ValidatedIntent:
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
    
    intent = ValidatedIntent(
        module=module,
        version=version,
        kind=kind,
        intent_id=intent_id,
        sender_pubkey=sender_pubkey,
        deadline=deadline,
        salt=salt,
        fields=fields,
    )
    _canonicalize_decodable_intent_identifiers(intent)
    _validate_intent_fields(intent)
    
    return intent


_COMMON_INTENT_FIELD_KEYS = frozenset(
    {
        "nonce",
        "recipient",
        "submission_order",
        "quote_receipt_hash",
        "quote_pool_fingerprint",
        "quote_receipt_leg_index",
        "oracle_authorization",
    }
)

_KIND_INTENT_FIELD_KEYS = {
    IntentKind.SWAP_EXACT_IN: frozenset(
        {
            "pool_id",
            "asset_in",
            "asset_out",
            "amount_in",
            "min_amount_out",
        }
    ),
    IntentKind.SWAP_EXACT_OUT: frozenset(
        {
            "pool_id",
            "asset_in",
            "asset_out",
            "amount_out",
            "max_amount_in",
        }
    ),
    IntentKind.CREATE_POOL: frozenset(
        {
            "asset0",
            "asset1",
            "fee_bps",
            "amount0",
            "amount1",
            "created_at",
            "curve_tag",
            "curve_params",
        }
    ),
    IntentKind.ADD_LIQUIDITY: frozenset(
        {
            "pool_id",
            "amount0_desired",
            "amount1_desired",
            "amount0_min",
            "amount1_min",
        }
    ),
    IntentKind.REMOVE_LIQUIDITY: frozenset(
        {
            "pool_id",
            "lp_amount",
            "amount0_min",
            "amount1_min",
        }
    ),
    IntentKind.ROUTE_EXACT_IN: frozenset(
        {
            "asset_in",
            "asset_out",
            "leg_indices",
            "total_amount_in",
            "total_min_amount_out",
            # Engine-internal fields are listed here so user-supplied values
            # reach the route witness gate, where they are rejected with the
            # route-specific reserved-field error.
            "route_legs",
            "route_pool_fingerprints",
        }
    ),
    IntentKind.ROUTE_EXACT_OUT: frozenset(
        {
            "asset_in",
            "asset_out",
            "leg_indices",
            "total_amount_out",
            "total_max_amount_in",
            "route_legs",
            "route_pool_fingerprints",
        }
    ),
}


def _reject_unknown_intent_fields(fields: Dict[str, Any], *, intent_kind: IntentKind) -> None:
    allowed = _COMMON_INTENT_FIELD_KEYS | _KIND_INTENT_FIELD_KEYS.get(intent_kind, frozenset())
    unknown = sorted(set(fields) - allowed)
    if unknown:
        joined = ", ".join(unknown)
        raise ValueError(f"unsupported field for {intent_kind.value}: {joined}")


def _require_field(fields: Dict[str, Any], key: str, *, intent_kind: IntentKind) -> Any:
    if key not in fields:
        raise ValueError(f"Missing required field for {intent_kind.value}: {key}")
    return fields[key]


def _require_field_str(fields: Dict[str, Any], key: str, *, intent_kind: IntentKind, max_len: int = 256) -> str:
    return _require_str(
        _require_field(fields, key, intent_kind=intent_kind),
        name=f"intent.{key}",
        non_empty=True,
        max_len=max_len,
    )


def _require_field_int_range(
    fields: Dict[str, Any],
    key: str,
    *,
    intent_kind: IntentKind,
    minimum: int | None = None,
    maximum: int | None = None,
) -> int:
    return _require_int_range(
        _require_field(fields, key, intent_kind=intent_kind),
        name=f"intent.{key}",
        minimum=minimum,
        maximum=maximum,
    )


def _validate_common_intent_fields(fields: Dict[str, Any]) -> None:
    if "nonce" in fields:
        _require_int_range(fields["nonce"], name="intent.nonce", minimum=1, maximum=0xFFFFFFFF)
    if "recipient" in fields:
        _require_str(fields["recipient"], name="intent.recipient", non_empty=True, max_len=512)
    if "submission_order" in fields:
        _require_int_range(fields["submission_order"], name="intent.submission_order", minimum=0)
    if "quote_receipt_hash" in fields:
        _require_str(fields["quote_receipt_hash"], name="intent.quote_receipt_hash", non_empty=True, max_len=512)
    if "quote_pool_fingerprint" in fields:
        _require_str(fields["quote_pool_fingerprint"], name="intent.quote_pool_fingerprint", non_empty=True, max_len=512)
    if "quote_receipt_leg_index" in fields:
        _require_int_range(fields["quote_receipt_leg_index"], name="intent.quote_receipt_leg_index", minimum=0)
    if "oracle_authorization" in fields:
        _require_dict_str_keys(fields["oracle_authorization"], name="intent.oracle_authorization")


def _validate_swap_intent_fields(intent: Intent, fields: Dict[str, Any]) -> None:
    kind = intent.kind
    asset_in = _require_field_str(fields, "asset_in", intent_kind=kind)
    asset_out = _require_field_str(fields, "asset_out", intent_kind=kind)
    if asset_in == asset_out:
        raise ValueError("intent.asset_in and intent.asset_out must differ")
    _require_field_str(fields, "pool_id", intent_kind=kind)

    if kind == IntentKind.SWAP_EXACT_IN:
        _require_field_int_range(
            fields,
            "amount_in",
            intent_kind=kind,
            minimum=1,
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
        _require_field_int_range(
            fields,
            "min_amount_out",
            intent_kind=kind,
            minimum=0,
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
        return

    _require_field_int_range(
        fields,
        "amount_out",
        intent_kind=kind,
        minimum=1,
        maximum=DEX_SWAP_AMOUNT_MAX,
    )
    _require_field_int_range(
        fields,
        "max_amount_in",
        intent_kind=kind,
        minimum=1,
        maximum=DEX_SWAP_AMOUNT_MAX,
    )


def _validate_create_pool_intent_fields(intent: Intent, fields: Dict[str, Any]) -> None:
    kind = intent.kind
    asset0 = _require_field_str(fields, "asset0", intent_kind=kind)
    asset1 = _require_field_str(fields, "asset1", intent_kind=kind)
    try:
        asset0_norm, asset1_norm = normalize_pool_asset_pair(asset0, asset1)
    except Exception as exc:
        raise ValueError(f"intent assets must be in canonical order: {asset0} < {asset1}") from exc
    fields["asset0"] = asset0_norm
    fields["asset1"] = asset1_norm
    _require_field_int_range(
        fields,
        "fee_bps",
        intent_kind=kind,
        minimum=POOL_FEE_BPS_MIN,
        maximum=POOL_FEE_BPS_MAX,
    )
    _require_field_int_range(
        fields,
        "amount0",
        intent_kind=kind,
        minimum=1,
        maximum=DEX_LP_AMOUNT_MAX,
    )
    _require_field_int_range(
        fields,
        "amount1",
        intent_kind=kind,
        minimum=1,
        maximum=DEX_LP_AMOUNT_MAX,
    )
    if "created_at" in fields:
        _require_int_range(fields["created_at"], name="intent.created_at", minimum=0)
    try:
        normalize_curve_config(curve_tag=fields.get("curve_tag"), curve_params=fields.get("curve_params"))
    except Exception as exc:
        raise ValueError(f"invalid curve configuration: {exc}") from exc


def _validate_add_liquidity_intent_fields(intent: Intent, fields: Dict[str, Any]) -> None:
    kind = intent.kind
    _require_field_str(fields, "pool_id", intent_kind=kind)
    _require_field_int_range(
        fields,
        "amount0_desired",
        intent_kind=kind,
        minimum=1,
        maximum=DEX_LP_AMOUNT_MAX,
    )
    _require_field_int_range(
        fields,
        "amount1_desired",
        intent_kind=kind,
        minimum=1,
        maximum=DEX_LP_AMOUNT_MAX,
    )
    _require_field_int_range(
        fields,
        "amount0_min",
        intent_kind=kind,
        minimum=0,
        maximum=DEX_LP_AMOUNT_MAX,
    )
    _require_field_int_range(
        fields,
        "amount1_min",
        intent_kind=kind,
        minimum=0,
        maximum=DEX_LP_AMOUNT_MAX,
    )


def _validate_remove_liquidity_intent_fields(intent: Intent, fields: Dict[str, Any]) -> None:
    kind = intent.kind
    _require_field_str(fields, "pool_id", intent_kind=kind)
    _require_field_int_range(
        fields,
        "lp_amount",
        intent_kind=kind,
        minimum=1,
        maximum=DEX_LP_SUPPLY_MAX,
    )
    _require_field_int_range(
        fields,
        "amount0_min",
        intent_kind=kind,
        minimum=0,
        maximum=DEX_POOL_RESERVE_MAX,
    )
    _require_field_int_range(
        fields,
        "amount1_min",
        intent_kind=kind,
        minimum=0,
        maximum=DEX_POOL_RESERVE_MAX,
    )


def _validate_route_intent_fields(intent: Intent, fields: Dict[str, Any]) -> None:
    # Routes are receipt-bound by construction. The generic parser only
    # enforces basic JSON domain bounds; receipt coverage, duplicate leg
    # rejection, and reserved binding fields are checked by the engine witness
    # gate so errors stay tied to the validated quote receipt.
    kind = intent.kind
    if "quote_receipt_hash" in fields:
        _require_str(fields["quote_receipt_hash"], name="intent.quote_receipt_hash", non_empty=True, max_len=512)
    if "asset_in" in fields:
        _require_str(fields["asset_in"], name="intent.asset_in", non_empty=True, max_len=256)
    if "asset_out" in fields:
        _require_str(fields["asset_out"], name="intent.asset_out", non_empty=True, max_len=256)
    if "asset_in" in fields and "asset_out" in fields and fields["asset_in"] == fields["asset_out"]:
        raise ValueError("intent.asset_in and intent.asset_out must differ")
    if "leg_indices" in fields:
        leg_indices = fields["leg_indices"]
        if not isinstance(leg_indices, list) or not leg_indices:
            raise ValueError("intent.leg_indices must be a non-empty list")
        for idx in leg_indices:
            if not isinstance(idx, int) or isinstance(idx, bool) or idx < 0:
                raise ValueError("intent.leg_indices must contain non-negative ints")

    if kind == IntentKind.ROUTE_EXACT_IN:
        if "total_amount_in" in fields:
            _require_int_range(
                fields["total_amount_in"],
                name="intent.total_amount_in",
                minimum=1,
                maximum=DEX_SWAP_AMOUNT_MAX,
            )
        if "total_min_amount_out" in fields:
            _require_int_range(
                fields["total_min_amount_out"],
                name="intent.total_min_amount_out",
                minimum=0,
                maximum=DEX_SWAP_AMOUNT_MAX,
            )
        return

    if "total_amount_out" in fields:
        _require_int_range(
            fields["total_amount_out"],
            name="intent.total_amount_out",
            minimum=1,
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
    if "total_max_amount_in" in fields:
        _require_int_range(
            fields["total_max_amount_in"],
            name="intent.total_max_amount_in",
            minimum=0,
            maximum=DEX_SWAP_AMOUNT_MAX,
        )


def _validate_intent_fields(intent: Intent) -> None:
    """
    Validate the kind-specific normal form produced by the JSON parser.

    The state-layer `Intent` object stays intentionally generic for internal
    tests and generated fixtures. Parsed user operations must still enter the
    engine with all value-moving fields present, typed, and inside kernel
    domains.
    """
    fields = intent.fields or {}
    _reject_unknown_intent_fields(fields, intent_kind=intent.kind)
    _validate_common_intent_fields(fields)

    if intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        _validate_swap_intent_fields(intent, fields)
        return
    if intent.kind == IntentKind.CREATE_POOL:
        _validate_create_pool_intent_fields(intent, fields)
        return
    if intent.kind == IntentKind.ADD_LIQUIDITY:
        _validate_add_liquidity_intent_fields(intent, fields)
        return
    if intent.kind == IntentKind.REMOVE_LIQUIDITY:
        _validate_remove_liquidity_intent_fields(intent, fields)
        return
    if intent.kind in (IntentKind.ROUTE_EXACT_IN, IntentKind.ROUTE_EXACT_OUT):
        _validate_route_intent_fields(intent, fields)
        return
    raise ValueError(f"unsupported intent kind: {intent.kind}")


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

    raw_oracle_authorization = settlement_data.get("oracle_authorization")
    oracle_authorization = None
    if raw_oracle_authorization is not None:
        if not isinstance(raw_oracle_authorization, dict):
            raise ValueError("settlement oracle_authorization must be an object")
        oracle_authorization = raw_oracle_authorization

    raw_uniform_batch_certificate = settlement_data.get("uniform_batch_certificate")
    uniform_batch_certificate = None
    if raw_uniform_batch_certificate is not None:
        if not isinstance(raw_uniform_batch_certificate, dict):
            raise ValueError("settlement uniform_batch_certificate must be an object")
        uniform_batch_certificate = raw_uniform_batch_certificate

    raw_uniform_batch_optimality_certificate = settlement_data.get("uniform_batch_optimality_certificate")
    uniform_batch_optimality_certificate = None
    if raw_uniform_batch_optimality_certificate is not None:
        if not isinstance(raw_uniform_batch_optimality_certificate, dict):
            raise ValueError("settlement uniform_batch_optimality_certificate must be an object")
        uniform_batch_optimality_certificate = raw_uniform_batch_optimality_certificate

    raw_uniform_batch_v2_bounded_grid = settlement_data.get("uniform_batch_v2_bounded_grid")
    uniform_batch_v2_bounded_grid = None
    if raw_uniform_batch_v2_bounded_grid is not None:
        if not isinstance(raw_uniform_batch_v2_bounded_grid, dict):
            raise ValueError("settlement uniform_batch_v2_bounded_grid must be an object")
        uniform_batch_v2_bounded_grid = raw_uniform_batch_v2_bounded_grid

    raw_uniform_batch_v3_exact_out_grid = settlement_data.get("uniform_batch_v3_exact_out_grid")
    uniform_batch_v3_exact_out_grid = None
    if raw_uniform_batch_v3_exact_out_grid is not None:
        if not isinstance(raw_uniform_batch_v3_exact_out_grid, dict):
            raise ValueError("settlement uniform_batch_v3_exact_out_grid must be an object")
        uniform_batch_v3_exact_out_grid = raw_uniform_batch_v3_exact_out_grid

    settlement_data_no_proof = {
        k: v
        for k, v in settlement_data.items()
        if k
        not in (
            "proof",
            "zk_proof",
            "oracle_authorization",
            "uniform_batch_certificate",
            "uniform_batch_optimality_certificate",
            "uniform_batch_v2_bounded_grid",
            "uniform_batch_v3_exact_out_grid",
        )
    }
    settlement = _parse_settlement(settlement_data_no_proof)
    return SettlementEnvelope(
        settlement=settlement,
        proof=proof,
        oracle_authorization=oracle_authorization,
        uniform_batch_certificate=uniform_batch_certificate,
        uniform_batch_optimality_certificate=uniform_batch_optimality_certificate,
        uniform_batch_v2_bounded_grid=uniform_batch_v2_bounded_grid,
        uniform_batch_v3_exact_out_grid=uniform_batch_v3_exact_out_grid,
    )


def _parse_settlement(settlement_data: Dict[str, Any]) -> Settlement:
    """
    Parse settlement from dictionary.
    
    Args:
        settlement_data: Settlement dictionary
        
    Returns:
        Settlement object
    """
    settlement_data = _require_dict_str_keys(settlement_data, name="settlement")

    module = _require_str(settlement_data.get("module"), name="settlement.module", non_empty=True, max_len=64)
    if module != "TauSwap":
        raise ValueError(f"Invalid module: {module}")

    version = _require_str(settlement_data.get("version"), name="settlement.version", non_empty=True, max_len=64)
    if version != "0.1":
        raise ValueError(f"Invalid version: {version}")

    included_intents = _parse_included_intents(settlement_data.get("included_intents", []))
    fills = [_parse_fill(fill_data) for fill_data in _require_list_or_empty(settlement_data.get("fills", []), name="settlement.fills")]
    balance_deltas = [
        _parse_balance_delta(entry)
        for entry in _require_list_or_empty(settlement_data.get("balance_deltas", []), name="settlement.balance_deltas")
    ]
    reserve_deltas = [
        _parse_reserve_delta(entry)
        for entry in _require_list_or_empty(settlement_data.get("reserve_deltas", []), name="settlement.reserve_deltas")
    ]
    lp_deltas = [
        _parse_lp_delta(entry)
        for entry in _require_list_or_empty(settlement_data.get("lp_deltas", []), name="settlement.lp_deltas")
    ]

    batch_ref = settlement_data.get("batch_ref", "")
    if batch_ref is None:
        batch_ref = ""
    if not isinstance(batch_ref, str):
        raise ValueError("settlement.batch_ref must be a string")

    events = _parse_events(settlement_data.get("events"))
    
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
    reserved_keys = {
        "module",
        "version",
        "kind",
        "intent_id",
        "sender_pubkey",
        "deadline",
        "salt",
        "signature",
        "quote_receipt",
    }

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
                intent_dict[k] = deep_thaw_json(v)
        
        intents_data.append(intent_dict)
    
    return {"2": intents_data}


def create_signed_intent_operation(signed_intents: List[SignedIntentEnvelope]) -> Dict[str, Any]:
    """
    Create operations["2"] from signed intent envelopes, preserving transport-only
    metadata such as per-intent signatures and attached quote receipt witnesses.
    """
    base = create_intent_operation([env.intent for env in signed_intents])
    intents_data = base["2"]
    for entry, env in zip(intents_data, signed_intents, strict=True):
        if env.signature is not None:
            _require_str(env.signature, name="signature", non_empty=True, max_len=4096)
            entry["signature"] = env.signature
        if env.quote_receipt is not None:
            receipt = deep_thaw_json(env.quote_receipt)
            entry["quote_receipt"] = _parse_quote_receipt_transport(receipt, name="quote_receipt")
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
                "protocol_fee_paid": fill.protocol_fee_paid,
                "amount0_used": fill.amount0_used,
                "amount1_used": fill.amount1_used,
                "lp_minted": fill.lp_minted,
                "amount0_out": fill.amount0_out,
                "amount1_out": fill.amount1_out,
                "lp_burned": fill.lp_burned,
                "reserve_in_before": fill.reserve_in_before,
                "reserve_out_before": fill.reserve_out_before,
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

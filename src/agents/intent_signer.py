"""Intent creation and signing for autonomous agents."""

import hashlib
from collections.abc import Mapping
from typing import Any, Dict, Optional

from ..core.quote_receipts import pool_state_fingerprint
from ..integration.tau_net_client import sign_dex_intent_for_engine
from ..state.balances import Amount, AssetId, PubKey
from ..state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes, domain_sep_bytes
from ..state.immutable_collections import deep_thaw_json
from ..state.intents import Intent, IntentKind, SignedIntent

# For BLS12-381 signing (same as tau-testnet)
try:
    from py_ecc.bls import G2Basic
except ImportError:
    G2Basic = None


def _guardrail_severity(action: str) -> int:
    a = str(action or "").strip().lower()
    if a == "allow":
        return 0
    if a == "confirm":
        return 1
    if a == "typed_confirm":
        return 2
    if a == "block":
        return 3
    return 9


def _pool_reserves_for_swap(pool: Any, *, asset_in: str, asset_out: str) -> tuple[int, int] | None:
    if asset_in == getattr(pool, "asset0", None) and asset_out == getattr(pool, "asset1", None):
        return int(getattr(pool, "reserve0", 0)), int(getattr(pool, "reserve1", 0))
    if asset_in == getattr(pool, "asset1", None) and asset_out == getattr(pool, "asset0", None):
        return int(getattr(pool, "reserve1", 0)), int(getattr(pool, "reserve0", 0))
    return None


def _preflight_swap_pokayoke_exact_in_cpmm(
    *,
    pool: Any,
    asset_in: str,
    asset_out: str,
    amount_in: int,
    user_slippage_bps: int,
    pending_volume_same_direction: int = 0,
    confidence_bps: int = 9500,
    slippage_options_bps: Optional[list[int]] = None,
    max_attacker_amount_in: int = 2000,
) -> Any:
    # Import lazily to keep agent surfaces lightweight.
    from src.core.pokayoke_swap_guardrails import SwapGuardrailContext, decide_swap_guardrails
    from src.core.slippage_advisor import slippage_advice_exact_in_cpmm

    curve = str(getattr(pool, "curve_tag", "")).strip().upper()
    if curve != "CPMM":
        raise ValueError(f"pokayoke_unsupported_curve:{curve or 'unknown'}")

    reserves = _pool_reserves_for_swap(pool, asset_in=str(asset_in), asset_out=str(asset_out))
    if reserves is None:
        raise ValueError("pokayoke_bad_pool_direction")
    reserve_in, reserve_out = reserves

    # Ensure the user's slippage choice is included among evaluated options.
    opts = list(slippage_options_bps) if isinstance(slippage_options_bps, list) else [10, 50, 100, 300]
    opts.append(int(user_slippage_bps))

    advice = slippage_advice_exact_in_cpmm(
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
        fee_bps=int(getattr(pool, "fee_bps", 0)),
        amount_in=int(amount_in),
        pending_volume_same_direction=int(pending_volume_same_direction),
        confidence_bps=int(confidence_bps),
        slippage_options_bps=opts,
        max_attacker_amount_in=int(max_attacker_amount_in),
    )

    ctx = SwapGuardrailContext(
        price_impact_bps=int(advice.price_impact_bps),
        slippage_advice_status=str(advice.status),
        required_slippage_bps=int(advice.required_slippage_bps),
        recommended_slippage_bps_revert_safe=(
            int(advice.recommended_slippage_bps_revert_safe) if advice.recommended_slippage_bps_revert_safe is not None else None
        ),
        recommended_slippage_bps_mev_safe=(
            int(advice.recommended_slippage_bps_mev_safe) if advice.recommended_slippage_bps_mev_safe is not None else None
        ),
        recommended_slippage_bps=(int(advice.recommended_slippage_bps) if advice.recommended_slippage_bps is not None else None),
    )
    decision = decide_swap_guardrails(ctx=ctx, user_slippage_bps=int(user_slippage_bps))
    return advice, decision


def _enforce_pokayoke_max_action(*, decision: Any, max_action: str) -> None:
    max_sev = _guardrail_severity(str(max_action))
    got_sev = _guardrail_severity(str(getattr(decision, "action", "")))
    if got_sev > max_sev:
        reasons = getattr(decision, "reasons", ()) or ()
        raise ValueError(f"pokayoke_guardrail:{getattr(decision, 'action', 'unknown')}:{max_action}:{','.join(map(str, reasons))}")


def _quote_receipt_value_error(reason: str, **kwargs: Any) -> ValueError:
    details = ", ".join(f"{key}={value!r}" for key, value in kwargs.items() if value is not None)
    if not details:
        return ValueError(reason)
    return ValueError(f"{reason}: {details}")


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
    quote_receipt_hash: Optional[str] = None,
    quote_pool_fingerprint: Optional[str] = None,
    quote_receipt_leg_index: Optional[int] = None,
    nonce: Optional[int] = None,
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

    if quote_receipt_hash is not None:
        if not isinstance(quote_receipt_hash, str) or not quote_receipt_hash:
            raise ValueError("quote_receipt_hash must be a non-empty string")
        fields["quote_receipt_hash"] = quote_receipt_hash
    if quote_pool_fingerprint is not None:
        if not isinstance(quote_pool_fingerprint, str) or not quote_pool_fingerprint:
            raise ValueError("quote_pool_fingerprint must be a non-empty string")
        fields["quote_pool_fingerprint"] = quote_pool_fingerprint
    if quote_receipt_leg_index is not None:
        if (
            not isinstance(quote_receipt_leg_index, int)
            or isinstance(quote_receipt_leg_index, bool)
            or quote_receipt_leg_index < 0
        ):
            raise ValueError("quote_receipt_leg_index must be a non-negative int")
        fields["quote_receipt_leg_index"] = int(quote_receipt_leg_index)

    if nonce is not None:
        if not isinstance(nonce, int) or isinstance(nonce, bool) or nonce <= 0 or nonce > 0xFFFFFFFF:
            raise ValueError("nonce must be an int in [1, 2^32-1]")
        fields["nonce"] = int(nonce)
    
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


def create_swap_intent_from_quote_receipt(
    *,
    receipt: Dict[str, Any],
    pools_by_id: Dict[str, Any],
    sender_pubkey: PubKey,
    deadline: int,
    slippage_bps: int = 50,
    pokayoke_max_action: Optional[str] = None,
    pokayoke_pending_volume_same_direction: int = 0,
    pokayoke_confidence_bps: int = 9500,
    pokayoke_slippage_options_bps: Optional[list[int]] = None,
    pokayoke_max_attacker_amount_in: int = 2000,
    recipient: Optional[PubKey] = None,
    salt: Optional[str] = None,
) -> Intent:
    """
    Create a single-pool swap intent from a verified quote receipt.

    Restrictions:
    - Only supports receipts with exactly one leg and one hop (single pool).
    - Multi-hop/split receipts are rejected (future work: route intents).
    """
    if not isinstance(slippage_bps, int) or isinstance(slippage_bps, bool) or slippage_bps < 0 or slippage_bps > 10_000:
        raise ValueError("slippage_bps must be an int in [0, 10_000]")

    # Import lazily to avoid coupling agent code to routing modules unless used.
    from src.core.quote_receipts import verify_route_quote_receipt

    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools_by_id)
    if not ok:
        raise ValueError(f"invalid_quote_receipt:{err}")

    body = receipt.get("body", {})
    if not isinstance(body, dict):
        raise ValueError("invalid_quote_receipt_body")
    kind = str(body.get("kind", "")).strip().lower()
    if kind not in {"exact_in", "exact_out"}:
        raise ValueError("invalid_quote_receipt_kind")

    legs = body.get("legs")
    if not isinstance(legs, list) or len(legs) != 1:
        leg_count = len(legs) if isinstance(legs, list) else None
        raise _quote_receipt_value_error(
            "unsupported_multi_leg_receipt",
            leg_count=leg_count,
            guidance="use create_swap_intents_from_quote_receipt for split receipts",
        )
    hops = legs[0].get("hops") if isinstance(legs[0], dict) else None
    if not isinstance(hops, list) or len(hops) != 1:
        hop_count = len(hops) if isinstance(hops, list) else None
        raise _quote_receipt_value_error(
            "unsupported_multi_hop_receipt",
            leg_index=0,
            hop_count=hop_count,
            guidance="route-intent execution is not supported yet",
        )

    hop = hops[0]
    if not isinstance(hop, dict):
        raise ValueError("invalid_quote_receipt_hop")
    pool_id = str(hop.get("pool_id", "")).strip()
    asset_in = str(hop.get("asset_in", "")).strip()
    asset_out = str(hop.get("asset_out", "")).strip()
    if not pool_id or not asset_in or not asset_out or asset_in == asset_out:
        raise ValueError("invalid_quote_receipt_hop_fields")

    receipt_hash = receipt.get("receipt_hash")
    if not isinstance(receipt_hash, str) or not receipt_hash:
        raise ValueError("invalid_quote_receipt_hash")
    pool = pools_by_id.get(pool_id)
    if pool is None:
        raise _quote_receipt_value_error("missing_pool", pool_id=pool_id)
    quote_pool_fingerprint = pool_state_fingerprint(pool)

    if kind == "exact_in":
        amount_in = int(hop.get("amount_in", 0))
        amount_out_quote = int(hop.get("amount_out", 0))
        if amount_in <= 0 or amount_out_quote <= 0:
            raise _quote_receipt_value_error(
                "invalid_quote_receipt_amounts",
                kind=kind,
                pool_id=pool_id,
                amount_in=amount_in,
                amount_out=amount_out_quote,
            )
        # floor(amount_out_quote * (1 - s/10_000))
        min_amount_out = (int(amount_out_quote) * (10_000 - int(slippage_bps))) // 10_000

        if pokayoke_max_action is not None:
            pool = pools_by_id.get(pool_id)
            if pool is None:
                raise _quote_receipt_value_error("missing_pool", pool_id=pool_id)
            _, decision = _preflight_swap_pokayoke_exact_in_cpmm(
                pool=pool,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=int(amount_in),
                user_slippage_bps=int(slippage_bps),
                pending_volume_same_direction=int(pokayoke_pending_volume_same_direction),
                confidence_bps=int(pokayoke_confidence_bps),
                slippage_options_bps=pokayoke_slippage_options_bps,
                max_attacker_amount_in=int(pokayoke_max_attacker_amount_in),
            )
            _enforce_pokayoke_max_action(decision=decision, max_action=str(pokayoke_max_action))

        return create_swap_intent(
            pool_id=pool_id,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=int(amount_in),
            min_amount_out=int(min_amount_out),
            deadline=int(deadline),
            sender_pubkey=sender_pubkey,
            recipient=recipient,
            salt=salt,
            quote_receipt_hash=receipt_hash,
            quote_pool_fingerprint=quote_pool_fingerprint,
            quote_receipt_leg_index=0,
        )

    amount_out = int(hop.get("amount_out", 0))
    amount_in_quote = int(hop.get("amount_in", 0))
    if amount_out <= 0 or amount_in_quote <= 0:
        raise _quote_receipt_value_error(
            "invalid_quote_receipt_amounts",
            kind=kind,
            pool_id=pool_id,
            amount_in=amount_in_quote,
            amount_out=amount_out,
        )
    if pokayoke_max_action is not None:
        raise _quote_receipt_value_error("pokayoke_exact_out_unsupported", kind=kind, pool_id=pool_id)
    # ceil(amount_in_quote * (1 + s/10_000))
    max_amount_in = (int(amount_in_quote) * (10_000 + int(slippage_bps)) + 9_999) // 10_000
    return create_swap_intent(
        pool_id=pool_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=1,  # ignored for exact-out
        min_amount_out=0,  # ignored for exact-out
        deadline=int(deadline),
        sender_pubkey=sender_pubkey,
        exact_out=True,
        amount_out=int(amount_out),
        max_amount_in=int(max_amount_in),
        recipient=recipient,
        salt=salt,
        quote_receipt_hash=receipt_hash,
        quote_pool_fingerprint=quote_pool_fingerprint,
        quote_receipt_leg_index=0,
    )


def create_swap_intents_from_quote_receipt(
    *,
    receipt: Dict[str, Any],
    pools_by_id: Dict[str, Any],
    sender_pubkey: PubKey,
    deadline: int,
    slippage_bps: int = 50,
    pokayoke_max_action: Optional[str] = None,
    pokayoke_pending_volume_same_direction: int = 0,
    pokayoke_confidence_bps: int = 9500,
    pokayoke_slippage_options_bps: Optional[list[int]] = None,
    pokayoke_max_attacker_amount_in: int = 2000,
    recipient: Optional[PubKey] = None,
    salt: Optional[str] = None,
    nonce_start: Optional[int] = None,
) -> list[Intent]:
    """
    Create a list of swap intents from a verified quote receipt.

    Supported receipt shapes (current):
    - Multi-leg split routing where each leg has exactly one hop (parallel pools).
    - All legs share the same (asset_in, asset_out) as the receipt body.

    Not supported:
    - Multi-hop legs (route ordering is not enforced by batch clearing today).
    - Mixed asset pairs across legs.

    Nonces:
    - If nonce_start is provided, assign sequential u32 nonces in deterministic
      pool_id order (nonce_start, nonce_start+1, ...).
    """
    if not isinstance(slippage_bps, int) or isinstance(slippage_bps, bool) or slippage_bps < 0 or slippage_bps > 10_000:
        raise ValueError("slippage_bps must be an int in [0, 10_000]")
    if nonce_start is not None:
        if not isinstance(nonce_start, int) or isinstance(nonce_start, bool) or nonce_start <= 0 or nonce_start > 0xFFFFFFFF:
            raise ValueError("nonce_start must be an int in [1, 2^32-1]")

    from src.core.quote_receipts import verify_route_quote_receipt

    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools_by_id)
    if not ok:
        raise ValueError(f"invalid_quote_receipt:{err}")

    body = receipt.get("body", {})
    if not isinstance(body, dict):
        raise ValueError("invalid_quote_receipt_body")
    kind = str(body.get("kind", "")).strip().lower()
    if kind not in {"exact_in", "exact_out"}:
        raise ValueError("invalid_quote_receipt_kind")

    body_asset_in = str(body.get("asset_in", "")).strip()
    body_asset_out = str(body.get("asset_out", "")).strip()
    if not body_asset_in or not body_asset_out or body_asset_in == body_asset_out:
        raise ValueError("invalid_quote_receipt_assets")

    legs = body.get("legs")
    if not isinstance(legs, list) or not legs:
        raise ValueError("invalid_quote_receipt_legs")

    receipt_hash = receipt.get("receipt_hash")
    if not isinstance(receipt_hash, str) or not receipt_hash:
        raise ValueError("invalid_quote_receipt_hash")
    receipt_pools = body.get("pools")
    if not isinstance(receipt_pools, dict):
        raise ValueError("invalid_quote_receipt_pools")

    hop_rows: list[tuple[int, dict[str, Any]]] = []
    for leg_index, leg in enumerate(legs):
        if not isinstance(leg, dict):
            raise ValueError("invalid_quote_receipt_leg")
        hops = leg.get("hops")
        if not isinstance(hops, list) or len(hops) != 1:
            hop_count = len(hops) if isinstance(hops, list) else None
            raise _quote_receipt_value_error(
                "unsupported_multi_hop_receipt",
                leg_index=leg_index,
                hop_count=hop_count,
                guidance="route-intent execution is not supported yet",
            )
        hop = hops[0]
        if not isinstance(hop, dict):
            raise ValueError("invalid_quote_receipt_hop")
        hop_rows.append((int(leg_index), hop))

    if nonce_start is not None and int(nonce_start) + len(hop_rows) - 1 > 0xFFFFFFFF:
        raise _quote_receipt_value_error(
            "nonce_start_range_overflow",
            nonce_start=int(nonce_start),
            intent_count=len(hop_rows),
            max_nonce=0xFFFFFFFF,
        )

    # Canonicalize by pool_id to ensure deterministic intent list ordering and nonce assignment.
    hop_rows.sort(key=lambda item: (str(item[1].get("pool_id", "")), int(item[0])))

    intents: list[Intent] = []
    for i, (leg_index, hop) in enumerate(hop_rows):
        pool_id = str(hop.get("pool_id", "")).strip()
        asset_in = str(hop.get("asset_in", "")).strip()
        asset_out = str(hop.get("asset_out", "")).strip()
        if not pool_id or not asset_in or not asset_out or asset_in == asset_out:
            raise ValueError("invalid_quote_receipt_hop_fields")
        if asset_in != body_asset_in or asset_out != body_asset_out:
            raise _quote_receipt_value_error(
                "unsupported_mixed_asset_pairs",
                leg_index=leg_index,
                pool_id=pool_id,
                body_asset_in=body_asset_in,
                body_asset_out=body_asset_out,
                leg_asset_in=asset_in,
                leg_asset_out=asset_out,
            )
        quote_pool_fingerprint = receipt_pools.get(pool_id)
        if not isinstance(quote_pool_fingerprint, str) or not quote_pool_fingerprint:
            raise _quote_receipt_value_error(
                "missing_quote_pool_fingerprint",
                leg_index=leg_index,
                pool_id=pool_id,
            )

        nonce = None
        if nonce_start is not None:
            nonce = int(nonce_start) + int(i)

        if kind == "exact_in":
            amount_in = int(hop.get("amount_in", 0))
            amount_out_quote = int(hop.get("amount_out", 0))
            if amount_in <= 0 or amount_out_quote <= 0:
                raise _quote_receipt_value_error(
                    "invalid_quote_receipt_amounts",
                    kind=kind,
                    leg_index=leg_index,
                    pool_id=pool_id,
                    amount_in=amount_in,
                    amount_out=amount_out_quote,
                )
            min_amount_out = (int(amount_out_quote) * (10_000 - int(slippage_bps))) // 10_000

            if pokayoke_max_action is not None:
                pool = pools_by_id.get(pool_id)
                if pool is None:
                    raise _quote_receipt_value_error("missing_pool", pool_id=pool_id)
                _, decision = _preflight_swap_pokayoke_exact_in_cpmm(
                    pool=pool,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=int(amount_in),
                    user_slippage_bps=int(slippage_bps),
                    pending_volume_same_direction=int(pokayoke_pending_volume_same_direction),
                    confidence_bps=int(pokayoke_confidence_bps),
                    slippage_options_bps=pokayoke_slippage_options_bps,
                    max_attacker_amount_in=int(pokayoke_max_attacker_amount_in),
                )
                _enforce_pokayoke_max_action(decision=decision, max_action=str(pokayoke_max_action))

            intents.append(
                create_swap_intent(
                    pool_id=pool_id,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=int(amount_in),
                    min_amount_out=int(min_amount_out),
                    deadline=int(deadline),
                    sender_pubkey=sender_pubkey,
                    recipient=recipient,
                    salt=salt,
                    quote_receipt_hash=receipt_hash,
                    quote_pool_fingerprint=quote_pool_fingerprint,
                    quote_receipt_leg_index=int(leg_index),
                    nonce=nonce,
                )
            )
            continue

        amount_out = int(hop.get("amount_out", 0))
        amount_in_quote = int(hop.get("amount_in", 0))
        if amount_out <= 0 or amount_in_quote <= 0:
            raise _quote_receipt_value_error(
                "invalid_quote_receipt_amounts",
                kind=kind,
                leg_index=leg_index,
                pool_id=pool_id,
                amount_in=amount_in_quote,
                amount_out=amount_out,
            )
        if pokayoke_max_action is not None:
            raise _quote_receipt_value_error(
                "pokayoke_exact_out_unsupported",
                kind=kind,
                leg_index=leg_index,
                pool_id=pool_id,
            )
        max_amount_in = (int(amount_in_quote) * (10_000 + int(slippage_bps)) + 9_999) // 10_000
        intents.append(
            create_swap_intent(
                pool_id=pool_id,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=1,  # ignored for exact-out
                min_amount_out=0,  # ignored for exact-out
                deadline=int(deadline),
                sender_pubkey=sender_pubkey,
                exact_out=True,
                amount_out=int(amount_out),
                max_amount_in=int(max_amount_in),
                recipient=recipient,
                salt=salt,
                quote_receipt_hash=receipt_hash,
                quote_pool_fingerprint=quote_pool_fingerprint,
                quote_receipt_leg_index=int(leg_index),
                nonce=nonce,
            )
        )

    return intents


def _generate_intent_id(
    sender: PubKey,
    deadline: int,
    kind: str,
    fields: Dict[str, Any],
    salt: Optional[str],
) -> str:
    """
    Generate deterministic intent ID.
    
    Formula: H(sender || deadline || kind || canonical_json_bytes(fields) || salt)
    
    Args:
        sender: Sender public key
        deadline: Deadline timestamp
        kind: Intent kind
        fields: Intent fields
        salt: Optional salt
        
    Returns:
        32-byte hex string (0x...)
    """
    # Reuse the shared canonical encoder so every hash/signature input follows
    # the same scalar-value and float-rejection rules.
    canonical_json = canonical_json_bytes(fields)

    # Hash components
    data = (
        sender.encode('utf-8')
        + str(deadline).encode('utf-8')
        + kind.encode('utf-8')
        + canonical_json
    )
    
    if salt:
        data += salt.encode('utf-8')
    
    intent_id_hash = hashlib.sha256(data).hexdigest()
    return "0x" + intent_id_hash


def _intent_signing_dict(intent: Intent) -> dict[str, Any]:
    fields = intent.fields or {}
    if not isinstance(fields, Mapping):
        raise TypeError("intent.fields must be a mapping")
    out: dict[str, Any] = {
        "module": intent.module,
        "version": intent.version,
        "kind": intent.kind.value,
        "intent_id": intent.intent_id,
        "sender_pubkey": intent.sender_pubkey,
        "deadline": int(intent.deadline),
        "fields": deep_thaw_json(fields),
    }
    if intent.salt is not None:
        out["salt"] = intent.salt
    return out


def _intent_transport_dict(intent: Intent) -> dict[str, Any]:
    out: dict[str, Any] = {
        "module": intent.module,
        "version": intent.version,
        "kind": intent.kind.value,
        "intent_id": intent.intent_id,
        "sender_pubkey": intent.sender_pubkey,
        "deadline": int(intent.deadline),
    }
    if intent.salt is not None:
        out["salt"] = intent.salt
    if intent.fields:
        out.update(deep_thaw_json(intent.fields))
    return out


def sign_intent(
    intent: Intent,
    private_key: str | int | bytes | bytearray,
    *,
    chain_id: str = "tau-net-alpha",
) -> SignedIntent:
    """
    Sign an intent with BLS12-381 signature.
    
    Args:
        intent: Intent to sign
        private_key: BLS12-381 private key
        chain_id: Domain separator chain id used by the engine verifier
        
    Returns:
        SignedIntent object
        
    Raises:
        ImportError: If py_ecc is not available
    """
    if G2Basic is None:
        raise ImportError(
            "py_ecc not available. Install with: "
            "python3 -m pip install --require-hashes -r requirements-dev.lock.txt"
        )

    signature = sign_dex_intent_for_engine(
        _intent_transport_dict(intent),
        privkey=private_key,
        chain_id=chain_id,
    )
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
    return canonical_json_bytes(_intent_signing_dict(intent))


def verify_intent_signature(
    signed_intent: SignedIntent,
    *,
    chain_id: str = "tau-net-alpha",
) -> bool:
    """
    Verify intent signature.
    
    Args:
        signed_intent: Signed intent to verify
        
    Returns:
        True if signature is valid
        
    Raises:
        ImportError: If py_ecc is not available
    """
    if G2Basic is None:
        raise ImportError(
            "py_ecc not available. Install with: "
            "python3 -m pip install --require-hashes -r requirements-dev.lock.txt"
        )

    try:
        sender_pubkey = canonical_hex_fixed_allow_0x(
            signed_intent.intent.sender_pubkey,
            nbytes=48,
            name="sender_pubkey",
        )
        signature = canonical_hex_fixed_allow_0x(
            signed_intent.signature,
            nbytes=96,
            name="signature",
        )
        signing_payload = _create_canonical_message(signed_intent.intent)
        msg = domain_sep_bytes(f"dex_intent_sig:{chain_id}", version=1) + signing_payload
        msg_hash = hashlib.sha256(msg).digest()
        pubkey_bytes = bytes.fromhex(sender_pubkey[2:])
        signature_bytes = bytes.fromhex(signature[2:])
    except (TypeError, ValueError):
        return False
    return bool(G2Basic.Verify(pubkey_bytes, msg_hash, signature_bytes))

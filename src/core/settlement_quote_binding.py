"""Quote receipt binding checks for strong settlement validation.

Quote receipt fields cross the engine-to-core boundary. Raw transport metadata
must be stripped unless the engine has already validated the witness and passed
only the sanitized pool snapshot binding into the strong validator.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from ..state.intents import Intent, IntentKind
from .domain_limits import is_strict_int


def _format_error_details(**kwargs: object) -> str:
    parts: list[str] = []
    for key, value in kwargs.items():
        if value is None:
            continue
        parts.append(f"{key}={value!r}")
    return ", ".join(parts)


def quote_binding_error(reason: str, **kwargs: object) -> str:
    details = _format_error_details(**kwargs)
    if not details:
        return reason
    return f"{reason}: {details}"


def quote_binding_context(intent: Intent) -> dict[str, object]:
    return {
        "intent_id": intent.intent_id,
        "quote_hash": intent.get_field("quote_receipt_hash"),
        "quote_pool_fingerprint": intent.get_field("quote_pool_fingerprint"),
        "leg_index": intent.get_field("quote_receipt_leg_index"),
        "pool_id": intent.get_field("pool_id"),
    }


@dataclass(frozen=True)
class _QuoteBindingFields:
    receipt_hash: object
    pool_fingerprint: object
    leg_index: object


def _quote_binding_fields(intent: Intent) -> _QuoteBindingFields:
    return _QuoteBindingFields(
        receipt_hash=intent.get_field("quote_receipt_hash"),
        pool_fingerprint=intent.get_field("quote_pool_fingerprint"),
        leg_index=intent.get_field("quote_receipt_leg_index"),
    )


def _has_quote_binding(fields: _QuoteBindingFields) -> bool:
    return fields.receipt_hash is not None or fields.pool_fingerprint is not None or fields.leg_index is not None


def _validate_quote_binding_kind(intent: Intent, fields: _QuoteBindingFields) -> Optional[str]:
    if not _has_quote_binding(fields) or intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        return None
    return quote_binding_error(
        "quote receipt binding only supported for swap intents",
        **quote_binding_context(intent),
        intent_kind=intent.kind.value,
    )


def _validate_quote_leg_index_transport(intent: Intent, fields: _QuoteBindingFields) -> Optional[str]:
    if fields.leg_index is None:
        return None
    if not is_strict_int(fields.leg_index) or int(fields.leg_index) < 0:
        return quote_binding_error("invalid quote_receipt_leg_index", **quote_binding_context(intent))
    return quote_binding_error(
        "quote receipt transport metadata requires validated engine witness",
        **quote_binding_context(intent),
        guidance="strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation",
    )


def _validate_quote_receipt_hash_transport(intent: Intent, fields: _QuoteBindingFields) -> Optional[str]:
    if fields.receipt_hash is None:
        return None
    if not isinstance(fields.receipt_hash, str) or not fields.receipt_hash:
        return quote_binding_error("invalid quote_receipt_hash", **quote_binding_context(intent))
    return quote_binding_error(
        "quote receipt transport metadata requires validated engine witness",
        **quote_binding_context(intent),
        guidance="strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation",
    )


def _validate_quote_pool_fingerprint_transport(
    intent: Intent,
    fields: _QuoteBindingFields,
    *,
    allow_snapshot_bound_quote_bindings: bool,
) -> Optional[str]:
    if fields.pool_fingerprint is None:
        return None
    if not isinstance(fields.pool_fingerprint, str) or not fields.pool_fingerprint:
        return quote_binding_error("missing quote_pool_fingerprint", **quote_binding_context(intent))
    if not allow_snapshot_bound_quote_bindings:
        return quote_binding_error(
            "quote receipt snapshot binding requires validated engine witness",
            **quote_binding_context(intent),
            guidance="only pass sanitized quote_pool_fingerprint through the validated engine path",
        )
    return None


def validate_quote_binding_transport(
    intent: Intent,
    *,
    allow_snapshot_bound_quote_bindings: bool,
) -> Optional[str]:
    fields = _quote_binding_fields(intent)
    for validator in (
        _validate_quote_binding_kind,
        _validate_quote_leg_index_transport,
        _validate_quote_receipt_hash_transport,
    ):
        error = validator(intent, fields)
        if error is not None:
            return error
    error = _validate_quote_pool_fingerprint_transport(
        intent,
        fields,
        allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
    )
    if error is not None:
        return error
    return None

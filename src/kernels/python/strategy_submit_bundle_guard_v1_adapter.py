from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass

from ...agents.intent_signer import verify_intent_signature
from ...integration.operations import SignedIntentEnvelope, parse_signed_intents
from ...integration.tau_net_rpc import (
    encode_tau_operations_for_wire,
    verify_tau_transaction_payload_signature,
)
from ...state.intents import SignedIntent


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_chain_id(value: object) -> str:
    if not isinstance(value, str):
        raise TypeError("chain_id must be a string")
    text = value.strip()
    if not text:
        raise ValueError("chain_id must be non-empty")
    return text


def _require_pubkey(value: object) -> str:
    if not isinstance(value, str):
        raise TypeError("signer_pubkey must be a string")
    text = value.strip()
    if not text:
        raise ValueError("signer_pubkey must be non-empty")
    return text


def _normalize_hexish(value: object) -> str | None:
    if not isinstance(value, str):
        return None
    text = value.strip()
    if not text:
        return None
    if text.lower().startswith("0x"):
        text = text[2:]
    return text.lower()


def _require_signed_intents(value: object) -> tuple[SignedIntentEnvelope, ...]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError("signed_intents must be a sequence of SignedIntentEnvelope")
    out: list[SignedIntentEnvelope] = []
    for env in value:
        if not isinstance(env, SignedIntentEnvelope):
            raise TypeError("signed_intents must contain SignedIntentEnvelope items")
        out.append(env)
    return tuple(out)


def _quote_receipt_hash(value: object) -> str | None:
    if not isinstance(value, Mapping):
        return None
    receipt_hash = value.get("receipt_hash")
    if not isinstance(receipt_hash, str) or not receipt_hash:
        return None
    return receipt_hash


def _verify_signed_intent_bundle(
    *,
    signed_intents: tuple[SignedIntentEnvelope, ...],
    operations: Mapping[str, object],
    chain_id: str,
    signer_pubkey: str,
) -> tuple[bool, bool, bool, bool, bool]:
    signatures_present = all(
        isinstance(env.signature, str) and env.signature.strip() for env in signed_intents
    )
    if signatures_present:
        verified_flags: list[bool] = []
        for env in signed_intents:
            try:
                verified_flags.append(
                    verify_intent_signature(
                        SignedIntent(intent=env.intent, signature=str(env.signature)),
                        chain_id=chain_id,
                    )
                )
            except (ImportError, ValueError):
                verified_flags.append(False)
        signatures_verify = all(verified_flags)
    else:
        signatures_verify = False
    sender_binding_ok = all(env.intent.sender_pubkey == signer_pubkey for env in signed_intents)
    quote_receipts_present = all(_quote_receipt_hash(env.quote_receipt) is not None for env in signed_intents)
    try:
        parsed = parse_signed_intents(dict(operations))
    except ValueError:
        operations_roundtrip_ok = False
    else:
        operations_roundtrip_ok = len(parsed) == len(signed_intents) and all(
            parsed_env.intent.intent_id == env.intent.intent_id
            and parsed_env.intent.sender_pubkey == env.intent.sender_pubkey
            and parsed_env.signature == env.signature
            and _quote_receipt_hash(parsed_env.quote_receipt) == _quote_receipt_hash(env.quote_receipt)
            for parsed_env, env in zip(parsed, signed_intents, strict=True)
        )
    return (
        signatures_present,
        signatures_verify,
        sender_binding_ok,
        quote_receipts_present,
        operations_roundtrip_ok,
    )


def _tx_payload_matches(
    *,
    tx_requested: bool,
    tau_tx_payload: Mapping[str, object] | None,
    operations: Mapping[str, object],
    signer_pubkey: str,
    sequence_number: object,
    expiration_time: object,
    fee_limit: object,
) -> bool:
    if not tx_requested:
        return tau_tx_payload is None
    if not isinstance(tau_tx_payload, Mapping):
        return False
    if _normalize_hexish(tau_tx_payload.get("sender_pubkey")) != _normalize_hexish(signer_pubkey):
        return False
    if tau_tx_payload.get("sequence_number") != sequence_number:
        return False
    if tau_tx_payload.get("expiration_time") != expiration_time:
        return False
    if tau_tx_payload.get("fee_limit") != str(fee_limit):
        return False
    try:
        expected_ops = encode_tau_operations_for_wire(operations)
    except (TypeError, ValueError):
        return False
    if tau_tx_payload.get("operations") != expected_ops:
        return False
    signature = tau_tx_payload.get("signature")
    if not isinstance(signature, str) or not signature.strip():
        return False
    return verify_tau_transaction_payload_signature(tau_tx_payload)


@dataclass(frozen=True)
class StrategySubmitBundleGuardResult:
    ok: bool
    emit_requested: bool
    signed_intents_present: bool
    signatures_present: bool
    signatures_verify: bool
    sender_binding_ok: bool
    quote_receipts_present: bool
    operations_roundtrip_ok: bool
    tx_payload_ok: bool
    error: str | None = None


def check_strategy_submit_bundle(
    *,
    emit_requested: bool,
    signed_intents: Sequence[SignedIntentEnvelope],
    operations: Mapping[str, object],
    chain_id: str,
    signer_pubkey: str,
    tx_requested: bool,
    sequence_number: object = None,
    expiration_time: object = None,
    fee_limit: object = "0",
    tau_tx_payload: Mapping[str, object] | None = None,
) -> StrategySubmitBundleGuardResult:
    emit_requested = _require_bool("emit_requested", emit_requested)
    tx_requested = _require_bool("tx_requested", tx_requested)
    signed_intents_tuple = _require_signed_intents(signed_intents)
    if not isinstance(operations, Mapping):
        raise TypeError("operations must be a mapping")
    chain_id = _require_chain_id(chain_id)
    signer_pubkey = _require_pubkey(signer_pubkey)

    signed_intents_present = len(signed_intents_tuple) > 0
    (
        signatures_present,
        signatures_verify,
        sender_binding_ok,
        quote_receipts_present,
        operations_roundtrip_ok,
    ) = _verify_signed_intent_bundle(
        signed_intents=signed_intents_tuple,
        operations=operations,
        chain_id=chain_id,
        signer_pubkey=signer_pubkey,
    )
    tx_payload_ok = _tx_payload_matches(
        tx_requested=tx_requested,
        tau_tx_payload=tau_tx_payload,
        operations=operations,
        signer_pubkey=signer_pubkey,
        sequence_number=sequence_number,
        expiration_time=expiration_time,
        fee_limit=fee_limit,
    )

    if not emit_requested:
        unexpected_artifacts = signed_intents_present or bool(operations) or tau_tx_payload is not None
        error = "submit_bundle_unexpected_artifacts" if unexpected_artifacts else None
        return StrategySubmitBundleGuardResult(
            ok=error is None,
            emit_requested=False,
            signed_intents_present=signed_intents_present,
            signatures_present=signatures_present,
            signatures_verify=signatures_verify,
            sender_binding_ok=sender_binding_ok,
            quote_receipts_present=quote_receipts_present,
            operations_roundtrip_ok=operations_roundtrip_ok,
            tx_payload_ok=tx_payload_ok,
            error=error,
        )

    if not signed_intents_present:
        error = "submit_bundle_missing_signed_intents"
    elif not signatures_present:
        error = "submit_bundle_missing_signature"
    elif not signatures_verify:
        error = "submit_bundle_signature_invalid"
    elif not sender_binding_ok:
        error = "submit_bundle_sender_mismatch"
    elif not quote_receipts_present:
        error = "submit_bundle_missing_quote_receipt"
    elif not operations_roundtrip_ok:
        error = "submit_bundle_operations_roundtrip_rejected"
    elif not tx_payload_ok:
        error = "submit_bundle_tx_payload_rejected"
    else:
        error = None

    return StrategySubmitBundleGuardResult(
        ok=error is None,
        emit_requested=True,
        signed_intents_present=signed_intents_present,
        signatures_present=signatures_present,
        signatures_verify=signatures_verify,
        sender_binding_ok=sender_binding_ok,
        quote_receipts_present=quote_receipts_present,
        operations_roundtrip_ok=operations_roundtrip_ok,
        tx_payload_ok=tx_payload_ok,
        error=error,
    )

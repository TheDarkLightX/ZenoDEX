from __future__ import annotations

import json

import pytest

from src.agents.intent_signer import create_swap_intent, sign_intent
from src.integration.operations import SignedIntentEnvelope, create_signed_intent_operation
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, build_signed_tau_transaction
from src.kernels.python import strategy_submit_bundle_guard_v1_adapter
from src.kernels.python.strategy_submit_bundle_guard_v1_adapter import check_strategy_submit_bundle
from src.state.intents import Intent, IntentKind


def _signed_bundle(*, privkey: int = 7) -> tuple[str, tuple[SignedIntentEnvelope, ...], dict[str, object]]:
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    intent = create_swap_intent(
        pool_id="pool.ab",
        asset_in="A",
        asset_out="B",
        amount_in=100,
        min_amount_out=1,
        deadline=99,
        sender_pubkey=signer_pubkey,
        nonce=1,
    )
    signature = sign_intent(intent, privkey, chain_id="tau-local").signature
    signed_intents = (
        SignedIntentEnvelope(
            intent=intent,
            signature=signature,
            quote_receipt={"body": {}, "receipt_hash": "hash.alpha"},
        ),
    )
    operations = create_signed_intent_operation(list(signed_intents))
    return signer_pubkey, signed_intents, operations


def test_check_strategy_submit_bundle_accepts_signed_bundle_without_tx() -> None:
    signer_pubkey, signed_intents, operations = _signed_bundle()
    result = check_strategy_submit_bundle(
        emit_requested=True,
        signed_intents=signed_intents,
        operations=operations,
        chain_id="tau-local",
        signer_pubkey=signer_pubkey,
        tx_requested=False,
    )
    assert result.ok is True
    assert result.error is None


def test_check_strategy_submit_bundle_accepts_signed_bundle_with_tx() -> None:
    signer_pubkey, signed_intents, operations = _signed_bundle()
    tau_tx_payload = build_signed_tau_transaction(
        privkey=7,
        sequence_number=9,
        expiration_time=999,
        operations=operations,
        fee_limit="0",
    )
    result = check_strategy_submit_bundle(
        emit_requested=True,
        signed_intents=signed_intents,
        operations=operations,
        chain_id="tau-local",
        signer_pubkey=signer_pubkey,
        tx_requested=True,
        sequence_number=9,
        expiration_time=999,
        fee_limit="0",
        tau_tx_payload=tau_tx_payload,
    )
    assert result.ok is True
    assert result.tx_payload_ok is True


def test_check_strategy_submit_bundle_preserves_nested_signing_parity_and_rejects_mutation() -> None:
    privkey = 11
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "39" * 32,
        sender_pubkey=signer_pubkey,
        deadline=99,
        fields={
            "nonce": 1,
            "route": {
                "assets": ["A", "B"],
                "limits": {"amount_in": 7, "min_amount_out": 6},
            },
        },
    )
    signature = sign_intent(intent, privkey, chain_id="tau-local").signature
    envelope = SignedIntentEnvelope(
        intent=intent,
        signature=signature,
        quote_receipt={"body": {}, "receipt_hash": "hash.nested"},
    )
    operations = create_signed_intent_operation([envelope])

    accepted = check_strategy_submit_bundle(
        emit_requested=True,
        signed_intents=(envelope,),
        operations=operations,
        chain_id="tau-local",
        signer_pubkey=signer_pubkey,
        tx_requested=False,
    )
    mutated = intent.with_field(
        "route",
        {
            "assets": ["A", "B"],
            "limits": {"amount_in": 8, "min_amount_out": 6},
        },
    )
    mutated_envelope = SignedIntentEnvelope(
        intent=mutated,
        signature=signature,
        quote_receipt=envelope.quote_receipt,
    )
    rejected = check_strategy_submit_bundle(
        emit_requested=True,
        signed_intents=(mutated_envelope,),
        operations=create_signed_intent_operation([mutated_envelope]),
        chain_id="tau-local",
        signer_pubkey=signer_pubkey,
        tx_requested=False,
    )

    json.dumps(operations, sort_keys=True)
    assert accepted.ok is True
    assert accepted.error is None
    assert rejected.ok is False
    assert rejected.error == "submit_bundle_signature_invalid"


def test_check_strategy_submit_bundle_rejects_independently_mutated_nested_operations() -> None:
    """RIPR: signed envelope and emitted operations must bind the same full intent."""

    privkey = 13
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "4a" * 32,
        sender_pubkey=signer_pubkey,
        deadline=99,
        fields={
            "nonce": 1,
            "route": {
                "assets": ["A", "B"],
                "limits": {"amount_in": 7, "min_amount_out": 6},
            },
        },
    )
    signature = sign_intent(intent, privkey, chain_id="tau-local").signature
    envelope = SignedIntentEnvelope(
        intent=intent,
        signature=signature,
        quote_receipt={"body": {}, "receipt_hash": "hash.nested-independent"},
    )
    mutated_intent = intent.with_field(
        "route",
        {
            "assets": ["A", "B"],
            "limits": {"amount_in": 8, "min_amount_out": 6},
        },
    )
    mutated_operations = create_signed_intent_operation(
        [
            SignedIntentEnvelope(
                intent=mutated_intent,
                signature=signature,
                quote_receipt=envelope.quote_receipt,
            )
        ]
    )

    result = check_strategy_submit_bundle(
        emit_requested=True,
        signed_intents=(envelope,),
        operations=mutated_operations,
        chain_id="tau-local",
        signer_pubkey=signer_pubkey,
        tx_requested=False,
    )

    assert result.ok is False
    assert result.operations_roundtrip_ok is False
    assert result.error == "submit_bundle_operations_roundtrip_rejected"


@pytest.mark.parametrize(
    ("signed_intents", "operations", "signer_pubkey", "tx_requested", "tau_tx_payload", "error"),
    [
        ((), {}, "0xabc", False, None, "submit_bundle_missing_signed_intents"),
        (
            lambda bundle: (SignedIntentEnvelope(intent=bundle[1][0].intent, signature=None, quote_receipt=bundle[1][0].quote_receipt),),
            lambda bundle: create_signed_intent_operation([SignedIntentEnvelope(intent=bundle[1][0].intent, signature=None, quote_receipt=bundle[1][0].quote_receipt)]),
            lambda bundle: bundle[0],
            False,
            None,
            "submit_bundle_missing_signature",
        ),
        (
            lambda bundle: (SignedIntentEnvelope(intent=bundle[1][0].intent, signature="0x00", quote_receipt=bundle[1][0].quote_receipt),),
            lambda bundle: create_signed_intent_operation([SignedIntentEnvelope(intent=bundle[1][0].intent, signature="0x00", quote_receipt=bundle[1][0].quote_receipt)]),
            lambda bundle: bundle[0],
            False,
            None,
            "submit_bundle_signature_invalid",
        ),
        (
            lambda bundle: bundle[1],
            lambda bundle: bundle[2],
            lambda bundle: "0x" + bls_pubkey_hex_from_privkey(999),
            False,
            None,
            "submit_bundle_sender_mismatch",
        ),
        (
            lambda bundle: (SignedIntentEnvelope(intent=bundle[1][0].intent, signature=bundle[1][0].signature, quote_receipt=None),),
            lambda bundle: create_signed_intent_operation([SignedIntentEnvelope(intent=bundle[1][0].intent, signature=bundle[1][0].signature, quote_receipt=None)]),
            lambda bundle: bundle[0],
            False,
            None,
            "submit_bundle_missing_quote_receipt",
        ),
        (
            lambda bundle: bundle[1],
            lambda bundle: {"2": "bad"},
            lambda bundle: bundle[0],
            False,
            None,
            "submit_bundle_operations_roundtrip_rejected",
        ),
        (
            lambda bundle: bundle[1],
            lambda bundle: bundle[2],
            lambda bundle: bundle[0],
            True,
            None,
            "submit_bundle_tx_payload_rejected",
        ),
    ],
)
def test_check_strategy_submit_bundle_rejects_invalid_artifacts(
    signed_intents,
    operations,
    signer_pubkey,
    tx_requested: bool,
    tau_tx_payload,
    error: str,
) -> None:
    bundle = _signed_bundle()
    resolved_signed_intents = signed_intents(bundle) if callable(signed_intents) else signed_intents
    resolved_operations = operations(bundle) if callable(operations) else operations
    resolved_signer_pubkey = signer_pubkey(bundle) if callable(signer_pubkey) else signer_pubkey
    result = check_strategy_submit_bundle(
        emit_requested=True,
        signed_intents=resolved_signed_intents,
        operations=resolved_operations,
        chain_id="tau-local",
        signer_pubkey=resolved_signer_pubkey,
        tx_requested=tx_requested,
        sequence_number=9 if tx_requested else None,
        expiration_time=999 if tx_requested else None,
        fee_limit="0",
        tau_tx_payload=tau_tx_payload,
    )
    assert result.ok is False
    assert result.error == error


def test_check_strategy_submit_bundle_rejects_unexpected_artifacts_when_emit_not_requested() -> None:
    signer_pubkey, signed_intents, operations = _signed_bundle()
    result = check_strategy_submit_bundle(
        emit_requested=False,
        signed_intents=signed_intents,
        operations=operations,
        chain_id="tau-local",
        signer_pubkey=signer_pubkey,
        tx_requested=False,
    )
    assert result.ok is False
    assert result.error == "submit_bundle_unexpected_artifacts"


def test_check_strategy_submit_bundle_rejects_bad_types() -> None:
    signer_pubkey, signed_intents, operations = _signed_bundle()
    with pytest.raises(TypeError, match="emit_requested must be a bool"):
        check_strategy_submit_bundle(
            emit_requested=1,
            signed_intents=signed_intents,
            operations=operations,
            chain_id="tau-local",
            signer_pubkey=signer_pubkey,
            tx_requested=False,
        )
    with pytest.raises(TypeError, match="signed_intents must be a sequence of SignedIntentEnvelope"):
        check_strategy_submit_bundle(
            emit_requested=True,
            signed_intents="bad",
            operations=operations,
            chain_id="tau-local",
            signer_pubkey=signer_pubkey,
            tx_requested=False,
        )
    with pytest.raises(ValueError, match="chain_id must be non-empty"):
        check_strategy_submit_bundle(
            emit_requested=True,
            signed_intents=signed_intents,
            operations=operations,
            chain_id=" ",
            signer_pubkey=signer_pubkey,
            tx_requested=False,
        )


def test_check_strategy_submit_bundle_rejects_additional_type_edges() -> None:
    signer_pubkey, signed_intents, operations = _signed_bundle()
    with pytest.raises(TypeError, match="signer_pubkey must be a string"):
        check_strategy_submit_bundle(
            emit_requested=True,
            signed_intents=signed_intents,
            operations=operations,
            chain_id="tau-local",
            signer_pubkey=object(),  # type: ignore[arg-type]
            tx_requested=False,
        )
    with pytest.raises(ValueError, match="signer_pubkey must be non-empty"):
        check_strategy_submit_bundle(
            emit_requested=True,
            signed_intents=signed_intents,
            operations=operations,
            chain_id="tau-local",
            signer_pubkey=" ",
            tx_requested=False,
        )
    with pytest.raises(TypeError, match="chain_id must be a string"):
        check_strategy_submit_bundle(
            emit_requested=True,
            signed_intents=signed_intents,
            operations=operations,
            chain_id=object(),  # type: ignore[arg-type]
            signer_pubkey=signer_pubkey,
            tx_requested=False,
        )
    with pytest.raises(TypeError, match="signed_intents must contain SignedIntentEnvelope items"):
        check_strategy_submit_bundle(
            emit_requested=True,
            signed_intents=(object(),),  # type: ignore[arg-type]
            operations=operations,
            chain_id="tau-local",
            signer_pubkey=signer_pubkey,
            tx_requested=False,
        )
    with pytest.raises(TypeError, match="operations must be a mapping"):
        check_strategy_submit_bundle(
            emit_requested=True,
            signed_intents=signed_intents,
            operations=(),  # type: ignore[arg-type]
            chain_id="tau-local",
            signer_pubkey=signer_pubkey,
            tx_requested=False,
        )


@pytest.mark.parametrize(
    ("tau_tx_payload", "operations"),
    [
        (
            lambda bundle: {
                **build_signed_tau_transaction(
                    privkey=7,
                    sequence_number=9,
                    expiration_time=999,
                    operations=bundle[2],
                    fee_limit="0",
                ),
                "sender_pubkey": "deadbeef",
            },
            lambda bundle: bundle[2],
        ),
        (
            lambda bundle: {
                **build_signed_tau_transaction(
                    privkey=7,
                    sequence_number=9,
                    expiration_time=999,
                    operations=bundle[2],
                    fee_limit="0",
                ),
                "sequence_number": 10,
            },
            lambda bundle: bundle[2],
        ),
        (
            lambda bundle: {
                **build_signed_tau_transaction(
                    privkey=7,
                    sequence_number=9,
                    expiration_time=999,
                    operations=bundle[2],
                    fee_limit="0",
                ),
                "expiration_time": 1000,
            },
            lambda bundle: bundle[2],
        ),
        (
            lambda bundle: {
                **build_signed_tau_transaction(
                    privkey=7,
                    sequence_number=9,
                    expiration_time=999,
                    operations=bundle[2],
                    fee_limit="0",
                ),
                "fee_limit": "1",
            },
            lambda bundle: bundle[2],
        ),
        (
            lambda bundle: {
                **build_signed_tau_transaction(
                    privkey=7,
                    sequence_number=9,
                    expiration_time=999,
                    operations=bundle[2],
                    fee_limit="0",
                ),
                "signature": "",
            },
            lambda bundle: bundle[2],
        ),
        (
            lambda bundle: {
                **build_signed_tau_transaction(
                    privkey=7,
                    sequence_number=9,
                    expiration_time=999,
                    operations=bundle[2],
                    fee_limit="0",
                ),
                "signature": "zz",
            },
            lambda bundle: bundle[2],
        ),
    ],
)
def test_check_strategy_submit_bundle_rejects_tx_payload_edge_mismatches(
    tau_tx_payload,
    operations,
) -> None:
    bundle = _signed_bundle()
    resolved_payload = tau_tx_payload(bundle) if callable(tau_tx_payload) else tau_tx_payload
    resolved_operations = operations(bundle) if callable(operations) else operations
    result = check_strategy_submit_bundle(
        emit_requested=True,
        signed_intents=bundle[1],
        operations=resolved_operations,
        chain_id="tau-local",
        signer_pubkey=bundle[0],
        tx_requested=True,
        sequence_number=9,
        expiration_time=999,
        fee_limit="0",
        tau_tx_payload=resolved_payload,
    )
    assert result.ok is False
    assert result.error == "submit_bundle_tx_payload_rejected"


def test_check_strategy_submit_bundle_rejects_quote_receipt_without_hash() -> None:
    signer_pubkey, signed_intents, _operations = _signed_bundle()
    signed_intents = (
        SignedIntentEnvelope(
            intent=signed_intents[0].intent,
            signature=signed_intents[0].signature,
            quote_receipt={"body": {}},
        ),
    )
    result = check_strategy_submit_bundle(
        emit_requested=True,
        signed_intents=signed_intents,
        operations=_operations,
        chain_id="tau-local",
        signer_pubkey=signer_pubkey,
        tx_requested=False,
    )
    assert result.ok is False
    assert result.error == "submit_bundle_missing_quote_receipt"


def test_check_strategy_submit_bundle_helper_edges(monkeypatch: pytest.MonkeyPatch) -> None:
    assert strategy_submit_bundle_guard_v1_adapter._normalize_hexish(object()) is None
    assert strategy_submit_bundle_guard_v1_adapter._normalize_hexish(" ") is None
    assert strategy_submit_bundle_guard_v1_adapter._quote_receipt_hash({"body": {}}) is None

    signer_pubkey, signed_intents, operations = _signed_bundle()
    monkeypatch.setattr(
        strategy_submit_bundle_guard_v1_adapter,
        "encode_tau_operations_for_wire",
        lambda _ops: (_ for _ in ()).throw(ValueError("bad ops")),
    )
    result = check_strategy_submit_bundle(
        emit_requested=True,
        signed_intents=signed_intents,
        operations=operations,
        chain_id="tau-local",
        signer_pubkey=signer_pubkey,
        tx_requested=True,
        sequence_number=9,
        expiration_time=999,
        fee_limit="0",
        tau_tx_payload=build_signed_tau_transaction(
            privkey=7,
            sequence_number=9,
            expiration_time=999,
            operations=operations,
            fee_limit="0",
        ),
    )
    assert result.ok is False
    assert result.error == "submit_bundle_tx_payload_rejected"


def test_check_strategy_submit_bundle_propagates_signature_verifier_bug(monkeypatch: pytest.MonkeyPatch) -> None:
    signer_pubkey, signed_intents, operations = _signed_bundle()

    def _bug(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("signature verifier bug")

    monkeypatch.setattr(strategy_submit_bundle_guard_v1_adapter, "verify_intent_signature", _bug)

    with pytest.raises(RuntimeError, match="signature verifier bug"):
        check_strategy_submit_bundle(
            emit_requested=True,
            signed_intents=signed_intents,
            operations=operations,
            chain_id="tau-local",
            signer_pubkey=signer_pubkey,
            tx_requested=False,
        )


def test_check_strategy_submit_bundle_propagates_operations_parser_bug(monkeypatch: pytest.MonkeyPatch) -> None:
    signer_pubkey, signed_intents, operations = _signed_bundle()

    def _bug(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("operations parser bug")

    monkeypatch.setattr(strategy_submit_bundle_guard_v1_adapter, "parse_signed_intents", _bug)

    with pytest.raises(RuntimeError, match="operations parser bug"):
        check_strategy_submit_bundle(
            emit_requested=True,
            signed_intents=signed_intents,
            operations=operations,
            chain_id="tau-local",
            signer_pubkey=signer_pubkey,
            tx_requested=False,
        )


def test_check_strategy_submit_bundle_propagates_tau_encoder_bug(monkeypatch: pytest.MonkeyPatch) -> None:
    signer_pubkey, signed_intents, operations = _signed_bundle()
    tau_tx_payload = build_signed_tau_transaction(
        privkey=7,
        sequence_number=9,
        expiration_time=999,
        operations=operations,
        fee_limit="0",
    )

    def _bug(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("tau encoder bug")

    monkeypatch.setattr(strategy_submit_bundle_guard_v1_adapter, "encode_tau_operations_for_wire", _bug)

    with pytest.raises(RuntimeError, match="tau encoder bug"):
        check_strategy_submit_bundle(
            emit_requested=True,
            signed_intents=signed_intents,
            operations=operations,
            chain_id="tau-local",
            signer_pubkey=signer_pubkey,
            tx_requested=True,
            sequence_number=9,
            expiration_time=999,
            fee_limit="0",
            tau_tx_payload=tau_tx_payload,
        )

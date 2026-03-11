# [TESTER] v1

from __future__ import annotations

from typing import Any, Mapping, Optional

import pytest

from src.core.settlement import Settlement
from src.integration.dex_engine import (
    DexFaultInjectionConfig,
    DexEngineConfig,
    _build_signing_payloads,
    _clean_error,
    _format_error_details,
    _hex_to_bytes_allow_0x,
    _pubkey_bytes48_or_none,
    _quote_receipt_error,
    _sanitize_intents_after_quote_receipt_validation,
    _settlement_commitment_dict,
    _settlement_rewrite_normal_form_dict,
    _validate_external_tool_policy,
    _validate_intent_preconditions,
    _validate_raw_intent_ops,
    _validate_raw_settlement_op,
    _verify_all_intent_signatures,
    _verify_intent_signature_bytes,
    _verify_proof_if_present,
)
from src.integration.operations import SettlementEnvelope, SignedIntentEnvelope
from src.integration.proof_verifier import MisconfiguredProofVerifier, ProofVerifier
from src.state.intents import Intent, IntentKind


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _swap_intent(*, sender: str = "0x" + "11" * 48, intent_id: str | None = None, fields: Optional[dict[str, Any]] = None) -> Intent:
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=intent_id or _iid(1),
        sender_pubkey=sender,
        deadline=100,
        fields={
            "pool_id": "0x" + "aa" * 32,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 10,
            "min_amount_out": 1,
            **(fields or {}),
        },
    )


def _empty_settlement_env(*, proof: Optional[dict[str, Any]]) -> SettlementEnvelope:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
    )
    return SettlementEnvelope(settlement=settlement, proof=proof)


class _DummyVerifier(ProofVerifier):
    def __init__(self, result: tuple[bool, Optional[str]]) -> None:
        self.result = result
        self.seen_payload: Optional[Mapping[str, Any]] = None

    def verify(self, payload: Mapping[str, Any]) -> tuple[bool, Optional[str]]:
        self.seen_payload = payload
        return self.result


def test_error_helpers_compact_context() -> None:
    assert _format_error_details(a=1, b=None, c="x") == "a=1, c='x'"
    assert _quote_receipt_error("bad receipt") == "bad receipt"
    assert _quote_receipt_error("bad receipt", intent_id="0x1") == "bad receipt: intent_id='0x1'"
    assert _clean_error("  bad \n   input\tvalue  ") == "bad input value"


def test_hex_and_pubkey_helpers_fail_closed() -> None:
    assert _hex_to_bytes_allow_0x("0x12ab", name="x") == bytes.fromhex("12ab")
    with pytest.raises(TypeError, match="must be a string"):
        _hex_to_bytes_allow_0x(123, name="x")  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="must be non-empty hex"):
        _hex_to_bytes_allow_0x("0x", name="x")
    with pytest.raises(ValueError, match="must have an even number of hex chars"):
        _hex_to_bytes_allow_0x("0x123", name="x")
    with pytest.raises(ValueError, match="must be valid hex"):
        _hex_to_bytes_allow_0x("0xzz", name="x")
    with pytest.raises(ValueError, match="must be 1 bytes"):
        _hex_to_bytes_allow_0x("0x12ab", name="x", expected_nbytes=1)
    with pytest.raises(ValueError, match="expected_nbytes must be a positive int"):
        _hex_to_bytes_allow_0x("0x12", name="x", expected_nbytes=0)
    assert _pubkey_bytes48_or_none("0x" + "11" * 48, name="pk") is not None
    assert _pubkey_bytes48_or_none(123, name="pk") is None  # type: ignore[arg-type]
    assert _pubkey_bytes48_or_none("not-hex", name="pk") is None
    assert _pubkey_bytes48_or_none(None, name="pk") is None


def test_fault_injection_config_rejects_unknown_stage() -> None:
    with pytest.raises(ValueError, match="unknown fault injection stage: no_such_stage"):
        DexFaultInjectionConfig(fail_at_stage="no_such_stage")


def test_validate_external_tool_policy_covers_consensus_and_disable_paths() -> None:
    assert (
        _validate_external_tool_policy(
            DexEngineConfig(consensus_mode=True, proof_config=DexEngineConfig().proof_config.__class__(enabled=True))
        )
        == "external tools not permitted in consensus_mode"
    )
    assert (
        _validate_external_tool_policy(
            DexEngineConfig(consensus_mode=False, allow_external_tools=False, proof_config=DexEngineConfig().proof_config.__class__(enabled=True))
        )
        == "external tools disabled (set DexEngineConfig.allow_external_tools=True)"
    )
    assert _validate_external_tool_policy(DexEngineConfig()) is None


def test_validate_raw_operation_guards_fail_early() -> None:
    config = DexEngineConfig(max_settlement_op_bytes=32, max_settlement_fills=1, max_intents=1, max_intent_entry_bytes=32, max_total_intent_entry_bytes=32)
    assert _validate_raw_settlement_op(config, ["bad"]) == "operations['3'] must be an object"
    assert _validate_raw_settlement_op(config, {"fills": [{}, {}]}) == "too many settlement fills: 2 > 1"
    assert _validate_raw_settlement_op(config, {"blob": "A" * 100}) == "settlement operation too large"
    assert _validate_raw_intent_ops(config, [{}, {}]) == "too many intents: 2 > 1"
    assert _validate_raw_intent_ops(config, [{"x": "A" * 100}]) == "intent operation too large: index 0"
    assert _validate_raw_intent_ops(config, "not-a-list") is None


def test_validate_raw_operation_guards_report_invalid_payloads_and_total_size(monkeypatch: pytest.MonkeyPatch) -> None:
    config = DexEngineConfig(max_settlement_op_bytes=128, max_intents=4, max_intent_entry_bytes=64, max_total_intent_entry_bytes=10)

    def bad_size(_value: object, *, max_bytes: int) -> int:
        if max_bytes == config.max_settlement_op_bytes:
            raise RuntimeError("bad settlement encoding")
        raise RuntimeError("bad intent encoding")

    monkeypatch.setattr("src.integration.dex_engine.bounded_json_utf8_size", bad_size)
    assert _validate_raw_settlement_op(config, {"x": 1}) == "invalid settlement operation: bad settlement encoding"
    assert _validate_raw_intent_ops(config, [{"x": 1}]) == "invalid intent operation: bad intent encoding"

    monkeypatch.setattr("src.integration.dex_engine.bounded_json_utf8_size", lambda value, *, max_bytes: 6)
    assert _validate_raw_intent_ops(config, [{"a": 1}, {"b": 2}]) == "total intent operation too large"


def test_validate_intent_preconditions_rejects_missing_or_expired_batches() -> None:
    intent = _swap_intent(intent_id=_iid(7))
    assert _validate_intent_preconditions(intents=[], settlement=_empty_settlement_env(proof=None).settlement, block_timestamp=0) == "settlement provided without intents"
    assert _validate_intent_preconditions(intents=[intent], settlement=None, block_timestamp=101) == f"Intent expired: {intent.intent_id}"
    assert _validate_intent_preconditions(intents=[intent], settlement=None, block_timestamp=100) is None


def test_sanitize_intents_after_quote_receipt_validation_strips_transport_fields() -> None:
    intent = _swap_intent(
        fields={
            "quote_receipt_hash": "0x" + "ab" * 32,
            "quote_receipt_leg_index": 0,
            "quote_pool_fingerprint": "fingerprint",
        }
    )
    sanitized = _sanitize_intents_after_quote_receipt_validation([intent])[0]
    assert sanitized.get_field("quote_receipt_hash") is None
    assert sanitized.get_field("quote_receipt_leg_index") is None
    assert sanitized.get_field("quote_pool_fingerprint") == "fingerprint"


def test_build_signing_payloads_rejects_invalid_or_oversized_signing_dicts() -> None:
    intent = _swap_intent()
    env = SignedIntentEnvelope(intent=intent, signature=None, quote_receipt=None)
    signing_dicts, payloads = _build_signing_payloads([env], max_intent_bytes=4096, max_total_intent_bytes=4096)
    assert len(signing_dicts) == len(payloads) == 1

    salted_intent = _swap_intent(intent_id=_iid(4))
    salted_intent.salt = "salt"
    signing_dicts, _payloads = _build_signing_payloads([SignedIntentEnvelope(intent=salted_intent)], max_intent_bytes=4096, max_total_intent_bytes=4096)
    assert signing_dicts[0]["salt"] == "salt"

    bad_fields_intent = _swap_intent(intent_id=_iid(2))
    bad_fields_intent.fields = 7  # type: ignore[assignment]
    with pytest.raises(TypeError, match="intent.fields must be a dict"):
        _build_signing_payloads([SignedIntentEnvelope(intent=bad_fields_intent)], max_intent_bytes=4096, max_total_intent_bytes=4096)

    too_large = _swap_intent(intent_id=_iid(3), fields={"blob": "A" * 5000})
    with pytest.raises(ValueError, match=f"intent signing payload too large: {too_large.intent_id}"):
        _build_signing_payloads([SignedIntentEnvelope(intent=too_large)], max_intent_bytes=256, max_total_intent_bytes=256)


def test_verify_all_intent_signatures_covers_unsigned_policy_paths() -> None:
    sender = "0x" + "11" * 48
    other = "0x" + "22" * 48
    intent = _swap_intent(sender=sender)
    env = SignedIntentEnvelope(intent=intent, signature=None)
    payload = [b"{}"]

    ok, err = _verify_all_intent_signatures(
        [env],
        require=False,
        tx_sender_pubkey=sender,
        allow_tx_sender_bypass=False,
        signing_payloads=payload,
        chain_id="tau-net-alpha",
    )
    assert (ok, err) == (False, "unsigned intents disabled (tx sender binding required)")

    ok, err = _verify_all_intent_signatures(
        [env],
        require=False,
        tx_sender_pubkey="bad-pubkey",
        allow_tx_sender_bypass=True,
        signing_payloads=payload,
        chain_id="tau-net-alpha",
    )
    assert (ok, err) == (False, "tx_sender_pubkey must be a 48-byte hex pubkey for unsigned intents")

    ok, err = _verify_all_intent_signatures(
        [env],
        require=False,
        tx_sender_pubkey=other,
        allow_tx_sender_bypass=True,
        signing_payloads=payload,
        chain_id="tau-net-alpha",
    )
    assert (ok, err) == (False, f"intent sender mismatch: {intent.intent_id}")

    ok, err = _verify_all_intent_signatures(
        [env],
        require=True,
        tx_sender_pubkey=sender,
        allow_tx_sender_bypass=True,
        signing_payloads=payload,
        chain_id="tau-net-alpha",
    )
    assert (ok, err) == (True, None)


def test_verify_all_intent_signatures_covers_internal_mismatch_and_signature_failures(monkeypatch: pytest.MonkeyPatch) -> None:
    sender = "0x" + "11" * 48
    intent = _swap_intent(sender=sender)
    env = SignedIntentEnvelope(intent=intent, signature="0x" + "22" * 96)

    ok, err = _verify_all_intent_signatures(
        [env],
        require=True,
        tx_sender_pubkey=sender,
        allow_tx_sender_bypass=False,
        signing_payloads=[],
        chain_id="tau-net-alpha",
    )
    assert (ok, err) == (False, "internal error: signing payload mismatch")

    monkeypatch.setattr("src.integration.dex_engine._BLS_AVAILABLE", False)
    ok, err = _verify_all_intent_signatures(
        [env],
        require=True,
        tx_sender_pubkey=sender,
        allow_tx_sender_bypass=False,
        signing_payloads=[b"{}"],
        chain_id="tau-net-alpha",
    )
    assert (ok, err) == (False, "py_ecc (BLS) not available")

    monkeypatch.setattr("src.integration.dex_engine._BLS_AVAILABLE", True)
    monkeypatch.setattr("src.integration.dex_engine._verify_intent_signature_bytes", lambda **kwargs: (False, "bad sig"))
    ok, err = _verify_all_intent_signatures(
        [env],
        require=True,
        tx_sender_pubkey=sender,
        allow_tx_sender_bypass=False,
        signing_payloads=[b"{}"],
        chain_id="tau-net-alpha",
    )
    assert (ok, err) == (False, f"intent signature invalid: {intent.intent_id}: bad sig")


def test_verify_intent_signature_bytes_rejects_missing_bls_and_internal_errors(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr("src.integration.dex_engine._BLS_AVAILABLE", False)
    ok, err = _verify_intent_signature_bytes(
        sender_pubkey_hex="0x" + "11" * 48,
        signature_hex="0x" + "22" * 96,
        signing_payload_bytes=b"{}",
        chain_id="tau-net-alpha",
    )
    assert (ok, err) == (False, "py_ecc (BLS) not available")

    monkeypatch.setattr("src.integration.dex_engine._BLS_AVAILABLE", True)
    monkeypatch.setattr("src.integration.dex_engine.domain_sep_bytes", lambda *args, **kwargs: (_ for _ in ()).throw(RuntimeError("domain boom")))
    ok, err = _verify_intent_signature_bytes(
        sender_pubkey_hex="0x" + "11" * 48,
        signature_hex="0x" + "22" * 96,
        signing_payload_bytes=b"{}",
        chain_id="tau-net-alpha",
    )
    assert ok is False
    assert err == "intent signature verification error: domain boom"


def test_verify_proof_if_present_covers_missing_mismatch_and_reject_paths(monkeypatch: pytest.MonkeyPatch) -> None:
    verifier = _DummyVerifier((True, None))

    assert _verify_proof_if_present(
        verifier,
        intents=[],
        settlement_env=None,
        require_proof=False,
        verifier_enforcing=False,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=1024,
    ) == (True, None)

    assert _verify_proof_if_present(
        verifier,
        intents=[SignedIntentEnvelope(intent=_swap_intent())],
        settlement_env=None,
        require_proof=True,
        verifier_enforcing=False,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=1024,
    ) == (False, "missing required proof")

    bad_type_env = _empty_settlement_env(proof="bad")  # type: ignore[arg-type]
    assert _verify_proof_if_present(
        verifier,
        intents=[],
        settlement_env=bad_type_env,
        require_proof=False,
        verifier_enforcing=True,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=1024,
    ) == (False, "proof must be an object")

    misconfigured = MisconfiguredProofVerifier("bad verifier")
    assert _verify_proof_if_present(
        misconfigured,
        intents=[],
        settlement_env=_empty_settlement_env(proof={"pre_state_commitment": "0x1", "batch_commitment": "0x2"}),
        require_proof=False,
        verifier_enforcing=True,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=1024,
    ) == (False, "bad verifier")

    assert _verify_proof_if_present(
        verifier,
        intents=[SignedIntentEnvelope(intent=_swap_intent())],
        settlement_env=_empty_settlement_env(proof={"x": 1}),
        require_proof=True,
        verifier_enforcing=False,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=1024,
    ) == (False, "proof required but verification disabled")

    assert _verify_proof_if_present(
        verifier,
        intents=[],
        settlement_env=_empty_settlement_env(proof={"batch_commitment": "0x2"}),
        require_proof=False,
        verifier_enforcing=True,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=1024,
    ) == (False, "proof missing pre_state_commitment")

    assert _verify_proof_if_present(
        verifier,
        intents=[],
        settlement_env=_empty_settlement_env(proof={"pre_state_commitment": "0x9", "batch_commitment": "0x2"}),
        require_proof=False,
        verifier_enforcing=True,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=1024,
    ) == (False, "proof pre_state_commitment mismatch")

    assert _verify_proof_if_present(
        verifier,
        intents=[],
        settlement_env=_empty_settlement_env(proof={"pre_state_commitment": "0x1"}),
        require_proof=False,
        verifier_enforcing=True,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=1024,
    ) == (False, "proof missing batch_commitment")

    assert _verify_proof_if_present(
        verifier,
        intents=[],
        settlement_env=_empty_settlement_env(proof={"pre_state_commitment": "0x1", "batch_commitment": "0x9"}),
        require_proof=False,
        verifier_enforcing=True,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=1024,
    ) == (False, "proof batch_commitment mismatch")

    rejecting = _DummyVerifier((False, "bad proof"))
    assert _verify_proof_if_present(
        rejecting,
        intents=[],
        settlement_env=_empty_settlement_env(proof={"pre_state_commitment": "0x1", "batch_commitment": "0x2"}),
        require_proof=False,
        verifier_enforcing=True,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=1024,
    ) == (False, "proof rejected: bad proof")

    too_large_payload = {"pre_state_commitment": "0x1", "batch_commitment": "0x2", "blob": "A" * 5000}
    assert _verify_proof_if_present(
        verifier,
        intents=[],
        settlement_env=_empty_settlement_env(proof=too_large_payload),
        require_proof=False,
        verifier_enforcing=True,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=64,
    ) == (False, "proof payload too large")

    monkeypatch.setattr("src.integration.dex_engine.bounded_json_utf8_size", lambda payload, *, max_bytes: (_ for _ in ()).throw(RuntimeError("bad encoding")))
    assert _verify_proof_if_present(
        verifier,
        intents=[],
        settlement_env=_empty_settlement_env(proof={"pre_state_commitment": "0x1", "batch_commitment": "0x2"}),
        require_proof=False,
        verifier_enforcing=True,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=1024,
    ) == (False, "invalid proof payload encoding")

    monkeypatch.undo()
    ok_verifier = _DummyVerifier((True, None))
    assert _verify_proof_if_present(
        ok_verifier,
        intents=[],
        settlement_env=_empty_settlement_env(proof={"pre_state_commitment": "0x1", "batch_commitment": "0x2"}),
        require_proof=False,
        verifier_enforcing=True,
        pre_state_commitment="0x1",
        batch_commitment="0x2",
        max_verifier_payload_bytes=1024,
    ) == (True, None)


def test_settlement_canonicalization_helpers_fail_closed_on_malformed_operation(monkeypatch: pytest.MonkeyPatch) -> None:
    settlement = _empty_settlement_env(proof=None).settlement

    monkeypatch.setattr("src.integration.dex_engine.create_settlement_operation", lambda _settlement: {"3": []})
    with pytest.raises(TypeError, match="settlement operation must be an object"):
        _settlement_commitment_dict(settlement)
    with pytest.raises(TypeError, match="settlement operation must be an object"):
        _settlement_rewrite_normal_form_dict(settlement)

    monkeypatch.setattr("src.integration.dex_engine.create_settlement_operation", lambda _settlement: {"3": {"fills": {}}})
    with pytest.raises(TypeError, match="settlement.fills must be a list"):
        _settlement_commitment_dict(settlement)

    monkeypatch.setattr(
        "src.integration.dex_engine.create_settlement_operation",
        lambda _settlement: {"3": {"fills": ["bad"]}},
    )
    with pytest.raises(TypeError, match="settlement fill must be an object"):
        _settlement_commitment_dict(settlement)

# [TESTER] v1

from __future__ import annotations

from dataclasses import replace
from types import SimpleNamespace
from typing import Any, Mapping, Optional

import pytest

import src.integration.dex_engine as dex_engine
from src.core.dex import DexConfig, DexState
from src.core.settlement import Fill, FillAction, Settlement
from src.integration.dex_engine import (
    DexEngineConfig,
    DexFaultInjectionConfig,
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
    _validate_intent_against_quote_receipt,
    _validate_intent_preconditions,
    _validate_quote_receipt_witnesses,
    _validate_raw_intent_ops,
    _validate_raw_settlement_op,
    _verify_all_intent_signatures,
    _verify_intent_signature_bytes,
    _verify_proof_if_present,
    apply_ops,
)
from src.integration.operations import SettlementEnvelope, SignedIntentEnvelope
from src.integration.proof_verifier import (
    MisconfiguredProofVerifier,
    ProofVerifier,
    ProofVerifierConfig,
)
from src.integration.settlement_end_to_end_certificate_packet import (
    SettlementEndToEndCertificateInputs,
)
from src.integration.settlement_feature_extension_packet import SettlementFeatureExtensionInputs
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    build_settlement_spot_price_packet,
)
from src.integration.settlement_strong_certificate import SettlementProofFlags
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _feature_extension_inputs() -> SettlementFeatureExtensionInputs:
    return SettlementFeatureExtensionInputs(
        trade_amount=100,
        fee_charged=1,
        buyback_amount=1,
        burned_amount=1,
        supply_before=1_000,
        supply_after=999,
        supply_floor=500,
        unit_scale=1,
        rebate_rate_bps=500,
        rebate_amount=1,
        rebate_cap=1,
        lock_days=60,
        stake_amount=50,
        tier1_days=30,
        tier2_days=90,
        weight_t1=1,
        weight_t2=2,
        weight_t3=3,
        weight_claimed=2,
        weighted_stake=100,
    )


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


def _receipt(
    *,
    kind: str = "exact_in",
    pool_id: str = "0x" + "aa" * 32,
    asset_in: str = "0x" + "01" * 32,
    asset_out: str = "0x" + "02" * 32,
    amount_in: int = 10,
    amount_out: int = 9,
    pools: Optional[dict[str, Any]] = None,
    legs: Optional[list[Any]] = None,
    receipt_hash: str = "0x" + "ab" * 32,
) -> dict[str, Any]:
    if pools is None:
        pools = {pool_id: "fingerprint"}
    if legs is None:
        legs = [
            {
                "hops": [
                    {
                        "pool_id": pool_id,
                        "asset_in": asset_in,
                        "asset_out": asset_out,
                        "amount_in": amount_in,
                        "amount_out": amount_out,
                    }
                ]
            }
        ]
    return {"body": {"kind": kind, "pools": pools, "legs": legs}, "receipt_hash": receipt_hash}


def _empty_state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())


def _reject_settlement(intent_id: str) -> Settlement:
    return Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch",
        included_intents=[(intent_id, FillAction.REJECT)],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
    )


def _filled_settlement(intent_id: str, *, fee_paid: int = 0) -> Settlement:
    return Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch",
        included_intents=[(intent_id, FillAction.FILL)],
        fills=[Fill(intent_id=intent_id, action=FillAction.FILL, fee_paid=fee_paid)],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
    )


def _patch_apply_ops_happy_path(
    monkeypatch: pytest.MonkeyPatch,
    *,
    signed_intents: Optional[list[SignedIntentEnvelope]] = None,
    settlement_env: Optional[SettlementEnvelope] = None,
    computed_settlement: Optional[Settlement] = None,
    validate_result: tuple[bool, Optional[str]] = (True, None),
    verify_result: tuple[bool, Optional[str]] = (True, None),
) -> list[SignedIntentEnvelope]:
    envs = signed_intents or [SignedIntentEnvelope(intent=_swap_intent(fields={"nonce": 1}))]
    settlement = computed_settlement or _reject_settlement(envs[0].intent.intent_id)
    monkeypatch.setattr(dex_engine, "parse_signed_intents", lambda operations: envs)
    monkeypatch.setattr(dex_engine, "parse_settlement_envelope", lambda operations: settlement_env)
    monkeypatch.setattr(
        dex_engine,
        "_build_signing_payloads",
        lambda signed_intents, *, max_intent_bytes, max_total_intent_bytes: (
            [{} for _ in signed_intents],
            [b"{}" for _ in signed_intents],
        ),
    )
    monkeypatch.setattr(dex_engine, "_verify_all_intent_signatures", lambda *args, **kwargs: (True, None))
    monkeypatch.setattr(dex_engine, "_validate_quote_receipt_witnesses", lambda **kwargs: None)
    monkeypatch.setattr(dex_engine, "_validate_and_apply_nonce_batch", lambda **kwargs: (True, None, kwargs["nonces"]))
    monkeypatch.setattr(dex_engine, "compute_settlement", lambda **kwargs: settlement)
    monkeypatch.setattr(dex_engine, "validate_operations", lambda **kwargs: validate_result)
    monkeypatch.setattr(dex_engine, "_verify_proof_if_present", lambda *args, **kwargs: verify_result)
    monkeypatch.setattr(
        dex_engine,
        "apply_settlement_pure",
        lambda **kwargs: (kwargs["balances"], kwargs["pools"], kwargs["lp_balances"]),
    )
    monkeypatch.setattr(dex_engine, "make_proof_verifier", lambda config: _DummyVerifier((True, None)))
    return envs


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


def test_hex_helper_covers_defensive_fromhex_paths(monkeypatch: pytest.MonkeyPatch) -> None:
    class _BytesValueError:
        @staticmethod
        def fromhex(_hex: str) -> bytes:
            raise ValueError("boom")

    class _BytesWrongLength:
        @staticmethod
        def fromhex(_hex: str) -> bytes:
            return b"\x12"

    monkeypatch.setattr(dex_engine, "bytes", _BytesValueError, raising=False)
    with pytest.raises(ValueError, match="must be valid hex"):
        _hex_to_bytes_allow_0x("0x12ab", name="x")

    monkeypatch.setattr(dex_engine, "bytes", _BytesWrongLength, raising=False)
    with pytest.raises(ValueError, match="must decode to exactly 2 bytes"):
        _hex_to_bytes_allow_0x("0x12ab", name="x", expected_nbytes=2)


def test_fault_injection_config_rejects_unknown_stage() -> None:
    with pytest.raises(ValueError, match="unknown fault injection stage: no_such_stage"):
        DexFaultInjectionConfig(fail_at_stage="no_such_stage")


def test_fault_injection_config_accepts_none_stage() -> None:
    assert DexFaultInjectionConfig().fail_at_stage is None


def test_dex_engine_config_rejects_certificate_mode_without_proof_flags() -> None:
    with pytest.raises(
        ValueError,
        match="require_settlement_certificate=True requires settlement_end_to_end_certificate_inputs",
    ):
        DexEngineConfig(
            require_settlement_certificate=True,
            settlement_certificate_price_history=(100, 110, 120),
        )


def test_dex_engine_config_rejects_certificate_mode_without_price_history() -> None:
    with pytest.raises(
        ValueError,
        match="require_settlement_certificate=True requires settlement_end_to_end_certificate_inputs",
    ):
        DexEngineConfig(
            require_settlement_certificate=True,
            settlement_certificate_proof_flags=SettlementProofFlags.all_true(),
        )


def test_dex_engine_config_rejects_malformed_certificate_price_history() -> None:
    with pytest.raises(
        ValueError,
        match="settlement_certificate_price_history must be a 3-tuple",
    ):
        DexEngineConfig(
            settlement_certificate_price_history=(100, 110),  # type: ignore[arg-type]
        )

    with pytest.raises(
        ValueError,
        match="settlement_certificate_price_history\\[1\\] must be an int",
    ):
        DexEngineConfig(
            settlement_certificate_price_history=(100, "110", 120),  # type: ignore[arg-type]
        )


def test_dex_engine_config_allows_unified_inputs_under_existing_certificate_flag() -> None:
    packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset="0x" + "01" * 32, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset="0x" + "02" * 32, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    cfg = DexEngineConfig(
        require_settlement_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_packet=packet,
        ),
    )
    assert cfg.require_settlement_certificate is True
    assert cfg.settlement_end_to_end_certificate_inputs is not None


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


def test_validate_intent_against_quote_receipt_rejects_non_swap_and_invalid_receipt_shapes() -> None:
    add_liq = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(30),
        sender_pubkey="0x" + "11" * 48,
        deadline=100,
        fields={"pool_id": "0x" + "aa" * 32},
    )
    assert "quote receipt only supported for swap intents" in _validate_intent_against_quote_receipt(add_liq, _receipt())  # type: ignore[arg-type]

    swap = _swap_intent(intent_id=_iid(31))
    assert "invalid quote receipt body" in _validate_intent_against_quote_receipt(swap, {"body": None})  # type: ignore[arg-type]
    assert "quote receipt kind mismatch" in _validate_intent_against_quote_receipt(swap, _receipt(kind="exact_out"))  # type: ignore[arg-type]
    assert "invalid quote receipt-bound swap fields" in _validate_intent_against_quote_receipt(
        _swap_intent(intent_id=_iid(32), fields={"pool_id": 7}),  # type: ignore[arg-type]
        _receipt(),
    )  # type: ignore[arg-type]
    assert "invalid quote receipt pools" in _validate_intent_against_quote_receipt(
        _swap_intent(intent_id=_iid(33)),
        _receipt(pools=[]),  # type: ignore[arg-type]
    )  # type: ignore[arg-type]
    assert "invalid quote_pool_fingerprint" in _validate_intent_against_quote_receipt(
        _swap_intent(intent_id=_iid(34), fields={"quote_pool_fingerprint": ""}),
        _receipt(),
    )  # type: ignore[arg-type]
    assert "quote receipt pool fingerprint mismatch" in _validate_intent_against_quote_receipt(
        _swap_intent(intent_id=_iid(35), fields={"quote_pool_fingerprint": "wrong"}),
        _receipt(),
    )  # type: ignore[arg-type]
    assert "invalid quote receipt legs" in _validate_intent_against_quote_receipt(
        _swap_intent(intent_id=_iid(36)),
        _receipt(legs=[]),
    )  # type: ignore[arg-type]


def test_validate_intent_against_quote_receipt_covers_leg_index_and_exact_in_reject_paths() -> None:
    assert "invalid quote_receipt_leg_index" in _validate_intent_against_quote_receipt(
        _swap_intent(intent_id=_iid(37), fields={"quote_receipt_leg_index": True}),
        _receipt(),
    )  # type: ignore[arg-type]
    assert "quote receipt leg index out of range" in _validate_intent_against_quote_receipt(
        _swap_intent(intent_id=_iid(38), fields={"quote_receipt_leg_index": 5}),
        _receipt(),
    )  # type: ignore[arg-type]
    assert "intent does not match quote receipt leg" in _validate_intent_against_quote_receipt(
        _swap_intent(intent_id=_iid(39), fields={"quote_receipt_leg_index": 0}),
        _receipt(legs=[{"hops": [{"pool_id": "0x" + "bb" * 32, "asset_in": "x", "asset_out": "y", "amount_in": 1, "amount_out": 1}]}]),
    )  # type: ignore[arg-type]
    assert "invalid amount_in for quote receipt binding" in _validate_intent_against_quote_receipt(
        _swap_intent(intent_id=_iid(40), fields={"amount_in": True}),
        _receipt(),
    )  # type: ignore[arg-type]
    assert "invalid min_amount_out for quote receipt binding" in _validate_intent_against_quote_receipt(
        _swap_intent(intent_id=_iid(41), fields={"min_amount_out": -1}),
        _receipt(),
    )  # type: ignore[arg-type]
    assert "exact-in quote receipt leg mismatch" in _validate_intent_against_quote_receipt(
        _swap_intent(intent_id=_iid(42), fields={"amount_in": 11}),
        _receipt(),
    )  # type: ignore[arg-type]


def test_validate_intent_against_quote_receipt_covers_multi_hop_and_exact_out_paths() -> None:
    exact_out = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(43),
        sender_pubkey="0x" + "11" * 48,
        deadline=100,
        fields={
            "pool_id": "0x" + "aa" * 32,
            "asset_in": "0x" + "01" * 32,
            "asset_out": "0x" + "02" * 32,
            "amount_out": 9,
            "max_amount_in": 10,
        },
    )
    multi_hop = _receipt(
        kind="exact_out",
        legs=[
            {
                "hops": [
                    "bad-hop",
                    {
                        "pool_id": "0x" + "aa" * 32,
                        "asset_in": "0x" + "01" * 32,
                        "asset_out": "0x" + "02" * 32,
                        "amount_in": 10,
                        "amount_out": 9,
                    },
                ]
            }
        ]
    )
    assert "quote receipt multi-hop leg unsupported for direct intent binding" in _validate_intent_against_quote_receipt(exact_out, multi_hop)  # type: ignore[arg-type]
    assert _validate_intent_against_quote_receipt(exact_out, _receipt(kind="exact_out")) is None
    assert "invalid amount_out for quote receipt binding" in _validate_intent_against_quote_receipt(
        replace(exact_out, fields={**(exact_out.fields or {}), "amount_out": True}),
        _receipt(kind="exact_out"),
    )  # type: ignore[arg-type]
    assert "invalid max_amount_in for quote receipt binding" in _validate_intent_against_quote_receipt(
        replace(exact_out, fields={**(exact_out.fields or {}), "max_amount_in": -1}),
        _receipt(kind="exact_out"),
    )  # type: ignore[arg-type]
    assert "exact-out quote receipt leg mismatch" in _validate_intent_against_quote_receipt(
        replace(exact_out, fields={**(exact_out.fields or {}), "max_amount_in": 9}),
        _receipt(kind="exact_out"),
    )  # type: ignore[arg-type]


def test_validate_intent_against_quote_receipt_covers_remaining_defensive_continue_paths() -> None:
    swap = _swap_intent(intent_id=_iid(430))

    assert "intent does not match quote receipt" in _validate_intent_against_quote_receipt(
        swap,
        _receipt(legs=["bad"]),  # type: ignore[arg-type]
    )  # type: ignore[arg-type]
    assert "intent does not match quote receipt" in _validate_intent_against_quote_receipt(
        swap,
        _receipt(
            legs=[
                {
                    "hops": [
                        {"pool_id": "other", "asset_in": "x", "asset_out": "y", "amount_in": 1, "amount_out": 1},
                        {"pool_id": "still-other", "asset_in": "x", "asset_out": "y", "amount_in": 2, "amount_out": 2},
                    ]
                }
            ]
        ),
    )  # type: ignore[arg-type]
    assert "intent does not match quote receipt" in _validate_intent_against_quote_receipt(
        swap,
        _receipt(legs=[{"hops": "bad"}]),  # type: ignore[arg-type]
    )  # type: ignore[arg-type]
    assert "intent does not match quote receipt" in _validate_intent_against_quote_receipt(
        swap,
        _receipt(legs=[{"hops": [None]}]),  # type: ignore[arg-type]
    )  # type: ignore[arg-type]
    assert "intent does not match quote receipt" in _validate_intent_against_quote_receipt(
        swap,
        _receipt(
            legs=[
                {
                    "hops": [
                        {
                            "pool_id": swap.get_field("pool_id"),
                            "asset_in": swap.get_field("asset_in"),
                            "asset_out": swap.get_field("asset_out"),
                            "amount_in": "bad",
                            "amount_out": 9,
                        }
                    ]
                }
            ]
        ),
    )  # type: ignore[arg-type]
    assert "intent does not match quote receipt" in _validate_intent_against_quote_receipt(
        swap,
        _receipt(
            legs=[
                {
                    "hops": [
                        {
                            "pool_id": swap.get_field("pool_id"),
                            "asset_in": swap.get_field("asset_in"),
                            "asset_out": swap.get_field("asset_out"),
                            "amount_in": 10,
                            "amount_out": "bad",
                        }
                    ]
                }
            ]
        ),
    )  # type: ignore[arg-type]


def test_validate_quote_receipt_witnesses_covers_missing_hash_invalid_hash_and_group_checks(monkeypatch: pytest.MonkeyPatch) -> None:
    env_missing_hash = SignedIntentEnvelope(intent=_swap_intent(intent_id=_iid(44)), quote_receipt=_receipt())
    assert "quote receipt provided without quote_receipt_hash" in _validate_quote_receipt_witnesses(
        signed_intents=[env_missing_hash],
        pools={},
    )  # type: ignore[arg-type]

    env_invalid_hash = SignedIntentEnvelope(
        intent=_swap_intent(intent_id=_iid(45), fields={"quote_receipt_hash": ""}),
        quote_receipt=_receipt(),
    )
    assert "invalid quote_receipt_hash" in _validate_quote_receipt_witnesses(signed_intents=[env_invalid_hash], pools={})  # type: ignore[arg-type]

    monkeypatch.setattr("src.integration.dex_engine.verify_route_quote_receipt", lambda receipt, pools_by_id: (True, None))
    monkeypatch.setattr("src.integration.dex_engine._validate_intent_against_quote_receipt", lambda intent, receipt: None)

    good_env = SignedIntentEnvelope(
        intent=_swap_intent(intent_id=_iid(46), fields={"quote_receipt_hash": "0x" + "ab" * 32, "quote_receipt_leg_index": 0}),
        quote_receipt=_receipt(legs="bad"),  # type: ignore[arg-type]
    )
    assert _validate_quote_receipt_witnesses(signed_intents=[good_env], pools={}) == f"invalid quote receipt legs: {good_env.intent.intent_id}"

    calls = {"n": 0}

    original_get_field = Intent.get_field

    def _stateful_get_field(self: Intent, key: str, default: Any = None) -> Any:
        if key == "quote_receipt_leg_index":
            calls["n"] += 1
            return 0 if calls["n"] == 1 else -1
        return original_get_field(self, key, default)

    monkeypatch.setattr(Intent, "get_field", _stateful_get_field)
    object.__setattr__(good_env, "quote_receipt", _receipt())
    assert "missing quote_receipt_leg_index" in _validate_quote_receipt_witnesses(signed_intents=[good_env], pools={})  # type: ignore[arg-type]


def test_build_signing_payloads_rejects_invalid_or_oversized_signing_dicts() -> None:
    intent = _swap_intent()
    env = SignedIntentEnvelope(intent=intent, signature=None, quote_receipt=None)
    signing_dicts, payloads = _build_signing_payloads([env], max_intent_bytes=4096, max_total_intent_bytes=4096)
    assert len(signing_dicts) == len(payloads) == 1

    salted_intent = replace(_swap_intent(intent_id=_iid(4)), salt="salt")
    signing_dicts, _payloads = _build_signing_payloads([SignedIntentEnvelope(intent=salted_intent)], max_intent_bytes=4096, max_total_intent_bytes=4096)
    assert signing_dicts[0]["salt"] == "salt"

    bad_fields_intent = _swap_intent(intent_id=_iid(2))
    object.__setattr__(bad_fields_intent, "fields", 7)
    with pytest.raises(TypeError, match="intent.fields must be a dict"):
        _build_signing_payloads([SignedIntentEnvelope(intent=bad_fields_intent)], max_intent_bytes=4096, max_total_intent_bytes=4096)

    too_large = _swap_intent(intent_id=_iid(3), fields={"blob": "A" * 5000})
    with pytest.raises(ValueError, match=f"intent signing payload too large: {too_large.intent_id}"):
        _build_signing_payloads([SignedIntentEnvelope(intent=too_large)], max_intent_bytes=256, max_total_intent_bytes=256)


def test_build_signing_payloads_covers_invalid_encoding_and_total_size_guards(monkeypatch: pytest.MonkeyPatch) -> None:
    env = SignedIntentEnvelope(intent=_swap_intent(intent_id=_iid(470)))

    monkeypatch.setattr(dex_engine, "bounded_json_utf8_size", lambda value, *, max_bytes: 1)
    monkeypatch.setattr(dex_engine, "canonical_json_bytes", lambda value: (_ for _ in ()).throw(TypeError("bad json")))
    with pytest.raises(ValueError, match=f"invalid intent signing payload: {env.intent.intent_id}"):
        _build_signing_payloads([env], max_intent_bytes=32, max_total_intent_bytes=32)

    monkeypatch.setattr(dex_engine, "bounded_json_utf8_size", lambda value, *, max_bytes: 1)
    monkeypatch.setattr(dex_engine, "canonical_json_bytes", lambda value: b"012345")
    with pytest.raises(ValueError, match=f"intent signing payload too large: {env.intent.intent_id}"):
        _build_signing_payloads([env], max_intent_bytes=4, max_total_intent_bytes=32)

    env2 = SignedIntentEnvelope(intent=_swap_intent(intent_id=_iid(471)))
    monkeypatch.setattr(dex_engine, "bounded_json_utf8_size", lambda value, *, max_bytes: 1)
    monkeypatch.setattr(dex_engine, "canonical_json_bytes", lambda value: b"1234")
    with pytest.raises(ValueError, match="total intent payload too large"):
        _build_signing_payloads([env, env2], max_intent_bytes=8, max_total_intent_bytes=7)


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


def test_verify_all_intent_signatures_covers_missing_signature_without_bypass_and_successful_signature_loop(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    sender = "0x" + "11" * 48
    other = "0x" + "22" * 48
    missing_sig_intent = _swap_intent(sender=sender, intent_id=_iid(472))
    missing_sig_env = SignedIntentEnvelope(intent=missing_sig_intent, signature=None)

    ok, err = _verify_all_intent_signatures(
        [missing_sig_env],
        require=True,
        tx_sender_pubkey=other,
        allow_tx_sender_bypass=True,
        signing_payloads=[b"{}"],
        chain_id="tau-net-alpha",
    )
    assert (ok, err) == (False, f"missing intent signature: {missing_sig_intent.intent_id}")

    env1 = SignedIntentEnvelope(intent=_swap_intent(sender=sender, intent_id=_iid(473)), signature="0x" + "22" * 96)
    env2 = SignedIntentEnvelope(intent=_swap_intent(sender=sender, intent_id=_iid(474)), signature="0x" + "33" * 96)
    monkeypatch.setattr(dex_engine, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(dex_engine, "_verify_intent_signature_bytes", lambda **kwargs: (True, None))
    ok, err = _verify_all_intent_signatures(
        [env1, env2],
        require=True,
        tx_sender_pubkey=None,
        allow_tx_sender_bypass=False,
        signing_payloads=[b"{}", b"{}"],
        chain_id="tau-net-alpha",
    )
    assert (ok, err) == (True, None)


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


def test_verify_intent_signature_bytes_covers_invalid_signature_and_success(monkeypatch: pytest.MonkeyPatch) -> None:
    class _RejectingBLS:
        @staticmethod
        def Verify(pubkey: bytes, message: bytes, signature: bytes) -> bool:
            return False

    class _AcceptingBLS:
        @staticmethod
        def Verify(pubkey: bytes, message: bytes, signature: bytes) -> bool:
            return True

    monkeypatch.setattr(dex_engine, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(dex_engine, "domain_sep_bytes", lambda *args, **kwargs: b"dex")
    monkeypatch.setattr(dex_engine, "G2Basic", _RejectingBLS)
    assert _verify_intent_signature_bytes(
        sender_pubkey_hex="0x" + "11" * 48,
        signature_hex="0x" + "22" * 96,
        signing_payload_bytes=b"{}",
        chain_id="tau-net-alpha",
    ) == (False, "invalid intent signature")

    monkeypatch.setattr(dex_engine, "G2Basic", _AcceptingBLS)
    assert _verify_intent_signature_bytes(
        sender_pubkey_hex="0x" + "11" * 48,
        signature_hex="0x" + "22" * 96,
        signing_payload_bytes=b"{}",
        chain_id="tau-net-alpha",
    ) == (True, None)


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

    monkeypatch.setattr("src.integration.dex_engine.bounded_json_utf8_size", lambda payload, *, max_bytes: (_ for _ in ()).throw(TypeError("bad encoding")))
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

    monkeypatch.setattr("src.integration.dex_engine.bounded_json_utf8_size", lambda payload, *, max_bytes: (_ for _ in ()).throw(RuntimeError("bad encoding")))
    with pytest.raises(RuntimeError, match="bad encoding"):
        _verify_proof_if_present(
            verifier,
            intents=[],
            settlement_env=_empty_settlement_env(proof={"pre_state_commitment": "0x1", "batch_commitment": "0x2"}),
            require_proof=False,
            verifier_enforcing=True,
            pre_state_commitment="0x1",
            batch_commitment="0x2",
            max_verifier_payload_bytes=1024,
        )

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


def test_apply_ops_covers_external_tool_policy_and_intent_parse_errors(monkeypatch: pytest.MonkeyPatch) -> None:
    state = _empty_state()

    res = apply_ops(
        config=DexEngineConfig(
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=["/bin/true"]),
            consensus_mode=True,
            allow_external_tools=True,
        ),
        state=state,
        operations={},
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error == "external tools not permitted in consensus_mode"

    monkeypatch.setattr(dex_engine, "parse_signed_intents", lambda operations: (_ for _ in ()).throw(ValueError("bad\nintents")))
    res = apply_ops(config=DexEngineConfig(), state=state, operations={"2": "ignored"}, block_timestamp=0)
    assert res.error == "invalid intents: bad intents"

    monkeypatch.setattr(dex_engine, "parse_signed_intents", lambda operations: (_ for _ in ()).throw(RuntimeError("boom")))
    res = apply_ops(config=DexEngineConfig(), state=state, operations={"2": "ignored"}, block_timestamp=0)
    assert res.error == "internal error"


def test_apply_ops_covers_too_many_intents_and_settlement_parse_errors(monkeypatch: pytest.MonkeyPatch) -> None:
    state = _empty_state()
    envs = [
        SignedIntentEnvelope(intent=_swap_intent(intent_id=_iid(500), fields={"nonce": 1})),
        SignedIntentEnvelope(intent=_swap_intent(intent_id=_iid(501), fields={"nonce": 2})),
    ]
    monkeypatch.setattr(dex_engine, "parse_signed_intents", lambda operations: envs)
    res = apply_ops(
        config=DexEngineConfig(max_intents=1),
        state=state,
        operations={"2": "ignored"},
        block_timestamp=0,
    )
    assert res.error == "too many intents: 2 > 1"

    monkeypatch.setattr(dex_engine, "parse_signed_intents", lambda operations: [])
    monkeypatch.setattr(dex_engine, "parse_settlement_envelope", lambda operations: (_ for _ in ()).throw(ValueError("bad\nsettlement")))
    res = apply_ops(config=DexEngineConfig(), state=state, operations={}, block_timestamp=0)
    assert res.error == "invalid settlement: bad settlement"

    monkeypatch.setattr(dex_engine, "parse_settlement_envelope", lambda operations: (_ for _ in ()).throw(RuntimeError("boom")))
    res = apply_ops(config=DexEngineConfig(), state=state, operations={}, block_timestamp=0)
    assert res.error == "internal error"


def test_apply_ops_covers_invalid_proof_payload_and_signing_payload_errors(monkeypatch: pytest.MonkeyPatch) -> None:
    state = _empty_state()
    monkeypatch.setattr(dex_engine, "parse_signed_intents", lambda operations: [])
    monkeypatch.setattr(
        dex_engine,
        "parse_settlement_envelope",
        lambda operations: SettlementEnvelope(settlement=_reject_settlement(_iid(510)), proof={"scheme": "dummy"}),
    )
    monkeypatch.setattr(
        dex_engine,
        "bounded_json_utf8_size",
        lambda value, *, max_bytes: (_ for _ in ()).throw(TypeError("bad proof json")) if value == {"scheme": "dummy"} else 0,
    )
    res = apply_ops(
        config=DexEngineConfig(
            consensus_mode=False,
            allow_external_tools=True,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=["/bin/true"]),
        ),
        state=state,
        operations={},
        block_timestamp=0,
    )
    assert res.error == "invalid proof payload encoding"


    monkeypatch.setattr(
        dex_engine,
        "bounded_json_utf8_size",
        lambda value, *, max_bytes: (_ for _ in ()).throw(RuntimeError("bad proof json")) if value == {"scheme": "dummy"} else 0,
    )
    res = apply_ops(
        config=DexEngineConfig(
            consensus_mode=False,
            allow_external_tools=True,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=["/bin/true"]),
        ),
        state=state,
        operations={},
        block_timestamp=0,
    )
    assert res.error == "internal error"
    _patch_apply_ops_happy_path(monkeypatch)
    monkeypatch.setattr(dex_engine, "_build_signing_payloads", lambda *args, **kwargs: (_ for _ in ()).throw(ValueError("payload boom")))
    res = apply_ops(config=DexEngineConfig(), state=state, operations={"2": "ignored"}, block_timestamp=0)
    assert res.error == "payload boom"


def test_apply_ops_covers_missing_settlement_skip_match_and_comparison_errors(monkeypatch: pytest.MonkeyPatch) -> None:
    state = _empty_state()
    envs = _patch_apply_ops_happy_path(monkeypatch, settlement_env=None)
    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=False),
        state=state,
        operations={"2": "ignored"},
        block_timestamp=0,
    )
    assert res.error == "missing settlement"

    provided = _reject_settlement(envs[0].intent.intent_id)
    _patch_apply_ops_happy_path(
        monkeypatch,
        settlement_env=SettlementEnvelope(settlement=provided, proof=None),
        computed_settlement=provided,
    )
    monkeypatch.setattr(
        dex_engine,
        "_settlement_rewrite_normal_form_dict",
        lambda settlement: (_ for _ in ()).throw(AssertionError("should not compare")),
    )
    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_settlement_match=False,
            dex_config=DexConfig(reject_settlements_with_rejected_intents=False),
        ),
        state=state,
        operations={"2": "ignored"},
        block_timestamp=0,
    )
    assert res.ok is True

    _patch_apply_ops_happy_path(
        monkeypatch,
        settlement_env=SettlementEnvelope(settlement=provided, proof=None),
        computed_settlement=provided,
    )
    monkeypatch.setattr(
        dex_engine,
        "_settlement_rewrite_normal_form_dict",
        lambda settlement: (_ for _ in ()).throw(TypeError("bad compare")),
    )
    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=False, require_settlement_match=True),
        state=state,
        operations={"2": "ignored"},
        block_timestamp=0,
    )
    assert res.error == "invalid settlement payload for comparison"


def test_apply_ops_covers_validation_fee_split_proof_context_and_internal_error_paths(monkeypatch: pytest.MonkeyPatch) -> None:
    state = _empty_state()
    validation_settlement = _filled_settlement(_iid(519), fee_paid=0)
    envs = _patch_apply_ops_happy_path(
        monkeypatch,
        signed_intents=[SignedIntentEnvelope(intent=_swap_intent(intent_id=_iid(519), fields={"nonce": 1}))],
        settlement_env=SettlementEnvelope(settlement=validation_settlement, proof=None),
        computed_settlement=validation_settlement,
        validate_result=(False, None),
    )
    res = apply_ops(
        config=DexEngineConfig(require_settlement_match=False),
        state=state,
        operations={"2": "ignored"},
        block_timestamp=0,
    )
    assert res.error == "operations invalid"

    settlement = _filled_settlement(envs[0].intent.intent_id, fee_paid=7)
    _patch_apply_ops_happy_path(
        monkeypatch,
        settlement_env=SettlementEnvelope(settlement=settlement, proof=None),
        computed_settlement=settlement,
    )
    monkeypatch.setattr(dex_engine, "split_fee_with_dust_carry", lambda **kwargs: ("split", "next-fee"))
    res = apply_ops(
        config=DexEngineConfig(dex_config=DexConfig(fee_split_params=object()), require_settlement_match=False),
        state=state,
        operations={"2": "ignored"},
        block_timestamp=0,
    )
    assert res.ok is True
    assert res.state is not None
    assert res.state.fee_accumulator == "next-fee"

    proof = {"scheme": "dummy", "pre_state_commitment": "0x1", "batch_commitment": "0x2"}
    _patch_apply_ops_happy_path(
        monkeypatch,
        settlement_env=SettlementEnvelope(settlement=settlement, proof=proof),
        computed_settlement=settlement,
    )
    monkeypatch.setattr(dex_engine, "require_normal_form", lambda intents, strict_lp_order: None)
    monkeypatch.setattr(dex_engine, "_settlement_commitment_dict", lambda settlement: {"fills": []})
    monkeypatch.setattr(dex_engine, "bounded_json_utf8_size", lambda value, *, max_bytes: 1)
    monkeypatch.setattr(dex_engine, "canonical_json_bytes", lambda value: b"{}")
    monkeypatch.setattr(
        dex_engine,
        "build_proof_mining_context",
        lambda **kwargs: (_ for _ in ()).throw(RuntimeError("bad ctx")),
    )
    res = apply_ops(
        config=DexEngineConfig(
            consensus_mode=False,
            allow_external_tools=True,
            require_settlement_match=False,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=["/bin/true"]),
        ),
        state=state,
        operations={"2": "ignored"},
        block_timestamp=0,
    )
    assert res.error == "invalid proof mining context: bad ctx"

    internal_settlement = _filled_settlement(_iid(522), fee_paid=0)
    _patch_apply_ops_happy_path(
        monkeypatch,
        signed_intents=[SignedIntentEnvelope(intent=_swap_intent(intent_id=_iid(522), fields={"nonce": 1}))],
        settlement_env=SettlementEnvelope(settlement=internal_settlement, proof=None),
        computed_settlement=internal_settlement,
    )
    monkeypatch.setattr(dex_engine, "apply_settlement_pure", lambda **kwargs: (_ for _ in ()).throw(RuntimeError("boom")))
    res = apply_ops(
        config=DexEngineConfig(require_settlement_match=False),
        state=state,
        operations={"2": "ignored"},
        block_timestamp=0,
    )
    assert res.error == "internal error"


@pytest.mark.parametrize(
    ("proof", "patcher", "expected_error"),
    [
        (
            {"scheme": "dummy", "pre_state_commitment": "0x1", "batch_commitment": "0x2"},
            lambda monkeypatch: monkeypatch.setattr(
                dex_engine,
                "compute_state_root",
                lambda **kwargs: (_ for _ in ()).throw(RuntimeError("bad state")),
            ),
            "invalid state for commitment: bad state",
        ),
        (
            {"scheme": "recompute_batch_v4", "pre_state_commitment": "0x1", "batch_commitment": "0x2"},
            lambda monkeypatch: monkeypatch.setattr(dex_engine, "create_settlement_operation", lambda settlement: {"3": []}),
            "invalid settlement payload for commitment: settlement operation must be an object",
        ),
        (
            {"scheme": "dummy", "pre_state_commitment": "0x1", "batch_commitment": "0x2"},
            lambda monkeypatch: monkeypatch.setattr(
                dex_engine,
                "_settlement_commitment_dict",
                lambda settlement: (_ for _ in ()).throw(RuntimeError("bad settlement")),
            ),
            "invalid settlement payload for commitment: bad settlement",
        ),
        (
            {"scheme": "dummy", "pre_state_commitment": "0x1", "batch_commitment": "0x2"},
            lambda monkeypatch: monkeypatch.setattr(
                dex_engine,
                "bounded_json_utf8_size",
                lambda value, *, max_bytes: (_ for _ in ()).throw(ValueError("too large")) if value == {"fills": []} else 1,
            ),
            "settlement payload too large",
        ),
        (
            {"scheme": "dummy", "pre_state_commitment": "0x1", "batch_commitment": "0x2"},
            lambda monkeypatch: monkeypatch.setattr(
                dex_engine,
                "bounded_json_utf8_size",
                lambda value, *, max_bytes: (_ for _ in ()).throw(RuntimeError("bad settlement payload")) if value == {"fills": []} else 1,
            ),
            "invalid settlement payload: bad settlement payload",
        ),
        (
            {"scheme": "dummy", "pre_state_commitment": "0x1", "batch_commitment": "0x2"},
            lambda monkeypatch: monkeypatch.setattr(
                dex_engine,
                "bounded_json_utf8_size",
                lambda value, *, max_bytes: (_ for _ in ()).throw(ValueError("batch too large"))
                if isinstance(value, dict) and value.get("schema") == "zenodex_batch"
                else 1,
            ),
            "batch payload too large",
        ),
        (
            {"scheme": "dummy", "pre_state_commitment": "0x1", "batch_commitment": "0x2"},
            lambda monkeypatch: monkeypatch.setattr(
                dex_engine,
                "canonical_json_bytes",
                lambda value: (_ for _ in ()).throw(RuntimeError("bad batch payload")),
            ),
            "invalid batch payload: bad batch payload",
        ),
    ],
)
def test_apply_ops_covers_commitment_error_paths(
    monkeypatch: pytest.MonkeyPatch,
    proof: dict[str, Any],
    patcher: Any,
    expected_error: str,
) -> None:
    state = _empty_state()
    settlement = _filled_settlement(_iid(520), fee_paid=1)
    _patch_apply_ops_happy_path(
        monkeypatch,
        signed_intents=[SignedIntentEnvelope(intent=_swap_intent(intent_id=_iid(520), fields={"nonce": 1}))],
        settlement_env=SettlementEnvelope(settlement=settlement, proof=proof),
        computed_settlement=settlement,
    )
    monkeypatch.setattr(dex_engine, "require_normal_form", lambda intents, strict_lp_order: None)
    monkeypatch.setattr(dex_engine, "_settlement_commitment_dict", lambda settlement: {"fills": []})
    monkeypatch.setattr(dex_engine, "bounded_json_utf8_size", lambda value, *, max_bytes: 1)
    monkeypatch.setattr(dex_engine, "canonical_json_bytes", lambda value: b"{}")
    patcher(monkeypatch)
    res = apply_ops(
        config=DexEngineConfig(
            consensus_mode=False,
            allow_external_tools=True,
            require_settlement_match=False,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=["/bin/true"]),
        ),
        state=state,
        operations={"2": "ignored"},
        block_timestamp=0,
    )
    assert res.error == expected_error


def test_apply_ops_rejects_proof_without_settlement(monkeypatch: pytest.MonkeyPatch) -> None:
    state = _empty_state()
    proof = {"scheme": "dummy", "pre_state_commitment": "0x1", "batch_commitment": "0x2"}
    monkeypatch.setattr(dex_engine, "parse_signed_intents", lambda operations: [])
    monkeypatch.setattr(dex_engine, "parse_settlement_envelope", lambda operations: SimpleNamespace(settlement=None, proof=proof))
    monkeypatch.setattr(dex_engine, "_build_signing_payloads", lambda *args, **kwargs: ([], []))
    monkeypatch.setattr(dex_engine, "_verify_all_intent_signatures", lambda *args, **kwargs: (True, None))
    monkeypatch.setattr(dex_engine, "_validate_quote_receipt_witnesses", lambda **kwargs: None)
    monkeypatch.setattr(dex_engine, "validate_operations", lambda **kwargs: (True, None))
    monkeypatch.setattr(dex_engine, "make_proof_verifier", lambda config: _DummyVerifier((True, None)))

    res = apply_ops(
        config=DexEngineConfig(
            consensus_mode=False,
            allow_external_tools=True,
            require_settlement_match=False,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=["/bin/true"]),
        ),
        state=state,
        operations={"2": "ignored"},
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error == "proof requires settlement"

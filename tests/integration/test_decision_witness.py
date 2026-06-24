from __future__ import annotations

import src.integration.decision_witness as decision_witness
from src.integration.decision_witness import (
    DECISION_WITNESS_SCHEMA,
    DecisionWitness,
    DecisionWitnessBinding,
    verify_decision_witness_payload,
)


def _sample_witness() -> DecisionWitness:
    return DecisionWitness(
        witness_kind="exact_out_route",
        state_binding=DecisionWitnessBinding(
            binding_kind="state_snapshot",
            binding_id="pool-set:v1",
            binding_digest="abc123",
            payload={"pool_count": 3},
        ),
        request_binding=DecisionWitnessBinding(
            binding_kind="request",
            binding_id="req-1",
            binding_digest="reqdigest",
            payload={"asset_in": "A", "asset_out": "B", "amount_out_total": 6},
        ),
        quote_binding=DecisionWitnessBinding(
            binding_kind="quote",
            binding_id="quote-1",
            binding_digest="quotedigest",
            payload={"quote_source": "repaired_selected_domain"},
        ),
        epoch_binding=DecisionWitnessBinding(
            binding_kind="epoch",
            binding_id="epoch-100",
            binding_digest="epochdigest",
            payload={"epoch": 100},
        ),
        expires_at=105,
        feasibility_payload={"selected_domain_ok": True, "projection_cover_holds": True},
        canonical_key=(7, 1, "[(p0,2,5)]"),
        accounting_receipt={"amount_in_total": 7, "amount_out_total": 6},
        proof_payload={"proof_kind": "bounded_replay", "packet_schema": "zenodex/exact-out-many-pool-certified-advisory-packet/v1"},
        metadata={"note": "initial phase-2 witness shell"},
    )


def test_decision_witness_round_trips() -> None:
    witness = _sample_witness()
    assert witness.schema == DECISION_WITNESS_SCHEMA
    rebuilt = DecisionWitness.from_dict(witness.to_dict())
    assert rebuilt == witness


def test_verify_decision_witness_payload_accepts_expected_kind() -> None:
    witness = _sample_witness()
    ok, err = verify_decision_witness_payload(
        witness.to_dict(),
        expected_witness_kind="exact_out_route",
    )
    assert ok is True
    assert err is None


def test_verify_decision_witness_payload_rejects_kind_mismatch() -> None:
    witness = _sample_witness()
    ok, err = verify_decision_witness_payload(
        witness.to_dict(),
        expected_witness_kind="batch_winner",
    )
    assert ok is False
    assert err == "decision witness kind mismatch"


def test_decision_witness_rejects_non_scalar_canonical_key_item() -> None:
    payload = _sample_witness().to_dict()
    payload["canonical_key"] = [7, {"bad": True}]
    ok, err = verify_decision_witness_payload(payload)
    assert ok is False
    assert err == "canonical_key items must be int, str, or bool"


def test_verify_decision_witness_payload_sanitizes_unexpected_fault(monkeypatch) -> None:
    def _faulting_from_dict(_payload):
        raise RuntimeError("do not leak decision witness internals")

    monkeypatch.setattr(decision_witness.DecisionWitness, "from_dict", _faulting_from_dict)

    ok, err = verify_decision_witness_payload(_sample_witness().to_dict())

    assert ok is False
    assert err == "internal_error:RuntimeError"

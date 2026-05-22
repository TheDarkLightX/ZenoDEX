from __future__ import annotations

import pytest

from src.agents.zenograph_schema import (
    ZGEntity,
    ZGEntityKind,
    ZGFact,
    ZGFactStatus,
    ZGSourceKind,
    zg_entity_from_dict,
    zg_fact_from_dict,
)


def test_zg_entity_roundtrip() -> None:
    entity = ZGEntity(
        entity_id="wallet.alpha",
        kind=ZGEntityKind.WALLET,
        attrs={"chain": "ethereum", "automation_enabled": True},
    )
    roundtrip = zg_entity_from_dict(entity.to_dict())
    assert roundtrip == entity


def test_zg_fact_roundtrip() -> None:
    fact = ZGFact(
        fact_id="fact.accepted.1",
        status=ZGFactStatus.ACCEPTED,
        subject_id="wallet.alpha",
        predicate="holds",
        object_id="asset.btc",
        microtheory="OnChainFacts",
        source_id="source.chain.1",
        source_kind=ZGSourceKind.ONCHAIN,
        observed_at=10,
        effective_at=10,
        confidence_bps=10_000,
        extraction_method="indexer",
        validator_status="validated",
        validation_receipt_ids=("receipt.1",),
        accepted_by="validator.local.1",
    )
    roundtrip = zg_fact_from_dict(fact.to_dict())
    assert roundtrip == fact


def test_accepted_fact_requires_receipt_and_acceptor() -> None:
    with pytest.raises(ValueError, match="accepted facts require validation_receipt_ids"):
        ZGFact(
            fact_id="fact.accepted.bad",
            status=ZGFactStatus.ACCEPTED,
            subject_id="wallet.alpha",
            predicate="holds",
            object_id="asset.btc",
        )
    with pytest.raises(ValueError, match="accepted facts require accepted_by"):
        ZGFact(
            fact_id="fact.accepted.bad2",
            status=ZGFactStatus.ACCEPTED,
            subject_id="wallet.alpha",
            predicate="holds",
            object_id="asset.btc",
            validation_receipt_ids=("receipt.1",),
        )


def test_proposed_fact_cannot_claim_validated_status() -> None:
    with pytest.raises(ValueError, match="proposed facts cannot be validator_status=validated"):
        ZGFact(
            fact_id="fact.proposed.bad",
            status=ZGFactStatus.PROPOSED,
            subject_id="wallet.alpha",
            predicate="holds",
            object_id="asset.btc",
            validator_status="validated",
        )


def test_fact_requires_object_or_value() -> None:
    with pytest.raises(ValueError, match="fact must have object_id or value"):
        ZGFact(
            fact_id="fact.empty",
            status=ZGFactStatus.PROPOSED,
            subject_id="wallet.alpha",
            predicate="holds",
        )

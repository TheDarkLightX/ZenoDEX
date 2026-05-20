from __future__ import annotations

from src.agents.zenograph_schema import ZGEntity, ZGEntityKind, ZGFact, ZGFactStatus, ZGSourceKind
from src.agents.zenograph_store import ZenoGraphStore

import pytest


def test_store_appends_and_partitions_records(tmp_path) -> None:
    store = ZenoGraphStore(tmp_path / "zenograph")
    entity = ZGEntity(entity_id="wallet.alpha", kind=ZGEntityKind.WALLET, attrs={"chain": "ethereum"})
    proposed = ZGFact(
        fact_id="fact.proposed.1",
        status=ZGFactStatus.PROPOSED,
        subject_id="wallet.alpha",
        predicate="holds",
        object_id="asset.btc",
        source_kind=ZGSourceKind.MODEL,
        proposed_by="llm.extractor.1",
    )
    accepted = ZGFact(
        fact_id="fact.accepted.1",
        status=ZGFactStatus.ACCEPTED,
        subject_id="wallet.alpha",
        predicate="holds",
        object_id="asset.btc",
        source_kind=ZGSourceKind.ONCHAIN,
        validator_status="validated",
        validation_receipt_ids=("receipt.1",),
        accepted_by="validator.local.1",
    )

    store.append_entity(entity)
    store.append_fact(proposed)
    store.append_fact(accepted)

    assert tuple(store.iter_entities()) == (entity,)
    assert tuple(store.iter_facts(status=ZGFactStatus.PROPOSED)) == (proposed,)
    assert tuple(store.iter_facts(status=ZGFactStatus.ACCEPTED)) == (accepted,)
    assert store.has_entity("wallet.alpha") is True
    assert store.has_fact("fact.accepted.1") is True


def test_store_rejects_duplicate_ids(tmp_path) -> None:
    store = ZenoGraphStore(tmp_path / "zenograph")
    entity = ZGEntity(entity_id="wallet.alpha", kind=ZGEntityKind.WALLET, attrs={})
    store.append_entity(entity)
    with pytest.raises(ValueError, match="duplicate entity_id"):
        store.append_entity(entity)

    fact = ZGFact(
        fact_id="fact.proposed.1",
        status=ZGFactStatus.PROPOSED,
        subject_id="wallet.alpha",
        predicate="holds",
        object_id="asset.btc",
    )
    store.append_fact(fact)
    with pytest.raises(ValueError, match="duplicate fact_id"):
        store.append_fact(fact)


def test_store_reloads_existing_jsonl(tmp_path) -> None:
    root = tmp_path / "zenograph"
    first = ZenoGraphStore(root)
    first.append_entity(ZGEntity(entity_id="wallet.alpha", kind=ZGEntityKind.WALLET, attrs={}))
    first.append_fact(
        ZGFact(
            fact_id="fact.rejected.1",
            status=ZGFactStatus.REJECTED,
            subject_id="wallet.alpha",
            predicate="holds",
            object_id="asset.btc",
            validator_status="failed",
        )
    )

    second = ZenoGraphStore(root)
    assert second.has_entity("wallet.alpha") is True
    assert second.has_fact("fact.rejected.1") is True
    assert len(tuple(second.iter_facts(status=ZGFactStatus.REJECTED))) == 1

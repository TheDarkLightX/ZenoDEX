from __future__ import annotations

import pytest

from src.integration.zeno_oracle_authorization import oracle_value_hash, semantic_hash
from src.integration.zeno_oracle_trigger_authorization import (
    TriggerExecutionFacts,
    check_trigger_execute_oracle_authorization,
    trigger_execute_runtime_facts,
    trigger_execution_facts_from_obj,
)


def _facts() -> TriggerExecutionFacts:
    return TriggerExecutionFacts(
        trigger_id="trigger:take-profit:1",
        owner_pubkey="0x" + "aa" * 48,
        action_kind="execute",
        query_id="zenodex.oracle.AGRS/ZDEX.price_e8",
        observed_value_e8=125_000_000,
        trigger_price_e8=120_000_000,
        condition="gte",
        current_epoch=20,
        valid_from_epoch=10,
        valid_until_epoch=30,
        max_oracle_staleness_epochs=2,
        order_amount=500,
        asset_in="AGRS",
        asset_out="ZDEX",
    )


def _authorization_for(runtime: dict[str, object], *, value_e8: int | None = None) -> dict[str, object]:
    value = int(runtime["runtime_value_e8"] if value_e8 is None else value_e8)
    query_id = str(runtime["query_id"])
    observed_epoch = int(runtime["now_epoch"])
    return {
        "consumer_module": "zenodex.trigger",
        "action_kind": "execute",
        "action_id": str(runtime["action_id"]),
        "action_facts_hash": str(runtime["action_facts_hash"]),
        "pre_state_hash": str(runtime["pre_state_hash"]),
        "profile_id": "critical-trigger-v1",
        "query_id": query_id,
        "value_e8": value,
        "value_hash": oracle_value_hash(query_id=query_id, value_e8=value, observed_epoch=observed_epoch),
        "confidence_e8": 2_000,
        "deviation_bps": 15,
        "observed_epoch": observed_epoch,
        "expires_at_epoch": observed_epoch,
        "feed_id": "feed:agrs-zdex",
        "feed_registry_root": semantic_hash("test.feed-root", {"surface": "trigger"}),
        "query_policy_root": semantic_hash("test.query-policy-root", {"surface": "trigger"}),
        "source_registry_root": semantic_hash("test.source-root", {"surface": "trigger"}),
        "reporter_registry_root": semantic_hash("test.reporter-root", {"surface": "trigger"}),
        "evidence_class": "O3",
        "economic_envelope_id": "trigger-critical-envelope",
        "receipt_graph_root": semantic_hash("test.receipt-graph-root", {"surface": "trigger"}),
    }


def test_trigger_execute_accepts_matching_typed_oracle_authorization() -> None:
    facts = _facts()
    runtime = trigger_execute_runtime_facts(facts)
    auth = _authorization_for(runtime)

    result = check_trigger_execute_oracle_authorization(authorization_payload=auth, facts=facts)

    assert result["typed_ok"] is True


def test_trigger_execute_rejects_wrong_oracle_value() -> None:
    facts = _facts()
    runtime = trigger_execute_runtime_facts(facts)
    auth = _authorization_for(runtime, value_e8=int(runtime["runtime_value_e8"]) + 1)

    result = check_trigger_execute_oracle_authorization(authorization_payload=auth, facts=facts)

    assert result["typed_ok"] is False
    assert "runtime_value_e8 mismatch" in result["typed_errors"]


def test_trigger_execute_rejects_wrong_pre_state_context() -> None:
    facts = _facts()
    runtime = trigger_execute_runtime_facts(facts)
    auth = _authorization_for(runtime)
    auth["pre_state_hash"] = semantic_hash("test.wrong-trigger-state", {"trigger_id": facts.trigger_id})

    result = check_trigger_execute_oracle_authorization(authorization_payload=auth, facts=facts)

    assert result["typed_ok"] is False
    assert "pre_state_hash mismatch" in result["typed_errors"]


def test_trigger_execute_rejects_unsatisfied_trigger_condition() -> None:
    facts = TriggerExecutionFacts(
        **{
            **_facts().__dict__,
            "observed_value_e8": 119_999_999,
        }
    )
    auth = _authorization_for(trigger_execute_runtime_facts(_facts()))

    with pytest.raises(ValueError, match="trigger condition not satisfied"):
        check_trigger_execute_oracle_authorization(authorization_payload=auth, facts=facts)


def test_trigger_execution_facts_from_obj_normalizes_mapping_input() -> None:
    facts = trigger_execution_facts_from_obj(_facts().__dict__)

    assert facts == _facts()

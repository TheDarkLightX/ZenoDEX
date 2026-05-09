from __future__ import annotations

import pytest

from src.integration.zeno_oracle_authorization import oracle_value_hash, semantic_hash
from src.integration.zeno_oracle_trigger_authorization import (
    _ORACLE_TRIGGER_EXECUTE_PROFILE_ID,
    _ORACLE_TRIGGER_REFERENCE_QUERY_ID,
    TriggerExecutionFacts,
    check_trigger_execute_oracle_adapter_bridge,
    check_trigger_execute_oracle_authorization,
    trigger_execute_runtime_facts,
    trigger_execution_facts_from_obj,
)
from tests.integration.oracle_authorization_test_helpers import authorization_bundle


def _facts() -> TriggerExecutionFacts:
    return TriggerExecutionFacts(
        trigger_id="trigger:take-profit:1",
        owner_pubkey="0x" + "aa" * 48,
        action_kind="execute",
        query_id=_ORACLE_TRIGGER_REFERENCE_QUERY_ID,
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


def _authorization_for(
    runtime: dict[str, object],
    *,
    value_e8: int | None = None,
    evidence_class: str = "O3",
    expires_at_epoch: int | None = None,
) -> dict[str, object]:
    value = int(runtime["runtime_value_e8"] if value_e8 is None else value_e8)
    query_id = str(runtime["query_id"])
    observed_epoch = int(runtime["now_epoch"])
    auth = {
        "consumer_module": "zenodex.trigger",
        "action_kind": "execute_trigger",
        "action_id": str(runtime["action_id"]),
        "action_facts_hash": str(runtime["action_facts_hash"]),
        "pre_state_hash": str(runtime["pre_state_hash"]),
        "profile_id": _ORACLE_TRIGGER_EXECUTE_PROFILE_ID,
        "query_id": query_id,
        "value_e8": value,
        "value_hash": oracle_value_hash(query_id=query_id, value_e8=value, observed_epoch=observed_epoch),
        "confidence_e8": 2_000,
        "deviation_bps": 15,
        "observed_epoch": observed_epoch,
        "expires_at_epoch": observed_epoch if expires_at_epoch is None else int(expires_at_epoch),
        "feed_id": "feed:agrs-zdex",
        "feed_registry_root": semantic_hash("test.feed-root", {"surface": "trigger"}),
        "query_policy_root": semantic_hash("test.query-policy-root", {"surface": "trigger"}),
        "source_registry_root": semantic_hash("test.source-root", {"surface": "trigger"}),
        "reporter_registry_root": semantic_hash("test.reporter-root", {"surface": "trigger"}),
        "evidence_class": evidence_class,
        "economic_envelope_id": "trigger-critical-envelope",
        "receipt_graph_root": semantic_hash("test.receipt-graph-root", {"surface": "trigger"}),
    }
    return authorization_bundle(auth)


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
    auth["authorization"]["pre_state_hash"] = semantic_hash("test.wrong-trigger-state", {"trigger_id": facts.trigger_id})

    result = check_trigger_execute_oracle_authorization(authorization_payload=auth, facts=facts)

    assert result["typed_ok"] is False
    assert "pre_state_hash mismatch" in result["typed_errors"]


def test_trigger_execute_rejects_below_o3_authorization_evidence() -> None:
    facts = _facts()
    runtime = trigger_execute_runtime_facts(facts)
    auth = _authorization_for(runtime, evidence_class="O2")

    result = check_trigger_execute_oracle_authorization(authorization_payload=auth, facts=facts)

    assert result["typed_ok"] is False
    assert "evidence_class below required O3" in result["typed_errors"]


def test_trigger_execute_rejects_expired_authorization() -> None:
    facts = _facts()
    runtime = trigger_execute_runtime_facts(facts)
    auth = _authorization_for(runtime, expires_at_epoch=int(runtime["now_epoch"]) - 1)

    result = check_trigger_execute_oracle_authorization(authorization_payload=auth, facts=facts)

    assert result["typed_ok"] is False
    assert "authorization expired" in result["typed_errors"]


def test_trigger_execute_rejects_legacy_execute_authorization_alias() -> None:
    facts = _facts()
    runtime = trigger_execute_runtime_facts(facts)
    auth = _authorization_for(runtime)
    auth["authorization"]["action_kind"] = "execute"
    auth["authorization"]["profile_id"] = "critical-trigger-v1"

    result = check_trigger_execute_oracle_authorization(authorization_payload=auth, facts=facts)

    assert result["typed_ok"] is False
    assert "action_kind mismatch" in result["typed_errors"]
    assert "profile_id mismatch" in result["typed_errors"]


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


def test_trigger_execute_oracle_adapter_bridge_accepts_matching_runtime_action() -> None:
    facts = _facts()
    runtime = trigger_execute_runtime_facts(facts)

    def verifier(_bridge: object) -> dict[str, object]:
        return {
            "status": "accepted",
            "consumer_module": "zenodex.trigger",
            "action_kind": "execute_trigger",
            "query_id": _ORACLE_TRIGGER_REFERENCE_QUERY_ID,
            "profile_id": _ORACLE_TRIGGER_EXECUTE_PROFILE_ID,
            "action_id": runtime["action_id"],
            "errors": [],
        }

    error = check_trigger_execute_oracle_adapter_bridge(
        bridge={"schema": "test.bridge"},
        facts=facts,
        required=True,
        bridge_verifier=verifier,
    )

    assert error is None


def test_trigger_execute_oracle_adapter_bridge_rejects_missing_required_bridge() -> None:
    error = check_trigger_execute_oracle_adapter_bridge(
        bridge=None,
        facts=_facts(),
        required=True,
        bridge_verifier=lambda _bridge: {"status": "accepted"},
    )

    assert error == "execute_trigger requires oracle_adapter_bridge"


def test_trigger_execute_oracle_adapter_bridge_rejects_wrong_action_id() -> None:
    facts = _facts()

    def verifier(_bridge: object) -> dict[str, object]:
        return {
            "status": "accepted",
            "consumer_module": "zenodex.trigger",
            "action_kind": "execute_trigger",
            "query_id": _ORACLE_TRIGGER_REFERENCE_QUERY_ID,
            "profile_id": _ORACLE_TRIGGER_EXECUTE_PROFILE_ID,
            "action_id": semantic_hash("test.wrong-trigger-action", {"trigger_id": facts.trigger_id}),
            "errors": [],
        }

    error = check_trigger_execute_oracle_adapter_bridge(
        bridge={"schema": "test.bridge"},
        facts=facts,
        required=True,
        bridge_verifier=verifier,
    )

    assert error == "oracle_adapter_bridge action_id mismatch"


def test_trigger_execute_oracle_adapter_bridge_rejects_wrong_query_facts() -> None:
    facts = TriggerExecutionFacts(
        **{
            **_facts().__dict__,
            "query_id": semantic_hash("test.wrong-trigger-query", {"trigger_id": "x"}),
        }
    )

    error = check_trigger_execute_oracle_adapter_bridge(
        bridge={"schema": "test.bridge"},
        facts=facts,
        required=True,
        bridge_verifier=lambda _bridge: {"status": "accepted"},
    )

    assert error == "trigger facts query mismatch"

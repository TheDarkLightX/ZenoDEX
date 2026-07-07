from __future__ import annotations

from typing import Any, Mapping

from src.integration.zeno_oracle_authorization import semantic_hash


def terminal_receipt_graph_for_authorization(authorization: Mapping[str, Any]) -> dict[str, Any]:
    query_id = str(authorization["query_id"])
    report_ids = [
        semantic_hash("test.oracle.report", {"query_id": query_id, "i": i})
        for i in range(3)
    ]
    source_ids = [f"source:test:{i}" for i in range(3)]
    leaves_unsorted = [
        {
            "active": True,
            "bond_e8": 1_000,
            "control_group_id": f"operator:test:{i}",
            "price_e8": int(authorization["value_e8"]) + i,
            "query_id": query_id,
            "report_id": report_id,
            "reported_epoch": int(authorization["observed_epoch"]),
            "reporter_id": f"reporter:test:{i}",
            "required_bond_e8": 1_000,
            "sequence": i + 1,
            "signature": f"local-dev-sha256:{i + 1:064x}",
            "signing_payload_hash": semantic_hash("test.oracle.signing-payload", {"i": i}),
            "slash_state": "clear",
            "source_id": source_id,
            "source_observed_epoch": int(authorization["observed_epoch"]),
        }
        for i, (report_id, source_id) in enumerate(zip(report_ids, source_ids, strict=True))
    ]
    leaves = sorted(leaves_unsorted, key=lambda leaf: str(leaf["report_id"]))
    report_ids = [str(leaf["report_id"]) for leaf in leaves]
    source_ids = [str(leaf["source_id"]) for leaf in leaves]
    body: dict[str, Any] = {
        "schema": "zeno_oracle.receipt_graph.v1",
        "read_id": semantic_hash("test.oracle.read", {"query_id": query_id}),
        "aggregate_id": semantic_hash("test.oracle.aggregate", {"query_id": query_id}),
        "query_id": query_id,
        "value_hash": authorization["value_hash"],
        "value_e8": int(authorization["value_e8"]),
        "confidence_e8": int(authorization["confidence_e8"]),
        "deviation_bps": int(authorization["deviation_bps"]),
        "observed_epoch": int(authorization["observed_epoch"]),
        "expires_at_epoch": int(authorization["expires_at_epoch"]),
        "read_evidence_class": authorization["evidence_class"],
        "aggregate_evidence_class": authorization["evidence_class"],
        "reporter_count": 3,
        "min_reporters": 3,
        "source_policy_id": "source-policy:test-diverse-v1",
        "source_count": 3,
        "reporter_control_group_count": 3,
        "included_source_ids": source_ids,
        "included_report_ids": report_ids,
        "report_leaf_commitments": leaves,
        "report_leaf_root": semantic_hash("zeno_oracle.report_leaf_root.v1", {"reports": leaves}),
        "dispute_state_root": semantic_hash("test.oracle.dispute-state", {"reports": report_ids}),
        "disputed_report_ids": [],
        "feed_registry_root": authorization["feed_registry_root"],
        "query_policy_root": authorization["query_policy_root"],
        "source_registry_root": authorization["source_registry_root"],
        "reporter_registry_root": authorization["reporter_registry_root"],
    }
    body["receipt_graph_root"] = semantic_hash("zeno_oracle.receipt_graph.v1", body)
    return body


def economic_envelope_for_authorization(
    authorization: Mapping[str, Any],
    *,
    notional_value_e8: int = 1_000_000_000_000,
    max_extractable_value_e8: int = 1_000,
    reporter_count: int = 3,
    reporter_bond_required_e8: int = 1_000,
) -> dict[str, Any]:
    return {
        "schema": "zenodex.oracle.economic_security_envelope.v1",
        "query_id": authorization["query_id"],
        "consumer_module": authorization["consumer_module"],
        "action_kind": authorization["action_kind"],
        "notional_value_e8": notional_value_e8,
        "max_extractable_value_e8": max_extractable_value_e8,
        "attack_cost_floor_e8": max_extractable_value_e8,
        "required_attack_margin_bps": 0,
        "reporter_count": reporter_count,
        "reporter_reward_budget_e8": 90_000_000,
        "reporter_reward_per_report_e8": 30_000_000,
        "honest_reporter_cost_e8": 20_000_000,
        "honest_reporter_risk_premium_e8": 5_000_000,
        "reporter_bond_required_e8": reporter_bond_required_e8,
        "slash_fraction_bps": 10_000,
        "expected_cheat_gain_e8": max_extractable_value_e8,
        "deterrence_margin_bps": 0,
        "dispute_reward_e8": 10_000_000,
        "dispute_budget_e8": 20_000_000,
        "fee_paid_e8": 100_000_000,
        "reporter_fee_share_e8": 30_000_000,
        "treasury_fee_share_e8": 40_000_000,
        "burn_fee_share_e8": 30_000_000,
    }


def economic_envelope_hash(envelope: Mapping[str, Any]) -> str:
    return semantic_hash("zenodex.oracle.economic_envelope.v1", envelope)


def authorization_bundle(
    authorization: Mapping[str, Any],
    *,
    include_economic_envelope: bool = True,
    bind_economic_envelope_id: bool = True,
) -> dict[str, Any]:
    auth = dict(authorization)
    graph = terminal_receipt_graph_for_authorization(auth)
    auth["receipt_graph_root"] = graph["receipt_graph_root"]
    bundle = {
        "schema": "zeno_oracle.oracle_authorization_bundle.v1",
        "authorization": auth,
        "receipt_graph": graph,
    }
    if include_economic_envelope:
        envelope = economic_envelope_for_authorization(auth)
        if bind_economic_envelope_id:
            auth["economic_envelope_id"] = economic_envelope_hash(envelope)
        bundle["economic_envelope"] = envelope
    return bundle

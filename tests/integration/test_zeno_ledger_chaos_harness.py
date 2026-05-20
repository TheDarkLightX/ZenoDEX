from __future__ import annotations

from tools.zeno_ledger_chaos_harness import run_chaos_harness, scenario_equivocation, scenario_gossip_flood
from tools.zeno_ledger_network_scenario import ChaosNetworkModel


def test_chaos_harness_runs_all_named_scenarios() -> None:
    report = run_chaos_harness()

    assert report["ok"] is True
    assert report["scenario_count"] == 8
    assert {item["scenario"] for item in report["scenarios"]} == {
        "auth_failures",
        "degraded_network",
        "equivocation",
        "fork_choice",
        "gossip_flood",
        "live_quorum",
        "peer_churn",
        "validator_schedule",
    }


def test_gossip_flood_rejects_duplicate_envelope() -> None:
    report = scenario_gossip_flood()
    metrics = report["model_report"]["metrics"]

    assert report["ok"] is True
    assert metrics["block_rejected:duplicate_gossip_envelope"] == 1
    assert metrics["block_rejected:gossip_oversized_tx_count"] == 1


def test_equivocation_emits_slashing_receipt() -> None:
    report = scenario_equivocation()
    node = report["model_report"]["nodes"]["node-a"]

    assert report["ok"] is True
    assert node["equivocation_event_count"] == 1
    assert node["slashing_receipt_count"] == 1


def test_network_model_rejects_wrong_chain_peer() -> None:
    model = ChaosNetworkModel()
    model.add_node("node-a")
    result = model.admit_peer(node_id="node-a", peer_id="node-b", peer_chain_id="wrong")

    assert result["ok"] is False
    assert result["errors"] == ["peer_chain_id_mismatch"]

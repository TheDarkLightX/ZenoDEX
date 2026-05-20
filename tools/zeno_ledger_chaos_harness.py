#!/usr/bin/env python3
"""Run deterministic ZenoLedger adversarial chaos scenarios."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.zeno_ledger_network_scenario import BlockEnvelope, ChaosNetworkModel, VALID_AUTH_TOKEN


REPORT_SCHEMA = "zenodex.zeno_ledger.chaos_harness_report.v0"


def _base_model() -> ChaosNetworkModel:
    model = ChaosNetworkModel()
    model.add_node("node-a")
    model.add_node("node-b")
    return model


def scenario_peer_churn() -> dict[str, Any]:
    model = _base_model()
    accepted = model.admit_peer(node_id="node-a", peer_id="node-b")
    duplicate = model.admit_peer(node_id="node-a", peer_id="node-b")
    wrong_chain = model.admit_peer(node_id="node-a", peer_id="node-c", peer_chain_id="wrong")
    return _scenario_report("peer_churn", model, [accepted, duplicate, wrong_chain])


def scenario_gossip_flood() -> dict[str, Any]:
    model = _base_model()
    block = model.make_block(node_id="node-a")
    first = model.submit_block(node_id="node-a", envelope=block)
    duplicate = model.submit_block(node_id="node-a", envelope=block)
    oversize = BlockEnvelope(
        **{**block.__dict__, "envelope_id": "oversize", "height": model.node("node-a").height + 1, "previous_hash": model.node("node-a").tip_hash, "tx_count": 101}
    )
    oversized = model.submit_block(node_id="node-a", envelope=oversize)
    return _scenario_report("gossip_flood", model, [first, duplicate, oversized])


def scenario_equivocation() -> dict[str, Any]:
    model = _base_model()
    block = model.make_block(node_id="node-a")
    first = model.submit_block(node_id="node-a", envelope=block)
    conflict = BlockEnvelope(
        envelope_id="conflict",
        height=block.height,
        previous_hash=block.previous_hash,
        block_hash="0x" + "12" * 32,
        proposer_id=block.proposer_id,
        body_root=block.body_root,
        checkpoint_hash=block.checkpoint_hash,
    )
    second = model.submit_block(node_id="node-a", envelope=conflict)
    return _scenario_report("equivocation", model, [first, second])


def scenario_fork_choice() -> dict[str, Any]:
    model = _base_model()
    block1 = model.make_block(node_id="node-a")
    accepted = model.submit_block(node_id="node-a", envelope=block1)
    stale = model.make_block(node_id="node-a", height=1, salt="stale")
    stale_result = model.submit_block(node_id="node-a", envelope=stale)
    extending = model.make_block(node_id="node-a", salt="extend")
    extend_result = model.submit_block(node_id="node-a", envelope=extending)
    return _scenario_report("fork_choice", model, [accepted, stale_result, extend_result])


def scenario_auth_failures() -> dict[str, Any]:
    model = _base_model()
    block = model.make_block(node_id="node-a")
    bad_auth = BlockEnvelope(**{**block.__dict__, "auth_token": "bad"})
    rejected = model.submit_block(node_id="node-a", envelope=bad_auth)
    accepted_block = BlockEnvelope(**{**block.__dict__, "envelope_id": "auth-valid-retry"})
    accepted = model.submit_block(node_id="node-a", envelope=accepted_block)
    return _scenario_report("auth_failures", model, [rejected, accepted])


def scenario_validator_schedule() -> dict[str, Any]:
    model = _base_model()
    wrong = model.make_block(node_id="node-a", proposer_id="validator-c")
    wrong_result = model.submit_block(node_id="node-a", envelope=wrong)
    right = model.make_block(node_id="node-a", proposer_id=model.scheduled_proposer(1), salt="right")
    right_result = model.submit_block(node_id="node-a", envelope=right)
    return _scenario_report("validator_schedule", model, [wrong_result, right_result])


def scenario_live_quorum() -> dict[str, Any]:
    model = _base_model()
    missing = model.checkpoint_quorum_check(node_id="node-a", payload_hash="0x" + "01" * 32, signers=["validator-a"])
    duplicate = model.checkpoint_quorum_check(
        node_id="node-a",
        payload_hash="0x" + "01" * 32,
        signers=["validator-a", "validator-a"],
    )
    good = model.checkpoint_quorum_check(
        node_id="node-a",
        payload_hash="0x" + "01" * 32,
        signers=["validator-a", "validator-b"],
    )
    return _scenario_report("live_quorum", model, [missing, duplicate, good])


def scenario_degraded_network() -> dict[str, Any]:
    model = _base_model()
    a1 = model.submit_block(node_id="node-a", envelope=model.make_block(node_id="node-a"))
    delayed = model.make_block(node_id="node-b", height=1, salt="delayed")
    delayed_result = model.submit_block(node_id="node-b", envelope=delayed)
    b2 = model.submit_block(node_id="node-b", envelope=model.make_block(node_id="node-b", salt="heal"))
    return _scenario_report("degraded_network", model, [a1, delayed_result, b2])


SCENARIOS: dict[str, Callable[[], dict[str, Any]]] = {
    "peer_churn": scenario_peer_churn,
    "gossip_flood": scenario_gossip_flood,
    "equivocation": scenario_equivocation,
    "fork_choice": scenario_fork_choice,
    "auth_failures": scenario_auth_failures,
    "validator_schedule": scenario_validator_schedule,
    "live_quorum": scenario_live_quorum,
    "degraded_network": scenario_degraded_network,
}


def run_chaos_harness(selected: list[str] | None = None) -> dict[str, Any]:
    names = selected or sorted(SCENARIOS)
    scenario_reports = [SCENARIOS[name]() for name in names]
    errors: list[str] = []
    for report in scenario_reports:
        errors.extend(f"{report['scenario']}: {error}" for error in report["errors"])
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "scenario_count": len(scenario_reports),
        "scenarios": scenario_reports,
    }


def _scenario_report(name: str, model: ChaosNetworkModel, results: list[dict[str, Any]]) -> dict[str, Any]:
    report = model.report()
    errors = _invariant_errors(name, report, results)
    return {
        "schema": "zenodex.zeno_ledger.chaos_scenario_report.v0",
        "scenario": name,
        "ok": not errors,
        "errors": errors,
        "steps": results,
        "model_report": report,
    }


def _invariant_errors(name: str, report: dict[str, Any], results: list[dict[str, Any]]) -> list[str]:
    errors: list[str] = []
    metrics = report["metrics"]
    if name == "gossip_flood" and metrics.get("block_rejected:duplicate_gossip_envelope", 0) < 1:
        errors.append("duplicate gossip envelope was not rejected")
    if name == "equivocation":
        node = report["nodes"]["node-a"]
        if node["equivocation_event_count"] < 1 or node["slashing_receipt_count"] < 1:
            errors.append("same-height conflict did not emit equivocation/slashing evidence")
    if name == "auth_failures" and metrics.get("block_rejected:auth_failed", 0) < 1:
        errors.append("auth failure was not rejected")
    if name == "validator_schedule" and metrics.get("block_rejected:wrong_proposer", 0) < 1:
        errors.append("wrong proposer was not rejected")
    if name == "live_quorum":
        if metrics.get("checkpoint_rejected:checkpoint_quorum_missing", 0) < 1:
            errors.append("missing quorum was not rejected")
        if metrics.get("checkpoint_accepted", 0) < 1:
            errors.append("valid checkpoint quorum was not accepted")
    if name == "peer_churn":
        if metrics.get("peer_rejected:duplicate_peer", 0) < 1:
            errors.append("duplicate peer was not rejected")
        if metrics.get("peer_rejected:peer_chain_id_mismatch", 0) < 1:
            errors.append("wrong-chain peer was not rejected")
    if not any(step["ok"] for step in results):
        errors.append("scenario did not accept any valid action")
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scenario", action="append", choices=sorted(SCENARIOS))
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    report = run_chaos_harness(args.scenario)
    print(json.dumps(report, indent=2 if args.json else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

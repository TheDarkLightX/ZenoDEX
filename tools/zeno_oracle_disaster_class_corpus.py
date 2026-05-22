#!/usr/bin/env python3
"""Replay the public first-shell ZenoOracle named disaster-class corpus."""

from __future__ import annotations

import argparse
import copy
import json
import sys
import tempfile
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
TOOLS = ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from check_cross_module_oracle_split_brain_v1 import check_cross_module_oracle_split_brain_v1  # noqa: E402
from zenodex_oracle_devnet_disaster_harness import run_harness  # noqa: E402
from zenodex_oracle_feed_registry import sample_feed_registry, verify_feed_registry  # noqa: E402
from zenodex_oracle_reporter_economics_replay import (  # noqa: E402
    sample_replay,
    verify_reporter_economics_replay,
)
from zenodex_oracle_source_diversity import (  # noqa: E402
    sample_source_diversity,
    source_set_content_hash,
    verify_source_diversity,
)
from zenoproof_verify import (  # noqa: E402
    artifact_content_hash,
    oracle_o4_bridge_content_hash,
    sample_artifact,
    sample_oracle_o5_bridge,
    sample_hash as zenoproof_sample_hash,
    verify_oracle_o4_bridge,
    verify_zenoproof_artifact,
)


CORPUS_SCHEMA = "zenodex.oracle.disaster_class_corpus.v1"
DEFAULT_ZENOPROOF_REGISTRY = ROOT / "tools" / "zenoproof_registry_manifest.json"
REPLAY_COMMAND = "python3 tools/zeno_oracle_disaster_class_corpus.py --format text"
NOT_CLAIMED = [
    "does_not_claim_exhaustive_production_oracle_safety",
    "does_not_claim_true_market_price",
    "does_not_claim_reporter_honesty",
    "does_not_claim_live_proof_network",
    "does_not_claim_onchain_governance_live",
]


class CorpusError(RuntimeError):
    pass


def _case_receipt(
    class_id: str,
    *,
    manifest_axis: str,
    guard_family: str,
    obligations: list[str],
    ok: bool,
    expected: str,
    observed: Mapping[str, Any],
    replay_command: str = REPLAY_COMMAND,
) -> dict[str, Any]:
    return {
        "class_id": class_id,
        "manifest_axis": manifest_axis,
        "guard_family": guard_family,
        "obligations": obligations,
        "ok": bool(ok),
        "status": "closed" if ok else "failed",
        "expected": expected,
        "observed": dict(observed),
        "replay_command": replay_command,
    }


def _has_error(errors: list[str], expected: str) -> bool:
    return expected in errors or any(error.startswith(f"{expected}:") for error in errors)


def _source_cartel_case() -> dict[str, Any]:
    source_set = copy.deepcopy(sample_source_diversity())
    for source in source_set["sources"]:
        source["operator_id"] = "operator.cartel"
        source["venue_id"] = "venue.cartel"
        source["data_family_id"] = "family.cartel"
        source["transport_id"] = "transport.cartel"
        source["jurisdiction_id"] = "jurisdiction.cartel"
    source_set["source_set_id"] = source_set_content_hash(source_set)

    result = verify_source_diversity(source_set).to_json_obj()
    required_errors = [
        "not_enough_distinct_operators",
        "not_enough_distinct_venues",
        "not_enough_distinct_data_families",
        "not_enough_distinct_transports",
        "not_enough_distinct_jurisdictions",
        "operator_concentration_exceeds_policy",
    ]
    ok = result["status"] == "rejected" and all(error in result["errors"] for error in required_errors)
    return _case_receipt(
        "source_cartel",
        manifest_axis="source_cartel_collapses_quorum",
        guard_family="source_reporter_quorum_gate",
        obligations=["evidence_floor_o3", "reporter_independence", "source_diversity"],
        ok=ok,
        expected="collapsed source/operator diversity is rejected before quorum can satisfy O3 policy",
        observed={
            "verifier": "zenodex_oracle_source_diversity.verify_source_diversity",
            "status": result["status"],
            "errors": result["errors"],
            "distinct_operator_count": result["distinct_operator_count"],
            "distinct_venue_count": result["distinct_venue_count"],
            "distinct_data_family_count": result["distinct_data_family_count"],
        },
    )


def _dispute_griefing_case() -> dict[str, Any]:
    replay = copy.deepcopy(sample_replay())
    for event in replay["events"]:
        if event.get("type") == "open_dispute":
            event["dispute_bond_e8"] = 0
            break
    else:  # pragma: no cover
        raise CorpusError("sample reporter replay has no open_dispute event")

    result = verify_reporter_economics_replay(replay).to_json_obj()
    ok = result["status"] == "rejected" and "dispute_bond_required" in result["errors"]
    return _case_receipt(
        "dispute_griefing",
        manifest_axis="open_dispute_feeds_critical_read",
        guard_family="freshness_dispute_gate",
        obligations=["dispute_clear", "economic_margin", "reporter_bonded"],
        ok=ok,
        expected="zero-bond dispute griefing is rejected by the reporter economics replay",
        observed={
            "verifier": "zenodex_oracle_reporter_economics_replay.verify_reporter_economics_replay",
            "status": result["status"],
            "errors": result["errors"],
            "dispute_count": result["dispute_count"],
        },
    )


def _registry_drift_case() -> dict[str, Any]:
    registry = copy.deepcopy(sample_feed_registry())
    registry["feeds"][0]["query_spec"]["base_asset"] = "zdex"
    result = verify_feed_registry(registry).to_json_obj()
    ok = result["status"] == "rejected" and all(
        _has_error(result["errors"], expected)
        for expected in (
            "registry_content_hash_mismatch",
            "feed_content_hash_mismatch",
            "query_spec_content_hash_mismatch",
        )
    )
    return _case_receipt(
        "registry_drift",
        manifest_axis="registry_root_drift",
        guard_family="query_registry_policy_gate",
        obligations=["query_semantics", "registry_root_binding", "schema_total"],
        ok=ok,
        expected="registry/query drift is rejected by nested content-hash bindings",
        observed={
            "verifier": "zenodex_oracle_feed_registry.verify_feed_registry",
            "status": result["status"],
            "errors": result["errors"],
        },
    )


def _load_registry(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise CorpusError(f"ZenoProof registry root is not an object: {path}")
    return obj


def _verifier_spoofing_case(registry_path: Path) -> dict[str, Any]:
    registry = _load_registry(registry_path)
    artifact = sample_artifact()
    artifact["verifier_id"] = zenoproof_sample_hash("zenodex.zenoproof.spoofed.verifier")
    artifact["proof_id"] = artifact_content_hash(artifact)
    result = verify_zenoproof_artifact(artifact, registry, now_epoch=150).to_json_obj()
    ok = result["status"] == "rejected" and "verifier_not_registered" in result["errors"]
    return _case_receipt(
        "verifier_spoofing",
        manifest_axis="verifier_spoofed_o4_upgrade",
        guard_family="proof_verifier_registry_gate",
        obligations=["evidence_floor_o3", "proof_verifier_bound", "registry_root_binding"],
        ok=ok,
        expected="artifact signed under an unknown verifier id cannot upgrade Oracle evidence",
        observed={
            "verifier": "zenoproof_verify.verify_zenoproof_artifact",
            "status": result["status"],
            "errors": result["errors"],
            "policy_ok": result["policy_ok"],
            "verifier_id": result["verifier_id"],
        },
    )


def _o5_independence_spoofing_case(registry_path: Path) -> dict[str, Any]:
    registry = _load_registry(registry_path)
    bridge = sample_oracle_o5_bridge()
    del bridge["o5_independence_witness"]
    bridge["bridge_id"] = oracle_o4_bridge_content_hash(bridge)
    result = verify_oracle_o4_bridge(bridge, registry, now_epoch=150).to_json_obj()
    ok = (
        result["status"] == "rejected"
        and result["receipt_status"] == "accepted"
        and result["proof_status"] == "accepted"
        and "o5_independence_witness_required" in result["errors"]
    )
    return _case_receipt(
        "o5_independence_spoofing",
        manifest_axis="o5_upgrade_without_independent_evidence",
        guard_family="proof_independence_gate",
        obligations=["evidence_floor_o3", "proof_independence", "proof_verifier_bound", "registry_root_binding"],
        ok=ok,
        expected="an O5-labeled Oracle bridge with an accepted O3 receipt and accepted primary proof is rejected without an independence witness",
        observed={
            "verifier": "zenoproof_verify.verify_oracle_o4_bridge",
            "status": result["status"],
            "errors": result["errors"],
            "receipt_status": result["receipt_status"],
            "proof_status": result["proof_status"],
            "o5_witness_status": result["o5_witness_status"],
        },
    )


def _proof_timeout_case(registry_path: Path) -> dict[str, Any]:
    registry = copy.deepcopy(_load_registry(registry_path))
    slow_verifier_id = zenoproof_sample_hash("zenodex.zenoproof.timeout.verifier")
    slow_policy_root = zenoproof_sample_hash("zenodex.zenoproof.timeout.policy")
    slow_toolchain_id = zenoproof_sample_hash("zenodex.zenoproof.timeout.toolchain")
    registry["verifiers"].append(
        {
            "verifier_id": slow_verifier_id,
            "name": "timeout-must-not-succeed-v0",
            "proof_kinds": ["tla"],
            "current_policy_root": slow_policy_root,
            "toolchain_ids": [slow_toolchain_id],
            "revoked": False,
            "max_input_bytes": 1_000_000,
            "timeout_ms": 10,
            "execution_mode": "subprocess_json",
            "verifier_command": [
                sys.executable,
                "-c",
                "import time; time.sleep(1); print('{\"ok\": true}')",
            ],
            "allow_path_lookup": False,
        }
    )
    artifact = sample_artifact()
    artifact["verifier_id"] = slow_verifier_id
    artifact["verifier_policy_root"] = slow_policy_root
    artifact["toolchain_id"] = slow_toolchain_id
    artifact["proof_id"] = artifact_content_hash(artifact)
    result = verify_zenoproof_artifact(artifact, registry, now_epoch=150).to_json_obj()
    expected_error = "external_verifier_failed:proof verification timed out"
    ok = result["status"] == "rejected" and expected_error in result["errors"]
    return _case_receipt(
        "proof_timeout_treated_as_success",
        manifest_axis="proof_timeout_treated_as_success",
        guard_family="proof_verifier_registry_gate",
        obligations=["proof_verifier_bound", "resource_budget"],
        ok=ok,
        expected="a verifier subprocess timeout rejects even if the child would later print an ok result",
        observed={
            "verifier": "zenoproof_verify.verify_zenoproof_artifact",
            "status": result["status"],
            "errors": result["errors"],
            "proof_ok": result["proof_ok"],
            "verifier_id": result["verifier_id"],
        },
    )


def _replay_integrity_case(store_root: Path | None) -> dict[str, Any]:
    if store_root is None:
        with tempfile.TemporaryDirectory(prefix="zeno-oracle-class-corpus-") as tmp:
            receipt = run_harness(Path(tmp))
    else:
        store_root.mkdir(parents=True, exist_ok=True)
        receipt = run_harness(store_root)

    closed = {case["disaster_state"] for case in receipt["cases"] if case["ok"]}
    required = {
        "replay_state_differs_from_live_state",
        "missing_artifact_survives_replay",
        "tampered_artifact_survives_replay",
        "duplicate_event_changes_balance_or_reward",
        "reordered_event_survives_replay",
        "partial_event_write_survives_replay",
    }
    ok = receipt["status"] == "accepted" and required.issubset(closed)
    return _case_receipt(
        "terminal_replay_integrity",
        manifest_axis="terminal_dag_missing_dependency",
        guard_family="terminal_receipt_dag_gate",
        obligations=["dependency_order", "duplicate_reject", "receipt_dag_closed", "schema_total"],
        ok=ok,
        expected="terminal replay rejects missing, tampered, duplicate, reordered, and partial journal states",
        observed={
            "verifier": "zenodex_oracle_devnet_disaster_harness.run_harness",
            "status": receipt["status"],
            "selected_disaster_state_count": receipt["selected_disaster_state_count"],
            "failed_count": receipt["failed_count"],
            "required_replay_states": sorted(required),
            "closed_required_replay_states": sorted(required.intersection(closed)),
        },
        replay_command="python3 tools/zenodex_oracle_devnet_disaster_harness.py --format text",
    )


def _cross_module_split_brain_case() -> dict[str, Any]:
    report = check_cross_module_oracle_split_brain_v1()
    scenarios = {scenario["scenario_id"]: scenario for scenario in report["scenarios"]}
    required_rejections = {
        "recovery_divergence_split_brain_rejects",
        "recovery_epoch_lag_split_brain_rejects",
    }
    ok = report["ok"] is True and required_rejections.issubset(scenarios)
    for scenario_id in required_rejections:
        scenario = scenarios.get(scenario_id, {})
        ok = ok and scenario.get("status") == "OK"
        ok = ok and scenario.get("rejection_reason") == "current_cross_module_sync_not_ok"
    ok = ok and scenarios.get("aligned_shared_world_reenables_under_same_local_gate", {}).get("status") == "OK"
    return _case_receipt(
        "cross_module_split_brain",
        manifest_axis="cross_module_split_brain_divergence",
        guard_family="cross_module_sync_gate",
        obligations=["cross_module_sync", "runtime_state_binding", "time_freshness"],
        ok=bool(ok),
        expected="local-green but cross-module-divergent oracle worlds reject risky recovery while aligned control accepts",
        observed={
            "verifier": "check_cross_module_oracle_split_brain_v1.check_cross_module_oracle_split_brain_v1",
            "scenario_count": report["scenario_count"],
            "required_rejection_scenarios": sorted(required_rejections),
            "scenario_ids": sorted(scenarios),
        },
        replay_command="python3 tools/check_cross_module_oracle_split_brain_v1.py",
    )


def build_corpus(
    *,
    zenoproof_registry: Path = DEFAULT_ZENOPROOF_REGISTRY,
    store_root: Path | None = None,
) -> dict[str, Any]:
    cases: list[dict[str, Any]] = []
    for builder in (
        _source_cartel_case,
        _dispute_griefing_case,
        _registry_drift_case,
        lambda: _verifier_spoofing_case(zenoproof_registry),
        lambda: _o5_independence_spoofing_case(zenoproof_registry),
        lambda: _proof_timeout_case(zenoproof_registry),
        lambda: _replay_integrity_case(store_root),
        _cross_module_split_brain_case,
    ):
        try:
            cases.append(builder())
        except Exception as exc:  # pragma: no cover - tests keep this closed.
            cases.append(
                _case_receipt(
                    getattr(builder, "__name__", "anonymous_case"),
                    manifest_axis="unknown",
                    guard_family="unknown",
                    obligations=[],
                    ok=False,
                    expected="case executes without uncaught exception",
                    observed={"exception": f"{type(exc).__name__}:{exc}"},
                )
            )
    failed = [case for case in cases if not case["ok"]]
    return {
        "schema": CORPUS_SCHEMA,
        "ok": not failed,
        "status": "accepted" if not failed else "rejected",
        "named_disaster_class_count": len(cases),
        "closed_class_count": len(cases) - len(failed),
        "failed_class_count": len(failed),
        "cases": cases,
        "not_claimed": NOT_CLAIMED,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zenoproof-registry", default=str(DEFAULT_ZENOPROOF_REGISTRY))
    parser.add_argument("--store-root", default=None, help="optional root directory for devnet replay stores")
    parser.add_argument("--output", default=None, help="optional output path for the corpus receipt")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    receipt = build_corpus(
        zenoproof_registry=Path(args.zenoproof_registry),
        store_root=None if args.store_root is None else Path(args.store_root),
    )
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    if args.format == "json":
        sys.stdout.write(text)
    else:
        sys.stdout.write(
            "\n".join(
                [
                    f"named_disaster_class_count = {receipt['named_disaster_class_count']}",
                    f"closed_class_count = {receipt['closed_class_count']}",
                    f"failed_class_count = {receipt['failed_class_count']}",
                    f"status = {receipt['status']}",
                ]
            )
            + "\n"
        )
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

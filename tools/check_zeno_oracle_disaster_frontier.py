#!/usr/bin/env python3
"""Check the public ZenoOracle production-disaster frontier catalog."""

from __future__ import annotations

import argparse
import hashlib
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
    sys.path.insert(1, str(TOOLS))

from check_disaster_obligation_certificate import evaluate_manifest  # noqa: E402
from zeno_oracle_disaster_class_corpus import build_corpus  # noqa: E402
from zenodex_oracle_devnet_disaster_harness import run_harness  # noqa: E402


FRONTIER_SCHEMA = "zenodex.oracle.production_disaster_frontier.v1"
REPORT_SCHEMA = "zenodex.oracle.production_disaster_frontier_check.v1"
DEFAULT_MANIFEST = ROOT / "tools" / "zeno_oracle_disaster_obligation_certificate_manifest.json"
ALLOWED_STATUS = {"bounded_devnet_closed", "public_corpus_closed", "production_blocked", "research_backlog"}
FRONTIER_KEYS = {"schema", "frontier_id", "families", "not_claimed"}
FAMILY_KEYS = {
    "family_id",
    "source",
    "status",
    "manifest_axis",
    "manifest_obligations",
    "corpus_class_id",
    "devnet_disaster_state",
    "replay_commands",
    "blockers",
}
REQUIRED_NOT_CLAIMS = {
    "does_not_claim_exhaustive_production_disaster_search",
    "does_not_claim_live_oracle_network_safety",
    "does_not_claim_reporter_honesty",
    "does_not_claim_cross_domain_finality",
}


def _canonical_bytes(obj: Mapping[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def frontier_content_hash(frontier: Mapping[str, Any]) -> str:
    payload = dict(frontier)
    payload.pop("frontier_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def _unknown_fields(obj: Mapping[str, Any], *, allowed: set[str], label: str, errors: list[str]) -> None:
    for key in obj:
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _string_list(obj: Mapping[str, Any], key: str, errors: list[str], *, required: bool = False) -> list[str]:
    raw = obj.get(key)
    if raw is None and not required:
        return []
    if not isinstance(raw, list):
        errors.append(f"{key}_must_be_list")
        return []
    values: list[str] = []
    for index, item in enumerate(raw):
        if not isinstance(item, str) or not item.strip():
            errors.append(f"{key}_{index}_must_be_nonempty_string")
        else:
            values.append(item)
    return values


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must be a JSON object")
    return obj


def _family(
    family_id: str,
    *,
    source: str,
    status: str,
    manifest_axis: str,
    manifest_obligations: list[str],
    corpus_class_id: str | None = None,
    devnet_disaster_state: str | None = None,
    replay_commands: list[str] | None = None,
    blockers: list[str] | None = None,
) -> dict[str, Any]:
    result: dict[str, Any] = {
        "family_id": family_id,
        "source": source,
        "status": status,
        "manifest_axis": manifest_axis,
        "manifest_obligations": sorted(manifest_obligations),
        "replay_commands": list(replay_commands or []),
        "blockers": list(blockers or []),
    }
    if corpus_class_id is not None:
        result["corpus_class_id"] = corpus_class_id
    if devnet_disaster_state is not None:
        result["devnet_disaster_state"] = devnet_disaster_state
    return result


def sample_frontier() -> dict[str, Any]:
    devnet_command = "python3 tools/zenodex_oracle_devnet_disaster_harness.py --format text"
    corpus_command = "python3 tools/zeno_oracle_disaster_class_corpus.py --format text"
    policy_command = "python3 tools/check_zeno_oracle_live_economics_policy.py --format text"
    perps_snapshot_command = "python3 tools/check_zeno_oracle_perps_snapshot_gate.py --format text"
    finality_command = "python3 tools/check_zeno_oracle_cross_domain_finality_gate.py --format text"
    reporter_soak_command = "python3 tools/check_zeno_oracle_reporter_soak_gate.py --format text"
    families = [
        _family(
            "accepted_read_without_accepted_aggregate",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="terminal_dag_missing_dependency",
            manifest_obligations=["dependency_order", "receipt_dag_closed", "schema_total"],
            devnet_disaster_state="accepted_read_without_accepted_aggregate",
            replay_commands=[devnet_command],
        ),
        _family(
            "adapter_bridge_without_matching_read",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="terminal_dag_missing_dependency",
            manifest_obligations=["dependency_order", "receipt_dag_closed", "schema_total"],
            devnet_disaster_state="adapter_bridge_without_matching_read",
            replay_commands=[devnet_command],
        ),
        _family(
            "receipt_borrowed_across_consumer_action",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="trigger_receipt_borrowing",
            manifest_obligations=["critical_action_bound", "receipt_dag_closed", "runtime_state_binding", "schema_total", "value_binding"],
            devnet_disaster_state="receipt_borrowed_across_consumer_action",
            replay_commands=[devnet_command],
        ),
        _family(
            "replay_state_differs_from_live_state",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="terminal_graph_authorization_mismatch",
            manifest_obligations=["receipt_dag_closed", "registry_root_binding", "runtime_state_binding", "schema_total", "value_binding"],
            devnet_disaster_state="replay_state_differs_from_live_state",
            replay_commands=[devnet_command],
        ),
        _family(
            "missing_artifact_survives_replay",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="terminal_dag_missing_dependency",
            manifest_obligations=["dependency_order", "receipt_dag_closed", "schema_total"],
            devnet_disaster_state="missing_artifact_survives_replay",
            replay_commands=[devnet_command],
        ),
        _family(
            "tampered_artifact_survives_replay",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="terminal_graph_authorization_mismatch",
            manifest_obligations=["receipt_dag_closed", "registry_root_binding", "runtime_state_binding", "schema_total", "value_binding"],
            devnet_disaster_state="tampered_artifact_survives_replay",
            replay_commands=[devnet_command],
        ),
        _family(
            "duplicate_event_changes_balance_or_reward",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="duplicate_receipt_id_shadowing",
            manifest_obligations=["dependency_order", "duplicate_reject", "receipt_dag_closed", "schema_total"],
            devnet_disaster_state="duplicate_event_changes_balance_or_reward",
            replay_commands=[devnet_command],
        ),
        _family(
            "revoked_or_unregistered_reporter_admitted",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="underbonded_reporter_accepted",
            manifest_obligations=["economic_margin", "receipt_dag_closed", "reporter_bonded", "schema_total"],
            devnet_disaster_state="revoked_or_unregistered_reporter_admitted",
            replay_commands=[devnet_command],
        ),
        _family(
            "policy_downgrade_changes_existing_query_semantics",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="governance_policy_downgrade",
            manifest_obligations=["evidence_floor_o3", "query_semantics", "registry_root_binding", "schema_total"],
            devnet_disaster_state="policy_downgrade_changes_existing_query_semantics",
            replay_commands=[devnet_command],
        ),
        _family(
            "high_uncertainty_price_used_by_critical_action",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="wrong_value_hash_consumed_by_action",
            manifest_obligations=["critical_action_bound", "receipt_dag_closed", "schema_total", "value_binding"],
            devnet_disaster_state="high_uncertainty_price_used_by_critical_action",
            replay_commands=[devnet_command],
        ),
        _family(
            "resource_bound_controlled_by_external_input",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="public_corpus_closed",
            manifest_axis="proof_timeout_treated_as_success",
            manifest_obligations=["proof_verifier_bound", "resource_budget", "schema_total"],
            corpus_class_id="proof_timeout_treated_as_success",
            replay_commands=[corpus_command],
        ),
        _family(
            "reward_exceeds_verified_budget",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="reward_budget_overdraft",
            manifest_obligations=["budget_conservation", "economic_margin", "schema_total"],
            devnet_disaster_state="reward_exceeds_verified_budget",
            replay_commands=[devnet_command],
        ),
        _family(
            "slash_exceeds_bond",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="slash_exceeds_reporter_bond",
            manifest_obligations=["budget_conservation", "economic_margin", "reporter_bonded", "schema_total"],
            devnet_disaster_state="slash_exceeds_bond",
            replay_commands=[devnet_command],
        ),
        _family(
            "fee_split_exceeds_fee_paid",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="reward_budget_overdraft",
            manifest_obligations=["budget_conservation", "economic_margin", "schema_total"],
            devnet_disaster_state="fee_split_exceeds_fee_paid",
            replay_commands=[devnet_command],
        ),
        _family(
            "critical_action_without_consumer_profile",
            source="docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
            status="bounded_devnet_closed",
            manifest_axis="raw_report_consumed_by_critical_action",
            manifest_obligations=["critical_action_bound", "evidence_floor_o3", "receipt_dag_closed", "schema_total"],
            devnet_disaster_state="critical_action_without_consumer_profile",
            replay_commands=[devnet_command],
        ),
        _family(
            "source_cartel",
            source="tools/zeno_oracle_disaster_class_corpus.py",
            status="public_corpus_closed",
            manifest_axis="source_cartel_collapses_quorum",
            manifest_obligations=["evidence_floor_o3", "receipt_dag_closed", "reporter_independence", "schema_total", "source_diversity"],
            corpus_class_id="source_cartel",
            replay_commands=[corpus_command],
        ),
        _family(
            "dispute_griefing",
            source="tools/zeno_oracle_disaster_class_corpus.py",
            status="public_corpus_closed",
            manifest_axis="open_dispute_feeds_critical_read",
            manifest_obligations=["critical_action_bound", "dispute_clear", "receipt_dag_closed", "schema_total"],
            corpus_class_id="dispute_griefing",
            replay_commands=[corpus_command],
        ),
        _family(
            "registry_drift",
            source="tools/zeno_oracle_disaster_class_corpus.py",
            status="public_corpus_closed",
            manifest_axis="registry_root_drift",
            manifest_obligations=["query_semantics", "receipt_dag_closed", "registry_root_binding", "schema_total"],
            corpus_class_id="registry_drift",
            replay_commands=[corpus_command],
        ),
        _family(
            "verifier_spoofing",
            source="tools/zeno_oracle_disaster_class_corpus.py",
            status="public_corpus_closed",
            manifest_axis="verifier_spoofed_o4_upgrade",
            manifest_obligations=["evidence_floor_o3", "proof_verifier_bound", "registry_root_binding", "schema_total"],
            corpus_class_id="verifier_spoofing",
            replay_commands=[corpus_command],
        ),
        _family(
            "o5_independence_spoofing",
            source="tools/zeno_oracle_disaster_class_corpus.py",
            status="public_corpus_closed",
            manifest_axis="o5_upgrade_without_independent_evidence",
            manifest_obligations=["evidence_floor_o3", "proof_independence", "proof_verifier_bound", "registry_root_binding", "schema_total"],
            corpus_class_id="o5_independence_spoofing",
            replay_commands=[corpus_command],
        ),
        _family(
            "proof_timeout_treated_as_success",
            source="tools/zeno_oracle_disaster_class_corpus.py",
            status="public_corpus_closed",
            manifest_axis="proof_timeout_treated_as_success",
            manifest_obligations=["proof_verifier_bound", "resource_budget", "schema_total"],
            corpus_class_id="proof_timeout_treated_as_success",
            replay_commands=[corpus_command],
        ),
        _family(
            "terminal_replay_integrity",
            source="tools/zeno_oracle_disaster_class_corpus.py",
            status="public_corpus_closed",
            manifest_axis="duplicate_receipt_id_shadowing",
            manifest_obligations=["dependency_order", "duplicate_reject", "receipt_dag_closed", "schema_total"],
            corpus_class_id="terminal_replay_integrity",
            replay_commands=[corpus_command],
        ),
        _family(
            "cross_module_split_brain",
            source="tools/zeno_oracle_disaster_class_corpus.py",
            status="public_corpus_closed",
            manifest_axis="cross_module_split_brain_divergence",
            manifest_obligations=["cross_module_sync", "economic_margin", "runtime_state_binding", "schema_total", "time_freshness"],
            corpus_class_id="cross_module_split_brain",
            replay_commands=[corpus_command],
        ),
        _family(
            "oracle_settlement_without_usable_snapshot",
            source="production-frontier-seed",
            status="production_blocked",
            manifest_axis="stale_read_used_for_critical_action",
            manifest_obligations=["critical_action_bound", "receipt_dag_closed", "schema_total", "time_freshness"],
            replay_commands=["python3 tools/check_zeno_oracle_critical_action_map.py", perps_snapshot_command],
            blockers=["perps_snapshot_gate_is_bounded_replay_not_general_theorem", "production_runtime_policy_not_live"],
        ),
        _family(
            "cross_domain_finality_reorg_feeds_oracle_read",
            source="production-frontier-seed",
            status="production_blocked",
            manifest_axis="cross_domain_finality_reorg_feeds_oracle_read",
            manifest_obligations=["cross_domain_finality", "dependency_order", "receipt_dag_closed", "schema_total"],
            replay_commands=[finality_command],
            blockers=[
                "cross_domain_finality_gate_is_local_receipt_replay_not_live",
                "no_live_finality_adapter_receipts",
            ],
        ),
        _family(
            "live_escrow_shortfall_blocks_reporter_payout",
            source="production-frontier-seed",
            status="production_blocked",
            manifest_axis="reward_budget_overdraft",
            manifest_obligations=["budget_conservation", "economic_margin", "schema_total"],
            replay_commands=[policy_command],
            blockers=["escrow_funding_receipt_not_verified_onchain", "live_token_settlement_not_replayed"],
        ),
        _family(
            "onchain_governance_timelock_bypass",
            source="production-frontier-seed",
            status="production_blocked",
            manifest_axis="governance_policy_downgrade",
            manifest_obligations=["evidence_floor_o3", "query_semantics", "registry_root_binding", "schema_total"],
            replay_commands=["python3 tools/check_zeno_oracle_production_network_config.py --format text"],
            blockers=[
                "feed_governance_execution_gate_is_local_receipt_replay_not_live",
                "onchain_feed_governance_not_live",
                "governance_execution_receipts_not_verified_onchain",
            ],
        ),
        _family(
            "public_reporter_cartel_after_soak_window",
            source="production-frontier-seed",
            status="research_backlog",
            manifest_axis="source_cartel_collapses_quorum",
            manifest_obligations=["evidence_floor_o3", "reporter_independence", "schema_total", "source_diversity"],
            replay_commands=[reporter_soak_command],
            blockers=[
                "reporter_soak_gate_is_local_observation_replay_not_public_soak",
                "public_soak_not_completed",
                "reporter_honesty_and_operator_independence_not_proven",
            ],
        ),
    ]
    frontier: dict[str, Any] = {
        "schema": FRONTIER_SCHEMA,
        "families": families,
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }
    frontier["frontier_id"] = frontier_content_hash(frontier)
    return frontier


def _closed_devnet_states(harness_receipt: Mapping[str, Any]) -> set[str]:
    cases = harness_receipt.get("cases")
    if not isinstance(cases, list):
        return set()
    return {str(case.get("disaster_state")) for case in cases if isinstance(case, Mapping) and case.get("ok") is True}


def _closed_corpus_classes(corpus_receipt: Mapping[str, Any]) -> set[str]:
    cases = corpus_receipt.get("cases")
    if not isinstance(cases, list):
        return set()
    return {str(case.get("class_id")) for case in cases if isinstance(case, Mapping) and case.get("ok") is True}


def _manifest_axes(manifest: Mapping[str, Any]) -> dict[str, set[str]]:
    axes: dict[str, set[str]] = {}
    raw_axes = manifest.get("axes")
    if not isinstance(raw_axes, list):
        return axes
    for raw_axis in raw_axes:
        if not isinstance(raw_axis, Mapping):
            continue
        name = raw_axis.get("name")
        obligations = raw_axis.get("obligations")
        if isinstance(name, str) and isinstance(obligations, list):
            axes[name] = {item for item in obligations if isinstance(item, str)}
    return axes


def check_frontier(
    frontier: Mapping[str, Any],
    *,
    manifest: Mapping[str, Any],
    corpus_receipt: Mapping[str, Any],
    harness_receipt: Mapping[str, Any],
) -> dict[str, Any]:
    errors: list[str] = []
    _unknown_fields(frontier, allowed=FRONTIER_KEYS, label="frontier", errors=errors)
    if frontier.get("schema") != FRONTIER_SCHEMA:
        errors.append("frontier_schema_mismatch")
    expected_frontier_id = frontier_content_hash(frontier)
    if frontier.get("frontier_id") != expected_frontier_id:
        errors.append("frontier_id_mismatch")

    manifest_report = evaluate_manifest(manifest)
    axes = _manifest_axes(manifest)
    known_obligations = {obligation for obligations in axes.values() for obligation in obligations}
    closed_devnet = _closed_devnet_states(harness_receipt)
    closed_corpus = _closed_corpus_classes(corpus_receipt)

    not_claimed = frontier.get("not_claimed")
    if not isinstance(not_claimed, list):
        errors.append("not_claimed_must_be_list")
    else:
        values = {str(item) for item in not_claimed if isinstance(item, str)}
        errors.extend(f"missing_not_claim:{item}" for item in sorted(REQUIRED_NOT_CLAIMS - values))

    raw_families = frontier.get("families")
    if not isinstance(raw_families, list):
        errors.append("families_must_be_list")
        raw_families = []

    seen: set[str] = set()
    family_results: list[dict[str, Any]] = []
    closure_blockers: list[dict[str, Any]] = []
    new_obligation_families: list[dict[str, Any]] = []
    closed_count = 0
    for index, raw_family in enumerate(raw_families):
        if not isinstance(raw_family, Mapping):
            errors.append(f"family_{index}_must_be_object")
            continue
        _unknown_fields(raw_family, allowed=FAMILY_KEYS, label=f"family_{index}", errors=errors)
        family_id = raw_family.get("family_id")
        if not isinstance(family_id, str) or not family_id:
            errors.append(f"family_{index}_id_invalid")
            family_id = f"<invalid:{index}>"
        elif family_id in seen:
            errors.append(f"duplicate_family_id:{family_id}")
        seen.add(str(family_id))

        status = raw_family.get("status")
        if status not in ALLOWED_STATUS:
            errors.append(f"family_status_invalid:{family_id}")
            status = "invalid"

        manifest_axis = raw_family.get("manifest_axis")
        if not isinstance(manifest_axis, str) or not manifest_axis:
            errors.append(f"manifest_axis_missing:{family_id}")
            axis_obligations: set[str] = set()
        elif manifest_axis not in axes:
            errors.append(f"manifest_axis_unknown:{family_id}:{manifest_axis}")
            axis_obligations = set()
        else:
            axis_obligations = axes[manifest_axis]

        listed_obligations = set(_string_list(raw_family, "manifest_obligations", errors, required=True))
        if axis_obligations and not listed_obligations.issubset(axis_obligations):
            unknown_for_axis = sorted(listed_obligations - axis_obligations)
            if not (status in {"production_blocked", "research_backlog"} and unknown_for_axis):
                errors.append(f"manifest_obligation_not_on_axis:{family_id}:{','.join(unknown_for_axis)}")

        unknown_obligations = sorted(listed_obligations - known_obligations)
        blockers = _string_list(raw_family, "blockers", errors)
        replay_commands = _string_list(raw_family, "replay_commands", errors)
        if unknown_obligations:
            new_obligation_families.append(
                {
                    "family_id": family_id,
                    "missing_obligations": unknown_obligations,
                    "status": status,
                }
            )
            if status not in {"production_blocked", "research_backlog"} or not blockers:
                errors.append(f"new_obligation_without_blocker:{family_id}:{','.join(unknown_obligations)}")

        evidence_ok = False
        if status == "bounded_devnet_closed":
            devnet_state = raw_family.get("devnet_disaster_state")
            if not isinstance(devnet_state, str) or devnet_state not in closed_devnet:
                errors.append(f"missing_devnet_disaster_state:{family_id}:{devnet_state}")
            else:
                evidence_ok = True
        elif status == "public_corpus_closed":
            class_id = raw_family.get("corpus_class_id")
            if not isinstance(class_id, str) or class_id not in closed_corpus:
                errors.append(f"missing_corpus_class:{family_id}:{class_id}")
            else:
                evidence_ok = True
        elif status in {"production_blocked", "research_backlog"}:
            if not blockers:
                errors.append(f"blockers_required:{family_id}")
            closure_blockers.append({"family_id": family_id, "status": status, "blockers": blockers})

        if status in {"bounded_devnet_closed", "public_corpus_closed"}:
            if not replay_commands:
                errors.append(f"replay_commands_required:{family_id}")
            if evidence_ok:
                closed_count += 1

        family_results.append(
            {
                "family_id": family_id,
                "status": status,
                "manifest_axis": manifest_axis,
                "evidence_ok": evidence_ok,
                "unknown_obligations": unknown_obligations,
            }
        )

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "frontier_id": expected_frontier_id,
        "error_count": len(errors),
        "errors": errors,
        "frontier_family_count": len(raw_families),
        "closed_family_count": closed_count,
        "blocked_or_backlog_count": len(closure_blockers),
        "new_obligation_family_count": len(new_obligation_families),
        "manifest_axis_count": manifest_report["axis_count"],
        "manifest_antichain_class_count": manifest_report["antichain_class_count"],
        "closed_devnet_state_count": len(closed_devnet),
        "closed_corpus_class_count": len(closed_corpus),
        "closure_blockers": closure_blockers,
        "new_obligation_families": new_obligation_families,
        "families": family_results,
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }


def _build_live_inputs(manifest_path: Path) -> tuple[Mapping[str, Any], Mapping[str, Any], Mapping[str, Any]]:
    manifest = _load_json(manifest_path)
    with tempfile.TemporaryDirectory(prefix="zeno-oracle-frontier-") as tmp:
        harness_receipt = run_harness(Path(tmp) / "harness")
        corpus_receipt = build_corpus(store_root=Path(tmp) / "corpus")
    return manifest, corpus_receipt, harness_receipt


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontier", type=Path, help="frontier JSON; defaults to built-in sample frontier")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--sample-frontier", action="store_true", help="emit the built-in sample frontier")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--require-closed", action="store_true", help="fail if blocker/backlog frontier families remain")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.sample_frontier:
        print(json.dumps(sample_frontier(), indent=2, sort_keys=True))
        return 0
    frontier = _load_json(args.frontier) if args.frontier else sample_frontier()
    manifest, corpus_receipt, harness_receipt = _build_live_inputs(args.manifest)
    result = check_frontier(
        frontier,
        manifest=manifest,
        corpus_receipt=corpus_receipt,
        harness_receipt=harness_receipt,
    )
    if args.require_closed and result["closure_blockers"]:
        result = dict(result)
        result["ok"] = False
        result["status"] = "rejected"
        result["errors"] = [*result["errors"], "frontier_blockers_present"]
        result["error_count"] = len(result["errors"])
    if args.format == "json":
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"status = {result['status']}")
        print(f"frontier_family_count = {result['frontier_family_count']}")
        print(f"closed_family_count = {result['closed_family_count']}")
        print(f"blocked_or_backlog_count = {result['blocked_or_backlog_count']}")
        print(f"new_obligation_family_count = {result['new_obligation_family_count']}")
        print(f"error_count = {result['error_count']}")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

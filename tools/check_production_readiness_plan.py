#!/usr/bin/env python3
"""Fail-closed structural gate for the production-readiness G0 bundle.

This gate checks source binding, graph closure, coverage arithmetic, and donor
inventory consistency. A pass confirms only that the G0 control artifacts are
internally consistent. It never reports M6, ZRPF, or production readiness.

The frozen requirement, command, and invariant sets are deliberately explicit
here so the checker does not derive its expected oracle from the JSON artifacts
it is checking.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PLAN = REPO_ROOT / "docs/PRODUCTION_READINESS_PLAN.md"
DEFAULT_TASK_GRAPH = REPO_ROOT / "docs/research/PRODUCTION_READINESS_TASK_GRAPH_V1.json"
DEFAULT_COVERAGE = REPO_ROOT / "docs/research/PRODUCTION_READINESS_COVERAGE_LEDGER_V1.json"
DEFAULT_DONORS = REPO_ROOT / "docs/research/PRODUCTION_READINESS_DONOR_INVENTORY_V1.json"
DEFAULT_README = REPO_ROOT / "README.md"

BASE_COMMIT = "b6842cd26aadf32b7ee774f58665570479cacfe6"
BASE_TREE = "d166dc8dff0baa00c7eea9cd04935e468b1fde3d"
REPORT_SCHEMA = "zenodex/production-readiness-plan-check/v1"

EXPECTED_DEPENDENCIES = {
    "G0": [],
    "G1": ["G0"],
    "G2": ["G1"],
    "G3": ["G1"],
    "G4": ["G1"],
    "G5": ["G2", "G3", "G4"],
    "G6": ["G5"],
    "G7": ["G2", "G3"],
    "G8": ["G6", "G7"],
}
EXPECTED_ACTIVATION_DEPENDENCIES: dict[str, list[str]] = {
    task_id: [] for task_id in EXPECTED_DEPENDENCIES
}
EXPECTED_ACTIVATION_DEPENDENCIES["G7"] = ["G6"]

EXPECTED_M6_REQUIREMENTS = {
    "M6-R01": "Canonical fee-occurrence semantics",
    "M6-R02": "Complete SRGD/AGQE adaptive-policy theorem",
    "M6-R03": "Entitlement identity, policy rotation, and migration",
    "M6-R04": "Concrete LineageCube composition theorem",
    "M6-R05": "Authenticated nonce and replay concurrency",
    "M6-R06": "Complete evidence recomputation",
    "M6-R07": "Authorized history, nullifiers, and reopen",
    "M6-R08": "Authenticated proof-context binding",
    "M6-R09": "Atomic publication and crash refinement",
    "M6-R10": "Outbox delivery and acknowledgment semantics",
    "M6-R11": "Migration and authority-switch state machine",
    "M6-R12": "Mounted no-bypass theorem",
    "M6-R13": "ZUSD-P0 whole-system invariant",
}

EXPECTED_COMMANDS = {
    "spot_swap",
    "lp_add",
    "lp_remove",
    "zusd_borrow",
    "zusd_repay",
    "zusd_redeem",
    "zusd_liquidate",
    "stability_pool_deposit",
    "stability_pool_withdraw",
    "zusd_redistribute",
    "perp_open",
    "perp_close",
    "perp_funding",
    "perp_liquidate",
    "oracle_submit",
    "oracle_dispute",
    "protocol_buy_and_burn",
    "zrpf_prover_reward",
    "seller_auction_commit",
    "seller_auction_reveal",
    "seller_auction_settle",
    "seller_auction_cancel",
    "seller_auction_expire",
    "private_swap_commit",
    "private_swap_reveal",
    "private_swap_settle",
    "private_swap_cancel",
    "private_swap_expire",
    "tau_escrow_deposit",
    "tau_withdrawal",
    "tau_withdrawal_ack",
    "fallback_activate",
    "tau_rejoin",
}
EXPECTED_DISABLED_COMMANDS = {
    "zusd_liquidate",
    "zusd_redistribute",
    "perp_funding",
    "perp_liquidate",
    "oracle_submit",
    "oracle_dispute",
    "protocol_buy_and_burn",
    "zrpf_prover_reward",
}
EXPECTED_GLOBAL_INVARIANTS = {
    "nonnegative_bounded_integer_quantities",
    "one_declared_issue_and_burn_authority_per_managed_asset",
    "zusd_issue_and_burn_only_through_collateralized_monetary_kernel",
    "per_asset_balance_custody_reserve_escrow_claim_reconciliation",
    "zusd_debt_supply_protocol_liability_reconciliation",
    "lp_reserve_share_fee_dust_reconciliation",
    "perps_margin_pnl_funding_insurance_reconciliation",
    "oracle_gated_risk_increase",
    "nonce_and_nullifier_uniqueness",
    "complete_terminal_drains",
    "no_unnamed_rounding_remainder",
    "no_external_effect_without_committed_outbox_ancestor",
    "reject_no_commit_preserves_state_and_effects",
}

TASK_GRAPH_KEYS = {
    "schema",
    "version",
    "status",
    "production_promotion",
    "base_commit",
    "base_tree",
    "subject_selection",
    "readiness_predicates",
    "tasks",
    "nonclaims",
}
TASK_KEYS = {
    "id",
    "title",
    "dependencies",
    "activation_dependencies",
    "status",
    "writable_paths",
    "invariant",
    "authority_boundary",
    "failing_evidence",
    "required_commands",
    "artifact_hashes",
    "nonclaims",
    "completion_receipt",
}
COVERAGE_KEYS = {
    "schema",
    "version",
    "status",
    "production_promotion",
    "base_commit",
    "coverage_subject",
    "source_observations",
    "readiness_predicates",
    "promotion_counts",
    "m6_requirements",
    "commands",
    "global_invariant",
    "nonclaims",
}
DONOR_KEYS = {
    "schema",
    "version",
    "status",
    "production_promotion",
    "base_commit",
    "discovery_rule",
    "matched_ref_snapshot_sha256",
    "matched_ref_tips",
    "counts",
    "candidates",
    "nonclaims",
}


@dataclass(frozen=True)
class BundlePaths:
    repo_root: Path
    plan: Path
    task_graph: Path
    coverage: Path
    donors: Path
    readme: Path


def _load_mapping(path: Path, label: str, errors: list[str]) -> Mapping[str, Any] | None:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        errors.append(f"{label}: cannot load JSON: {exc}")
        return None
    if not isinstance(value, Mapping):
        errors.append(f"{label}: root must be an object")
        return None
    return value


def _exact_keys(value: Mapping[str, Any], expected: set[str], label: str, errors: list[str]) -> None:
    actual = set(value)
    if actual != expected:
        errors.append(f"{label}: keys differ: missing={sorted(expected - actual)}, extra={sorted(actual - expected)}")


def _is_sha1(value: object) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{40}", value) is not None


def _is_sha256(value: object) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def _valid_relative_path(value: object) -> bool:
    if not isinstance(value, str) or not value:
        return False
    path = PurePosixPath(value)
    return not path.is_absolute() and ".." not in path.parts


def _check_git_binding(repo_root: Path, errors: list[str]) -> None:
    commands = [
        (["cat-file", "-e", f"{BASE_COMMIT}^{{commit}}"], None),
        (["merge-base", "--is-ancestor", BASE_COMMIT, "HEAD"], None),
        (["show", "-s", "--format=%T", BASE_COMMIT], BASE_TREE),
    ]
    for arguments, expected_stdout in commands:
        result = subprocess.run(
            ["git", *arguments],
            cwd=repo_root,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        if result.returncode != 0:
            errors.append(f"git binding failed: git {' '.join(arguments)}")
        elif expected_stdout is not None and result.stdout.strip() != expected_stdout:
            errors.append(f"git binding failed: base tree is {result.stdout.strip()!r}")


def _check_plan(plan_path: Path, readme_path: Path, errors: list[str]) -> None:
    try:
        plan = plan_path.read_text(encoding="utf-8")
        readme = readme_path.read_text(encoding="utf-8")
    except OSError as exc:
        errors.append(f"plan/readme: cannot read: {exc}")
        return
    required_fragments = {
        "# ZenoDEX Production Completion Plan V1",
        "Promotion posture: closed.",
        BASE_COMMIT,
        "M6DirectReady(P)",
        "ZRPFReady(P)",
        "ProductionReady(P)",
        "python3 tools/check_production_readiness_plan.py --json",
    }
    for task_id in EXPECTED_DEPENDENCIES:
        required_fragments.add(f"### {task_id}:")
    for fragment in sorted(required_fragments):
        if fragment not in plan:
            errors.append(f"plan: missing required fragment {fragment!r}")
    if "docs/PRODUCTION_READINESS_PLAN.md" not in readme:
        errors.append("README: production-readiness plan link is missing")


def _has_cycle(edges: Mapping[str, list[str]]) -> bool:
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node: str) -> bool:
        if node in visiting:
            return True
        if node in visited:
            return False
        visiting.add(node)
        for dependency in edges.get(node, []):
            if visit(dependency):
                return True
        visiting.remove(node)
        visited.add(node)
        return False

    return any(visit(node) for node in edges)


def _check_task_row(
    task_id: str,
    task: Mapping[str, Any],
    errors: list[str],
) -> list[str]:
    dependencies = task.get("dependencies")
    activation = task.get("activation_dependencies")
    if dependencies != EXPECTED_DEPENDENCIES.get(task_id):
        errors.append(f"task graph: {task_id} dependencies differ")
    if activation != EXPECTED_ACTIVATION_DEPENDENCIES.get(task_id):
        errors.append(f"task graph: {task_id} activation dependencies differ")
    for key in ("title", "invariant", "authority_boundary"):
        if not isinstance(task.get(key), str) or not task[key].strip():
            errors.append(f"task graph: {task_id}.{key} must be nonempty")
    for key in ("writable_paths", "failing_evidence", "required_commands", "nonclaims"):
        values = task.get(key)
        if not isinstance(values, list) or not values or not all(isinstance(item, str) and item for item in values):
            errors.append(f"task graph: {task_id}.{key} must be a nonempty string list")
    paths = task.get("writable_paths")
    if isinstance(paths, list) and not all(_valid_relative_path(path) for path in paths):
        errors.append(f"task graph: {task_id}.writable_paths contains an unsafe path")
    if task_id == "G0":
        if task.get("status") != "COMPLETE" or not isinstance(task.get("completion_receipt"), Mapping):
            errors.append("task graph: G0 must have a completion receipt")
    elif task.get("status") != "PENDING" or task.get("completion_receipt") is not None:
        errors.append(f"task graph: {task_id} must remain PENDING without a receipt")
    return [
        *(dependencies if isinstance(dependencies, list) else []),
        *(activation if isinstance(activation, list) else []),
    ]


def _check_task_graph(graph: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    _exact_keys(graph, TASK_GRAPH_KEYS, "task graph", errors)
    if graph.get("schema") != "zenodex/production-readiness-task-graph/v1":
        errors.append("task graph: wrong schema")
    if graph.get("base_commit") != BASE_COMMIT or graph.get("base_tree") != BASE_TREE:
        errors.append("task graph: base binding mismatch")
    if graph.get("production_promotion") is not False:
        errors.append("task graph: production_promotion must remain false in G0")
    predicates = graph.get("readiness_predicates")
    if not isinstance(predicates, Mapping) or set(predicates.values()) != {"OPEN"}:
        errors.append("task graph: every readiness predicate must remain OPEN")

    raw_tasks = graph.get("tasks")
    if not isinstance(raw_tasks, list):
        errors.append("task graph: tasks must be a list")
        return {"task_count": 0, "complete_task_count": 0}
    tasks: dict[str, Mapping[str, Any]] = {}
    for index, raw_task in enumerate(raw_tasks):
        if not isinstance(raw_task, Mapping):
            errors.append(f"task graph: tasks[{index}] must be an object")
            continue
        _exact_keys(raw_task, TASK_KEYS, f"task graph: tasks[{index}]", errors)
        task_id = raw_task.get("id")
        if not isinstance(task_id, str) or task_id in tasks:
            errors.append(f"task graph: invalid or duplicate task id {task_id!r}")
            continue
        tasks[task_id] = raw_task
    if set(tasks) != set(EXPECTED_DEPENDENCIES):
        errors.append("task graph: task ids must be exactly G0 through G8")

    combined_edges: dict[str, list[str]] = {}
    for task_id, task in tasks.items():
        combined_edges[task_id] = _check_task_row(task_id, task, errors)

    if _has_cycle(combined_edges):
        errors.append("task graph: dependency graph is cyclic")
    g0 = tasks.get("G0", {})
    artifacts = g0.get("artifact_hashes") if isinstance(g0, Mapping) else None
    if not isinstance(artifacts, list) or len(artifacts) != 2:
        errors.append("task graph: G0 must bind the private payload and manifest hashes")
    else:
        for artifact in artifacts:
            if not isinstance(artifact, Mapping) or artifact.get("algorithm") != "sha256" or not _is_sha256(artifact.get("digest")):
                errors.append("task graph: malformed G0 artifact hash")
    receipt = g0.get("completion_receipt") if isinstance(g0, Mapping) else None
    if isinstance(receipt, Mapping):
        if receipt.get("donor_imports") != [] or receipt.get("status") != "VERIFIED":
            errors.append("task graph: G0 receipt must be verified with zero donor imports")
    return {
        "task_count": len(tasks),
        "complete_task_count": sum(task.get("status") == "COMPLETE" for task in tasks.values()),
    }


def _m6_row_complete(row: Mapping[str, Any]) -> bool:
    return (
        row.get("formal_status") == "PROVED"
        and row.get("implementation_status") == "IMPLEMENTED"
        and row.get("mount_status") == "MOUNTED"
        and row.get("test_status") == "TESTED"
    )


def _command_row_complete(row: Mapping[str, Any]) -> bool:
    return (
        row.get("v2_specification") == "SPECIFIED"
        and row.get("v2_implementation") == "IMPLEMENTED"
        and row.get("v2_formal") == "PROVED"
        and row.get("v2_mounted") == "MOUNTED"
        and row.get("v2_tested") == "TESTED"
        and row.get("terminal_complete") == "TERMINAL_COMPLETE"
    )


def _check_m6_requirement_rows(ledger: Mapping[str, Any], errors: list[str]) -> int:
    raw_requirements = ledger.get("m6_requirements")
    requirement_rows = {
        row.get("id"): row
        for row in raw_requirements
        if isinstance(row, Mapping) and isinstance(row.get("id"), str)
    } if isinstance(raw_requirements, list) else {}
    if set(requirement_rows) != set(EXPECTED_M6_REQUIREMENTS) or len(requirement_rows) != 13:
        errors.append("coverage ledger: M6 requirements must be exactly M6-R01 through M6-R13")
    complete_count = 0
    for requirement_id, expected_title in EXPECTED_M6_REQUIREMENTS.items():
        row = requirement_rows.get(requirement_id)
        if row is None:
            continue
        if row.get("title") != expected_title:
            errors.append(f"coverage ledger: {requirement_id} title differs")
        calculated = _m6_row_complete(row)
        if row.get("promotion_complete") is not calculated:
            errors.append(f"coverage ledger: {requirement_id} promotion_complete is inconsistent")
        complete_count += int(calculated)
    return complete_count


def _check_command_rows(ledger: Mapping[str, Any], errors: list[str]) -> int:
    raw_commands = ledger.get("commands")
    command_rows: dict[str, Mapping[str, Any]] = {}
    if isinstance(raw_commands, list):
        for row in raw_commands:
            if isinstance(row, Mapping) and isinstance(row.get("id"), str):
                command_rows[row["id"]] = row
    if set(command_rows) != EXPECTED_COMMANDS or len(command_rows) != 33:
        errors.append("coverage ledger: command ids differ from the frozen 33-command registry")
    complete_count = 0
    observed_disabled = set()
    for command_id, row in command_rows.items():
        if "shutdown" in command_id:
            errors.append("coverage ledger: emergency shutdown must be absent from the launch registry")
        expected_profile = "RESEARCH_DISABLED" if command_id in EXPECTED_DISABLED_COMMANDS else "RESEARCH_ENABLED"
        if row.get("v1_profile") != expected_profile:
            errors.append(f"coverage ledger: {command_id} V1 profile differs")
        if row.get("v1_profile") == "RESEARCH_DISABLED":
            observed_disabled.add(command_id)
        calculated = _command_row_complete(row)
        if row.get("production_complete") is not calculated:
            errors.append(f"coverage ledger: {command_id} production_complete is inconsistent")
        complete_count += int(calculated)
    if observed_disabled != EXPECTED_DISABLED_COMMANDS:
        errors.append("coverage ledger: exact-base disabled partition differs")
    return complete_count


def _check_coverage(ledger: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    _exact_keys(ledger, COVERAGE_KEYS, "coverage ledger", errors)
    if ledger.get("schema") != "zenodex/production-readiness-coverage-ledger/v1":
        errors.append("coverage ledger: wrong schema")
    if ledger.get("base_commit") != BASE_COMMIT or ledger.get("production_promotion") is not False:
        errors.append("coverage ledger: G0 base/promotion binding mismatch")

    m6_complete = _check_m6_requirement_rows(ledger, errors)
    command_complete = _check_command_rows(ledger, errors)

    counts = ledger.get("promotion_counts")
    expected_counts = {
        "m6_requirements_complete": m6_complete,
        "m6_requirements_total": 13,
        "commands_v2_complete": command_complete,
        "commands_total": 33,
    }
    if counts != expected_counts:
        errors.append("coverage ledger: promotion counts are inconsistent")
    if m6_complete != 0 or command_complete != 0:
        errors.append("coverage ledger: G0 must remain 0/13 and 0/33")
    if ledger.get("readiness_predicates") != {
        "M6DirectReady": False,
        "ZRPFReady": False,
        "OperationalReady": False,
        "ProductionReady": False,
    }:
        errors.append("coverage ledger: every G0 readiness predicate must be false")
    observations = ledger.get("source_observations")
    if not isinstance(observations, Mapping) or observations.get("v1_command_count") != 33 or observations.get("v1_disabled_command_count") != 8 or observations.get("received_plan_disabled_command_count") != 10 or observations.get("disabled_count_reconciliation") != "GAP":
        errors.append("coverage ledger: source-observed disable-count conflict is missing")
    if set(ledger.get("global_invariant", [])) != EXPECTED_GLOBAL_INVARIANTS:
        errors.append("coverage ledger: global invariant set differs")
    return {
        "m6_requirements_complete": m6_complete,
        "m6_requirements_total": 13,
        "commands_complete": command_complete,
        "commands_total": 33,
    }


def _check_donor_refs(inventory: Mapping[str, Any], errors: list[str]) -> int:
    raw_refs = inventory.get("matched_ref_tips")
    refs = raw_refs if isinstance(raw_refs, list) else []
    canonical_lines: list[str] = []
    previous_ref = ""
    for index, row in enumerate(refs):
        if not isinstance(row, Mapping) or not isinstance(row.get("ref"), str) or not _is_sha1(row.get("tip")):
            errors.append(f"donor inventory: matched_ref_tips[{index}] is malformed")
            continue
        if row["ref"] <= previous_ref or re.search(r"(?:m6|zrpf)", row["ref"], re.IGNORECASE) is None:
            errors.append("donor inventory: matching refs must be sorted and match M6/ZRPF")
        previous_ref = row["ref"]
        canonical_lines.append(f"{row['tip']}\t{row['ref']}\n")
    ref_digest = hashlib.sha256("".join(canonical_lines).encode("utf-8")).hexdigest()
    if inventory.get("matched_ref_snapshot_sha256") != ref_digest:
        errors.append("donor inventory: matched ref snapshot hash differs")
    return len(refs)


def _check_donor_candidates(
    inventory: Mapping[str, Any],
    errors: list[str],
) -> tuple[int, int, dict[str, int]]:
    raw_candidates = inventory.get("candidates")
    candidates = raw_candidates if isinstance(raw_candidates, list) else []
    candidate_ids: list[str] = []
    imports = 0
    relation_counts = {
        "BASELINE": 0,
        "ANCESTOR_INCLUDED": 0,
        "DESCENDANT_UNVERIFIED": 0,
        "DIVERGED_UNREVIEWED": 0,
    }
    for index, row in enumerate(candidates):
        if not isinstance(row, Mapping) or not _is_sha1(row.get("commit")) or not _is_sha1(row.get("tree")):
            errors.append(f"donor inventory: candidates[{index}] has malformed object ids")
            continue
        candidate_ids.append(row["commit"])
        relation = row.get("relation_to_base")
        if relation not in relation_counts:
            errors.append(f"donor inventory: candidates[{index}] has invalid relation")
        else:
            relation_counts[relation] += 1
        imported = row.get("imported_into_g0")
        if imported is True:
            imports += 1
            if row.get("review_status") != "REVIEWED_OBLIGATION_SIZED" or not row.get("obligation_ids"):
                errors.append(f"donor inventory: imported candidate {row['commit']} lacks obligation-sized review")
        elif imported is not False:
            errors.append(f"donor inventory: candidates[{index}].imported_into_g0 must be boolean")
    if candidate_ids != sorted(set(candidate_ids)):
        errors.append("donor inventory: candidates must be unique and commit-sorted")
    return len(candidates), imports, relation_counts


def _check_donors(inventory: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    _exact_keys(inventory, DONOR_KEYS, "donor inventory", errors)
    if inventory.get("schema") != "zenodex/production-readiness-donor-inventory/v1":
        errors.append("donor inventory: wrong schema")
    if inventory.get("base_commit") != BASE_COMMIT or inventory.get("production_promotion") is not False:
        errors.append("donor inventory: G0 base/promotion binding mismatch")
    ref_count = _check_donor_refs(inventory, errors)
    candidate_count, imports, relation_counts = _check_donor_candidates(inventory, errors)
    expected_counts = {
        "matched_refs": ref_count,
        "unique_candidates": candidate_count,
        **relation_counts,
        "imports": imports,
    }
    if inventory.get("counts") != expected_counts:
        errors.append("donor inventory: counts are inconsistent")
    if relation_counts["DESCENDANT_UNVERIFIED"] != 0 or imports != 0:
        errors.append("donor inventory: G0 permits no unreviewed descendant selection or donor import")
    return {"donor_candidate_count": candidate_count, "donor_import_count": imports}


def check_bundle(paths: BundlePaths) -> dict[str, Any]:
    errors: list[str] = []
    _check_git_binding(paths.repo_root, errors)
    _check_plan(paths.plan, paths.readme, errors)
    graph = _load_mapping(paths.task_graph, "task graph", errors)
    coverage = _load_mapping(paths.coverage, "coverage ledger", errors)
    donors = _load_mapping(paths.donors, "donor inventory", errors)
    counts: dict[str, Any] = {}
    if graph is not None:
        counts.update(_check_task_graph(graph, errors))
    if coverage is not None:
        counts.update(_check_coverage(coverage, errors))
    if donors is not None:
        counts.update(_check_donors(donors, errors))
    return {
        "schema": REPORT_SCHEMA,
        "status": "PASS" if not errors else "FAIL",
        "base_commit": BASE_COMMIT,
        "production_ready": False,
        "counts": counts,
        "errors": errors,
        "nonclaims": [
            "PASS means only that the G0 planning bundle is structurally consistent.",
            "This checker does not prove, implement, mount, test, deploy, or promote M6 or ZRPF.",
        ],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--plan", type=Path, default=DEFAULT_PLAN)
    parser.add_argument("--task-graph", type=Path, default=DEFAULT_TASK_GRAPH)
    parser.add_argument("--coverage-ledger", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument("--donor-inventory", type=Path, default=DEFAULT_DONORS)
    parser.add_argument("--readme", type=Path, default=DEFAULT_README)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    report = check_bundle(
        BundlePaths(
            repo_root=args.repo_root.resolve(),
            plan=args.plan.resolve(),
            task_graph=args.task_graph.resolve(),
            coverage=args.coverage_ledger.resolve(),
            donors=args.donor_inventory.resolve(),
            readme=args.readme.resolve(),
        )
    )
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif report["status"] == "PASS":
        print("PASS: G0 production-readiness planning bundle is structurally consistent")
        print("NONCLAIM: production_ready=false")
    else:
        for error in report["errors"]:
            print(f"FAIL: {error}", file=sys.stderr)
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())

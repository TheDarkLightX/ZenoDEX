#!/usr/bin/env python3
"""Fail-closed checker: every live disaster axis has exactly one certified-status row.

Rejects when: any live axis lacks a manifest row or any row names a dead axis;
an axis definition drifted from its pinned sha; a status is outside the closed
vocabulary; an ``inductive_esso`` row's model or receipt is missing, drifted, or
its receipt does not record a two-solver VERIFIED agreement. Research-only.

``check_manifest_total`` is the entry point: it turns any unexpected shape or
internal error into a fail-closed verdict instead of a traceback.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

import yaml  # type: ignore[import-untyped]

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.build_disaster_axis_status_manifest import (  # noqa: E402
    INDUCTIVE_MODEL_BY_AXIS,
    MANIFEST_SCHEMA_V1,
    _axis_definition_sha,
)
from tools.stateful_scenario_bridge import DISASTER_SEARCH_EXPANSION_AXES  # noqa: E402

CLOSED_STATUSES = ("inductive_esso", "lean", "tau", "bounded_replay", "open", "out_of_scope")
PROOF_STATUSES = ("inductive_esso", "lean", "tau")


def expected_queries_for_model(model_path: Path) -> set[str]:
    """Derive the verify-multi query set the model itself demands.

    Declared ``checks`` win; otherwise the inductive family is
    ``init_implies_inv`` plus ``inductive_<action>`` per action (Opus review
    R1-R4: binding the receipt's query set to the model CONTENT, not its name).
    """

    document = yaml.safe_load(model_path.read_text(encoding="utf-8"))
    if not isinstance(document, dict):
        raise ValueError("model is not a mapping")
    declared = document.get("checks")
    if isinstance(declared, list) and declared:
        names = {str(item.get("id") if isinstance(item, dict) else item) for item in declared}
    else:
        actions = document.get("actions")
        if not isinstance(actions, list) or not actions:
            raise ValueError("model declares no actions")
        names = {"init_implies_inv"}
        for action in actions:
            if not isinstance(action, dict) or not isinstance(action.get("id"), str):
                raise ValueError("model action is not a mapping with an id")
            names.add(f"inductive_{action['id']}")
    return names


def check_manifest(root: Path, manifest_path: Path) -> dict:
    errors: list[str] = []
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        return {"ok": False, "errors": [f"manifest unreadable: {error}"]}
    if not isinstance(manifest, dict):
        return {"ok": False, "errors": ["manifest is not an object"]}
    if manifest.get("schema") != MANIFEST_SCHEMA_V1:
        errors.append("manifest schema drift")
    if list(manifest.get("status_vocabulary", [])) != list(CLOSED_STATUSES):
        errors.append("status vocabulary drift")
    live = {axis["axis_id"]: axis for axis in DISASTER_SEARCH_EXPANSION_AXES}
    rows = manifest.get("rows", [])
    if not isinstance(rows, list) or not all(isinstance(row, dict) for row in rows):
        return {"ok": False, "errors": ["manifest rows are not a list of objects"]}
    seen: set[str] = set()
    status_counts: dict[str, int] = {}
    for row in rows:
        axis_id = str(row.get("axis_id", ""))
        if axis_id in seen:
            errors.append(f"duplicate row: {axis_id}")
            continue
        seen.add(axis_id)
        if axis_id not in live:
            errors.append(f"row names a dead axis: {axis_id}")
            continue
        if _axis_definition_sha(live[axis_id]) != row.get("axis_definition_sha256"):
            errors.append(f"axis definition drift: {axis_id}")
        status = row.get("status")
        if status not in CLOSED_STATUSES:
            errors.append(f"unknown status for {axis_id}: {status!r}")
            continue
        status_counts[status] = status_counts.get(status, 0) + 1
        if status in PROOF_STATUSES:
            expected_model = INDUCTIVE_MODEL_BY_AXIS.get(axis_id)
            if expected_model is None:
                errors.append(f"{axis_id}: no inductive model is registered for this axis")
            elif not str(row.get("model_path", "")).endswith(f"/{expected_model}.yaml"):
                errors.append(f"{axis_id}: model_path does not name the registered model {expected_model}")
            for kind in ("model", "receipt"):
                rel = row.get(f"{kind}_path")
                pinned = row.get(f"{kind}_sha256")
                if not isinstance(rel, str) or not isinstance(pinned, str):
                    errors.append(f"{axis_id}: {kind} pin missing")
                    continue
                target = root / rel
                if not target.is_file():
                    errors.append(f"{axis_id}: {kind} artifact missing: {rel}")
                    continue
                if hashlib.sha256(target.read_bytes()).hexdigest() != pinned:
                    errors.append(f"{axis_id}: {kind} sha256 drift: {rel}")
            receipt_rel = row.get("receipt_path")
            if isinstance(receipt_rel, str) and (root / receipt_rel).is_file():
                try:
                    receipt = json.loads((root / receipt_rel).read_text(encoding="utf-8"))
                except (OSError, json.JSONDecodeError):
                    errors.append(f"{axis_id}: receipt not JSON")
                else:
                    report = receipt.get("report", {})
                    if receipt.get("ok") is not True:
                        errors.append(f"{axis_id}: receipt ok is not true")
                    if report.get("verdict") != "VERIFIED":
                        errors.append(f"{axis_id}: receipt verdict is not VERIFIED")
                    if report.get("solvers_agreed") is not True:
                        errors.append(f"{axis_id}: receipt solvers did not agree")
                    if report.get("failed_queries") != 0 or report.get("inconclusive_queries") != 0:
                        errors.append(f"{axis_id}: receipt has failed or inconclusive queries")
                    # Opus review P1-1: the receipt must certify THIS row's model.
                    receipt_model = receipt.get("model")
                    if not isinstance(receipt_model, dict) or receipt_model.get("path") != row.get("model_path"):
                        errors.append(f"{axis_id}: receipt certifies a different model path")
                    model_name = str(row.get("model_path", "")).rsplit("/", 1)[-1].removesuffix(".yaml")
                    if report.get("model_id") != model_name:
                        errors.append(f"{axis_id}: receipt model_id does not match the model")
                    # Opus round 3 T3: the receipt's two ir_hash fields must agree.
                    full_hash = str(receipt_model.get("ir_hash", "")) if isinstance(receipt_model, dict) else ""
                    if not full_hash.startswith("sha256:") or report.get("ir_hash") != full_hash[7:23]:
                        errors.append(f"{axis_id}: receipt ir_hash fields are absent or inconsistent")
                    # Opus review P1-2: a VERIFIED verdict alone is forgeable; require the
                    # two-solver query evidence itself.
                    if list(receipt.get("solvers", [])) != ["z3", "cvc5"]:
                        errors.append(f"{axis_id}: receipt solvers are not exactly z3+cvc5")
                    queries = receipt.get("queries", {})
                    if not isinstance(queries, dict) or not queries:
                        errors.append(f"{axis_id}: receipt carries no queries")
                    else:
                        for query_name, query in queries.items():
                            if not isinstance(query, dict) or query.get("agreed") is not True:
                                errors.append(f"{axis_id}: query {query_name} lacks solver agreement")
                                continue
                            for solver in ("z3", "cvc5"):
                                result = query.get(solver, {})
                                if not isinstance(result, dict) or result.get("result") != "unsat":
                                    errors.append(f"{axis_id}: query {query_name} lacks an unsat {solver} result")
                        if report.get("passed_queries") != len(queries) or report.get("total_queries") != len(queries):
                            errors.append(f"{axis_id}: receipt query counts disagree with its query set")
                        # Opus review R1-R4: the query set must be the one the model
                        # CONTENT demands, so a swapped or gutted model (or a stripped
                        # or invented query list) fails even with shas resynced.
                        model_rel = row.get("model_path")
                        if isinstance(model_rel, str) and (root / model_rel).is_file():
                            try:
                                expected_queries = expected_queries_for_model(root / model_rel)
                            except (ValueError, yaml.YAMLError) as error:
                                errors.append(f"{axis_id}: model does not parse as an ESSO model: {error}")
                            else:
                                if set(queries) != expected_queries:
                                    errors.append(
                                        f"{axis_id}: receipt query set does not match the model's "
                                        f"declared checks"
                                    )
    proof_rows = [row for row in rows if row.get("status") in PROOF_STATUSES]
    for kind in ("model_path", "receipt_path"):
        values = [row.get(kind) for row in proof_rows if row.get(kind)]
        if len(values) != len(set(values)):
            errors.append(f"duplicate {kind} shared across proof rows")
    unmapped = sorted(set(live) - seen)
    for axis_id in unmapped:
        errors.append(f"live axis has no status row: {axis_id}")
    if int(manifest.get("axis_count", -1)) != len(live):
        errors.append("axis_count drift")
    return {
        "ok": not errors,
        "axis_count": len(live),
        "status_counts": dict(sorted(status_counts.items())),
        "errors": errors,
    }


def check_manifest_total(root: Path, manifest_path: Path) -> dict:
    """Totalised wrapper: any unexpected shape rejects instead of raising."""

    try:
        return check_manifest(root, manifest_path)
    except Exception as error:  # noqa: BLE001 - fail-closed totality boundary
        return {"ok": False, "errors": [f"checker error: {type(error).__name__}: {error}"]}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default=str(REPO_ROOT))
    parser.add_argument("--manifest", default="tools/disaster_axis_status_manifest.json")
    args = parser.parse_args()
    root = Path(args.root).resolve()
    report = check_manifest_total(root, root / args.manifest)
    print(json.dumps(report, indent=2, sort_keys=False))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

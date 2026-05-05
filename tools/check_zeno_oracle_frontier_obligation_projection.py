#!/usr/bin/env python3
"""Project the live ZenoOracle disaster frontier onto the obligation antichain."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
TOOLS = ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(1, str(TOOLS))

from check_disaster_obligation_certificate import (  # noqa: E402
    CertificateError,
    check_result_against_manifest,
    evaluate_manifest,
)
from check_zeno_oracle_disaster_frontier import (  # noqa: E402
    DEFAULT_MANIFEST,
    _build_live_inputs,
    check_frontier,
    sample_frontier,
)


SCHEMA = "zenodex.oracle.frontier_obligation_projection.v1"
NOT_CLAIMED = [
    "does_not_claim_exhaustive_production_disaster_search",
    "does_not_claim_general_obligation_theorem",
    "does_not_claim_live_oracle_network_safety",
]


def _axis_to_class(report: Mapping[str, Any]) -> dict[str, str]:
    mapping: dict[str, str] = {}
    for qclass in report.get("quotient_classes", []):
        if not isinstance(qclass, Mapping):
            continue
        class_id = qclass.get("class_id")
        if not isinstance(class_id, str):
            continue
        axes = qclass.get("axes")
        if not isinstance(axes, list):
            continue
        for axis in axes:
            if isinstance(axis, str):
                mapping[axis] = class_id
    return mapping


def _dominated_by(report: Mapping[str, Any]) -> dict[str, list[str]]:
    dominated: dict[str, list[str]] = {}
    for row in report.get("dominated_classes", []):
        if not isinstance(row, Mapping):
            continue
        class_id = row.get("class_id")
        dominators = row.get("dominated_by")
        if isinstance(class_id, str) and isinstance(dominators, list):
            dominated[class_id] = sorted(str(item) for item in dominators if isinstance(item, str))
    return dominated


def check_projection(
    frontier: Mapping[str, Any],
    *,
    manifest: Mapping[str, Any],
    corpus_receipt: Mapping[str, Any],
    harness_receipt: Mapping[str, Any],
) -> dict[str, Any]:
    errors: list[str] = []

    manifest_report = evaluate_manifest(manifest)
    try:
        check_result_against_manifest(manifest_report, manifest)
    except CertificateError as exc:
        errors.append(f"manifest_certificate_rejected:{exc}")

    frontier_report = check_frontier(
        frontier,
        manifest=manifest,
        corpus_receipt=corpus_receipt,
        harness_receipt=harness_receipt,
    )
    if frontier_report.get("status") != "accepted":
        errors.append("frontier_rejected")
        errors.extend(f"frontier:{error}" for error in frontier_report.get("errors", []))

    axis_to_class = _axis_to_class(manifest_report)
    dominated_by = _dominated_by(manifest_report)
    antichain_ids = set(str(item) for item in manifest_report.get("antichain_class_ids", []) if isinstance(item, str))
    frontier_evidence = {
        str(row.get("family_id")): row
        for row in frontier_report.get("families", [])
        if isinstance(row, Mapping) and isinstance(row.get("family_id"), str)
    }

    projected: list[dict[str, Any]] = []
    for raw_family in frontier.get("families", []):
        if not isinstance(raw_family, Mapping):
            continue
        family_id = str(raw_family.get("family_id"))
        status = str(raw_family.get("status"))
        manifest_axis = raw_family.get("manifest_axis")
        class_id = axis_to_class.get(str(manifest_axis)) if isinstance(manifest_axis, str) else None
        if class_id is None:
            errors.append(f"family_axis_not_projected:{family_id}:{manifest_axis}")
            relation = "unprojected"
            dominators: list[str] = []
        elif class_id in antichain_ids:
            relation = "antichain_representative"
            dominators = []
        else:
            relation = "dominated_class"
            dominators = dominated_by.get(class_id, [])
            if not dominators:
                errors.append(f"dominated_family_without_dominator:{family_id}:{class_id}")

        evidence = frontier_evidence.get(family_id, {})
        evidence_ok = bool(evidence.get("evidence_ok"))
        blockers = raw_family.get("blockers")
        if status in {"bounded_devnet_closed", "public_corpus_closed"} and not evidence_ok:
            errors.append(f"closed_family_without_frontier_evidence:{family_id}")
        if status in {"production_blocked", "research_backlog"} and not (
            isinstance(blockers, list) and any(isinstance(item, str) and item for item in blockers)
        ):
            errors.append(f"blocked_family_without_blocker:{family_id}")

        projected.append(
            {
                "family_id": family_id,
                "status": status,
                "manifest_axis": manifest_axis,
                "quotient_class_id": class_id,
                "projection_relation": relation,
                "dominated_by": dominators,
                "evidence_ok": evidence_ok,
            }
        )

    relation_counts = {
        "antichain_representative": sum(1 for row in projected if row["projection_relation"] == "antichain_representative"),
        "dominated_class": sum(1 for row in projected if row["projection_relation"] == "dominated_class"),
        "unprojected": sum(1 for row in projected if row["projection_relation"] == "unprojected"),
    }

    status = "accepted" if not errors else "rejected"
    return {
        "schema": SCHEMA,
        "ok": status == "accepted",
        "status": status,
        "error_count": len(errors),
        "errors": errors,
        "frontier_status": frontier_report.get("status"),
        "frontier_family_count": frontier_report.get("frontier_family_count"),
        "closed_family_count": frontier_report.get("closed_family_count"),
        "blocked_or_backlog_count": frontier_report.get("blocked_or_backlog_count"),
        "new_obligation_family_count": frontier_report.get("new_obligation_family_count"),
        "manifest_axis_count": manifest_report.get("axis_count"),
        "quotient_class_count": manifest_report.get("quotient_class_count"),
        "antichain_class_count": manifest_report.get("antichain_class_count"),
        "projected_family_count": len(projected),
        "projection_relation_counts": relation_counts,
        "families": projected,
        "not_claimed": NOT_CLAIMED,
    }


def build_projection(*, manifest_path: Path = DEFAULT_MANIFEST) -> dict[str, Any]:
    manifest, corpus_receipt, harness_receipt = _build_live_inputs(manifest_path)
    return check_projection(
        sample_frontier(),
        manifest=manifest,
        corpus_receipt=corpus_receipt,
        harness_receipt=harness_receipt,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    result = build_projection(manifest_path=args.manifest)
    if args.format == "json":
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"status = {result['status']}")
        print(f"frontier_family_count = {result['frontier_family_count']}")
        print(f"projected_family_count = {result['projected_family_count']}")
        print(f"new_obligation_family_count = {result['new_obligation_family_count']}")
        print(f"error_count = {result['error_count']}")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

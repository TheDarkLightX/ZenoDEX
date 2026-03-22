#!/usr/bin/env python3
"""Evaluate ShapeForge target shapes against the current baseline."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.shapeforge_validate import validate_artifact
from tools.shapeforge_validate import _resolve_linked_path  # type: ignore


STATUS_RANK = {
    "hypothesis": 0,
    "tested_discovery": 1,
    "implemented": 2,
    "contract": 3,
    "proved": 4,
}

BLOCKING_STATUSES = {
    "blocked",
    "falsified",
    "narrowed",
}


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def _resolve(base: Path, raw: str) -> Path:
    resolved = _resolve_linked_path(base, raw)
    if resolved is None:
        raise ValueError(f"could not resolve linked path {raw!r} from {base}")
    return resolved


def _require_valid(path: Path) -> None:
    errors = validate_artifact(path)
    if errors:
        raise ValueError("\n".join(errors))


def _requirement_supported(
    requirement: dict[str, Any],
    *,
    slice_status_by_id: dict[str, str],
    invariant_ids: set[str],
) -> tuple[bool, str]:
    kind = str(requirement["kind"])
    if kind == "slice_status_at_least":
        slice_id = str(requirement["slice_id"])
        min_status = str(requirement["min_status"])
        actual = slice_status_by_id.get(slice_id)
        if actual is None:
            return False, f"missing slice {slice_id}"
        if STATUS_RANK[actual] < STATUS_RANK[min_status]:
            return False, f"slice {slice_id} status {actual} < {min_status}"
        return True, f"slice {slice_id} status {actual} >= {min_status}"
    if kind == "cross_invariant_present":
        invariant_id = str(requirement["invariant_id"])
        if invariant_id not in invariant_ids:
            return False, f"missing invariant {invariant_id}"
        return True, f"invariant {invariant_id} present"
    return False, f"unsupported requirement kind {kind}"


def evaluate_target_shapes(path: Path) -> dict[str, Any]:
    _require_valid(path)
    target_data = _load_json(path)
    world_model_path = _resolve(path, str(target_data["world_model_path"]))
    negative_knowledge_path = _resolve(path, str(target_data["negative_knowledge_path"]))
    _require_valid(world_model_path)
    _require_valid(negative_knowledge_path)

    world_model = _load_json(world_model_path)
    negative_knowledge = _load_json(negative_knowledge_path)

    slice_status_by_id = {
        str(slice_obj["slice_id"]): str(slice_obj["status"])
        for slice_obj in world_model["slices"]
    }
    invariant_ids = {
        str(invariant["id"])
        for invariant in world_model["cross_slice_invariants"]
    }
    negative_records_by_id = {
        str(record["hypothesis_id"]): record
        for record in negative_knowledge["records"]
    }

    results: list[dict[str, Any]] = []
    for target_shape in target_data["target_shapes"]:
        clause_results: list[dict[str, Any]] = []
        support_count = 0
        gap_count = 0
        blocked_count = 0
        for clause in target_shape["clauses"]:
            requirement_results = [
                _requirement_supported(
                    requirement,
                    slice_status_by_id=slice_status_by_id,
                    invariant_ids=invariant_ids,
                )
                for requirement in clause["requirements"]
            ]
            if clause["support_mode"] == "all_of":
                supported = all(ok for ok, _msg in requirement_results)
            else:
                supported = any(ok for ok, _msg in requirement_results)

            blockers: list[dict[str, str]] = []
            for hypothesis_id in clause["blocked_by_hypotheses"]:
                record = negative_records_by_id.get(str(hypothesis_id))
                if record is None:
                    continue
                status = str(record["status"])
                if status in BLOCKING_STATUSES:
                    blockers.append(
                        {
                            "hypothesis_id": str(hypothesis_id),
                            "status": status,
                            "negative_kind": str(record["negative_kind"]),
                            "replacement_claim": str(record.get("replacement_claim") or ""),
                        }
                    )

            if supported:
                support_count += 1
            else:
                gap_count += 1
            if blockers:
                blocked_count += 1

            clause_results.append(
                {
                    "clause_id": clause["clause_id"],
                    "label": clause["label"],
                    "target_evidence_class": clause["target_evidence_class"],
                    "supported": supported,
                    "requirement_results": [
                        {"ok": ok, "message": msg} for ok, msg in requirement_results
                    ],
                    "blocked": bool(blockers),
                    "blockers": blockers,
                    "notes": clause["notes"],
                }
            )

        clause_count = len(target_shape["clauses"])
        results.append(
            {
                "target_shape_id": target_shape["target_shape_id"],
                "name": target_shape["name"],
                "required": bool(target_shape["required"]),
                "clause_count": clause_count,
                "support_count": support_count,
                "gap_count": gap_count,
                "blocked_count": blocked_count,
                "support_ratio": 0.0 if clause_count == 0 else support_count / clause_count,
                "clauses": clause_results,
            }
        )

    return {
        "schema": "shapeforge/target-shape-eval-report/v1",
        "target_shapes_path": str(path),
        "world_model_path": str(world_model_path),
        "negative_knowledge_path": str(negative_knowledge_path),
        "results": results,
    }


def _render_text(report: dict[str, Any]) -> str:
    lines: list[str] = []
    for result in report["results"]:
        lines.append(
            f"{result['target_shape_id']}: support={result['support_count']}/{result['clause_count']} "
            f"gaps={result['gap_count']} blocked={result['blocked_count']} "
            f"ratio={result['support_ratio']:.2f}"
        )
        for clause in result["clauses"]:
            marker = "OK" if clause["supported"] else "GAP"
            blocked = " blocked" if clause["blocked"] else ""
            lines.append(f"  - {marker}{blocked} {clause['clause_id']}: {clause['label']}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate ShapeForge target shapes against a baseline world model.")
    parser.add_argument("path", type=Path, help="Path to a ShapeForge target-shapes JSON artifact")
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of text")
    args = parser.parse_args()

    report = evaluate_target_shapes(args.path.resolve())
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(_render_text(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

"""Fail-closed checker for the FCIS M6 J03 transport map."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, cast

_ARTIFACT_IDS = (
    "state",
    "configuration",
    "residual_fee_history",
    "proof_contexts",
    "receipts",
    "nullifiers",
    "history",
    "outbox_effects",
)
_EXPECTED_MAPPING = {
    "state": "TRANSPORTED_BY_PROVED_MAP",
    "configuration": "INVALIDATED_AND_REGENERATED",
    "residual_fee_history": "TRANSPORTED_BY_PROVED_MAP",
    "proof_contexts": "INVALIDATED_AND_REGENERATED",
    "receipts": "PRESERVED_UNCHANGED",
    "nullifiers": "PRESERVED_UNCHANGED",
    "history": "PRESERVED_UNCHANGED",
    "outbox_effects": "TRANSPORTED_BY_PROVED_MAP",
}
_MAPPINGS = frozenset(
    {
        "PRESERVED_UNCHANGED",
        "RECOMPUTED_UNDER_TARGET_PROFILE",
        "TRANSPORTED_BY_PROVED_MAP",
        "INVALIDATED_AND_REGENERATED",
        "FORBIDDEN_ACROSS_BOUNDARY",
    }
)
_ARTIFACT_FIELDS = frozenset(
    {
        "artifact_id",
        "mapping",
        "semantic_owner",
        "source_profile_policy",
        "target_profile_policy",
        "cross_boundary",
        "preservation_condition",
        "transport_checker_id",
        "transport_root",
        "required_evidence",
        "acceptance_gate",
        "nonclaims",
    }
)


def _strings(value: object, label: str) -> list[str]:
    if type(value) is not list or not value:
        raise ValueError(f"{label} must be a nonempty list")
    items = cast(list[str], value)
    if any(type(item) is not str or not item for item in items):
        raise ValueError(f"{label} must contain nonempty strings")
    if len(set(items)) != len(items):
        raise ValueError(f"{label} must not contain duplicates")
    return items


def _text(value: object, label: str) -> str:
    if type(value) is not str or not value:
        raise ValueError(f"{label} must be a nonempty string")
    return value


def _check_artifact(row: dict[str, Any]) -> None:
    if set(row) != _ARTIFACT_FIELDS:
        raise ValueError("artifact row fields are not exact")
    artifact_id = _text(row["artifact_id"], "artifact_id")
    if artifact_id not in _ARTIFACT_IDS:
        raise ValueError(f"unknown artifact: {artifact_id}")
    mapping = _text(row["mapping"], f"{artifact_id}.mapping")
    if mapping not in _MAPPINGS:
        raise ValueError(f"invalid mapping for {artifact_id}")
    if mapping != _EXPECTED_MAPPING[artifact_id]:
        raise ValueError(f"mapping policy mismatch for {artifact_id}")
    _text(row["semantic_owner"], f"{artifact_id}.semantic_owner")
    _text(row["source_profile_policy"], f"{artifact_id}.source_profile_policy")
    _text(row["target_profile_policy"], f"{artifact_id}.target_profile_policy")
    if type(row["cross_boundary"]) is not bool:
        raise ValueError(f"{artifact_id}.cross_boundary must be boolean")
    preservation_condition = _text(
        row["preservation_condition"], f"{artifact_id}.preservation_condition"
    )
    checker_id = _text(row["transport_checker_id"], f"{artifact_id}.transport_checker_id")
    transport_root = _text(row["transport_root"], f"{artifact_id}.transport_root")
    _strings(row["required_evidence"], f"{artifact_id}.required_evidence")
    _text(row["acceptance_gate"], f"{artifact_id}.acceptance_gate")
    nonclaims = _strings(row["nonclaims"], f"{artifact_id}.nonclaims")
    if "M6 remains unmounted and non-promotable" not in nonclaims:
        raise ValueError(f"{artifact_id} omits the unmounted M6 boundary")
    if not row["cross_boundary"]:
        raise ValueError(f"{artifact_id} must explicitly declare a migration boundary")
    if mapping == "PRESERVED_UNCHANGED" and not preservation_condition:
        raise ValueError(f"{artifact_id} preserves data without a condition")
    if mapping == "TRANSPORTED_BY_PROVED_MAP":
        if checker_id == "NONE" or transport_root == "NONE":
            raise ValueError(f"{artifact_id} transport map lacks checker/root")
    elif mapping == "INVALIDATED_AND_REGENERATED":
        if "regenerat" not in preservation_condition.lower():
            raise ValueError(f"{artifact_id} invalidation lacks regeneration rule")
    elif mapping == "FORBIDDEN_ACROSS_BOUNDARY":
        if "block" not in preservation_condition.lower():
            raise ValueError(f"{artifact_id} forbidden mapping lacks a blocking rule")


def check_transport_map(path: Path) -> None:
    payload = cast(dict[str, Any], json.loads(path.read_text(encoding="utf-8")))
    if payload.get("schema_version") != "zenodex.fcis.m6.j03.transport-map.v1":
        raise ValueError("wrong J03 transport-map schema")
    if payload.get("task_id") != "J03":
        raise ValueError("wrong J03 task ID")
    if payload.get("status") != "RESEARCH_ONLY_UNMOUNTED":
        raise ValueError("J03 status must remain research-only and unmounted")
    required = payload.get("required_artifact_ids")
    if type(required) is not list or tuple(required) != _ARTIFACT_IDS:
        raise ValueError("J03 artifact registry is incomplete or reordered")
    raw_artifacts = payload.get("artifacts")
    if type(raw_artifacts) is not list or len(raw_artifacts) != len(_ARTIFACT_IDS):
        raise ValueError("J03 must contain exactly eight artifact rows")
    artifacts = cast(list[dict[str, Any]], raw_artifacts)
    seen: set[str] = set()
    for artifact in artifacts:
        if type(artifact) is not dict:
            raise ValueError("artifact row must be an object")
        _check_artifact(artifact)
        artifact_id = cast(str, artifact["artifact_id"])
        if artifact_id in seen:
            raise ValueError(f"duplicate artifact: {artifact_id}")
        seen.add(artifact_id)
    if tuple(cast(str, artifact["artifact_id"]) for artifact in artifacts) != _ARTIFACT_IDS:
        raise ValueError("J03 artifact rows are not in the required order")
    if seen != set(_ARTIFACT_IDS):
        raise ValueError("J03 artifact coverage is incomplete")
    global_nonclaims = _strings(payload.get("global_nonclaims"), "global_nonclaims")
    if "M6 remains unmounted and non-promotable" not in global_nonclaims:
        raise ValueError("J03 global nonclaims omit the unmounted boundary")


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: check_fcis_m6_j03_transport_map.py <transport-map.json>", file=sys.stderr)
        return 2
    try:
        check_transport_map(Path(argv[1]))
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"J03_TRANSPORT_MAP_REJECT: {exc}", file=sys.stderr)
        return 1
    print("J03_TRANSPORT_MAP_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))

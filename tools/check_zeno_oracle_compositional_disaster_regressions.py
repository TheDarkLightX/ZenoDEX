#!/usr/bin/env python3
"""Validate the public projection of private compositional disaster campaigns."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "tools" / "zeno_oracle_compositional_disaster_regression_manifest.json"
MANIFEST_SCHEMA = "zenodex/zeno-oracle-compositional-disaster-regression-manifest/v1"
CHECK_SCHEMA = "zenodex/zeno-oracle-compositional-disaster-regression-check/v1"
ACCEPTED_PUBLIC_REPLAY = "accepted_public_replay"
DEFERRED_MISSING_SURFACE = "deferred_missing_public_surface"


@dataclass(frozen=True)
class CheckError(Exception):
    message: str

    def __str__(self) -> str:  # pragma: no cover
        return self.message


def _require_mapping(obj: Any, *, name: str) -> dict[str, Any]:
    if not isinstance(obj, dict):
        raise CheckError(f"{name} must be an object")
    return obj


def _require_list(obj: Any, *, name: str) -> list[Any]:
    if not isinstance(obj, list):
        raise CheckError(f"{name} must be a list")
    return obj


def _require_str(obj: Any, *, name: str) -> str:
    if not isinstance(obj, str) or not obj.strip():
        raise CheckError(f"{name} must be a non-empty string")
    return obj.strip()


def _require_bool(obj: Any, *, name: str) -> bool:
    if not isinstance(obj, bool):
        raise CheckError(f"{name} must be a bool")
    return obj


def _require_int(obj: Any, *, name: str, minimum: int = 0) -> int:
    if not isinstance(obj, int) or isinstance(obj, bool):
        raise CheckError(f"{name} must be an integer")
    if obj < minimum:
        raise CheckError(f"{name} must be >= {minimum}")
    return obj


def _require_str_list(obj: Any, *, name: str) -> list[str]:
    items = _require_list(obj, name=name)
    out: list[str] = []
    for index, item in enumerate(items):
        out.append(_require_str(item, name=f"{name}[{index}]"))
    return out


def _repo_path(rel_path: str, *, name: str) -> Path:
    if rel_path.startswith("/") or ".." in Path(rel_path).parts:
        raise CheckError(f"{name} must be a relative in-repo path")
    path = (ROOT / rel_path).resolve()
    if ROOT not in path.parents and path != ROOT:
        raise CheckError(f"{name} must stay inside repo")
    if not path.exists():
        raise CheckError(f"{name} missing: {rel_path}")
    return path


def _iter_strings(obj: Any) -> Iterable[str]:
    if isinstance(obj, str):
        yield obj
    elif isinstance(obj, dict):
        for key, value in obj.items():
            if isinstance(key, str):
                yield key
            yield from _iter_strings(value)
    elif isinstance(obj, list):
        for value in obj:
            yield from _iter_strings(value)


def _reject_private_path_strings(root: dict[str, Any]) -> None:
    forbidden = ("internal/", "runs/", "/home/", "/tmp/")
    for value in _iter_strings(root):
        for needle in forbidden:
            if needle in value:
                raise CheckError(f"manifest leaks private path marker {needle!r}: {value!r}")


def _validate_campaigns(root: dict[str, Any]) -> list[dict[str, Any]]:
    campaigns_raw = _require_list(root.get("campaign_summaries"), name="campaign_summaries")
    if len(campaigns_raw) != 2:
        raise CheckError("campaign_summaries must contain the two sanitized campaign summaries")
    campaigns: list[dict[str, Any]] = []
    seen: set[str] = set()
    for index, raw in enumerate(campaigns_raw):
        campaign = _require_mapping(raw, name=f"campaign_summaries[{index}]")
        campaign_id = _require_str(campaign.get("campaign_id"), name=f"campaign_summaries[{index}].campaign_id")
        if campaign_id in seen:
            raise CheckError(f"duplicate campaign_id: {campaign_id}")
        seen.add(campaign_id)
        if not campaign_id.startswith("compositional_aot100"):
            raise CheckError(f"unexpected campaign_id: {campaign_id}")
        _require_str(campaign.get("check_schema"), name=f"campaign_summaries[{index}].check_schema")
        if _require_bool(campaign.get("ok"), name=f"campaign_summaries[{index}].ok") is not True:
            raise CheckError(f"{campaign_id}: ok must be true")
        if _require_int(campaign.get("iteration_count"), name=f"{campaign_id}.iteration_count", minimum=1) != 100:
            raise CheckError(f"{campaign_id}: iteration_count must be 100")
        if _require_int(campaign.get("unique_atom_count"), name=f"{campaign_id}.unique_atom_count", minimum=1) != 100:
            raise CheckError(f"{campaign_id}: unique_atom_count must be 100")
        if _require_int(campaign.get("unique_candidate_count"), name=f"{campaign_id}.unique_candidate_count", minimum=1) != 100:
            raise CheckError(f"{campaign_id}: unique_candidate_count must be 100")
        if _require_int(campaign.get("promotion_ready_count"), name=f"{campaign_id}.promotion_ready_count") != 0:
            raise CheckError(f"{campaign_id}: promotion_ready_count must remain 0")
        lane_counts = _require_mapping(campaign.get("lane_counts"), name=f"{campaign_id}.lane_counts")
        shape_counts = _require_mapping(campaign.get("shape_counts"), name=f"{campaign_id}.shape_counts")
        if sum(_require_int(value, name=f"{campaign_id}.lane_counts.{key}") for key, value in lane_counts.items()) != 100:
            raise CheckError(f"{campaign_id}: lane_counts must sum to 100")
        if sum(_require_int(value, name=f"{campaign_id}.shape_counts.{key}") for key, value in shape_counts.items()) != 100:
            raise CheckError(f"{campaign_id}: shape_counts must sum to 100")
        campaigns.append(campaign)
    return campaigns


def _validate_expected(entry_id: str, expected_raw: Any) -> None:
    expected = _require_mapping(expected_raw, name=f"{entry_id}.expected")
    _require_str(expected.get("target"), name=f"{entry_id}.expected.target")
    _require_str(expected.get("derivation"), name=f"{entry_id}.expected.derivation")
    _require_str_list(expected.get("outcome_substrings"), name=f"{entry_id}.expected.outcome_substrings")
    original_size = _require_int(expected.get("original_size"), name=f"{entry_id}.expected.original_size", minimum=1)
    minimized_size = _require_int(expected.get("minimized_size"), name=f"{entry_id}.expected.minimized_size", minimum=1)
    if minimized_size > original_size:
        raise CheckError(f"{entry_id}: minimized_size cannot exceed original_size")
    _require_str(expected.get("path_id_policy"), name=f"{entry_id}.expected.path_id_policy")


def _validate_accepted_entry(entry: dict[str, Any], *, entry_id: str) -> None:
    test_file = _require_str(entry.get("test_file"), name=f"{entry_id}.test_file")
    test_path = _repo_path(test_file, name=f"{entry_id}.test_file")
    test_text = test_path.read_text(encoding="utf-8")
    for test_name in _require_str_list(entry.get("test_names"), name=f"{entry_id}.test_names"):
        if f"def {test_name}(" not in test_text:
            raise CheckError(f"{entry_id}.test_names missing in {test_file}: {test_name}")
    for source_file in _require_str_list(entry.get("source_files"), name=f"{entry_id}.source_files"):
        _repo_path(source_file, name=f"{entry_id}.source_files")
    commands = _require_str_list(entry.get("replay_commands"), name=f"{entry_id}.replay_commands")
    if not commands:
        raise CheckError(f"{entry_id}: replay_commands must be non-empty")
    _validate_expected(entry_id, entry.get("expected"))


def _validate_deferred_entry(entry: dict[str, Any], *, entry_id: str) -> None:
    _require_str(entry.get("deferred_reason"), name=f"{entry_id}.deferred_reason")
    _require_str(entry.get("expected_public_test"), name=f"{entry_id}.expected_public_test")
    if "replay_commands" in entry:
        raise CheckError(f"{entry_id}: deferred entries cannot declare replay_commands")


def _validate_projection(root: dict[str, Any]) -> dict[str, Any]:
    projection = _require_mapping(root.get("candidate_witness_projection"), name="candidate_witness_projection")
    source_campaign_id = _require_str(
        projection.get("source_campaign_id"),
        name="candidate_witness_projection.source_campaign_id",
    )
    if source_campaign_id != "compositional_aot100_expansion2_2026_05_05":
        raise CheckError("candidate_witness_projection.source_campaign_id must be expansion2")
    entries_raw = _require_list(projection.get("entries"), name="candidate_witness_projection.entries")
    expected_private_count = _require_int(
        projection.get("private_candidate_witness_count"),
        name="candidate_witness_projection.private_candidate_witness_count",
        minimum=1,
    )
    if expected_private_count != len(entries_raw):
        raise CheckError("private_candidate_witness_count must equal entries length")

    entries: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    seen_atoms: set[str] = set()
    accepted_count = 0
    deferred_count = 0
    for index, raw in enumerate(entries_raw):
        entry = _require_mapping(raw, name=f"candidate_witness_projection.entries[{index}]")
        entry_id = _require_str(entry.get("id"), name=f"entries[{index}].id")
        atom_id = _require_str(entry.get("atom_id"), name=f"{entry_id}.atom_id")
        if entry_id in seen_ids:
            raise CheckError(f"duplicate entry id: {entry_id}")
        if atom_id in seen_atoms:
            raise CheckError(f"duplicate atom id: {atom_id}")
        seen_ids.add(entry_id)
        seen_atoms.add(atom_id)
        if not atom_id.startswith("AOT-EXP2-"):
            raise CheckError(f"{entry_id}: atom_id must be an expansion2 atom")
        _require_str(entry.get("composition_shape"), name=f"{entry_id}.composition_shape")
        _require_str(entry.get("surface_pair"), name=f"{entry_id}.surface_pair")
        public_status = _require_str(entry.get("public_status"), name=f"{entry_id}.public_status")
        if public_status == ACCEPTED_PUBLIC_REPLAY:
            accepted_count += 1
            _validate_accepted_entry(entry, entry_id=entry_id)
        elif public_status == DEFERRED_MISSING_SURFACE:
            deferred_count += 1
            _validate_deferred_entry(entry, entry_id=entry_id)
        else:
            raise CheckError(f"{entry_id}: unsupported public_status {public_status!r}")
        entries.append(entry)

    if _require_int(projection.get("accepted_public_regression_count"), name="accepted_public_regression_count") != accepted_count:
        raise CheckError("accepted_public_regression_count mismatch")
    if _require_int(projection.get("deferred_projection_count"), name="deferred_projection_count") != deferred_count:
        raise CheckError("deferred_projection_count mismatch")
    return {
        "source_campaign_id": source_campaign_id,
        "private_candidate_witness_count": expected_private_count,
        "accepted_public_regression_count": accepted_count,
        "deferred_projection_count": deferred_count,
        "entries": entries,
    }


def _relative(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


def validate_manifest(path: Path = MANIFEST_PATH) -> dict[str, Any]:
    root = _require_mapping(json.loads(path.read_text(encoding="utf-8")), name="manifest")
    schema = _require_str(root.get("schema"), name="manifest.schema")
    if schema != MANIFEST_SCHEMA:
        raise CheckError(f"unsupported manifest.schema: {schema}")
    policy = _require_mapping(root.get("private_artifact_policy"), name="private_artifact_policy")
    if _require_bool(policy.get("private_campaign_artifacts_committed"), name="private_campaign_artifacts_committed"):
        raise CheckError("private campaign artifacts must remain uncommitted")
    if not _require_bool(policy.get("raw_private_paths_excluded"), name="raw_private_paths_excluded"):
        raise CheckError("raw private paths must be excluded")
    _require_str(policy.get("public_claim_tier"), name="private_artifact_policy.public_claim_tier")
    _require_str(policy.get("promotion_rule"), name="private_artifact_policy.promotion_rule")
    _reject_private_path_strings(root)
    campaigns = _validate_campaigns(root)
    projection = _validate_projection(root)
    return {
        "manifest": root,
        "campaigns": campaigns,
        "projection": projection,
    }


def build_receipt(path: Path = MANIFEST_PATH) -> dict[str, Any]:
    checked = validate_manifest(path)
    projection = checked["projection"]
    accepted_entries = [
        entry["id"]
        for entry in projection["entries"]
        if entry["public_status"] == ACCEPTED_PUBLIC_REPLAY
    ]
    deferred_entries = [
        entry["id"]
        for entry in projection["entries"]
        if entry["public_status"] == DEFERRED_MISSING_SURFACE
    ]
    return {
        "schema": CHECK_SCHEMA,
        "ok": True,
        "manifest_path": _relative(path),
        "campaign_count": len(checked["campaigns"]),
        "source_campaign_id": projection["source_campaign_id"],
        "private_candidate_witness_count": projection["private_candidate_witness_count"],
        "accepted_public_regression_count": projection["accepted_public_regression_count"],
        "deferred_projection_count": projection["deferred_projection_count"],
        "accepted_public_regressions": accepted_entries,
        "deferred_projections": deferred_entries,
        "limits": [
            "private_campaign_artifacts_are_not_public_evidence",
            "public_regressions_are_bounded_branch_local_replays",
            "new_private_candidates_require_source_surface_migration_before_claim_promotion"
        ],
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=MANIFEST_PATH)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        receipt = build_receipt(args.manifest)
    except (CheckError, OSError, json.JSONDecodeError) as exc:
        print(f"compositional disaster regression manifest invalid: {exc}", file=sys.stderr)
        return 1
    if args.format == "json":
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print("status = accepted")
        print(f"campaign_count = {receipt['campaign_count']}")
        print(f"private_candidate_witness_count = {receipt['private_candidate_witness_count']}")
        print(f"accepted_public_regression_count = {receipt['accepted_public_regression_count']}")
        print(f"deferred_projection_count = {receipt['deferred_projection_count']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Check the AB child-frontier deterministic generated-image producer manifest.

This research-only checker binds the committed n=7 zero-min child-frontier
pipeline to an ordered producer manifest. It verifies the script hashes, source
seed, stage order, checked report hashes, stage output digests, downstream link
digests, deterministic replay hashes, and no-authority rail.
"""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.check_ab_reserve_state_child_frontier_canonical_merkle_20260629 import (  # noqa: E402
    build_report as build_canonical_merkle_report,
)
from tools.check_ab_reserve_state_child_frontier_corpus_root_20260629 import (  # noqa: E402
    build_report as build_corpus_root_report,
)
from tools.check_ab_reserve_state_child_frontier_generation_20260629 import (  # noqa: E402
    build_report as build_generation_report,
)
from tools.check_ab_reserve_state_child_frontier_witness_compression_20260629 import (  # noqa: E402
    build_report as build_witness_compression_report,
)
from tools.check_ab_reserve_state_child_frontier_witness_merkle_20260629 import (  # noqa: E402
    build_report as build_witness_merkle_report,
)
from tools.check_ab_strict_zero_min_emitter_witness import _sha256_json, _strip_timing  # noqa: E402

OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_child_frontier_generated_image_producer_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_CHILD_FRONTIER_GENERATED_IMAGE_PRODUCER_20260629.md"

REPORT_SCHEMA = "zenodex.ab_child_frontier_generated_image_producer_report.v1"
MANIFEST_SCHEMA = "zenodex.ab_child_frontier_generated_image_producer_manifest.v1"
SCOPE = "n7_same_pool_same_direction_exact_in_zero_min_child_frontier_generated_image_producer"
AUTHORITY_BOUNDARY = "research_only_no_settlement_state_root_production_or_governance_authority"
EXPECTED_CASE_COUNT = 4
EXPECTED_CHILD_MASK_COUNT = 508
EXPECTED_CHILD_STATE_COUNT = 864
EXPECTED_STAGE_ORDER = (
    "generation",
    "canonical_merkle",
    "witness_compression",
    "witness_merkle_cross_binding",
    "corpus_root",
)
EXPECTED_NEGATIVE_CONTROL_COUNT = 10


@dataclass(frozen=True)
class StageSpec:
    stage_id: str
    script_path: Path
    report_path: Path
    schema: str
    build_report: Callable[[], dict[str, Any]]
    expected_script_sha256: str
    expected_deterministic_hash: str
    expected_outputs: Mapping[str, Any]


STAGE_SPECS = (
    StageSpec(
        stage_id="generation",
        script_path=REPO_ROOT / "tools" / "check_ab_reserve_state_child_frontier_generation_20260629.py",
        report_path=REPO_ROOT / "generated" / "zenodex_ab_reserve_state_child_frontier_generation_20260629" / "report.json",
        schema="zenodex.ab_reserve_state_child_frontier_generation_report.v1",
        build_report=build_generation_report,
        expected_script_sha256="647cc897c552253268f868c7c43885f08c01fa266c4f4487410449318fd8033b",
        expected_deterministic_hash="8d698629548edaa62cf8e7367cb0845d8cf4efd1d5583e9997b8ec878d4b0925",
        expected_outputs={
            "frontier_rows_digest": "b0536297bdec3e49204d98e4a52b4b43ea1467f7a32c2e184cf0bec07955fba4",
            "child_mask_count": EXPECTED_CHILD_MASK_COUNT,
            "child_state_count": EXPECTED_CHILD_STATE_COUNT,
            "generated_state_count": EXPECTED_CHILD_STATE_COUNT,
            "predecessor_transition_count": 2777,
            "negative_control_count": 7,
            "negative_control_accept_count": 0,
        },
    ),
    StageSpec(
        stage_id="canonical_merkle",
        script_path=REPO_ROOT / "tools" / "check_ab_reserve_state_child_frontier_canonical_merkle_20260629.py",
        report_path=REPO_ROOT / "generated" / "zenodex_ab_reserve_state_child_frontier_canonical_merkle_20260629" / "report.json",
        schema="zenodex.ab_reserve_state_child_frontier_canonical_merkle_report.v1",
        build_report=build_canonical_merkle_report,
        expected_script_sha256="a6ae402e0dd8d6814c6e58005ee532cffcff92a893be80b22b02c42e89a606ad",
        expected_deterministic_hash="f86d378183d5f81c1ebd5e9d04610dc35cb0343f95ae99ba2e2df127d76c5ab5",
        expected_outputs={
            "frontier_roots_digest": "42f3e7f10918fa3497183812cb316955c3382f4f3b4a4bb5309e47ec5855008b",
            "membership_rows_digest": "84cdbf4ebc62d758655f2ad253e541d072a7158f4c75bd939be521d613c84559",
            "child_mask_count": EXPECTED_CHILD_MASK_COUNT,
            "child_state_count": EXPECTED_CHILD_STATE_COUNT,
            "membership_count": EXPECTED_CHILD_STATE_COUNT,
            "negative_control_count": 8,
            "negative_control_accept_count": 0,
        },
    ),
    StageSpec(
        stage_id="witness_compression",
        script_path=REPO_ROOT / "tools" / "check_ab_reserve_state_child_frontier_witness_compression_20260629.py",
        report_path=REPO_ROOT / "generated" / "zenodex_ab_reserve_state_child_frontier_witness_compression_20260629" / "report.json",
        schema="zenodex.ab_reserve_state_child_frontier_witness_compression_report.v1",
        build_report=build_witness_compression_report,
        expected_script_sha256="15d83d36de5369efc5d7882e43f8e5648742a08813534699363cb1421ec0c57a",
        expected_deterministic_hash="b6ee02a7ebb46e71229b8e75f194d712d7874f77dfc6caa2096c9dcd8fde3a62",
        expected_outputs={
            "witness_rows_digest": "d689dd569b28abf3cb2636def322fa9d8185c2eb1fe4843bd83d07bce69138c3",
            "child_mask_count": EXPECTED_CHILD_MASK_COUNT,
            "witness_count": EXPECTED_CHILD_STATE_COUNT,
            "covered_child_state_count": EXPECTED_CHILD_STATE_COUNT,
            "predecessor_transition_count": 2777,
            "witness_transition_checks_saved": 1913,
            "negative_control_count": 8,
            "negative_control_accept_count": 0,
        },
    ),
    StageSpec(
        stage_id="witness_merkle_cross_binding",
        script_path=REPO_ROOT / "tools" / "check_ab_reserve_state_child_frontier_witness_merkle_20260629.py",
        report_path=REPO_ROOT / "generated" / "zenodex_ab_reserve_state_child_frontier_witness_merkle_20260629" / "report.json",
        schema="zenodex.ab_reserve_state_child_frontier_witness_merkle_report.v1",
        build_report=build_witness_merkle_report,
        expected_script_sha256="c9e6695fb81b1b1c8056ddb6e4e223771da5218bfe2469df8ca17e8fa6410150",
        expected_deterministic_hash="9a94b98c560a2e191407a34e9fd1b3a7435cf2bb3cdd60c73227ece673031b31",
        expected_outputs={
            "bound_rows_digest": "0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551",
            "child_mask_count": EXPECTED_CHILD_MASK_COUNT,
            "bound_row_count": EXPECTED_CHILD_STATE_COUNT,
            "witness_count": EXPECTED_CHILD_STATE_COUNT,
            "membership_count": EXPECTED_CHILD_STATE_COUNT,
            "negative_control_count": 10,
            "negative_control_accept_count": 0,
        },
    ),
    StageSpec(
        stage_id="corpus_root",
        script_path=REPO_ROOT / "tools" / "check_ab_reserve_state_child_frontier_corpus_root_20260629.py",
        report_path=REPO_ROOT / "generated" / "zenodex_ab_reserve_state_child_frontier_corpus_root_20260629" / "report.json",
        schema="zenodex.ab_reserve_state_child_frontier_corpus_root_report.v1",
        build_report=build_corpus_root_report,
        expected_script_sha256="1a3d21c0e9def26ffbe7407da8f8b4825933fe550a1f235d0da3bf9436a32b80",
        expected_deterministic_hash="b857b66aa96007bda748ae9489ee10f972248eaa30af25fd5ac7dffca73f4591",
        expected_outputs={
            "corpus_root": "8f4a1a08cf51215cdc9fd382dd2538cc199db35b87597aa9c468358925dfd3b0",
            "case_summaries_digest": "afd7706fd7ea10cee0df44d7578dabf44fc82a26d238f814d717c5fee3b5bc28",
            "row_receipts_digest": "d52f8c24411e841ae777999d6bfd3ec3fef5bb0a26cd98887f4e0a5902c0f092",
            "case_count": EXPECTED_CASE_COUNT,
            "row_receipt_count": EXPECTED_CHILD_STATE_COUNT,
            "covered_row_receipt_count": EXPECTED_CHILD_STATE_COUNT,
            "negative_control_count": 10,
            "negative_control_accept_count": 0,
        },
    ),
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _search(report: Mapping[str, Any]) -> Mapping[str, Any]:
    search = report.get("search")
    if not isinstance(search, Mapping):
        return {}
    return search


def _relative(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def _stage_outputs(stage_id: str, report: Mapping[str, Any]) -> dict[str, Any]:
    search = _search(report)
    if stage_id == "generation":
        return {
            "frontier_rows_digest": search.get("frontier_rows_digest"),
            "child_mask_count": search.get("child_mask_count"),
            "child_state_count": search.get("child_state_count"),
            "generated_state_count": search.get("generated_state_count"),
            "predecessor_transition_count": search.get("predecessor_transition_count"),
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
        }
    if stage_id == "canonical_merkle":
        return {
            "frontier_roots_digest": search.get("frontier_roots_digest"),
            "membership_rows_digest": search.get("membership_rows_digest"),
            "child_mask_count": search.get("child_mask_count"),
            "child_state_count": search.get("child_state_count"),
            "membership_count": search.get("membership_count"),
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
        }
    if stage_id == "witness_compression":
        return {
            "witness_rows_digest": search.get("witness_rows_digest"),
            "child_mask_count": search.get("child_mask_count"),
            "witness_count": search.get("witness_count"),
            "covered_child_state_count": search.get("covered_child_state_count"),
            "predecessor_transition_count": search.get("predecessor_transition_count"),
            "witness_transition_checks_saved": search.get("witness_transition_checks_saved"),
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
        }
    if stage_id == "witness_merkle_cross_binding":
        return {
            "bound_rows_digest": search.get("bound_rows_digest"),
            "child_mask_count": search.get("child_mask_count"),
            "bound_row_count": search.get("bound_row_count"),
            "witness_count": search.get("witness_count"),
            "membership_count": search.get("membership_count"),
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
        }
    if stage_id == "corpus_root":
        return {
            "corpus_root": search.get("corpus_root"),
            "case_summaries_digest": search.get("case_summaries_digest"),
            "row_receipts_digest": search.get("row_receipts_digest"),
            "case_count": search.get("case_count"),
            "row_receipt_count": search.get("row_receipt_count"),
            "covered_row_receipt_count": search.get("covered_row_receipt_count"),
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
        }
    raise ValueError(f"unknown stage_id: {stage_id}")


def _deterministic_hash(report: Mapping[str, Any]) -> str | None:
    replay = report.get("deterministic_replay")
    if not isinstance(replay, Mapping) or replay.get("ok") is not True:
        return None
    if replay.get("first_hash") != replay.get("second_hash"):
        return None
    first_hash = replay.get("first_hash")
    return str(first_hash) if isinstance(first_hash, str) else None


def _source_seed(report: Mapping[str, Any]) -> str | None:
    seed = _search(report).get("source_seed")
    return str(seed) if seed is not None else None


def _stage_manifest(spec: StageSpec, report: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "stage_id": spec.stage_id,
        "script_path": _relative(spec.script_path),
        "script_sha256": _sha256(spec.script_path),
        "report_path": _relative(spec.report_path),
        "report_sha256": _sha256(spec.report_path),
        "report_schema": report.get("schema"),
        "report_ok": bool(report.get("ok")),
        "source_seed": _source_seed(report),
        "deterministic_hash": _deterministic_hash(report),
        "outputs": _stage_outputs(spec.stage_id, report),
    }


def _cross_stage_links(reports: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    generation = _search(reports["generation"])
    canonical = _search(reports["canonical_merkle"])
    witness = _search(reports["witness_compression"])
    bound = _search(reports["witness_merkle_cross_binding"])
    corpus = _search(reports["corpus_root"])
    canonical_link = canonical.get("linked_frontier_summary", {})
    bound_merkle_link = bound.get("linked_merkle_summary", {})
    bound_witness_link = bound.get("linked_witness_summary", {})
    corpus_link = corpus.get("linked_cross_binding_summary", {})
    return {
        "canonical_frontier_digest_matches_generation": (
            isinstance(canonical_link, Mapping)
            and canonical_link.get("frontier_rows_digest") == generation.get("frontier_rows_digest")
        ),
        "witness_merkle_digest_matches_canonical": (
            isinstance(bound_merkle_link, Mapping)
            and bound_merkle_link.get("digest") == canonical.get("membership_rows_digest")
        ),
        "witness_rows_digest_matches_witness_compression": (
            isinstance(bound_witness_link, Mapping)
            and bound_witness_link.get("digest") == witness.get("witness_rows_digest")
        ),
        "corpus_bound_rows_digest_matches_cross_binding": (
            isinstance(corpus_link, Mapping)
            and corpus_link.get("bound_rows_digest") == bound.get("bound_rows_digest")
        ),
        "corpus_row_count_matches_cross_binding": (
            isinstance(corpus_link, Mapping)
            and int(corpus_link.get("bound_row_count", -1)) == int(bound.get("bound_row_count", -2))
        ),
    }


def _with_manifest_hash(manifest: Mapping[str, Any]) -> dict[str, Any]:
    packet = dict(manifest)
    packet.pop("manifest_hash", None)
    packet["manifest_hash"] = _sha256_json(packet)
    return packet


def load_checked_reports() -> dict[str, dict[str, Any]]:
    return {spec.stage_id: _load_json(spec.report_path) for spec in STAGE_SPECS}


def replay_stage_reports() -> dict[str, dict[str, Any]]:
    return {spec.stage_id: spec.build_report() for spec in STAGE_SPECS}


def build_manifest(reports: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    stage_manifests = [_stage_manifest(spec, reports[spec.stage_id]) for spec in STAGE_SPECS]
    source_seeds = sorted({stage["source_seed"] for stage in stage_manifests if stage["source_seed"]})
    manifest = {
        "schema": MANIFEST_SCHEMA,
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "no_authority_effect": True,
        "producer_stage_order_bound": True,
        "producer_stage_order": list(EXPECTED_STAGE_ORDER),
        "source_seed": source_seeds[0] if len(source_seeds) == 1 else None,
        "stage_manifests": stage_manifests,
        "cross_stage_links": _cross_stage_links(reports),
        "non_claims": [
            "bounded n=7 zero-min corpus only",
            "does not prove Python-to-Lean refinement",
            "does not prove child-frontier generation in Lean",
            "does not cover nonzero min_amount_out behavior",
            "does not authorize settlement or state roots",
        ],
    }
    return _with_manifest_hash(manifest)


def _stage_by_id(manifest: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    stages = manifest.get("stage_manifests")
    if not isinstance(stages, list):
        return {}
    output: dict[str, Mapping[str, Any]] = {}
    for stage in stages:
        if isinstance(stage, Mapping) and isinstance(stage.get("stage_id"), str):
            output[str(stage["stage_id"])] = stage
    return output


def verify_manifest(
    manifest: Mapping[str, Any],
    *,
    checked_reports: Mapping[str, Mapping[str, Any]],
    replayed_reports: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    reasons: list[str] = []
    if manifest.get("schema") != MANIFEST_SCHEMA:
        reasons.append("manifest_schema_mismatch")
    if manifest.get("scope") != SCOPE:
        reasons.append("manifest_scope_mismatch")
    if manifest.get("authority_boundary") != AUTHORITY_BOUNDARY:
        reasons.append("authority_boundary_mismatch")
    if manifest.get("no_authority_effect") is not True:
        reasons.append("authority_effect_present")
    if manifest.get("producer_stage_order_bound") is not True:
        reasons.append("producer_stage_order_bound_missing")
    if tuple(manifest.get("producer_stage_order", ())) != EXPECTED_STAGE_ORDER:
        reasons.append("producer_stage_order_mismatch")
    if manifest.get("manifest_hash") != _sha256_json({k: v for k, v in manifest.items() if k != "manifest_hash"}):
        reasons.append("manifest_hash_mismatch")
    if not isinstance(manifest.get("source_seed"), str):
        reasons.append("source_seed_missing")

    stages = _stage_by_id(manifest)
    if tuple(stages) != EXPECTED_STAGE_ORDER:
        reasons.append("stage_manifest_order_mismatch")
    missing_stages = [stage_id for stage_id in EXPECTED_STAGE_ORDER if stage_id not in stages]
    if missing_stages:
        reasons.append("stage_manifest_missing")

    for spec in STAGE_SPECS:
        stage = stages.get(spec.stage_id)
        if stage is None:
            continue
        checked = checked_reports[spec.stage_id]
        expected_outputs = dict(spec.expected_outputs)
        if stage.get("script_path") != _relative(spec.script_path):
            reasons.append(f"{spec.stage_id}_script_path_mismatch")
        if stage.get("script_sha256") != spec.expected_script_sha256:
            reasons.append(f"{spec.stage_id}_script_hash_mismatch")
        if _sha256(spec.script_path) != spec.expected_script_sha256:
            reasons.append(f"{spec.stage_id}_current_script_hash_mismatch")
        if stage.get("report_path") != _relative(spec.report_path):
            reasons.append(f"{spec.stage_id}_report_path_mismatch")
        if stage.get("report_sha256") != _sha256(spec.report_path):
            reasons.append(f"{spec.stage_id}_report_hash_mismatch")
        if stage.get("report_schema") != spec.schema or checked.get("schema") != spec.schema:
            reasons.append(f"{spec.stage_id}_report_schema_mismatch")
        if stage.get("report_ok") is not True or checked.get("ok") is not True:
            reasons.append(f"{spec.stage_id}_report_not_ok")
        if stage.get("deterministic_hash") != spec.expected_deterministic_hash:
            reasons.append(f"{spec.stage_id}_deterministic_hash_mismatch")
        if _deterministic_hash(checked) != spec.expected_deterministic_hash:
            reasons.append(f"{spec.stage_id}_checked_deterministic_hash_mismatch")
        if stage.get("outputs") != expected_outputs:
            reasons.append(f"{spec.stage_id}_output_digest_mismatch")
        if _stage_outputs(spec.stage_id, checked) != expected_outputs:
            reasons.append(f"{spec.stage_id}_checked_output_digest_mismatch")
        if stage.get("source_seed") != manifest.get("source_seed"):
            reasons.append(f"{spec.stage_id}_source_seed_mismatch")
        if replayed_reports is not None:
            replayed = replayed_reports[spec.stage_id]
            if bool(replayed.get("ok")) is not True:
                reasons.append(f"{spec.stage_id}_replay_not_ok")
            if _stage_outputs(spec.stage_id, replayed) != expected_outputs:
                reasons.append(f"{spec.stage_id}_replay_output_digest_mismatch")
            if _deterministic_hash(replayed) != spec.expected_deterministic_hash:
                reasons.append(f"{spec.stage_id}_replay_deterministic_hash_mismatch")

    source_seeds = {stage.get("source_seed") for stage in stages.values()}
    if len(source_seeds) != 1 or manifest.get("source_seed") not in source_seeds:
        reasons.append("source_seed_mismatch")

    links = manifest.get("cross_stage_links")
    expected_links = _cross_stage_links(checked_reports)
    if links != expected_links:
        reasons.append("cross_stage_links_mismatch")
    if not all(bool(value) for value in expected_links.values()):
        reasons.append("checked_cross_stage_link_failure")
    if isinstance(links, Mapping) and not all(bool(value) for value in links.values()):
        reasons.append("manifest_cross_stage_link_failure")

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "missing_stage_count": len(missing_stages),
    }


def _negative_controls(manifest: Mapping[str, Any], checked_reports: Mapping[str, Mapping[str, Any]]) -> list[dict[str, Any]]:
    controls: list[tuple[str, dict[str, Any], str]] = []

    stale_hash = copy.deepcopy(dict(manifest))
    stale_hash["manifest_hash"] = "0" * 64
    controls.append(("manifest_hash_mismatch", stale_hash, "manifest_hash_mismatch"))

    bad_order = copy.deepcopy(dict(manifest))
    bad_order["producer_stage_order"] = list(reversed(EXPECTED_STAGE_ORDER))
    controls.append(("producer_stage_order_mismatch", _with_manifest_hash(bad_order), "producer_stage_order_mismatch"))

    missing_stage = copy.deepcopy(dict(manifest))
    missing_stage["stage_manifests"] = list(missing_stage["stage_manifests"][:-1])
    controls.append(("stage_manifest_missing", _with_manifest_hash(missing_stage), "stage_manifest_missing"))

    bad_seed = copy.deepcopy(dict(manifest))
    bad_seed["source_seed"] = "stale-seed"
    controls.append(("source_seed_mismatch", _with_manifest_hash(bad_seed), "generation_source_seed_mismatch"))

    bad_script = copy.deepcopy(dict(manifest))
    bad_script["stage_manifests"][0]["script_sha256"] = "0" * 64
    controls.append(("generation_script_hash_mismatch", _with_manifest_hash(bad_script), "generation_script_hash_mismatch"))

    bad_report_hash = copy.deepcopy(dict(manifest))
    bad_report_hash["stage_manifests"][0]["report_sha256"] = "0" * 64
    controls.append(("generation_report_hash_mismatch", _with_manifest_hash(bad_report_hash), "generation_report_hash_mismatch"))

    bad_generation = copy.deepcopy(dict(manifest))
    bad_generation["stage_manifests"][0]["outputs"]["frontier_rows_digest"] = "0" * 64
    controls.append(("generation_output_digest_mismatch", _with_manifest_hash(bad_generation), "generation_output_digest_mismatch"))

    bad_canonical = copy.deepcopy(dict(manifest))
    bad_canonical["stage_manifests"][1]["outputs"]["membership_rows_digest"] = "0" * 64
    controls.append(("canonical_merkle_output_digest_mismatch", _with_manifest_hash(bad_canonical), "canonical_merkle_output_digest_mismatch"))

    bad_corpus = copy.deepcopy(dict(manifest))
    bad_corpus["stage_manifests"][4]["outputs"]["corpus_root"] = "0" * 64
    controls.append(("corpus_root_output_digest_mismatch", _with_manifest_hash(bad_corpus), "corpus_root_output_digest_mismatch"))

    bad_authority = copy.deepcopy(dict(manifest))
    bad_authority["no_authority_effect"] = False
    controls.append(("authority_effect_present", _with_manifest_hash(bad_authority), "authority_effect_present"))

    output: list[dict[str, Any]] = []
    for mutation_id, packet, expected_reason in controls:
        verification = verify_manifest(packet, checked_reports=checked_reports)
        output.append(
            {
                "mutation_id": mutation_id,
                "accepted": bool(verification["ok"]),
                "expected_reason": expected_reason,
                "reasons": verification["reasons"],
            }
        )
    return output


def build_report(*, replay_stages: bool = True) -> dict[str, Any]:
    started = time.perf_counter()
    checked_reports = load_checked_reports()
    manifest = build_manifest(checked_reports)
    replayed_reports = replay_stage_reports() if replay_stages else None
    verification = verify_manifest(
        manifest,
        checked_reports=checked_reports,
        replayed_reports=replayed_reports,
    )
    controls = _negative_controls(manifest, checked_reports)
    ok = bool(
        verification["ok"]
        and len(manifest["stage_manifests"]) == len(EXPECTED_STAGE_ORDER)
        and all(stage["report_ok"] for stage in manifest["stage_manifests"])
        and all(manifest["cross_stage_links"].values())
        and len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
        and sum(1 for control in controls if control["accepted"]) == 0
    )
    if replayed_reports is not None:
        ok = ok and all(report.get("ok") is True for report in replayed_reports.values())
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "authority_boundary": "research-only producer-manifest evidence; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority",
        "manifest": manifest,
        "verification": verification,
        "stage_replay": {
            "enabled": replayed_reports is not None,
            "ok": bool(replayed_reports is not None and all(report.get("ok") is True for report in replayed_reports.values())),
            "stage_count": len(replayed_reports) if replayed_reports is not None else 0,
        },
        "negative_control_count": len(controls),
        "negative_control_accept_count": sum(1 for control in controls if control["accepted"]),
        "negative_controls": controls,
        "hypothesis_card": {
            "hypothesis_id": "H-AB-N7-GENERATED-IMAGE-PRODUCER-20260629",
            "mechanism_change": "Bind the child-frontier generated-image pipeline to an ordered producer manifest with script and output digests.",
            "representation_shift_used": "certificate_boundary",
            "expected_metric_delta": {
                "safety": "+detects stale or reordered producer artifacts",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "+stage replay when enabled",
                "determinism_simplicity": "+single producer manifest over five reports",
            },
            "null_hypothesis": "A producer manifest gives no additional falsifiable boundary beyond the individual stage reports.",
            "falsification_recipe": "Mutate stage order, source seed, script hash, report hash, output digest, corpus root, or authority rail and require rejection.",
            "support_recipe": "Verify all checked reports, replay stages when enabled, confirm cross-stage links, and reject every mutation control.",
            "formal_obligations": "Production use still needs a Lean refinement or a production verifier grammar for this producer relation.",
            "risk_modes": [
                "stale generator script",
                "stale checked report",
                "stage reordering",
                "source seed drift",
                "digest drift",
                "authority leakage",
            ],
            "status": "supported_bounded" if ok else "falsified",
        },
        "non_claims": [
            "This producer manifest is bounded to the committed n=7 zero-min child-frontier corpus.",
            "This producer manifest does not prove Python-to-Lean refinement.",
            "This producer manifest does not prove child-frontier generation in Lean.",
            "This producer manifest does not cover nonzero min_amount_out behavior.",
            "This producer manifest does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.",
        ],
        "replay_command": "python3 tools/check_ab_child_frontier_generated_image_producer_20260629.py",
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    manifest = report["manifest"]
    lines = [
        "# ZenoDEX AB Child-Frontier Generated-Image Producer - 2026-06-29",
        "",
        "## Executive Result",
        "",
        "A bounded producer manifest now binds the n=7 child-frontier generated-image pipeline to ordered stages, script hashes, report hashes, output digests, cross-stage links, deterministic replay hashes, and a no-authority rail.",
        "",
        str(report["authority_boundary"]),
        "",
        "## Producer Manifest",
        "",
        f"- Manifest hash: `{manifest['manifest_hash']}`",
        f"- Source seed: `{manifest['source_seed']}`",
        f"- Stage order: `{', '.join(manifest['producer_stage_order'])}`",
        f"- Stage replay enabled: `{report['stage_replay']['enabled']}`",
        f"- Stage replay ok: `{report['stage_replay']['ok']}`",
        f"- Negative controls: `{report['negative_control_count']}`",
        f"- Negative control accepts: `{report['negative_control_accept_count']}`",
        "",
        "## Stage Outputs",
        "",
        "| stage | script hash | deterministic hash | key outputs |",
        "| --- | --- | --- | --- |",
    ]
    for stage in manifest["stage_manifests"]:
        outputs = ", ".join(f"{key}={value}" for key, value in stage["outputs"].items())
        lines.append(
            f"| `{stage['stage_id']}` | `{stage['script_sha256']}` | `{stage['deterministic_hash']}` | `{outputs}` |"
        )
    lines.extend(["", "## Cross-Stage Links", ""])
    for key, value in manifest["cross_stage_links"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(["", "## Negative Controls", "", "| mutation | accepted | expected reason |", "| --- | ---: | --- |"])
    for control in report["negative_controls"]:
        lines.append(
            f"| `{control['mutation_id']}` | `{control['accepted']}` | `{control['expected_reason']}` |"
        )
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```"])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    report = build_report(replay_stages=True)
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    print(
        json.dumps(
            {
                "ok": bool(report["ok"]),
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "manifest_hash": report["manifest"]["manifest_hash"],
                "negative_control_accept_count": report["negative_control_accept_count"],
                "stage_replay": report["stage_replay"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

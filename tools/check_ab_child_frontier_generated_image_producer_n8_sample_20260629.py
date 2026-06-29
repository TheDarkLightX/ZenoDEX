#!/usr/bin/env python3
"""Check the sampled n=8 AB child-frontier generated-image producer manifest.

This research-only checker binds the sampled n=8 zero-min child-frontier
pipeline to an ordered producer manifest. It verifies script hashes, normalized
report hashes, stage output digests, cross-stage links, deterministic replay
hashes, mutation controls, and the no-authority rail.
"""

from __future__ import annotations

import copy
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.check_ab_reserve_state_child_frontier_bidirectional_transition_n8_sample_20260629 import (  # noqa: E402
    build_report as build_bidirectional_transition_report,
)
from tools.check_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_20260629 import (  # noqa: E402
    build_report as build_canonical_merkle_report,
)
from tools.check_ab_reserve_state_child_frontier_n8_sample_20260629 import (  # noqa: E402
    build_report as build_generation_report,
)
from tools.check_ab_reserve_state_child_frontier_witness_compression_n8_sample_20260629 import (  # noqa: E402
    build_report as build_witness_compression_report,
)
from tools.check_ab_strict_zero_min_emitter_witness import _sha256_json, _strip_timing  # noqa: E402

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_generated_image_producer_n8_sample_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_CHILD_FRONTIER_GENERATED_IMAGE_PRODUCER_N8_SAMPLE_20260629.md"
)

REPORT_SCHEMA = "zenodex.ab_child_frontier_generated_image_producer_n8_sample_report.v1"
MANIFEST_SCHEMA = "zenodex.ab_child_frontier_generated_image_producer_n8_sample_manifest.v1"
SCOPE = "sampled_n8_same_pool_same_direction_exact_in_zero_min_child_frontier_generated_image_producer"
AUTHORITY_BOUNDARY = "research_only_no_settlement_state_root_production_or_governance_authority"
EXPECTED_CASE_COUNT = 3
EXPECTED_SAMPLED_CHILD_MASK_COUNT = 51
EXPECTED_CHILD_STATE_COUNT = 88
EXPECTED_PREDECESSOR_TRANSITION_COUNT = 268
EXPECTED_STAGE_ORDER = (
    "generation",
    "canonical_merkle",
    "witness_compression",
    "bidirectional_transition",
)
EXPECTED_NEGATIVE_CONTROL_COUNT = 11


@dataclass(frozen=True)
class StageSpec:
    stage_id: str
    script_path: Path
    report_path: Path
    schema: str
    build_report: Callable[[], dict[str, Any]]
    expected_script_sha256: str
    expected_normalized_report_sha256: str
    expected_deterministic_hash: str
    expected_outputs: Mapping[str, Any]


STAGE_SPECS = (
    StageSpec(
        stage_id="generation",
        script_path=REPO_ROOT / "tools" / "check_ab_reserve_state_child_frontier_n8_sample_20260629.py",
        report_path=REPO_ROOT
        / "generated"
        / "zenodex_ab_reserve_state_child_frontier_n8_sample_20260629"
        / "report.json",
        schema="zenodex.ab_reserve_state_child_frontier_n8_sample_report.v1",
        build_report=build_generation_report,
        expected_script_sha256="5ab65a27bed2258422b4e2930eefb928b2466da4e2ea814413a3709e2b989a34",
        expected_normalized_report_sha256="9d486b78b9d6121f28728a7124f336f209ea9bb1517c3362897c62db1680021a",
        expected_deterministic_hash="4a601edd060a6cfe8444d7db91f1806bf8bf42b07943642de7dd299e76aa877f",
        expected_outputs={
            "frontier_rows_digest": "37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919",
            "case_count": EXPECTED_CASE_COUNT,
            "valid_case_count": EXPECTED_CASE_COUNT,
            "sampled_child_mask_count": EXPECTED_SAMPLED_CHILD_MASK_COUNT,
            "sampled_child_state_count": EXPECTED_CHILD_STATE_COUNT,
            "generated_state_count": EXPECTED_CHILD_STATE_COUNT,
            "missing_child_state_count": 0,
            "extra_generated_state_count": 0,
            "predecessor_transition_count": EXPECTED_PREDECESSOR_TRANSITION_COUNT,
            "negative_control_count": 7,
            "negative_control_accept_count": 0,
        },
    ),
    StageSpec(
        stage_id="canonical_merkle",
        script_path=REPO_ROOT
        / "tools"
        / "check_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_20260629.py",
        report_path=REPO_ROOT
        / "generated"
        / "zenodex_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_20260629"
        / "report.json",
        schema="zenodex.ab_reserve_state_child_frontier_canonical_merkle_n8_sample_report.v1",
        build_report=build_canonical_merkle_report,
        expected_script_sha256="49f61084552ab1bc74c10a5a257f37984718665e4cd6521949f6e964e62a4e0f",
        expected_normalized_report_sha256="b4318b47670c43b4fce96e3cb5ed0b55cf2ad7a8dd4314ea04db95b7502b1f2a",
        expected_deterministic_hash="31df88fd8d43c07cd20742854e8553e5b3ab5fef4259726f9968c8ff67293f43",
        expected_outputs={
            "frontier_roots_digest": "53872b495fd6af55f5192e5577f6fb75fca8bd54c26110ff88f4b11a17edf6d4",
            "membership_rows_digest": "bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2",
            "case_count": EXPECTED_CASE_COUNT,
            "valid_case_count": EXPECTED_CASE_COUNT,
            "frontier_root_count": EXPECTED_SAMPLED_CHILD_MASK_COUNT,
            "sampled_child_mask_count": EXPECTED_SAMPLED_CHILD_MASK_COUNT,
            "sampled_child_state_count": EXPECTED_CHILD_STATE_COUNT,
            "membership_count": EXPECTED_CHILD_STATE_COUNT,
            "covered_sampled_child_state_count": EXPECTED_CHILD_STATE_COUNT,
            "missing_frontier_row_count": 0,
            "missing_membership_proof_count": 0,
            "invalid_membership_proof_count": 0,
            "root_mismatch_count": 0,
            "negative_control_count": 9,
            "negative_control_accept_count": 0,
        },
    ),
    StageSpec(
        stage_id="witness_compression",
        script_path=REPO_ROOT
        / "tools"
        / "check_ab_reserve_state_child_frontier_witness_compression_n8_sample_20260629.py",
        report_path=REPO_ROOT
        / "generated"
        / "zenodex_ab_reserve_state_child_frontier_witness_compression_n8_sample_20260629"
        / "report.json",
        schema="zenodex.ab_reserve_state_child_frontier_witness_compression_n8_sample_report.v1",
        build_report=build_witness_compression_report,
        expected_script_sha256="13e335e0a99916d01fdc9788f6bc97f30b63c0a80d66f11910985b71204c514e",
        expected_normalized_report_sha256="65895d94ecd7c8c0807264e5db95a30a990ebbc1b9189777fb4192335ca790f6",
        expected_deterministic_hash="f2946c81017d4b9102d20fd417c49fc821471606a4361a6550e4deddb4eb641d",
        expected_outputs={
            "witness_rows_digest": "4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd",
            "case_count": EXPECTED_CASE_COUNT,
            "valid_case_count": EXPECTED_CASE_COUNT,
            "sampled_child_mask_count": EXPECTED_SAMPLED_CHILD_MASK_COUNT,
            "witness_count": EXPECTED_CHILD_STATE_COUNT,
            "covered_sampled_child_state_count": EXPECTED_CHILD_STATE_COUNT,
            "predecessor_transition_count": EXPECTED_PREDECESSOR_TRANSITION_COUNT,
            "witness_transition_checks_saved": 180,
            "witness_compression_ratio": 3.045455,
            "missing_sampled_child_state_witness_count": 0,
            "extra_sampled_child_state_witness_count": 0,
            "invalid_witness_count": 0,
            "duplicate_witness_count": 0,
            "negative_control_count": 9,
            "negative_control_accept_count": 0,
        },
    ),
    StageSpec(
        stage_id="bidirectional_transition",
        script_path=REPO_ROOT
        / "tools"
        / "check_ab_reserve_state_child_frontier_bidirectional_transition_n8_sample_20260629.py",
        report_path=REPO_ROOT
        / "generated"
        / "zenodex_ab_reserve_state_child_frontier_bidirectional_transition_n8_sample_20260629"
        / "report.json",
        schema="zenodex.ab_reserve_state_child_frontier_bidirectional_transition_n8_sample_report.v1",
        build_report=build_bidirectional_transition_report,
        expected_script_sha256="fd4378f8d3697a8b75e68c9f8ee8f1c25c875984472700a7ff30d7495add125d",
        expected_normalized_report_sha256="91ee85516b795e953b36bb77d2b0c0bac216c42f74a4b3e01abd05a8527fd59a",
        expected_deterministic_hash="5757702bcda71094a7b861318efdb7d1ea1e39d119677f3324e7e05ec12d939b",
        expected_outputs={
            "transition_rows_digest": "0ed918d2b332430f57bf3561a5912fa50c0293c23661ff02f582a21e88f3ed09",
            "case_count": EXPECTED_CASE_COUNT,
            "valid_case_count": EXPECTED_CASE_COUNT,
            "sampled_child_mask_count": EXPECTED_SAMPLED_CHILD_MASK_COUNT,
            "transition_row_count": EXPECTED_PREDECESSOR_TRANSITION_COUNT,
            "expected_transition_count": EXPECTED_PREDECESSOR_TRANSITION_COUNT,
            "covered_transition_count": EXPECTED_PREDECESSOR_TRANSITION_COUNT,
            "unique_transition_count": EXPECTED_PREDECESSOR_TRANSITION_COUNT,
            "unique_generated_child_count": EXPECTED_CHILD_STATE_COUNT,
            "linked_child_coverage_witness_count": EXPECTED_CHILD_STATE_COUNT,
            "linked_canonical_membership_count": EXPECTED_CHILD_STATE_COUNT,
            "missing_transition_count": 0,
            "extra_transition_count": 0,
            "invalid_transition_row_count": 0,
            "duplicate_transition_row_count": 0,
            "negative_control_count": 11,
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


def _normalized_report_sha256(report: Mapping[str, Any]) -> str:
    return _sha256_json(_strip_timing(report))


def _stage_outputs(stage_id: str, report: Mapping[str, Any]) -> dict[str, Any]:
    search = _search(report)
    if stage_id == "generation":
        return {
            "frontier_rows_digest": search.get("frontier_rows_digest"),
            "case_count": search.get("case_count"),
            "valid_case_count": search.get("valid_case_count"),
            "sampled_child_mask_count": search.get("sampled_child_mask_count"),
            "sampled_child_state_count": search.get("sampled_child_state_count"),
            "generated_state_count": search.get("generated_state_count"),
            "missing_child_state_count": search.get("missing_child_state_count"),
            "extra_generated_state_count": search.get("extra_generated_state_count"),
            "predecessor_transition_count": search.get("predecessor_transition_count"),
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
        }
    if stage_id == "canonical_merkle":
        return {
            "frontier_roots_digest": search.get("frontier_roots_digest"),
            "membership_rows_digest": search.get("membership_rows_digest"),
            "case_count": search.get("case_count"),
            "valid_case_count": search.get("valid_case_count"),
            "frontier_root_count": search.get("frontier_root_count"),
            "sampled_child_mask_count": search.get("sampled_child_mask_count"),
            "sampled_child_state_count": search.get("sampled_child_state_count"),
            "membership_count": search.get("membership_count"),
            "covered_sampled_child_state_count": search.get("covered_sampled_child_state_count"),
            "missing_frontier_row_count": search.get("missing_frontier_row_count"),
            "missing_membership_proof_count": search.get("missing_membership_proof_count"),
            "invalid_membership_proof_count": search.get("invalid_membership_proof_count"),
            "root_mismatch_count": search.get("root_mismatch_count"),
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
        }
    if stage_id == "witness_compression":
        return {
            "witness_rows_digest": search.get("witness_rows_digest"),
            "case_count": search.get("case_count"),
            "valid_case_count": search.get("valid_case_count"),
            "sampled_child_mask_count": search.get("sampled_child_mask_count"),
            "witness_count": search.get("witness_count"),
            "covered_sampled_child_state_count": search.get("covered_sampled_child_state_count"),
            "predecessor_transition_count": search.get("predecessor_transition_count"),
            "witness_transition_checks_saved": search.get("witness_transition_checks_saved"),
            "witness_compression_ratio": search.get("witness_compression_ratio"),
            "missing_sampled_child_state_witness_count": search.get(
                "missing_sampled_child_state_witness_count"
            ),
            "extra_sampled_child_state_witness_count": search.get(
                "extra_sampled_child_state_witness_count"
            ),
            "invalid_witness_count": search.get("invalid_witness_count"),
            "duplicate_witness_count": search.get("duplicate_witness_count"),
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
        }
    if stage_id == "bidirectional_transition":
        return {
            "transition_rows_digest": search.get("transition_rows_digest"),
            "case_count": search.get("case_count"),
            "valid_case_count": search.get("valid_case_count"),
            "sampled_child_mask_count": search.get("sampled_child_mask_count"),
            "transition_row_count": search.get("transition_row_count"),
            "expected_transition_count": search.get("expected_transition_count"),
            "covered_transition_count": search.get("covered_transition_count"),
            "unique_transition_count": search.get("unique_transition_count"),
            "unique_generated_child_count": search.get("unique_generated_child_count"),
            "linked_child_coverage_witness_count": search.get(
                "linked_child_coverage_witness_count"
            ),
            "linked_canonical_membership_count": search.get(
                "linked_canonical_membership_count"
            ),
            "missing_transition_count": search.get("missing_transition_count"),
            "extra_transition_count": search.get("extra_transition_count"),
            "invalid_transition_row_count": search.get("invalid_transition_row_count"),
            "duplicate_transition_row_count": search.get("duplicate_transition_row_count"),
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
        "normalized_report_sha256": _normalized_report_sha256(report),
        "report_hash_normalization": "strip all elapsed_ms fields",
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
    transition = _search(reports["bidirectional_transition"])
    canonical_frontier = canonical.get("linked_frontier_summary", {})
    witness_frontier = witness.get("linked_frontier_summary", {})
    transition_witness = transition.get("linked_witness_summary", {})
    transition_merkle = transition.get("linked_canonical_merkle_summary", {})
    return {
        "canonical_frontier_digest_matches_generation": (
            isinstance(canonical_frontier, Mapping)
            and canonical_frontier.get("frontier_rows_digest")
            == generation.get("frontier_rows_digest")
        ),
        "witness_frontier_digest_matches_generation": (
            isinstance(witness_frontier, Mapping)
            and witness_frontier.get("frontier_rows_digest")
            == generation.get("frontier_rows_digest")
        ),
        "transition_witness_digest_matches_witness_compression": (
            isinstance(transition_witness, Mapping)
            and transition_witness.get("witness_rows_digest")
            == witness.get("witness_rows_digest")
        ),
        "transition_merkle_digest_matches_canonical": (
            isinstance(transition_merkle, Mapping)
            and transition_merkle.get("membership_rows_digest")
            == canonical.get("membership_rows_digest")
        ),
        "transition_child_count_matches_generation": (
            int(transition.get("unique_generated_child_count", -1))
            == int(generation.get("generated_state_count", -2))
        ),
        "transition_child_coverage_matches_witness": (
            int(transition.get("linked_child_coverage_witness_count", -1))
            == int(witness.get("witness_count", -2))
        ),
        "transition_child_membership_matches_canonical": (
            int(transition.get("linked_canonical_membership_count", -1))
            == int(canonical.get("membership_count", -2))
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
            "bounded sampled n=8 zero-min corpus only",
            "does not prove exhaustive n=8 coverage",
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
    if manifest.get("manifest_hash") != _sha256_json(
        {key: value for key, value in manifest.items() if key != "manifest_hash"}
    ):
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
        if stage.get("normalized_report_sha256") != spec.expected_normalized_report_sha256:
            reasons.append(f"{spec.stage_id}_report_hash_mismatch")
        if _normalized_report_sha256(checked) != spec.expected_normalized_report_sha256:
            reasons.append(f"{spec.stage_id}_checked_report_hash_mismatch")
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


def _negative_controls(
    manifest: Mapping[str, Any],
    checked_reports: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    controls: list[tuple[str, dict[str, Any], str]] = []

    stale_hash = copy.deepcopy(dict(manifest))
    stale_hash["manifest_hash"] = "0" * 64
    controls.append(("manifest_hash_mismatch", stale_hash, "manifest_hash_mismatch"))

    bad_order = copy.deepcopy(dict(manifest))
    bad_order["producer_stage_order"] = list(reversed(EXPECTED_STAGE_ORDER))
    controls.append(
        ("producer_stage_order_mismatch", _with_manifest_hash(bad_order), "producer_stage_order_mismatch")
    )

    missing_stage = copy.deepcopy(dict(manifest))
    missing_stage["stage_manifests"] = list(missing_stage["stage_manifests"][:-1])
    controls.append(("stage_manifest_missing", _with_manifest_hash(missing_stage), "stage_manifest_missing"))

    bad_seed = copy.deepcopy(dict(manifest))
    bad_seed["source_seed"] = "stale-seed"
    controls.append(("source_seed_mismatch", _with_manifest_hash(bad_seed), "generation_source_seed_mismatch"))

    bad_script = copy.deepcopy(dict(manifest))
    bad_script["stage_manifests"][0]["script_sha256"] = "0" * 64
    controls.append(
        ("generation_script_hash_mismatch", _with_manifest_hash(bad_script), "generation_script_hash_mismatch")
    )

    bad_report_hash = copy.deepcopy(dict(manifest))
    bad_report_hash["stage_manifests"][0]["normalized_report_sha256"] = "0" * 64
    controls.append(
        ("generation_report_hash_mismatch", _with_manifest_hash(bad_report_hash), "generation_report_hash_mismatch")
    )

    bad_generation = copy.deepcopy(dict(manifest))
    bad_generation["stage_manifests"][0]["outputs"]["frontier_rows_digest"] = "0" * 64
    controls.append(
        ("generation_output_digest_mismatch", _with_manifest_hash(bad_generation), "generation_output_digest_mismatch")
    )

    bad_canonical = copy.deepcopy(dict(manifest))
    bad_canonical["stage_manifests"][1]["outputs"]["membership_rows_digest"] = "0" * 64
    controls.append(
        (
            "canonical_merkle_output_digest_mismatch",
            _with_manifest_hash(bad_canonical),
            "canonical_merkle_output_digest_mismatch",
        )
    )

    bad_witness = copy.deepcopy(dict(manifest))
    bad_witness["stage_manifests"][2]["outputs"]["witness_rows_digest"] = "0" * 64
    controls.append(
        ("witness_output_digest_mismatch", _with_manifest_hash(bad_witness), "witness_compression_output_digest_mismatch")
    )

    bad_transition = copy.deepcopy(dict(manifest))
    bad_transition["stage_manifests"][3]["outputs"]["transition_rows_digest"] = "0" * 64
    controls.append(
        (
            "bidirectional_transition_output_digest_mismatch",
            _with_manifest_hash(bad_transition),
            "bidirectional_transition_output_digest_mismatch",
        )
    )

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
            "ok": bool(
                replayed_reports is not None
                and all(report.get("ok") is True for report in replayed_reports.values())
            ),
            "stage_count": len(replayed_reports) if replayed_reports is not None else 0,
        },
        "negative_control_count": len(controls),
        "negative_control_accept_count": sum(1 for control in controls if control["accepted"]),
        "negative_controls": controls,
        "hypothesis_card": {
            "hypothesis_id": "H-AB-N8-GENERATED-IMAGE-PRODUCER-20260629",
            "mechanism_change": "Bind the sampled n=8 child-frontier generated-image pipeline to an ordered producer manifest with script and output digests.",
            "representation_shift_used": "certificate_boundary",
            "expected_metric_delta": {
                "safety": "+detects stale, reordered, or cross-stage-inconsistent sampled n8 artifacts",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "+stage replay when enabled",
                "determinism_simplicity": "+single sampled n8 producer manifest over four reports",
            },
            "null_hypothesis": "A sampled n8 producer manifest gives no additional falsifiable boundary beyond individual stage reports.",
            "falsification_recipe": "Mutate stage order, source seed, script hash, report hash, output digest, transition digest, or authority rail and require rejection.",
            "support_recipe": "Verify all checked reports, replay stages when enabled, confirm cross-stage links, and reject every mutation control.",
            "formal_obligations": "Production use still needs exhaustive coverage or a Lean refinement of the child-frontier generation relation.",
            "risk_modes": [
                "stale generator script",
                "stale checked report",
                "stage reordering",
                "source seed drift",
                "digest drift",
                "cross-stage link drift",
                "authority leakage",
            ],
            "status": "supported_bounded" if ok else "falsified",
        },
        "non_claims": [
            "This producer manifest is bounded to the deterministic sampled n=8 zero-min child-frontier corpus.",
            "This producer manifest does not prove exhaustive n=8 coverage.",
            "This producer manifest does not prove Python-to-Lean refinement.",
            "This producer manifest does not prove child-frontier generation in Lean.",
            "This producer manifest does not cover nonzero min_amount_out behavior.",
            "This producer manifest does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.",
        ],
        "replay_command": "python3 tools/check_ab_child_frontier_generated_image_producer_n8_sample_20260629.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    manifest = report["manifest"]
    lines = [
        "# ZenoDEX AB Child-Frontier Generated-Image Producer N8 Sample - 2026-06-29",
        "",
        "## Executive Result",
        "",
        "A bounded producer manifest now binds the sampled n=8 child-frontier generated-image pipeline to ordered stages, script hashes, normalized report hashes, output digests, cross-stage links, deterministic replay hashes, and a no-authority rail.",
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
        "| stage | script hash | normalized report hash | deterministic hash | key outputs |",
        "| --- | --- | --- | --- | --- |",
    ]
    for stage in manifest["stage_manifests"]:
        outputs = ", ".join(f"{key}={value}" for key, value in stage["outputs"].items())
        lines.append(
            f"| `{stage['stage_id']}` | `{stage['script_sha256']}` | `{stage['normalized_report_sha256']}` | `{stage['deterministic_hash']}` | `{outputs}` |"
        )
    lines.extend(["", "## Cross-Stage Links", ""])
    for key, value in manifest["cross_stage_links"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(
        [
            "",
            "## Negative Controls",
            "",
            "| mutation | accepted | expected reason |",
            "| --- | ---: | --- |",
        ]
    )
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

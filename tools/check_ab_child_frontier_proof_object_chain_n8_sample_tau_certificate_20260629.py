#!/usr/bin/env python3
"""Replay the sampled n=8 child-frontier proof-object chain Tau certificate."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

_TAU_RUNNER_SPEC = importlib.util.spec_from_file_location(
    "zenodex_tau_runner_direct", REPO_ROOT / "src" / "integration" / "tau_runner.py"
)
if _TAU_RUNNER_SPEC is None or _TAU_RUNNER_SPEC.loader is None:
    raise RuntimeError("could not load tau_runner.py")
_TAU_RUNNER = importlib.util.module_from_spec(_TAU_RUNNER_SPEC)
sys.modules[_TAU_RUNNER_SPEC.name] = _TAU_RUNNER
_TAU_RUNNER_SPEC.loader.exec_module(_TAU_RUNNER)
find_tau_bin = _TAU_RUNNER.find_tau_bin
run_tau_spec_steps = _TAU_RUNNER.run_tau_spec_steps

SPEC_ID = "ab_child_frontier_proof_object_chain_n8_sample_scope_certificate_v1"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / f"{SPEC_ID}.tau"
OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_CHILD_FRONTIER_PROOF_OBJECT_CHAIN_N8_SAMPLE_TAU_CERTIFICATE_20260629.md"
)

GENERATION_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_generation_n8_sample_tau_certificate_20260629"
    / "report.json"
)
CANONICAL_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_tau_certificate_20260629"
    / "report.json"
)
WITNESS_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_witness_compression_n8_sample_tau_certificate_20260629"
    / "report.json"
)
TRANSITION_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_bidirectional_transition_n8_sample_tau_certificate_20260629"
    / "report.json"
)
PRODUCER_TAU_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_generated_image_producer_n8_sample_tau_certificate_20260629"
    / "report.json"
)
PRODUCER_SOURCE_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_generated_image_producer_n8_sample_20260629"
    / "report.json"
)

EXPECTED_REPORT_HASHES = {
    "generation": "8367a2bbc4f51cb18553102b7c318ba843d88e4e0a1ce9566a99c4707ca42f94",
    "canonical_merkle": "4dde23987a628b6e1c9e20da0eed3e1f615b962cb60a25e5ac8f3e06d8e15b91",
    "witness_compression": "994fd65edc822e648908090e14e312b626e7eb2d9bcd1066afcc054f43f2ae3b",
    "bidirectional_transition": "ca27f7e99c48cd067b8a43bf8e45df4f26cfca80b25953ae4632b404a66c6989",
    "producer": "1953a186822cc19b205a144415c02436fbe38bb9409762b30ae48c58a0ba3a27",
}
EXPECTED_SCHEMAS = {
    "generation": "zenodex.ab_reserve_state_child_frontier_generation_n8_sample_tau_certificate_report.v1",
    "canonical_merkle": "zenodex.ab_reserve_state_child_frontier_canonical_merkle_n8_sample_tau_certificate_report.v1",
    "witness_compression": "zenodex.ab_reserve_state_child_frontier_witness_compression_n8_sample_tau_certificate_report.v1",
    "bidirectional_transition": "zenodex.ab_child_frontier_bidirectional_transition_n8_sample_tau_certificate_report.v1",
    "producer": "zenodex.ab_child_frontier_generated_image_producer_n8_sample_tau_certificate_report.v1",
}
EXPECTED_SPEC_IDS = {
    "generation": "ab_reserve_state_child_frontier_generation_n8_sample_scope_certificate_v1",
    "canonical_merkle": "ab_reserve_state_child_frontier_canonical_merkle_n8_sample_scope_certificate_v1",
    "witness_compression": "ab_reserve_state_child_frontier_witness_compression_n8_sample_scope_certificate_v1",
    "bidirectional_transition": "ab_child_frontier_bidirectional_transition_n8_sample_scope_certificate_v1",
    "producer": "ab_child_frontier_generated_image_producer_n8_sample_scope_certificate_v1",
}
EXPECTED_SOURCE_SEED = "2026062908"
EXPECTED_CASE_COUNT = 3
EXPECTED_SAMPLED_CHILD_MASK_COUNT = 51
EXPECTED_CHILD_STATE_COUNT = 88
EXPECTED_TRANSITION_COUNT = 268
EXPECTED_GENERATION_DIGEST = (
    "37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919"
)
EXPECTED_CANONICAL_ROOTS_DIGEST = (
    "53872b495fd6af55f5192e5577f6fb75fca8bd54c26110ff88f4b11a17edf6d4"
)
EXPECTED_CANONICAL_MEMBERSHIP_DIGEST = (
    "bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2"
)
EXPECTED_WITNESS_DIGEST = (
    "4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd"
)
EXPECTED_TRANSITION_DIGEST = (
    "0ed918d2b332430f57bf3561a5912fa50c0293c23661ff02f582a21e88f3ed09"
)
EXPECTED_MANIFEST_HASH = (
    "db94660eb8c859821de08b629371e3c056b2469d707b94df56854a5f41f17394"
)
EXPECTED_STAGE_ORDER = (
    "generation",
    "canonical_merkle",
    "witness_compression",
    "bidirectional_transition",
)
EXPECTED_CHAIN_INDEX_HASH = (
    "7f6d4c6e21fe5118485de7094b27994a5fee96bc6f2db3c4273374d64ef159bb"
)


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _sha256_json(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _display_path(path: str | Path | None) -> str | None:
    if path is None:
        return None
    resolved = Path(path).resolve()
    try:
        return str(resolved.relative_to(REPO_ROOT))
    except ValueError:
        return str(resolved)


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _contains_all(text: str, needles: tuple[str, ...]) -> bool:
    lowered = text.lower()
    return all(needle.lower() in lowered for needle in needles)


def _stage_paths() -> dict[str, Path]:
    return {
        "generation": GENERATION_REPORT,
        "canonical_merkle": CANONICAL_REPORT,
        "witness_compression": WITNESS_REPORT,
        "bidirectional_transition": TRANSITION_REPORT,
        "producer": PRODUCER_TAU_REPORT,
    }


def _load_stage_reports() -> dict[str, dict[str, Any]]:
    return {stage: _read_json(path) for stage, path in _stage_paths().items()}


def _tau_report_ok(stage: str, report: Mapping[str, Any]) -> bool:
    tau = report.get("tau")
    facts = report.get("facts")
    return (
        report.get("schema") == EXPECTED_SCHEMAS[stage]
        and report.get("spec", {}).get("id") == EXPECTED_SPEC_IDS[stage]
        and isinstance(tau, Mapping)
        and tau.get("ok") is True
        and int(tau.get("invalid_accepts", -1)) == 0
        and isinstance(facts, Mapping)
        and bool(facts)
        and all(int(value) == 1 for value in facts.values())
        and int(report.get("breakthrough", {}).get("invalid_accepts", -1)) == 0
    )


def _all_negative_cases_clean(reports: Mapping[str, Mapping[str, Any]]) -> bool:
    for report in reports.values():
        if int(report.get("tau", {}).get("invalid_accepts", -1)) != 0:
            return False
        cases = report.get("tau", {}).get("case_results")
        if not isinstance(cases, list):
            return False
        negative_count = 0
        for case in cases:
            if not isinstance(case, Mapping):
                return False
            if case.get("ok") is not True:
                return False
            case_id = str(case.get("case_id", ""))
            if case_id.endswith("_pass"):
                continue
            if case_id == "inactive_safe":
                continue
            negative_count += 1
        if negative_count == 0:
            return False
    return True


def _authority_boundary_ok(reports: Mapping[str, Mapping[str, Any]]) -> bool:
    for report in reports.values():
        text = " ".join(
            [
                str(report.get("authority_boundary", "")),
                " ".join(str(item) for item in report.get("non_claims", [])),
            ]
        ).lower()
        if not _contains_all(
            text,
            (
                "no settlement",
                "state-root",
                "production",
                "routing",
                "matching",
                "governance",
            ),
        ):
            return False
        if "pool mutation" not in text and "pool-mutation" not in text:
            return False
    return True


def _shared_scope_ok(reports: Mapping[str, Mapping[str, Any]]) -> bool:
    for report in reports.values():
        text = " ".join(str(item) for item in report.get("non_claims", [])).lower()
        if not _contains_all(
            text,
            (
                "sampled n=8",
                "zero-min",
                "does not prove exhaustive n=8 coverage",
                "does not prove python-to-lean refinement",
                "does not cover nonzero min_amount_out",
            ),
        ):
            return False
    producer = reports["producer"].get("producer_manifest", {})
    return str(producer.get("source_seed")) == EXPECTED_SOURCE_SEED


def _producer_source_manifest() -> Mapping[str, Any]:
    source = _read_json(PRODUCER_SOURCE_REPORT)
    manifest = source.get("manifest")
    if not isinstance(manifest, Mapping):
        return {}
    return manifest


def _producer_stage_outputs(manifest: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    stages = manifest.get("stage_manifests")
    if not isinstance(stages, list):
        return {}
    out: dict[str, Mapping[str, Any]] = {}
    for stage in stages:
        if isinstance(stage, Mapping) and isinstance(stage.get("stage_id"), str):
            outputs = stage.get("outputs")
            out[str(stage["stage_id"])] = outputs if isinstance(outputs, Mapping) else {}
    return out


def _stage_counts_ok(reports: Mapping[str, Mapping[str, Any]], manifest: Mapping[str, Any]) -> bool:
    generation = reports["generation"].get("generation_corpus", {})
    canonical = reports["canonical_merkle"].get("canonical_merkle_corpus", {})
    witness = reports["witness_compression"].get("witness_corpus", {})
    transition = reports["bidirectional_transition"].get("transition_corpus", {})
    producer_outputs = _producer_stage_outputs(manifest)
    return (
        int(generation.get("case_count", -1)) == EXPECTED_CASE_COUNT
        and int(canonical.get("case_count", -1)) == EXPECTED_CASE_COUNT
        and int(witness.get("case_count", -1)) == EXPECTED_CASE_COUNT
        and int(transition.get("case_count", -1)) == EXPECTED_CASE_COUNT
        and int(generation.get("sampled_child_mask_count", -1))
        == EXPECTED_SAMPLED_CHILD_MASK_COUNT
        and int(canonical.get("sampled_child_mask_count", -1))
        == EXPECTED_SAMPLED_CHILD_MASK_COUNT
        and int(witness.get("sampled_child_mask_count", -1))
        == EXPECTED_SAMPLED_CHILD_MASK_COUNT
        and int(transition.get("sampled_child_mask_count", -1))
        == EXPECTED_SAMPLED_CHILD_MASK_COUNT
        and int(generation.get("sampled_child_state_count", -1))
        == EXPECTED_CHILD_STATE_COUNT
        and int(generation.get("generated_state_count", -1)) == EXPECTED_CHILD_STATE_COUNT
        and int(canonical.get("membership_count", -1)) == EXPECTED_CHILD_STATE_COUNT
        and int(witness.get("witness_count", -1)) == EXPECTED_CHILD_STATE_COUNT
        and int(transition.get("unique_generated_child_count", -1))
        == EXPECTED_CHILD_STATE_COUNT
        and int(generation.get("predecessor_transition_count", -1))
        == EXPECTED_TRANSITION_COUNT
        and int(witness.get("predecessor_transition_count", -1))
        == EXPECTED_TRANSITION_COUNT
        and int(transition.get("transition_row_count", -1)) == EXPECTED_TRANSITION_COUNT
        and int(transition.get("covered_transition_count", -1)) == EXPECTED_TRANSITION_COUNT
        and all(
            int(producer_outputs.get(stage, {}).get("case_count", -1)) == EXPECTED_CASE_COUNT
            for stage in EXPECTED_STAGE_ORDER
        )
    )


def _cross_stage_digests_ok(
    reports: Mapping[str, Mapping[str, Any]],
    manifest: Mapping[str, Any],
) -> bool:
    generation = reports["generation"].get("generation_corpus", {})
    canonical = reports["canonical_merkle"].get("canonical_merkle_corpus", {})
    canonical_link = reports["canonical_merkle"].get("linked_frontier", {})
    witness = reports["witness_compression"].get("witness_corpus", {})
    transition = reports["bidirectional_transition"].get("transition_corpus", {})
    producer_outputs = _producer_stage_outputs(manifest)
    return (
        generation.get("frontier_rows_digest") == EXPECTED_GENERATION_DIGEST
        and canonical_link.get("frontier_rows_digest") == EXPECTED_GENERATION_DIGEST
        and witness.get("linked_frontier_rows_digest") == EXPECTED_GENERATION_DIGEST
        and producer_outputs.get("generation", {}).get("frontier_rows_digest")
        == EXPECTED_GENERATION_DIGEST
        and canonical.get("frontier_roots_digest") == EXPECTED_CANONICAL_ROOTS_DIGEST
        and canonical.get("membership_rows_digest") == EXPECTED_CANONICAL_MEMBERSHIP_DIGEST
        and transition.get("linked_merkle_membership_rows_digest")
        == EXPECTED_CANONICAL_MEMBERSHIP_DIGEST
        and producer_outputs.get("canonical_merkle", {}).get("membership_rows_digest")
        == EXPECTED_CANONICAL_MEMBERSHIP_DIGEST
        and witness.get("witness_rows_digest") == EXPECTED_WITNESS_DIGEST
        and transition.get("linked_witness_rows_digest") == EXPECTED_WITNESS_DIGEST
        and producer_outputs.get("witness_compression", {}).get("witness_rows_digest")
        == EXPECTED_WITNESS_DIGEST
        and transition.get("transition_rows_digest") == EXPECTED_TRANSITION_DIGEST
        and producer_outputs.get("bidirectional_transition", {}).get(
            "transition_rows_digest"
        )
        == EXPECTED_TRANSITION_DIGEST
    )


def _producer_manifest_links_ok(
    reports: Mapping[str, Mapping[str, Any]],
    manifest: Mapping[str, Any],
) -> bool:
    producer = reports["producer"].get("producer_manifest", {})
    links = producer.get("cross_stage_links")
    source_links = manifest.get("cross_stage_links")
    return (
        producer.get("manifest_hash") == EXPECTED_MANIFEST_HASH
        and manifest.get("manifest_hash") == EXPECTED_MANIFEST_HASH
        and tuple(producer.get("producer_stage_order", ())) == EXPECTED_STAGE_ORDER
        and tuple(manifest.get("producer_stage_order", ())) == EXPECTED_STAGE_ORDER
        and isinstance(links, Mapping)
        and isinstance(source_links, Mapping)
        and bool(links)
        and links == source_links
        and all(value is True for value in links.values())
        and producer.get("stage_replay", {}).get("ok") is True
    )


def _deterministic_replay_pinned(reports: Mapping[str, Mapping[str, Any]]) -> bool:
    return (
        reports["generation"].get("generation_corpus", {}).get("deterministic_replay_hash")
        == "4a601edd060a6cfe8444d7db91f1806bf8bf42b07943642de7dd299e76aa877f"
        and reports["canonical_merkle"].get("canonical_merkle_corpus", {}).get(
            "deterministic_replay_hash"
        )
        == "31df88fd8d43c07cd20742854e8553e5b3ab5fef4259726f9968c8ff67293f43"
        and reports["witness_compression"].get("witness_corpus", {}).get(
            "deterministic_replay_hash"
        )
        == "f2946c81017d4b9102d20fd417c49fc821471606a4361a6550e4deddb4eb641d"
        and reports["bidirectional_transition"].get("transition_corpus", {}).get(
            "deterministic_replay_hash"
        )
        == "5757702bcda71094a7b861318efdb7d1ea1e39d119677f3324e7e05ec12d939b"
        and reports["producer"].get("producer_manifest", {}).get("stage_replay", {}).get(
            "ok"
        )
        is True
    )


def _stage_report_hashes_pinned() -> bool:
    return all(
        _sha256(path) == EXPECTED_REPORT_HASHES[stage]
        for stage, path in _stage_paths().items()
    )


def _chain_index(reports: Mapping[str, Mapping[str, Any]], manifest: Mapping[str, Any]) -> dict[str, Any]:
    generation = reports["generation"].get("generation_corpus", {})
    canonical = reports["canonical_merkle"].get("canonical_merkle_corpus", {})
    witness = reports["witness_compression"].get("witness_corpus", {})
    transition = reports["bidirectional_transition"].get("transition_corpus", {})
    return {
        "schema": "zenodex.ab_child_frontier_proof_object_chain_n8_sample_index.v1",
        "scope": "sampled_n8_zero_min_child_frontier_proof_object_chain",
        "source_seed": EXPECTED_SOURCE_SEED,
        "stage_order": list(EXPECTED_STAGE_ORDER) + ["producer"],
        "stage_reports": {
            stage: {
                "path": str(path.relative_to(REPO_ROOT)),
                "report_sha256": _sha256(path),
                "spec_id": reports[stage].get("spec", {}).get("id"),
                "spec_sha256": reports[stage].get("spec", {}).get("sha256"),
                "tau_cases": len(reports[stage].get("tau", {}).get("case_results", [])),
                "invalid_accepts": reports[stage].get("tau", {}).get("invalid_accepts"),
            }
            for stage, path in _stage_paths().items()
        },
        "counts": {
            "case_count": EXPECTED_CASE_COUNT,
            "sampled_child_mask_count": EXPECTED_SAMPLED_CHILD_MASK_COUNT,
            "sampled_child_state_count": EXPECTED_CHILD_STATE_COUNT,
            "predecessor_transition_count": EXPECTED_TRANSITION_COUNT,
            "generation_frontier_equal_count": generation.get("frontier_equal_count"),
            "canonical_membership_count": canonical.get("membership_count"),
            "witness_count": witness.get("witness_count"),
            "transition_row_count": transition.get("transition_row_count"),
        },
        "digests": {
            "generation_frontier_rows_digest": EXPECTED_GENERATION_DIGEST,
            "canonical_frontier_roots_digest": EXPECTED_CANONICAL_ROOTS_DIGEST,
            "canonical_membership_rows_digest": EXPECTED_CANONICAL_MEMBERSHIP_DIGEST,
            "witness_rows_digest": EXPECTED_WITNESS_DIGEST,
            "transition_rows_digest": EXPECTED_TRANSITION_DIGEST,
            "producer_manifest_hash": EXPECTED_MANIFEST_HASH,
        },
        "producer_links": manifest.get("cross_stage_links"),
        "authority_boundary": "research-only; no settlement/state-root/production/routing/matching/pool-mutation/governance authority",
    }


def _fact_bundle(
    reports: Mapping[str, Mapping[str, Any]], manifest: Mapping[str, Any]
) -> tuple[dict[str, int], dict[str, Any], str]:
    chain_index = _chain_index(reports, manifest)
    chain_index_hash = _sha256_json(chain_index)
    facts = {
        "generation_tau_ok": int(_tau_report_ok("generation", reports["generation"])),
        "canonical_merkle_tau_ok": int(
            _tau_report_ok("canonical_merkle", reports["canonical_merkle"])
        ),
        "witness_compression_tau_ok": int(
            _tau_report_ok("witness_compression", reports["witness_compression"])
        ),
        "bidirectional_transition_tau_ok": int(
            _tau_report_ok("bidirectional_transition", reports["bidirectional_transition"])
        ),
        "producer_tau_ok": int(_tau_report_ok("producer", reports["producer"])),
        "shared_scope_ok": int(_shared_scope_ok(reports)),
        "stage_counts_ok": int(_stage_counts_ok(reports, manifest)),
        "cross_stage_digests_ok": int(_cross_stage_digests_ok(reports, manifest)),
        "producer_manifest_links_ok": int(_producer_manifest_links_ok(reports, manifest)),
        "negative_cases_clean": int(_all_negative_cases_clean(reports)),
        "deterministic_replay_pinned": int(_deterministic_replay_pinned(reports)),
        "stage_report_hashes_pinned": int(_stage_report_hashes_pinned()),
        "chain_index_hash_pinned": int(chain_index_hash == EXPECTED_CHAIN_INDEX_HASH),
        "authority_boundary_ok": int(_authority_boundary_ok(reports)),
        "no_authority_effect": 1,
        "corpus_nonvacuous": int(
            EXPECTED_CASE_COUNT > 0
            and EXPECTED_SAMPLED_CHILD_MASK_COUNT > 0
            and EXPECTED_CHILD_STATE_COUNT > 0
            and EXPECTED_TRANSITION_COUNT > 0
        ),
    }
    return facts, chain_index, chain_index_hash


FACT_TO_INPUT = {
    "generation_tau_ok": "i2",
    "canonical_merkle_tau_ok": "i3",
    "witness_compression_tau_ok": "i4",
    "bidirectional_transition_tau_ok": "i5",
    "producer_tau_ok": "i6",
    "shared_scope_ok": "i7",
    "stage_counts_ok": "i8",
    "cross_stage_digests_ok": "i9",
    "producer_manifest_links_ok": "i10",
    "negative_cases_clean": "i11",
    "deterministic_replay_pinned": "i12",
    "stage_report_hashes_pinned": "i13",
    "chain_index_hash_pinned": "i14",
    "authority_boundary_ok": "i15",
    "no_authority_effect": "i16",
    "corpus_nonvacuous": "i17",
}

NEGATIVE_CASES = (
    ("generation_tau_reject", "generation_tau_ok", {"o1": 0, "o7": 0}),
    ("canonical_merkle_tau_reject", "canonical_merkle_tau_ok", {"o1": 0, "o7": 0}),
    ("witness_compression_tau_reject", "witness_compression_tau_ok", {"o1": 0, "o7": 0}),
    ("bidirectional_transition_tau_reject", "bidirectional_transition_tau_ok", {"o1": 0, "o7": 0}),
    ("producer_tau_reject", "producer_tau_ok", {"o1": 0, "o7": 0}),
    ("shared_scope_reject", "shared_scope_ok", {"o2": 0, "o7": 0}),
    ("stage_counts_reject", "stage_counts_ok", {"o2": 0, "o7": 0}),
    ("cross_stage_digest_reject", "cross_stage_digests_ok", {"o3": 0, "o7": 0}),
    ("producer_links_reject", "producer_manifest_links_ok", {"o3": 0, "o7": 0}),
    ("negative_cases_reject", "negative_cases_clean", {"o4": 0, "o7": 0}),
    ("deterministic_replay_reject", "deterministic_replay_pinned", {"o4": 0, "o7": 0}),
    ("stage_report_hash_reject", "stage_report_hashes_pinned", {"o4": 0, "o7": 0}),
    ("chain_index_hash_reject", "chain_index_hash_pinned", {"o6": 0, "o7": 0}),
    ("authority_boundary_reject", "authority_boundary_ok", {"o5": 0, "o7": 0}),
    ("authority_effect_reject", "no_authority_effect", {"o5": 0, "o7": 0}),
    ("empty_corpus_reject", "corpus_nonvacuous", {"o2": 0, "o7": 0}),
)


def _pass_step(facts: Mapping[str, int]) -> dict[str, int]:
    step = {"i1": 1}
    for fact, input_name in FACT_TO_INPUT.items():
        step[input_name] = int(facts[fact])
    return step


def _tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    pass_step = _pass_step(facts)
    inactive = dict(pass_step)
    inactive["i1"] = 0
    cases = [
        TauCase(
            "proof_object_chain_n8_sample_certificate_pass",
            pass_step,
            {
                "o1": 1,
                "o2": 1,
                "o3": 1,
                "o4": 1,
                "o5": 1,
                "o6": 1,
                "o7": 1,
                "o8": 0,
            },
            "All scoped stage Tau reports and chain links admit the sampled n=8 proof-object chain certificate.",
        )
    ]
    for case_id, fact, expected in NEGATIVE_CASES:
        cases.append(
            TauCase(
                case_id,
                {**pass_step, FACT_TO_INPUT[fact]: 0},
                expected,
                f"The `{fact}` host fact is required for chain certificate admission.",
            )
        )
    cases.append(
        TauCase(
            "inactive_safe",
            inactive,
            {"o7": 0, "o8": 1},
            "Inactive certificates do not admit while the no-authority rail remains true.",
        )
    )
    return tuple(cases)


def _run_tau(facts: Mapping[str, int]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    cases = _tau_cases(facts)
    if not tau_bin:
        return {
            "ok": False,
            "skipped": True,
            "error": "latest Tau binary not found",
            "case_results": [],
            "invalid_accepts": 0,
            "tau_bin": None,
            "tau_version": None,
        }
    proc = subprocess.run(
        [tau_bin, "--version"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[case.step for case in cases],
        timeout_s=20.0,
    )
    invalid_accepts = 0
    case_results = []
    ok = True
    for index, case in enumerate(cases):
        got = {str(key): int(value) for key, value in outputs.get(index, {}).items()}
        mismatches = {
            key: {"expected": int(value), "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != int(value)
        }
        if case.expected.get("o7") == 0 and got.get("o7") == 1:
            invalid_accepts += 1
        if mismatches:
            ok = False
        case_results.append(
            {
                "case_id": case.case_id,
                "ok": not mismatches,
                "expected": case.expected,
                "got": got,
                "mismatches": mismatches,
                "rationale": case.rationale,
            }
        )
    return {
        "ok": ok and invalid_accepts == 0,
        "skipped": False,
        "case_results": case_results,
        "invalid_accepts": invalid_accepts,
        "tau_bin": _display_path(tau_bin),
        "tau_version": (proc.stdout + proc.stderr).strip(),
    }


def build_report() -> dict[str, Any]:
    reports = _load_stage_reports()
    manifest = _producer_source_manifest()
    facts, chain_index, chain_index_hash = _fact_bundle(reports, manifest)
    tau = _run_tau(facts)
    stage_summary = {
        stage: {
            "report_path": str(path.relative_to(REPO_ROOT)),
            "report_sha256": _sha256(path),
            "expected_report_sha256": EXPECTED_REPORT_HASHES[stage],
            "spec_id": reports[stage].get("spec", {}).get("id"),
            "spec_sha256": reports[stage].get("spec", {}).get("sha256"),
            "tau_ok": reports[stage].get("tau", {}).get("ok"),
            "tau_cases": len(reports[stage].get("tau", {}).get("case_results", [])),
            "invalid_accepts": reports[stage].get("tau", {}).get("invalid_accepts"),
        }
        for stage, path in _stage_paths().items()
    }
    return {
        "schema": "zenodex.ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_report.v1",
        "date": "2026-06-29",
        "authority_boundary": "research evidence only; no settlement, state-root, production, governance, routing, matching, or pool-mutation authority",
        "spec": {
            "id": SPEC_ID,
            "path": str(TAU_SPEC.relative_to(REPO_ROOT)),
            "sha256": _sha256(TAU_SPEC),
        },
        "stage_summary": stage_summary,
        "chain_index": chain_index,
        "chain_index_sha256": chain_index_hash,
        "expected_chain_index_sha256": EXPECTED_CHAIN_INDEX_HASH,
        "chain_counts": {
            "stage_tau_report_count": len(stage_summary),
            "case_count": EXPECTED_CASE_COUNT,
            "sampled_child_mask_count": EXPECTED_SAMPLED_CHILD_MASK_COUNT,
            "sampled_child_state_count": EXPECTED_CHILD_STATE_COUNT,
            "predecessor_transition_count": EXPECTED_TRANSITION_COUNT,
        },
        "chain_digests": {
            "generation_frontier_rows_digest": EXPECTED_GENERATION_DIGEST,
            "canonical_frontier_roots_digest": EXPECTED_CANONICAL_ROOTS_DIGEST,
            "canonical_membership_rows_digest": EXPECTED_CANONICAL_MEMBERSHIP_DIGEST,
            "witness_rows_digest": EXPECTED_WITNESS_DIGEST,
            "transition_rows_digest": EXPECTED_TRANSITION_DIGEST,
            "producer_manifest_hash": EXPECTED_MANIFEST_HASH,
        },
        "facts": facts,
        "tau": tau,
        "breakthrough": {
            "name": "AB child-frontier proof-object chain n8 sample Tau certificate",
            "spec_id": SPEC_ID,
            "tau_cases": len(tau["case_results"]),
            "invalid_accepts": tau["invalid_accepts"],
            "scoped_claims": [
                "five sampled n=8 stage Tau reports are present and hash-pinned",
                "all stage Tau reports pass with zero invalid accepts",
                "shared sampled n=8 zero-min counts and digests match across generation, canonical Merkle, witness compression, bidirectional transition, and producer manifest reports",
                "the deterministic chain index is hash-pinned",
                "16 missing-fact Tau cases reject with zero invalid accepts",
                "the chain envelope carries no settlement or state authority",
            ],
        },
        "non_claims": [
            "This certificate is bounded to the deterministic sampled n=8 zero-min proof-object chain reports.",
            "This certificate composes existing stage Tau reports and producer manifest evidence; it does not replace those host checkers.",
            "This certificate does not prove exhaustive n=8 coverage.",
            "This certificate does not prove Python-to-Lean refinement.",
            "This certificate does not prove child-frontier generation in Lean.",
            "This certificate does not cover nonzero min_amount_out behavior.",
            "This certificate does not define canonical tie order or preserve order-id history.",
            "This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.",
        ],
        "hypothesis_card": {
            "hypothesis_id": "H-AB-N8-PROOF-OBJECT-CHAIN-TAU-20260629",
            "status": "supported_bounded",
            "mechanism_change": "Add a versioned Tau scope certificate over the complete sampled n=8 proof-object chain.",
            "representation_shift_used": "certificate_boundary",
            "null_hypothesis": "A chain-level Tau envelope gives no additional falsifiable boundary beyond separate stage Tau certificates.",
            "support_recipe": "Host checks all stage Tau reports, stage report hashes, shared counts, cross-stage digests, producer manifest links, deterministic replay pins, negative cases, chain-index hash, and no-authority rail; Tau rejects every missing-fact negative case.",
            "falsification_recipe": "Clear each required fact bit, mutate any stage report hash, break any digest equality, remove a producer link, remove a stage Tau report pass flag, or remove the no-authority rail and require Tau rejection.",
            "formal_obligations": "Production use still needs exhaustive coverage or a deeper Lean refinement of child-frontier generation and chain construction.",
        },
        "replay_command": (
            "python3 tools/check_ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_20260629.py"
        ),
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX AB Child-Frontier Proof-Object Chain N8 Sample Tau Certificate - 2026-06-29",
        "",
        "## Executive Result",
        "",
        "`ab_child_frontier_proof_object_chain_n8_sample_scope_certificate_v1` admits the sampled n=8 proof-object chain only when the generation, canonical-Merkle, witness-compression, bidirectional-transition, and producer Tau reports all pass; shared counts and cross-stage digests agree; the producer manifest links are intact; the deterministic chain index is hash-pinned; and the no-authority rail is present.",
        "",
        "Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.",
        "",
        "## Facts",
        "",
    ]
    for key, value in report["facts"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(
        [
            "",
            "## Chain Summary",
            "",
            f"- Stage Tau reports: `{report['chain_counts']['stage_tau_report_count']}`",
            f"- Sampled child masks: `{report['chain_counts']['sampled_child_mask_count']}`",
            f"- Sampled child states: `{report['chain_counts']['sampled_child_state_count']}`",
            f"- Predecessor transitions: `{report['chain_counts']['predecessor_transition_count']}`",
            f"- Chain index hash: `{report['chain_index_sha256']}`",
            f"- Expected chain index hash: `{report['expected_chain_index_sha256']}`",
            f"- Tau cases: `{report['breakthrough']['tau_cases']}`",
            f"- Invalid accepts: `{report['breakthrough']['invalid_accepts']}`",
            "",
            "## Stage Reports",
            "",
            "| stage | tau ok | tau cases | invalid accepts | report sha256 |",
            "| --- | ---: | ---: | ---: | --- |",
        ]
    )
    for stage, summary in report["stage_summary"].items():
        lines.append(
            f"| `{stage}` | `{summary['tau_ok']}` | `{summary['tau_cases']}` | "
            f"`{summary['invalid_accepts']}` | `{summary['report_sha256']}` |"
        )
    lines.extend(
        [
            "",
            "## Chain Digests",
            "",
        ]
    )
    for key, value in report["chain_digests"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(
        [
            "",
            "## Tau Cases",
            "",
            "| case | ok | o7 | rationale |",
            "| --- | ---: | ---: | --- |",
        ]
    )
    for case in report["tau"]["case_results"]:
        got = case.get("got", {})
        lines.append(
            f"| `{case['case_id']}` | `{case['ok']}` | `{got.get('o7')}` | {case['rationale']} |"
        )
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    ok = (
        bool(report["tau"]["ok"])
        and int(report["tau"]["invalid_accepts"]) == 0
        and all(value == 1 for value in report["facts"].values())
    )
    print(
        json.dumps(
            {
                "ok": ok,
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "spec": str(TAU_SPEC.relative_to(REPO_ROOT)),
                "chain_index_sha256": report["chain_index_sha256"],
                "expected_chain_index_sha256": report["expected_chain_index_sha256"],
                "tau_cases": len(report["tau"]["case_results"]),
                "invalid_accepts": report["tau"]["invalid_accepts"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return int(not ok)


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Replay the sampled n=8 AB child-frontier producer-manifest Tau certificate."""

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

SPEC_ID = "ab_child_frontier_generated_image_producer_n8_sample_scope_certificate_v1"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / f"{SPEC_ID}.tau"
SOURCE_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_generated_image_producer_n8_sample_20260629"
    / "report.json"
)
OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_generated_image_producer_n8_sample_tau_certificate_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_CHILD_FRONTIER_GENERATED_IMAGE_PRODUCER_N8_SAMPLE_TAU_CERTIFICATE_20260629.md"
)

EXPECTED_SCHEMA = "zenodex.ab_child_frontier_generated_image_producer_n8_sample_report.v1"
EXPECTED_MANIFEST_SCHEMA = (
    "zenodex.ab_child_frontier_generated_image_producer_n8_sample_manifest.v1"
)
EXPECTED_SOURCE_REPORT_HASH = (
    "1989c0862510d5c93177c58999368bafb49542f23bd4c3c9e73cfac95b2cf73e"
)
EXPECTED_MANIFEST_HASH = (
    "db94660eb8c859821de08b629371e3c056b2469d707b94df56854a5f41f17394"
)
EXPECTED_SOURCE_SEED = "2026062908"
EXPECTED_STAGE_ORDER = (
    "generation",
    "canonical_merkle",
    "witness_compression",
    "bidirectional_transition",
)
EXPECTED_STAGE_HASHES = {
    "generation": {
        "script_sha256": "5ab65a27bed2258422b4e2930eefb928b2466da4e2ea814413a3709e2b989a34",
        "normalized_report_sha256": "9d486b78b9d6121f28728a7124f336f209ea9bb1517c3362897c62db1680021a",
        "deterministic_hash": "4a601edd060a6cfe8444d7db91f1806bf8bf42b07943642de7dd299e76aa877f",
    },
    "canonical_merkle": {
        "script_sha256": "49f61084552ab1bc74c10a5a257f37984718665e4cd6521949f6e964e62a4e0f",
        "normalized_report_sha256": "b4318b47670c43b4fce96e3cb5ed0b55cf2ad7a8dd4314ea04db95b7502b1f2a",
        "deterministic_hash": "31df88fd8d43c07cd20742854e8553e5b3ab5fef4259726f9968c8ff67293f43",
    },
    "witness_compression": {
        "script_sha256": "13e335e0a99916d01fdc9788f6bc97f30b63c0a80d66f11910985b71204c514e",
        "normalized_report_sha256": "65895d94ecd7c8c0807264e5db95a30a990ebbc1b9189777fb4192335ca790f6",
        "deterministic_hash": "f2946c81017d4b9102d20fd417c49fc821471606a4361a6550e4deddb4eb641d",
    },
    "bidirectional_transition": {
        "script_sha256": "fd4378f8d3697a8b75e68c9f8ee8f1c25c875984472700a7ff30d7495add125d",
        "normalized_report_sha256": "91ee85516b795e953b36bb77d2b0c0bac216c42f74a4b3e01abd05a8527fd59a",
        "deterministic_hash": "5757702bcda71094a7b861318efdb7d1ea1e39d119677f3324e7e05ec12d939b",
    },
}
EXPECTED_CASE_COUNT = 3
EXPECTED_SAMPLED_CHILD_MASK_COUNT = 51
EXPECTED_GENERATED_CHILD_COUNT = 88
EXPECTED_TRANSITION_ROW_COUNT = 268
EXPECTED_NEGATIVE_CONTROL_COUNT = 11
EXPECTED_GENERATION_DIGEST = (
    "37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919"
)
EXPECTED_CANONICAL_DIGEST = (
    "bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2"
)
EXPECTED_WITNESS_DIGEST = (
    "4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd"
)
EXPECTED_TRANSITION_DIGEST = (
    "0ed918d2b332430f57bf3561a5912fa50c0293c23661ff02f582a21e88f3ed09"
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


def _manifest(report: Mapping[str, Any]) -> Mapping[str, Any]:
    manifest = report.get("manifest")
    if not isinstance(manifest, Mapping):
        return {}
    return manifest


def _stage_map(manifest: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    stages = manifest.get("stage_manifests")
    if not isinstance(stages, list):
        return {}
    out: dict[str, Mapping[str, Any]] = {}
    for stage in stages:
        if isinstance(stage, Mapping) and isinstance(stage.get("stage_id"), str):
            out[str(stage["stage_id"])] = stage
    return out


def _contains_all(text: str, needles: tuple[str, ...]) -> bool:
    lowered = text.lower()
    return all(needle.lower() in lowered for needle in needles)


def _authority_boundary_ok(report: Mapping[str, Any]) -> bool:
    text = " ".join(
        [
            str(report.get("authority_boundary", "")),
            " ".join(str(item) for item in report.get("non_claims", [])),
        ]
    ).lower()
    return (
        "research-only" in text
        and "no settlement" in text
        and "state-root" in text
        and "production" in text
        and "routing" in text
        and "matching" in text
        and "pool mutation" in text
        and "governance" in text
    )


def _manifest_hash_ok(manifest: Mapping[str, Any]) -> bool:
    return (
        manifest.get("manifest_hash") == EXPECTED_MANIFEST_HASH
        and manifest.get("manifest_hash")
        == _sha256_json({key: value for key, value in manifest.items() if key != "manifest_hash"})
    )


def _producer_stage_order_ok(manifest: Mapping[str, Any], stages: Mapping[str, Any]) -> bool:
    return (
        tuple(manifest.get("producer_stage_order", ())) == EXPECTED_STAGE_ORDER
        and tuple(stages) == EXPECTED_STAGE_ORDER
        and len(stages) == len(EXPECTED_STAGE_ORDER)
        and manifest.get("producer_stage_order_bound") is True
    )


def _stage_hashes_pinned(stages: Mapping[str, Mapping[str, Any]]) -> bool:
    for stage_id, expected in EXPECTED_STAGE_HASHES.items():
        stage = stages.get(stage_id)
        if not isinstance(stage, Mapping):
            return False
        for key, value in expected.items():
            if stage.get(key) != value:
                return False
        if stage.get("report_ok") is not True:
            return False
    return True


def _stage_outputs_pinned(stages: Mapping[str, Mapping[str, Any]]) -> bool:
    generation = stages.get("generation", {}).get("outputs", {})
    canonical = stages.get("canonical_merkle", {}).get("outputs", {})
    witness = stages.get("witness_compression", {}).get("outputs", {})
    transition = stages.get("bidirectional_transition", {}).get("outputs", {})
    if not all(isinstance(outputs, Mapping) for outputs in (generation, canonical, witness, transition)):
        return False
    return (
        generation.get("case_count") == EXPECTED_CASE_COUNT
        and generation.get("sampled_child_mask_count") == EXPECTED_SAMPLED_CHILD_MASK_COUNT
        and generation.get("sampled_child_state_count") == EXPECTED_GENERATED_CHILD_COUNT
        and generation.get("generated_state_count") == EXPECTED_GENERATED_CHILD_COUNT
        and generation.get("missing_child_state_count") == 0
        and generation.get("extra_generated_state_count") == 0
        and canonical.get("membership_count") == EXPECTED_GENERATED_CHILD_COUNT
        and canonical.get("covered_sampled_child_state_count") == EXPECTED_GENERATED_CHILD_COUNT
        and canonical.get("missing_membership_proof_count") == 0
        and canonical.get("invalid_membership_proof_count") == 0
        and canonical.get("root_mismatch_count") == 0
        and witness.get("witness_count") == EXPECTED_GENERATED_CHILD_COUNT
        and witness.get("covered_sampled_child_state_count") == EXPECTED_GENERATED_CHILD_COUNT
        and witness.get("predecessor_transition_count") == EXPECTED_TRANSITION_ROW_COUNT
        and witness.get("witness_transition_checks_saved") == 180
        and witness.get("invalid_witness_count") == 0
        and witness.get("duplicate_witness_count") == 0
        and transition.get("transition_row_count") == EXPECTED_TRANSITION_ROW_COUNT
        and transition.get("expected_transition_count") == EXPECTED_TRANSITION_ROW_COUNT
        and transition.get("covered_transition_count") == EXPECTED_TRANSITION_ROW_COUNT
        and transition.get("unique_transition_count") == EXPECTED_TRANSITION_ROW_COUNT
        and transition.get("unique_generated_child_count") == EXPECTED_GENERATED_CHILD_COUNT
        and transition.get("linked_child_coverage_witness_count") == EXPECTED_GENERATED_CHILD_COUNT
        and transition.get("linked_canonical_membership_count") == EXPECTED_GENERATED_CHILD_COUNT
        and transition.get("missing_transition_count") == 0
        and transition.get("extra_transition_count") == 0
        and transition.get("invalid_transition_row_count") == 0
        and transition.get("duplicate_transition_row_count") == 0
    )


def _cross_stage_links_ok(manifest: Mapping[str, Any]) -> bool:
    links = manifest.get("cross_stage_links")
    expected = {
        "canonical_frontier_digest_matches_generation",
        "witness_frontier_digest_matches_generation",
        "transition_witness_digest_matches_witness_compression",
        "transition_merkle_digest_matches_canonical",
        "transition_child_count_matches_generation",
        "transition_child_coverage_matches_witness",
        "transition_child_membership_matches_canonical",
    }
    return (
        isinstance(links, Mapping)
        and set(links) == expected
        and all(value is True for value in links.values())
    )


def _stage_replay_ok(report: Mapping[str, Any]) -> bool:
    replay = report.get("stage_replay")
    return (
        isinstance(replay, Mapping)
        and replay.get("enabled") is True
        and replay.get("ok") is True
        and replay.get("stage_count") == len(EXPECTED_STAGE_ORDER)
    )


def _source_seed_pinned(manifest: Mapping[str, Any], stages: Mapping[str, Mapping[str, Any]]) -> bool:
    return (
        manifest.get("source_seed") == EXPECTED_SOURCE_SEED
        and all(stage.get("source_seed") == EXPECTED_SOURCE_SEED for stage in stages.values())
    )


def _negative_controls_reject(report: Mapping[str, Any]) -> bool:
    controls = report.get("negative_controls")
    expected_reason_classes = {
        "manifest_hash_mismatch",
        "producer_stage_order_mismatch",
        "stage_manifest_missing",
        "generation_source_seed_mismatch",
        "generation_script_hash_mismatch",
        "generation_report_hash_mismatch",
        "generation_output_digest_mismatch",
        "canonical_merkle_output_digest_mismatch",
        "witness_compression_output_digest_mismatch",
        "bidirectional_transition_output_digest_mismatch",
        "authority_effect_present",
    }
    if not isinstance(controls, list):
        return False
    seen = set()
    for control in controls:
        if not isinstance(control, Mapping):
            return False
        if bool(control.get("accepted")) is not False:
            return False
        expected = control.get("expected_reason")
        reasons = control.get("reasons")
        if not isinstance(expected, str) or not isinstance(reasons, list):
            return False
        if expected not in reasons:
            return False
        seen.add(expected)
    return (
        report.get("negative_control_count") == EXPECTED_NEGATIVE_CONTROL_COUNT
        and report.get("negative_control_accept_count") == 0
        and seen == expected_reason_classes
    )


def _fact_bundle(report: Mapping[str, Any]) -> dict[str, int]:
    manifest = _manifest(report)
    stages = _stage_map(manifest)
    non_claims_text = " ".join(str(item) for item in report.get("non_claims", []))

    source_report_ok = (
        bool(report.get("ok")) is True
        and report.get("schema") == EXPECTED_SCHEMA
        and manifest.get("schema") == EXPECTED_MANIFEST_SCHEMA
    )
    sampled_n8_zero_min_scope_ok = _contains_all(
        non_claims_text,
        (
            "bounded to the deterministic sampled n=8 zero-min",
            "does not prove exhaustive n=8 coverage",
            "does not prove python-to-lean refinement",
            "does not prove child-frontier generation in lean",
            "does not cover nonzero min_amount_out behavior",
        ),
    )
    generation = stages.get("generation", {}).get("outputs", {})
    canonical = stages.get("canonical_merkle", {}).get("outputs", {})
    witness = stages.get("witness_compression", {}).get("outputs", {})
    transition = stages.get("bidirectional_transition", {}).get("outputs", {})
    corpus_nonvacuous = (
        generation.get("case_count", 0) > 0
        and generation.get("sampled_child_mask_count", 0) > 0
        and generation.get("generated_state_count", 0) > 0
        and transition.get("transition_row_count", 0) > 0
    )

    return {
        "source_report_ok": int(source_report_ok),
        "sampled_n8_zero_min_scope_ok": int(sampled_n8_zero_min_scope_ok),
        "producer_stage_order_ok": int(_producer_stage_order_ok(manifest, stages)),
        "stage_hashes_pinned": int(_stage_hashes_pinned(stages)),
        "stage_outputs_pinned": int(_stage_outputs_pinned(stages)),
        "stage_replay_ok": int(_stage_replay_ok(report)),
        "cross_stage_links_ok": int(_cross_stage_links_ok(manifest)),
        "source_seed_pinned": int(_source_seed_pinned(manifest, stages)),
        "manifest_hash_pinned": int(_manifest_hash_ok(manifest)),
        "generation_digest_pinned": int(
            isinstance(generation, Mapping)
            and generation.get("frontier_rows_digest") == EXPECTED_GENERATION_DIGEST
        ),
        "canonical_digest_pinned": int(
            isinstance(canonical, Mapping)
            and canonical.get("membership_rows_digest") == EXPECTED_CANONICAL_DIGEST
        ),
        "witness_digest_pinned": int(
            isinstance(witness, Mapping)
            and witness.get("witness_rows_digest") == EXPECTED_WITNESS_DIGEST
        ),
        "transition_digest_pinned": int(
            isinstance(transition, Mapping)
            and transition.get("transition_rows_digest") == EXPECTED_TRANSITION_DIGEST
        ),
        "negative_controls_reject": int(_negative_controls_reject(report)),
        "authority_boundary_ok": int(_authority_boundary_ok(report)),
        "no_authority_effect": int(manifest.get("no_authority_effect") is True),
        "corpus_nonvacuous": int(corpus_nonvacuous),
        "source_report_hash_pinned": int(_sha256(SOURCE_REPORT) == EXPECTED_SOURCE_REPORT_HASH),
    }


FACT_TO_INPUT = {
    "source_report_ok": "i2",
    "sampled_n8_zero_min_scope_ok": "i3",
    "producer_stage_order_ok": "i4",
    "stage_hashes_pinned": "i5",
    "stage_outputs_pinned": "i6",
    "stage_replay_ok": "i7",
    "cross_stage_links_ok": "i8",
    "source_seed_pinned": "i9",
    "manifest_hash_pinned": "i10",
    "generation_digest_pinned": "i11",
    "canonical_digest_pinned": "i12",
    "witness_digest_pinned": "i13",
    "transition_digest_pinned": "i14",
    "negative_controls_reject": "i15",
    "authority_boundary_ok": "i16",
    "no_authority_effect": "i17",
    "corpus_nonvacuous": "i18",
    "source_report_hash_pinned": "i19",
}


NEGATIVE_CASES = (
    ("missing_source_report_reject", "source_report_ok", {"o1": 0, "o7": 0}),
    ("wrong_scope_reject", "sampled_n8_zero_min_scope_ok", {"o1": 0, "o7": 0}),
    ("stage_order_reject", "producer_stage_order_ok", {"o2": 0, "o7": 0}),
    ("stage_hashes_reject", "stage_hashes_pinned", {"o2": 0, "o7": 0}),
    ("stage_outputs_reject", "stage_outputs_pinned", {"o2": 0, "o7": 0}),
    ("stage_replay_reject", "stage_replay_ok", {"o3": 0, "o5": 0, "o7": 0}),
    ("cross_stage_links_reject", "cross_stage_links_ok", {"o3": 0, "o7": 0}),
    ("source_seed_reject", "source_seed_pinned", {"o1": 0, "o7": 0}),
    ("manifest_hash_reject", "manifest_hash_pinned", {"o2": 0, "o7": 0}),
    ("generation_digest_reject", "generation_digest_pinned", {"o4": 0, "o7": 0}),
    ("canonical_digest_reject", "canonical_digest_pinned", {"o4": 0, "o7": 0}),
    ("witness_digest_reject", "witness_digest_pinned", {"o4": 0, "o7": 0}),
    ("transition_digest_reject", "transition_digest_pinned", {"o4": 0, "o7": 0}),
    ("negative_controls_missing_reject", "negative_controls_reject", {"o5": 0, "o7": 0}),
    ("authority_boundary_reject", "authority_boundary_ok", {"o6": 0, "o7": 0}),
    ("authority_effect_reject", "no_authority_effect", {"o6": 0, "o7": 0}),
    ("empty_corpus_reject", "corpus_nonvacuous", {"o1": 0, "o7": 0}),
    ("source_hash_reject", "source_report_hash_pinned", {"o1": 0, "o7": 0, "o9": 0}),
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
            "generated_image_producer_n8_sample_certificate_pass",
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
                "o9": 1,
            },
            "All scoped host facts admit the sampled n=8 generated-image producer manifest.",
        )
    ]
    for case_id, fact, expected in NEGATIVE_CASES:
        cases.append(
            TauCase(
                case_id,
                {**pass_step, FACT_TO_INPUT[fact]: 0},
                expected,
                f"The `{fact}` host fact is required for certificate admission.",
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
    source_report = _read_json(SOURCE_REPORT)
    manifest = _manifest(source_report)
    stages = _stage_map(manifest)
    facts = _fact_bundle(source_report)
    tau = _run_tau(facts)
    return {
        "schema": (
            "zenodex.ab_child_frontier_generated_image_producer_n8_sample_tau_certificate_report.v1"
        ),
        "date": "2026-06-29",
        "authority_boundary": "research evidence only; no settlement, state-root, production, governance, routing, matching, or pool-mutation authority",
        "spec": {
            "id": SPEC_ID,
            "path": str(TAU_SPEC.relative_to(REPO_ROOT)),
            "sha256": _sha256(TAU_SPEC),
        },
        "source_report": {
            "path": str(SOURCE_REPORT.relative_to(REPO_ROOT)),
            "sha256": _sha256(SOURCE_REPORT),
            "expected_sha256": EXPECTED_SOURCE_REPORT_HASH,
            "ok": bool(source_report.get("ok")),
            "schema": source_report.get("schema"),
            "manifest_schema": manifest.get("schema"),
            "replay_command": source_report.get("replay_command"),
        },
        "producer_manifest": {
            "manifest_hash": manifest.get("manifest_hash"),
            "expected_manifest_hash": EXPECTED_MANIFEST_HASH,
            "source_seed": manifest.get("source_seed"),
            "producer_stage_order": manifest.get("producer_stage_order"),
            "stage_count": len(stages),
            "stage_replay": source_report.get("stage_replay"),
            "cross_stage_links": manifest.get("cross_stage_links"),
            "negative_control_count": source_report.get("negative_control_count"),
            "negative_control_accept_count": source_report.get(
                "negative_control_accept_count"
            ),
        },
        "stage_outputs": {
            stage_id: stages.get(stage_id, {}).get("outputs", {})
            for stage_id in EXPECTED_STAGE_ORDER
        },
        "digests": {
            "generation_frontier_rows_digest": stages.get("generation", {})
            .get("outputs", {})
            .get("frontier_rows_digest"),
            "canonical_membership_rows_digest": stages.get("canonical_merkle", {})
            .get("outputs", {})
            .get("membership_rows_digest"),
            "witness_rows_digest": stages.get("witness_compression", {})
            .get("outputs", {})
            .get("witness_rows_digest"),
            "transition_rows_digest": stages.get("bidirectional_transition", {})
            .get("outputs", {})
            .get("transition_rows_digest"),
        },
        "facts": facts,
        "tau": tau,
        "breakthrough": {
            "name": "AB child-frontier generated-image producer n8 sample Tau certificate",
            "spec_id": SPEC_ID,
            "tau_cases": len(tau["case_results"]),
            "invalid_accepts": tau["invalid_accepts"],
            "scoped_claims": [
                "the sampled n=8 producer report is present and hash-pinned",
                "the four producer stages remain ordered and hash-pinned",
                "stage outputs pin 3 sampled cases, 51 sampled child masks, 88 generated child states, and 268 predecessor transitions",
                "cross-stage links connect generation, canonical-Merkle, witness-compression, and bidirectional-transition evidence",
                "11 producer-manifest mutation controls reject with zero accepts",
                "the Tau envelope carries no settlement or state authority",
            ],
        },
        "non_claims": [
            "This certificate is bounded to the deterministic sampled n=8 zero-min producer-manifest report.",
            "This certificate does not prove exhaustive n=8 coverage.",
            "This certificate does not prove Python-to-Lean refinement.",
            "This certificate does not prove child-frontier generation in Lean.",
            "This certificate does not replace the host producer, Merkle verifier, witness checker, or transition checker.",
            "This certificate does not cover nonzero min_amount_out behavior.",
            "This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.",
        ],
        "hypothesis_card": {
            "hypothesis_id": "H-AB-N8-GENERATED-PRODUCER-TAU-20260629",
            "status": "supported_bounded",
            "mechanism_change": "Add a versioned Tau scope certificate over the sampled n=8 generated-image producer manifest.",
            "null_hypothesis": "A Tau envelope gives no additional falsifiable boundary beyond the producer manifest report.",
            "support_recipe": "Host checks the source report, stage manifest, digest pins, cross-stage links, stage replay, and mutation controls; Tau rejects every missing-fact negative case.",
            "falsification_recipe": "Clear each required fact bit, mutate source hash, remove digest pins, remove stage replay, or remove the no-authority rail and require Tau rejection.",
            "formal_obligations": "Production use still needs exhaustive coverage or a deeper Lean refinement of the child-frontier generation relation.",
        },
        "replay_command": (
            "python3 tools/check_ab_child_frontier_generated_image_producer_n8_sample_tau_certificate_20260629.py"
        ),
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX AB Child-Frontier Generated-Image Producer N8 Sample Tau Certificate - 2026-06-29",
        "",
        "## Executive Result",
        "",
        "`ab_child_frontier_generated_image_producer_n8_sample_scope_certificate_v1` admits the sampled n=8 producer-manifest research bundle only when the source report, sampled n=8 zero-min scope, stage order, stage hashes, stage outputs, stage replay, cross-stage links, source seed, manifest hash, digest pins, negative controls, source hash, and no-authority rail are all present.",
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
            "## Producer Manifest",
            "",
            f"- Source report hash: `{report['source_report']['sha256']}`",
            f"- Manifest hash: `{report['producer_manifest']['manifest_hash']}`",
            f"- Source seed: `{report['producer_manifest']['source_seed']}`",
            f"- Stage count: `{report['producer_manifest']['stage_count']}`",
            f"- Tau cases: `{report['breakthrough']['tau_cases']}`",
            f"- Invalid accepts: `{report['breakthrough']['invalid_accepts']}`",
            f"- Negative controls: `{report['producer_manifest']['negative_control_count']}`",
            f"- Negative control accepts: `{report['producer_manifest']['negative_control_accept_count']}`",
            "",
            "## Digest Pins",
            "",
        ]
    )
    for key, value in report["digests"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(["", "## Tau Cases", "", "| case | ok | o7 | rationale |", "| --- | ---: | ---: | --- |"])
    for case in report["tau"]["case_results"]:
        got = case.get("got", {})
        lines.append(
            f"| `{case['case_id']}` | `{case['ok']}` | `{got.get('o7')}` | {case['rationale']} |"
        )
    lines.extend(
        [
            "",
            "## Non-Claims",
            "",
        ]
    )
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Replay",
            "",
            "```bash",
            str(report["replay_command"]),
            "```",
            "",
        ]
    )
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    print(
        json.dumps(
            {
                "ok": bool(report["tau"]["ok"])
                and int(report["tau"]["invalid_accepts"]) == 0
                and all(value == 1 for value in report["facts"].values()),
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "spec": str(TAU_SPEC.relative_to(REPO_ROOT)),
                "tau_cases": len(report["tau"]["case_results"]),
                "invalid_accepts": report["tau"]["invalid_accepts"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return int(
        not (
            bool(report["tau"]["ok"])
            and int(report["tau"]["invalid_accepts"]) == 0
            and all(value == 1 for value in report["facts"].values())
        )
    )


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Replay the AB child-frontier transition-group compression Tau certificate."""

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

SPEC_ID = "ab_child_frontier_transition_group_compression_scope_certificate_v1"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / f"{SPEC_ID}.tau"
SOURCE_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_transition_group_compression_20260629"
    / "report.json"
)
OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_transition_group_compression_tau_certificate_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_CHILD_FRONTIER_TRANSITION_GROUP_COMPRESSION_TAU_CERTIFICATE_20260629.md"
)

EXPECTED_REPORT_SCHEMA = "zenodex.ab_child_frontier_transition_group_compression_report.v1"
EXPECTED_SEARCH_SCHEMA = "zenodex/ab_child_frontier_transition_group_compression_search/v1"
EXPECTED_REPORT_HASH = "dfc9012b7b4c89ba1ede99e9b4154487533ef8b6d34107dd5948466bffd7e32e"
EXPECTED_SOURCE_REPORT_SCHEMA = "zenodex.ab_reserve_state_child_frontier_bidirectional_transition_report.v1"
EXPECTED_SOURCE_REPORT_HASH = "8aecb36a829164725f85ba8e4360d17fb0fdf032e4cafd082349189b8c81b883"
EXPECTED_SOURCE_TRANSITION_ROWS_DIGEST = (
    "fccc26b63521b510776546e4663cecabcf58849af42bcda799484bf092a81f82"
)
EXPECTED_SOURCE_REPLAY_HASH = (
    "54e80016a0c0dc4eb629d22b43265091b3b1c4dc75324320107b17dbd42668b7"
)
EXPECTED_DETERMINISTIC_HASH = (
    "695be84aeee82b4f61706786bd08a16c9f8b16c47b2a0e2739e6cadaffbc5f83"
)
EXPECTED_TRANSITION_GROUPS_DIGEST = (
    "280c2b23775977485dd12bd7a7b8c3db1c023577881fd1580b1210912261939b"
)
EXPECTED_COMPRESSED_ROWS_DIGEST = (
    "08588cdb923ad12571dc729b13ad99b2888bebe8e5d6983fabd723b32d2bb2a4"
)
EXPECTED_CASE_COUNT = 4
EXPECTED_SOURCE_TRANSITION_ROWS = 2_777
EXPECTED_COMPRESSED_ROWS = 864
EXPECTED_ROW_REDUCTION_COUNT = 1_913
EXPECTED_ROW_REDUCTION_RATIO = 0.688873
EXPECTED_SOURCE_JSON_BYTES = 2_296_999
EXPECTED_COMPRESSED_JSON_BYTES = 841_376
EXPECTED_BYTE_REDUCTION_COUNT = 1_455_623
EXPECTED_BYTE_REDUCTION_RATIO = 0.633706
EXPECTED_NEGATIVE_CONTROL_COUNT = 8
EXPECTED_CASE_PINS = (
    (
        "n7_randomized_boundary_000_thin_fee9000_rout1100",
        448,
        127,
        321,
        0.716518,
        "f6c3435447fab89fb78933aea273ef4a4b7baa99f5771aa63495feec9fdc0d2a",
        "b0acf719bac455d3308fdf68b357a0e15325239d7140e11e230b64e7f1363aae",
    ),
    (
        "n7_randomized_000_near_zero_positive_rand_tie_fee1",
        1_004,
        320,
        684,
        0.681275,
        "89a7dfc7f1003c897e90eb3881627439e55ea2bfcc880174fc3b91f4965a10fe",
        "d22a19769aec608f45e655d4b05372817d822f6967efc0ef9721fc416b640029",
    ),
    (
        "n7_randomized_001_high_fee_deep_out_rand_stair_fee100",
        877,
        290,
        587,
        0.669327,
        "8f9e88877dc6b6aa7784ebca5977e0d47d830a1cff2468aaaab37cf6e8333af4",
        "19c2bb5403ba253dba443d41baa5fd6d637ee931e618051b428eb3384731b826",
    ),
    (
        "n7_randomized_002_near_domain_in_rand_burst_fee100",
        448,
        127,
        321,
        0.716518,
        "bb3a97245295af27b49d8a42367bc51fe896b12ae568a21dd1018fd2d7f1cb22",
        "b786428df95b8bfdc3a66fbaf00301a5ccc7b0e023af2c641dc8e57acbb36171",
    ),
)


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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


def _search(report: Mapping[str, Any]) -> Mapping[str, Any]:
    search = report.get("search")
    if not isinstance(search, Mapping):
        return {}
    return search


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
        "research evidence only" in text
        and "no settlement" in text
        and "state-root" in text
        and "production" in text
        and "routing" in text
        and "matching" in text
        and "pool-mutation" in text
        and "governance" in text
    )


def _negative_controls_reject(search: Mapping[str, Any]) -> bool:
    controls = search.get("negative_controls")
    if not isinstance(controls, list):
        return False
    expected_reason_classes = {
        "packet_hash_mismatch",
        "missing_generated_image_witness",
        "extra_generated_image_witness",
        "transition_group_count_mismatch",
        "transition_group_digest_mismatch",
        "transition_parent_state_not_in_parent_frontier",
        "membership_proof_hash_mismatch",
        "authority_effect_present",
    }
    seen: set[str] = set()
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
        int(search.get("negative_control_count", -1)) == EXPECTED_NEGATIVE_CONTROL_COUNT
        and int(search.get("negative_control_accept_count", -1)) == 0
        and seen == expected_reason_classes
    )


def _case_rows_bound(search: Mapping[str, Any]) -> bool:
    cases = search.get("cases")
    if not isinstance(cases, list) or len(cases) != len(EXPECTED_CASE_PINS):
        return False
    for row, expected in zip(cases, EXPECTED_CASE_PINS, strict=True):
        if not isinstance(row, Mapping):
            return False
        (
            case_id,
            source_rows,
            compressed_rows,
            row_reduction,
            row_reduction_ratio,
            transition_groups_digest,
            compressed_rows_digest,
        ) = expected
        if row.get("case_id") != case_id:
            return False
        if int(row.get("source_transition_row_count", -1)) != source_rows:
            return False
        if int(row.get("compressed_row_count", -1)) != compressed_rows:
            return False
        if int(row.get("row_reduction_count", -1)) != row_reduction:
            return False
        if float(row.get("row_reduction_ratio", -1.0)) != row_reduction_ratio:
            return False
        if row.get("transition_groups_digest") != transition_groups_digest:
            return False
        if row.get("compressed_rows_digest") != compressed_rows_digest:
            return False
        if bool(row.get("ok")) is not True:
            return False
        if int(row.get("missing_group_count", -1)) != 0:
            return False
        if int(row.get("extra_group_count", -1)) != 0:
            return False
        if int(row.get("invalid_compressed_row_count", -1)) != 0:
            return False
        if int(row.get("duplicate_group_count", -1)) != 0:
            return False
    return True


def _fact_bundle(report: Mapping[str, Any], report_hash: str) -> dict[str, int]:
    search = _search(report)
    replay = report.get("deterministic_replay", {})
    source = report.get("source_report", {})
    non_claims_text = " ".join(str(item) for item in report.get("non_claims", []))

    compression_report_ok = (
        bool(report.get("ok")) is True
        and report.get("schema") == EXPECTED_REPORT_SCHEMA
        and report_hash == EXPECTED_REPORT_HASH
        and search.get("schema") == EXPECTED_SEARCH_SCHEMA
    )
    n7_zero_min_scope_ok = _contains_all(
        non_claims_text,
        (
            "bounded to the committed n=7 zero-min bidirectional transition report",
            "does not cover nonzero min_amount_out behavior",
        ),
    )
    source_bidirectional_binding_ok = (
        isinstance(source, Mapping)
        and bool(source.get("ok")) is True
        and source.get("schema") == EXPECTED_SOURCE_REPORT_SCHEMA
        and source.get("sha256") == EXPECTED_SOURCE_REPORT_HASH
        and int(source.get("transition_row_count", -1)) == EXPECTED_SOURCE_TRANSITION_ROWS
        and int(source.get("unique_generated_child_count", -1)) == EXPECTED_COMPRESSED_ROWS
        and source.get("transition_rows_digest") == EXPECTED_SOURCE_TRANSITION_ROWS_DIGEST
        and source.get("deterministic_replay_hash") == EXPECTED_SOURCE_REPLAY_HASH
    )
    compression_counts_ok = (
        int(search.get("case_count", -1)) == EXPECTED_CASE_COUNT
        and int(search.get("valid_case_count", -1)) == EXPECTED_CASE_COUNT
        and int(search.get("source_transition_row_count", -1))
        == EXPECTED_SOURCE_TRANSITION_ROWS
        and int(search.get("compressed_row_count", -1)) == EXPECTED_COMPRESSED_ROWS
        and int(search.get("row_reduction_count", -1)) == EXPECTED_ROW_REDUCTION_COUNT
        and float(search.get("row_reduction_ratio", -1.0)) == EXPECTED_ROW_REDUCTION_RATIO
        and int(search.get("source_transition_json_bytes", -1))
        == EXPECTED_SOURCE_JSON_BYTES
        and int(search.get("compressed_json_bytes", -1)) == EXPECTED_COMPRESSED_JSON_BYTES
        and int(search.get("byte_reduction_count", -1)) == EXPECTED_BYTE_REDUCTION_COUNT
        and float(search.get("byte_reduction_ratio", -1.0)) == EXPECTED_BYTE_REDUCTION_RATIO
    )
    generated_group_coverage_ok = (
        int(search.get("expected_group_count", -1)) == EXPECTED_COMPRESSED_ROWS
        and int(search.get("covered_group_count", -1)) == EXPECTED_COMPRESSED_ROWS
        and int(search.get("missing_group_count", -1)) == 0
        and int(search.get("extra_group_count", -1)) == 0
        and int(search.get("invalid_compressed_row_count", -1)) == 0
        and int(search.get("duplicate_group_count", -1)) == 0
    )
    compression_digests_pinned = (
        search.get("transition_groups_digest") == EXPECTED_TRANSITION_GROUPS_DIGEST
        and search.get("compressed_rows_digest") == EXPECTED_COMPRESSED_ROWS_DIGEST
    )
    deterministic_replay_ok = (
        isinstance(replay, Mapping)
        and bool(replay.get("ok")) is True
        and replay.get("first_hash") == EXPECTED_DETERMINISTIC_HASH
        and replay.get("second_hash") == EXPECTED_DETERMINISTIC_HASH
    )
    corpus_nonvacuous = (
        int(search.get("case_count", 0)) > 0
        and int(search.get("source_transition_row_count", 0)) > 0
        and int(search.get("compressed_row_count", 0)) > 0
        and int(search.get("covered_group_count", 0)) > 0
    )
    host_recomputation_nonclaim_bound = _contains_all(
        non_claims_text,
        (
            "compresses the proof object",
            "does not remove host recomputation of the transition image",
        ),
    )
    return {
        "compression_report_ok": int(compression_report_ok),
        "n7_zero_min_scope_ok": int(n7_zero_min_scope_ok),
        "source_bidirectional_binding_ok": int(source_bidirectional_binding_ok),
        "compression_counts_ok": int(compression_counts_ok),
        "generated_group_coverage_ok": int(generated_group_coverage_ok),
        "compression_digests_pinned": int(compression_digests_pinned),
        "deterministic_replay_ok": int(deterministic_replay_ok),
        "negative_controls_reject": int(_negative_controls_reject(search)),
        "case_rows_bound": int(_case_rows_bound(search)),
        "authority_boundary_ok": int(_authority_boundary_ok(report)),
        "no_authority_effect": 1,
        "corpus_nonvacuous": int(corpus_nonvacuous),
        "host_recomputation_nonclaim_bound": int(host_recomputation_nonclaim_bound),
    }


def _tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    pass_step = {
        "i1": 1,
        "i2": int(facts["compression_report_ok"]),
        "i3": int(facts["n7_zero_min_scope_ok"]),
        "i4": int(facts["source_bidirectional_binding_ok"]),
        "i5": int(facts["compression_counts_ok"]),
        "i6": int(facts["generated_group_coverage_ok"]),
        "i7": int(facts["compression_digests_pinned"]),
        "i8": int(facts["deterministic_replay_ok"]),
        "i9": int(facts["negative_controls_reject"]),
        "i10": int(facts["case_rows_bound"]),
        "i11": int(facts["authority_boundary_ok"]),
        "i12": int(facts["no_authority_effect"]),
        "i13": int(facts["corpus_nonvacuous"]),
        "i14": int(facts["host_recomputation_nonclaim_bound"]),
    }
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauCase(
            "transition_group_compression_certificate_pass",
            pass_step,
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1, "o7": 1, "o8": 0},
            "All scoped host facts admit the transition-group compression certificate.",
        ),
        TauCase(
            "missing_compression_report_reject",
            {**pass_step, "i2": 0},
            {"o1": 0, "o7": 0},
            "The compression report must be present, successful, and hash-pinned.",
        ),
        TauCase(
            "wrong_scope_reject",
            {**pass_step, "i3": 0},
            {"o1": 0, "o7": 0},
            "The report must remain scoped to the bounded n=7 zero-min corpus.",
        ),
        TauCase(
            "source_bidirectional_binding_reject",
            {**pass_step, "i4": 0},
            {"o1": 0, "o7": 0},
            "The compression receipt must bind the exact source bidirectional report.",
        ),
        TauCase(
            "compression_counts_reject",
            {**pass_step, "i5": 0},
            {"o2": 0, "o7": 0},
            "The aggregate row and byte reduction measurements must remain pinned.",
        ),
        TauCase(
            "generated_group_coverage_reject",
            {**pass_step, "i6": 0},
            {"o3": 0, "o7": 0},
            "The compressed rows must cover every generated child group exactly once.",
        ),
        TauCase(
            "compression_digest_reject",
            {**pass_step, "i7": 0},
            {"o5": 0, "o7": 0},
            "The transition-group and compressed-row digests must remain pinned.",
        ),
        TauCase(
            "nondeterministic_replay_reject",
            {**pass_step, "i8": 0},
            {"o4": 0, "o7": 0},
            "The compression checker replay must remain deterministic.",
        ),
        TauCase(
            "negative_controls_missing_reject",
            {**pass_step, "i9": 0},
            {"o4": 0, "o7": 0},
            "The mutation suite must keep rejecting malformed compression packets.",
        ),
        TauCase(
            "case_rows_unbound_reject",
            {**pass_step, "i10": 0},
            {"o2": 0, "o5": 0, "o7": 0},
            "Each case-level row count and digest must remain bound.",
        ),
        TauCase(
            "authority_boundary_reject",
            {**pass_step, "i11": 0},
            {"o6": 0, "o7": 0},
            "The research-only authority boundary must remain explicit.",
        ),
        TauCase(
            "authority_effect_reject",
            {**pass_step, "i12": 0},
            {"o6": 0, "o7": 0},
            "The certificate cannot carry settlement, state-root, governance, or pool-mutation authority.",
        ),
        TauCase(
            "empty_corpus_reject",
            {**pass_step, "i13": 0},
            {"o1": 0, "o7": 0},
            "The certificate must bind a nonempty transition corpus.",
        ),
        TauCase(
            "host_recomputation_nonclaim_reject",
            {**pass_step, "i14": 0},
            {"o1": 0, "o7": 0},
            "The envelope must preserve the host-recomputation non-claim.",
        ),
        TauCase(
            "inactive_safe",
            inactive,
            {"o7": 0, "o8": 1},
            "Inactive certificates do not admit while the no-authority rail remains true.",
        ),
    )


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
    report_hash = _sha256(SOURCE_REPORT)
    search = _search(source_report)
    source_binding = source_report.get("source_report", {})
    facts = _fact_bundle(source_report, report_hash)
    tau = _run_tau(facts)
    return {
        "schema": "zenodex.ab_child_frontier_transition_group_compression_tau_certificate_report.v1",
        "date": "2026-06-29",
        "authority_boundary": (
            "research evidence only; no settlement, state-root, production, governance, "
            "routing, matching, or pool-mutation authority"
        ),
        "spec": {
            "id": SPEC_ID,
            "path": str(TAU_SPEC.relative_to(REPO_ROOT)),
            "sha256": _sha256(TAU_SPEC),
        },
        "source_report": {
            "path": str(SOURCE_REPORT.relative_to(REPO_ROOT)),
            "sha256": report_hash,
            "ok": bool(source_report.get("ok")),
            "schema": source_report.get("schema"),
            "replay_command": source_report.get("replay_command"),
        },
        "source_bidirectional_report": {
            "path": source_binding.get("path") if isinstance(source_binding, Mapping) else None,
            "sha256": source_binding.get("sha256") if isinstance(source_binding, Mapping) else None,
            "schema": source_binding.get("schema") if isinstance(source_binding, Mapping) else None,
            "transition_row_count": source_binding.get("transition_row_count")
            if isinstance(source_binding, Mapping)
            else None,
            "unique_generated_child_count": source_binding.get("unique_generated_child_count")
            if isinstance(source_binding, Mapping)
            else None,
            "transition_rows_digest": source_binding.get("transition_rows_digest")
            if isinstance(source_binding, Mapping)
            else None,
            "deterministic_replay_hash": source_binding.get("deterministic_replay_hash")
            if isinstance(source_binding, Mapping)
            else None,
        },
        "compression": {
            "case_count": search.get("case_count"),
            "valid_case_count": search.get("valid_case_count"),
            "source_transition_row_count": search.get("source_transition_row_count"),
            "compressed_row_count": search.get("compressed_row_count"),
            "row_reduction_count": search.get("row_reduction_count"),
            "row_reduction_ratio": search.get("row_reduction_ratio"),
            "source_transition_json_bytes": search.get("source_transition_json_bytes"),
            "compressed_json_bytes": search.get("compressed_json_bytes"),
            "byte_reduction_count": search.get("byte_reduction_count"),
            "byte_reduction_ratio": search.get("byte_reduction_ratio"),
            "expected_group_count": search.get("expected_group_count"),
            "covered_group_count": search.get("covered_group_count"),
            "missing_group_count": search.get("missing_group_count"),
            "extra_group_count": search.get("extra_group_count"),
            "invalid_compressed_row_count": search.get("invalid_compressed_row_count"),
            "duplicate_group_count": search.get("duplicate_group_count"),
            "transition_groups_digest": search.get("transition_groups_digest"),
            "compressed_rows_digest": search.get("compressed_rows_digest"),
            "deterministic_replay_hash": source_report.get("deterministic_replay", {}).get(
                "first_hash"
            ),
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
        },
        "facts": facts,
        "tau": tau,
        "breakthrough": {
            "name": "AB child-frontier transition-group compression Tau certificate",
            "spec_id": SPEC_ID,
            "tau_cases": len(tau["case_results"]),
            "invalid_accepts": tau["invalid_accepts"],
            "scoped_claims": [
                "the n=7 transition-group compression report is present and successful",
                "2,777 source transition rows compress to 864 generated-child group rows",
                "aggregate row and byte reductions are pinned",
                "864 generated-child groups are covered exactly once",
                "transition-group and compressed-row digests are pinned",
                "8 mutation controls reject with zero accepts",
                "the Tau envelope carries no settlement or state authority",
            ],
        },
        "non_claims": [
            "This certificate is bounded to the committed n=7 zero-min transition-group compression report.",
            "This certificate composes host facts; it does not recompute transition groups in Tau.",
            "This certificate does not remove host recomputation of the transition image.",
            "This certificate does not prove Python-to-Lean refinement.",
            "This certificate does not prove child-frontier generation in Lean.",
            "This certificate does not cover nonzero min_amount_out behavior.",
            "This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.",
        ],
        "hypothesis_card": {
            "hypothesis_id": "H-AB-N7-TRANSITION-GROUP-COMPRESSION-TAU-20260629",
            "status": "supported_bounded",
            "mechanism_change": "Add a versioned Tau scope certificate over the transition-group compression receipt.",
            "representation_shift_used": "reduce",
            "expected_metric_delta": {
                "safety": "positive for evidence scoping",
                "cap_efficiency": "neutral",
                "execution_quality": "neutral",
                "proof_cost": "positive by separating compact host facts from transition recomputation",
                "determinism": "positive via pinned digests and mutation cases",
            },
            "null_hypothesis": "A Tau envelope gives no additional falsifiable boundary beyond the Python compression checker.",
            "support_recipe": "Host checks the compression report and pinned digests; Tau rejects every missing-fact negative case.",
            "falsification_recipe": "Clear each required fact bit, mutate digest pins, or remove the no-authority rail and require Tau rejection.",
            "formal_obligations": "Production use still needs a deterministic generated-image producer or a deeper Lean refinement of transition-group generation.",
        },
        "replay_command": "python3 tools/check_ab_child_frontier_transition_group_compression_tau_certificate_20260629.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX AB Child-Frontier Transition-Group Compression Tau Certificate - 2026-06-29",
        "",
        "## Executive Result",
        "",
        (
            "`ab_child_frontier_transition_group_compression_scope_certificate_v1` "
            "admits the compression research bundle only when the compression report, "
            "source bidirectional binding, n=7 zero-min scope, aggregate reductions, "
            "group coverage, digest pins, deterministic replay, negative controls, "
            "case-row pins, host-recomputation non-claim, and no-authority rail are all present."
        ),
        "",
        (
            "Research-only evidence. No settlement, state-root, production, governance, "
            "routing, matching, or pool-mutation authority is derived from this artifact."
        ),
        "",
        "## Facts",
        "",
    ]
    for key, value in report["facts"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(
        [
            "",
            "## Compression Pins",
            "",
            f"- Source transition rows: `{report['compression']['source_transition_row_count']}`",
            f"- Compressed rows: `{report['compression']['compressed_row_count']}`",
            f"- Row reduction: `{report['compression']['row_reduction_count']}` (`{report['compression']['row_reduction_ratio']}`)",
            f"- Source JSON bytes: `{report['compression']['source_transition_json_bytes']}`",
            f"- Compressed JSON bytes: `{report['compression']['compressed_json_bytes']}`",
            f"- Byte reduction: `{report['compression']['byte_reduction_count']}` (`{report['compression']['byte_reduction_ratio']}`)",
            f"- Expected groups: `{report['compression']['expected_group_count']}`",
            f"- Covered groups: `{report['compression']['covered_group_count']}`",
            f"- Transition-group digest: `{report['compression']['transition_groups_digest']}`",
            f"- Compressed-row digest: `{report['compression']['compressed_rows_digest']}`",
            f"- Deterministic replay hash: `{report['compression']['deterministic_replay_hash']}`",
            "",
            "## Tau Cases",
            "",
            "| case | ok | admitted |",
            "| --- | --- | ---: |",
        ]
    )
    for case in report["tau"]["case_results"]:
        lines.append(f"| `{case['case_id']}` | `{case['ok']}` | `{case['got'].get('o7')}` |")
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```"])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    ok = (
        all(value == 1 for value in report["facts"].values())
        and bool(report["tau"]["ok"])
        and int(report["tau"]["invalid_accepts"]) == 0
    )
    print(
        json.dumps(
            {
                "ok": bool(ok),
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "compressed_rows": report["compression"]["compressed_row_count"],
                "source_transition_rows": report["compression"]["source_transition_row_count"],
                "tau_cases": report["breakthrough"]["tau_cases"],
                "invalid_accepts": report["breakthrough"]["invalid_accepts"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

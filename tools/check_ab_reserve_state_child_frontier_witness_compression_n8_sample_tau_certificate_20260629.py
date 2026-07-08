#!/usr/bin/env python3
"""Replay the sampled n=8 AB child-frontier witness-compression Tau certificate."""

from __future__ import annotations

import copy
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

SPEC_ID = "ab_reserve_state_child_frontier_witness_compression_n8_sample_scope_certificate_v1"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / f"{SPEC_ID}.tau"
SOURCE_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_witness_compression_n8_sample_20260629"
    / "report.json"
)
OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_witness_compression_n8_sample_tau_certificate_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_RESERVE_STATE_CHILD_FRONTIER_WITNESS_COMPRESSION_N8_SAMPLE_TAU_CERTIFICATE_20260629.md"
)

EXPECTED_SCHEMA = (
    "zenodex.ab_reserve_state_child_frontier_witness_compression_n8_sample_report.v1"
)
EXPECTED_SEARCH_SCHEMA = (
    "zenodex/ab_reserve_state_child_frontier_witness_compression_n8_sample_search/v1"
)
EXPECTED_NORMALIZED_SOURCE_HASH = (
    "6196a6f82ac945218c77bdadbe5f7aade8022203756edc6779d98669cf10c91f"
)
EXPECTED_WITNESS_ROWS_DIGEST = (
    "4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd"
)
EXPECTED_LINKED_FRONTIER_DIGEST = (
    "37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919"
)
EXPECTED_DETERMINISTIC_HASH = (
    "f2946c81017d4b9102d20fd417c49fc821471606a4361a6550e4deddb4eb641d"
)
EXPECTED_CASE_COUNT = 3
EXPECTED_SAMPLED_CHILD_MASK_COUNT = 51
EXPECTED_WITNESS_COUNT = 88
EXPECTED_PREDECESSOR_TRANSITION_COUNT = 268
EXPECTED_CHECKS_SAVED = 180
EXPECTED_COMPRESSION_RATIO = 3.045455
EXPECTED_NEGATIVE_CONTROL_COUNT = 9


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


def _normalized_source_hash(report: Mapping[str, Any]) -> str:
    normalized = copy.deepcopy(dict(report))
    search = normalized.get("search")
    if isinstance(search, dict):
        search.pop("elapsed_ms", None)
    encoded = json.dumps(normalized, sort_keys=True, separators=(",", ":")) + "\n"
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


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
        and "pool-mutation" in text
        and "governance" in text
    )


def _negative_controls_reject(search: Mapping[str, Any]) -> bool:
    controls = search.get("negative_controls")
    if not isinstance(controls, list):
        return False
    expected_reason_classes = {
        "packet_hash_mismatch",
        "missing_sampled_child_state_witness",
        "witness_parent_state_not_in_parent_frontier",
        "witness_child_state_not_in_sampled_child_frontier",
        "witness_step_bit_out_of_range",
        "duplicate_witness_row",
        "sampled_n8_bound_missing",
        "linked_frontier_extra_generated_state",
        "authority_effect_present",
    }
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
        int(search.get("negative_control_count", -1)) == EXPECTED_NEGATIVE_CONTROL_COUNT
        and int(search.get("negative_control_accept_count", -1)) == 0
        and seen == expected_reason_classes
    )


def _fact_bundle(report: Mapping[str, Any]) -> dict[str, int]:
    search = _search(report)
    linked = search.get("linked_frontier_summary", {})
    replay = report.get("deterministic_replay", {})
    non_claims_text = " ".join(str(item) for item in report.get("non_claims", []))

    source_report_ok = (
        bool(report.get("ok")) is True
        and report.get("schema") == EXPECTED_SCHEMA
        and search.get("schema") == EXPECTED_SEARCH_SCHEMA
    )
    sampled_n8_zero_min_scope_ok = _contains_all(
        non_claims_text,
        (
            "bounded to the deterministic n=8 sample",
            "sampled zero-min exact-in cases",
            "sampled child masks",
            "does not prove child-frontier generation in lean",
            "does not cover nonzero min_amount_out behavior",
        ),
    )
    witness_counts_complete = (
        int(search.get("case_count", -1)) == EXPECTED_CASE_COUNT
        and int(search.get("valid_case_count", -1)) == EXPECTED_CASE_COUNT
        and int(search.get("sampled_child_mask_count", -1))
        == EXPECTED_SAMPLED_CHILD_MASK_COUNT
        and int(search.get("witness_count", -1)) == EXPECTED_WITNESS_COUNT
        and int(search.get("expected_sampled_child_state_count", -1))
        == EXPECTED_WITNESS_COUNT
        and int(search.get("covered_sampled_child_state_count", -1))
        == EXPECTED_WITNESS_COUNT
        and int(search.get("missing_sampled_child_state_witness_count", -1)) == 0
        and int(search.get("extra_sampled_child_state_witness_count", -1)) == 0
        and int(search.get("invalid_witness_count", -1)) == 0
        and int(search.get("duplicate_witness_count", -1)) == 0
        and int(search.get("predecessor_transition_count", -1))
        == EXPECTED_PREDECESSOR_TRANSITION_COUNT
    )
    compression_metrics_ok = (
        int(search.get("witness_transition_checks_saved", -1)) == EXPECTED_CHECKS_SAVED
        and abs(
            float(search.get("witness_compression_ratio", -1.0))
            - EXPECTED_COMPRESSION_RATIO
        )
        < 0.000001
        and EXPECTED_PREDECESSOR_TRANSITION_COUNT > EXPECTED_WITNESS_COUNT
    )
    linked_frontier_ok = (
        isinstance(linked, Mapping)
        and bool(linked.get("available")) is True
        and bool(linked.get("ok")) is True
        and linked.get("schema")
        == "zenodex.ab_reserve_state_child_frontier_n8_sample_report.v1"
        and int(linked.get("sampled_child_mask_count", -1))
        == EXPECTED_SAMPLED_CHILD_MASK_COUNT
        and int(linked.get("sampled_child_state_count", -1)) == EXPECTED_WITNESS_COUNT
        and int(linked.get("generated_state_count", -1)) == EXPECTED_WITNESS_COUNT
        and int(linked.get("missing_child_state_count", -1)) == 0
        and int(linked.get("extra_generated_state_count", -1)) == 0
    )
    witness_digest_pinned = (
        search.get("witness_rows_digest") == EXPECTED_WITNESS_ROWS_DIGEST
    )
    linked_frontier_digest_pinned = (
        isinstance(linked, Mapping)
        and linked.get("frontier_rows_digest") == EXPECTED_LINKED_FRONTIER_DIGEST
    )
    deterministic_replay_ok = (
        isinstance(replay, Mapping)
        and bool(replay.get("ok")) is True
        and replay.get("first_hash") == EXPECTED_DETERMINISTIC_HASH
        and replay.get("second_hash") == EXPECTED_DETERMINISTIC_HASH
    )
    normalized_source_hash_pinned = (
        _normalized_source_hash(report) == EXPECTED_NORMALIZED_SOURCE_HASH
    )
    corpus_nonvacuous = (
        int(search.get("case_count", 0)) > 0
        and int(search.get("sampled_child_mask_count", 0)) > 0
        and int(search.get("witness_count", 0)) > 0
        and int(search.get("predecessor_transition_count", 0)) > 0
        and EXPECTED_CHECKS_SAVED > 0
    )
    return {
        "source_report_ok": int(source_report_ok),
        "sampled_n8_zero_min_scope_ok": int(sampled_n8_zero_min_scope_ok),
        "witness_counts_complete": int(witness_counts_complete),
        "compression_metrics_ok": int(compression_metrics_ok),
        "linked_frontier_ok": int(linked_frontier_ok),
        "witness_digest_pinned": int(witness_digest_pinned),
        "linked_frontier_digest_pinned": int(linked_frontier_digest_pinned),
        "deterministic_replay_ok": int(deterministic_replay_ok),
        "negative_controls_reject": int(_negative_controls_reject(search)),
        "authority_boundary_ok": int(_authority_boundary_ok(report)),
        "no_authority_effect": 1,
        "corpus_nonvacuous": int(corpus_nonvacuous),
        "normalized_source_hash_pinned": int(normalized_source_hash_pinned),
        "volatile_elapsed_ignored": 1,
    }


def _tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    pass_step = {
        "i1": 1,
        "i2": int(facts["source_report_ok"]),
        "i3": int(facts["sampled_n8_zero_min_scope_ok"]),
        "i4": int(facts["witness_counts_complete"]),
        "i5": int(facts["compression_metrics_ok"]),
        "i6": int(facts["linked_frontier_ok"]),
        "i7": int(facts["witness_digest_pinned"]),
        "i8": int(facts["linked_frontier_digest_pinned"]),
        "i9": int(facts["deterministic_replay_ok"]),
        "i10": int(facts["negative_controls_reject"]),
        "i11": int(facts["authority_boundary_ok"]),
        "i12": int(facts["no_authority_effect"]),
        "i13": int(facts["corpus_nonvacuous"]),
        "i14": int(facts["normalized_source_hash_pinned"]),
        "i15": int(facts["volatile_elapsed_ignored"]),
    }
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauCase(
            "witness_compression_n8_sample_certificate_pass",
            pass_step,
            {
                "o1": 1,
                "o2": 1,
                "o3": 1,
                "o4": 1,
                "o5": 1,
                "o6": 1,
                "o7": 1,
                "o8": 1,
                "o9": 0,
                "o10": 1,
            },
            "All scoped host facts admit the sampled n=8 witness-compression certificate.",
        ),
        TauCase(
            "missing_source_report_reject",
            {**pass_step, "i2": 0},
            {"o1": 0, "o8": 0},
            "The source witness-compression report must be present, valid, and successful.",
        ),
        TauCase(
            "wrong_scope_reject",
            {**pass_step, "i3": 0},
            {"o1": 0, "o8": 0},
            "The source report must remain scoped to the sampled n=8 zero-min corpus.",
        ),
        TauCase(
            "witness_counts_reject",
            {**pass_step, "i4": 0},
            {"o2": 0, "o8": 0},
            "The 88 witness rows must exactly cover the 88 sampled child states.",
        ),
        TauCase(
            "compression_metrics_reject",
            {**pass_step, "i5": 0},
            {"o3": 0, "o8": 0},
            "The 268-to-88 witness-compression metric must remain pinned.",
        ),
        TauCase(
            "linked_frontier_reject",
            {**pass_step, "i6": 0},
            {"o4": 0, "o8": 0},
            "The no-extra generated-state fact must stay linked to the frontier report.",
        ),
        TauCase(
            "witness_digest_reject",
            {**pass_step, "i7": 0},
            {"o6": 0, "o8": 0},
            "The witness-row digest must remain pinned.",
        ),
        TauCase(
            "linked_frontier_digest_reject",
            {**pass_step, "i8": 0},
            {"o6": 0, "o8": 0},
            "The linked frontier-row digest must remain pinned.",
        ),
        TauCase(
            "nondeterministic_replay_reject",
            {**pass_step, "i9": 0},
            {"o5": 0, "o8": 0},
            "The witness-compression checker replay must remain deterministic.",
        ),
        TauCase(
            "negative_controls_missing_reject",
            {**pass_step, "i10": 0},
            {"o5": 0, "o8": 0},
            "The mutation suite must keep rejecting malformed witness packets.",
        ),
        TauCase(
            "authority_boundary_reject",
            {**pass_step, "i11": 0},
            {"o7": 0, "o8": 0},
            "The research-only authority boundary must remain explicit.",
        ),
        TauCase(
            "authority_effect_reject",
            {**pass_step, "i12": 0},
            {"o7": 0, "o8": 0},
            "The certificate cannot carry settlement, state-root, governance, or pool-mutation authority.",
        ),
        TauCase(
            "empty_corpus_reject",
            {**pass_step, "i13": 0},
            {"o1": 0, "o8": 0},
            "The certificate must bind a nonempty sampled witness corpus.",
        ),
        TauCase(
            "normalized_source_hash_reject",
            {**pass_step, "i14": 0},
            {"o1": 0, "o8": 0, "o10": 0},
            "The normalized source report hash must match the pinned source packet.",
        ),
        TauCase(
            "volatile_elapsed_not_ignored_reject",
            {**pass_step, "i15": 0},
            {"o1": 0, "o8": 0},
            "The checker must explicitly use the elapsed-ms-normalized source hash.",
        ),
        TauCase(
            "inactive_safe",
            inactive,
            {"o8": 0, "o9": 1},
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
        if case.expected.get("o8") == 0 and got.get("o8") == 1:
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
    search = _search(source_report)
    linked = search.get("linked_frontier_summary", {})
    replay = source_report.get("deterministic_replay", {})
    facts = _fact_bundle(source_report)
    tau = _run_tau(facts)
    normalized_hash = _normalized_source_hash(source_report)
    return {
        "schema": (
            "zenodex.ab_reserve_state_child_frontier_witness_compression_n8_sample_tau_certificate_report.v1"
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
            "normalized_sha256": normalized_hash,
            "expected_normalized_sha256": EXPECTED_NORMALIZED_SOURCE_HASH,
            "normalization": "del(search.elapsed_ms)",
            "ok": bool(source_report.get("ok")),
            "schema": source_report.get("schema"),
            "search_schema": search.get("schema"),
            "replay_command": source_report.get("replay_command"),
        },
        "witness_corpus": {
            "case_count": search.get("case_count"),
            "valid_case_count": search.get("valid_case_count"),
            "sampled_child_mask_count": search.get("sampled_child_mask_count"),
            "witness_count": search.get("witness_count"),
            "expected_sampled_child_state_count": search.get(
                "expected_sampled_child_state_count"
            ),
            "covered_sampled_child_state_count": search.get(
                "covered_sampled_child_state_count"
            ),
            "missing_sampled_child_state_witness_count": search.get(
                "missing_sampled_child_state_witness_count"
            ),
            "extra_sampled_child_state_witness_count": search.get(
                "extra_sampled_child_state_witness_count"
            ),
            "invalid_witness_count": search.get("invalid_witness_count"),
            "duplicate_witness_count": search.get("duplicate_witness_count"),
            "predecessor_transition_count": search.get("predecessor_transition_count"),
            "witness_transition_checks_saved": search.get(
                "witness_transition_checks_saved"
            ),
            "witness_compression_ratio": search.get("witness_compression_ratio"),
            "witness_rows_digest": search.get("witness_rows_digest"),
            "linked_frontier_rows_digest": linked.get("frontier_rows_digest")
            if isinstance(linked, Mapping)
            else None,
            "deterministic_replay_hash": replay.get("first_hash")
            if isinstance(replay, Mapping)
            else None,
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
        },
        "linked_reports": {
            "frontier": linked if isinstance(linked, Mapping) else {},
        },
        "facts": facts,
        "tau": tau,
        "breakthrough": {
            "name": "AB reserve-state child-frontier witness-compression n8 sample Tau certificate",
            "spec_id": SPEC_ID,
            "tau_cases": len(tau["case_results"]),
            "invalid_accepts": tau["invalid_accepts"],
            "scoped_claims": [
                "the sampled n=8 witness-compression source report is present and normalized-hash-pinned",
                "88 witness rows cover 88 sampled child states",
                "268 predecessor transitions compress to 88 witness checks, saving 180 checks",
                "the no-extra generated-state fact is linked to the sampled n=8 frontier report",
                "witness, linked frontier, and normalized source-report digests are pinned",
                "9 mutation controls reject with zero accepts",
                "the Tau envelope carries no settlement or state authority",
            ],
        },
        "non_claims": [
            "This certificate is bounded to the deterministic sampled n=8 zero-min witness-compression report.",
            "This certificate does not prove exhaustive n=8 coverage.",
            "This certificate does not prove Python-to-Lean refinement.",
            "This certificate does not prove child-frontier generation in Lean.",
            "The no-extra generated-state fact is linked to the sampled n=8 frontier report, not reproved by the one-witness object alone.",
            "This certificate does not define canonical tie order or preserve order-id history.",
            "This certificate does not cover nonzero min_amount_out behavior.",
            "This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.",
        ],
        "hypothesis_card": {
            "hypothesis_id": "H-AB-N8-WITNESS-COMPRESSION-TAU-20260629",
            "status": "supported_bounded",
            "mechanism_change": "Add a versioned Tau scope certificate over sampled n=8 witness-compression proof-object evidence.",
            "null_hypothesis": "A Tau envelope gives no additional falsifiable boundary beyond the sampled n=8 Python witness checker.",
            "support_recipe": "Host checks the source report, linked frontier report, counts, compression metrics, and pinned digests; Tau rejects every missing-fact negative case.",
            "falsification_recipe": "Clear each required fact bit, mutate witness or linked digest pins, alter source semantic fields, or remove the no-authority rail and require Tau rejection.",
            "formal_obligations": "Production use still needs exhaustive coverage or a deeper Lean refinement of the child-frontier generation relation.",
        },
        "replay_command": (
            "python3 tools/check_ab_reserve_state_child_frontier_witness_compression_n8_sample_tau_certificate_20260629.py"
        ),
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX AB Reserve-State Child-Frontier Witness-Compression N8 Sample Tau Certificate - 2026-06-29",
        "",
        "## Executive Result",
        "",
        "`ab_reserve_state_child_frontier_witness_compression_n8_sample_scope_certificate_v1` admits the sampled n=8 witness-compression research bundle only when the source report, sampled n=8 zero-min scope, witness coverage, compression metric, linked frontier summary, digest pins, deterministic replay, negative controls, normalized source hash, elapsed-ms normalization declaration, and no-authority rail are all present.",
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
            "## Witness Pins",
            "",
            f"- Cases: `{report['witness_corpus']['case_count']}`",
            f"- Sampled child masks: `{report['witness_corpus']['sampled_child_mask_count']}`",
            f"- Witness rows: `{report['witness_corpus']['witness_count']}`",
            f"- Covered sampled child states: `{report['witness_corpus']['covered_sampled_child_state_count']}`",
            f"- Predecessor transitions: `{report['witness_corpus']['predecessor_transition_count']}`",
            f"- Checks saved: `{report['witness_corpus']['witness_transition_checks_saved']}`",
            f"- Compression ratio: `{report['witness_corpus']['witness_compression_ratio']}`",
            f"- Normalized source report hash: `{report['source_report']['normalized_sha256']}`",
            f"- Witness digest: `{report['witness_corpus']['witness_rows_digest']}`",
            f"- Linked frontier digest: `{report['witness_corpus']['linked_frontier_rows_digest']}`",
            f"- Deterministic replay hash: `{report['witness_corpus']['deterministic_replay_hash']}`",
            "",
            "## Tau Cases",
            "",
            "| case | ok | admitted |",
            "| --- | --- | ---: |",
        ]
    )
    for case in report["tau"]["case_results"]:
        lines.append(f"| `{case['case_id']}` | `{case['ok']}` | `{case['got'].get('o8')}` |")
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
                "breakthrough": report["breakthrough"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Replay the AB child-frontier bidirectional transition Tau certificate."""

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

SPEC_ID = "ab_child_frontier_bidirectional_transition_scope_certificate_v1"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / f"{SPEC_ID}.tau"
SOURCE_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_bidirectional_transition_20260629"
    / "report.json"
)
OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_bidirectional_transition_tau_certificate_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_CHILD_FRONTIER_BIDIRECTIONAL_TRANSITION_TAU_CERTIFICATE_20260629.md"
)

EXPECTED_SCHEMA = "zenodex.ab_reserve_state_child_frontier_bidirectional_transition_report.v1"
EXPECTED_SEARCH_SCHEMA = (
    "zenodex/ab_reserve_state_child_frontier_bidirectional_transition_search/v1"
)
EXPECTED_TRANSITION_ROWS_DIGEST = (
    "fccc26b63521b510776546e4663cecabcf58849af42bcda799484bf092a81f82"
)
EXPECTED_LINKED_BOUND_ROWS_DIGEST = (
    "0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551"
)
EXPECTED_DETERMINISTIC_HASH = (
    "54e80016a0c0dc4eb629d22b43265091b3b1c4dc75324320107b17dbd42668b7"
)
EXPECTED_CASE_COUNT = 4
EXPECTED_CHILD_MASK_COUNT = 508
EXPECTED_TRANSITION_ROW_COUNT = 2_777
EXPECTED_GENERATED_CHILD_COUNT = 864
EXPECTED_LINKED_CHILD_COVERAGE_COUNT = 864
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
        "missing_predecessor_transition_row",
        "transition_parent_state_not_in_parent_frontier",
        "afterstep_generated_child_mismatch",
        "transition_step_bit_out_of_range",
        "generated_state_root_mismatch",
        "membership_proof_hash_mismatch",
        "linked_witness_merkle_bound_row_count_mismatch",
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
        seen.add(str(control.get("expected_reason")))
    return (
        int(search.get("negative_control_count", -1)) == EXPECTED_NEGATIVE_CONTROL_COUNT
        and int(search.get("negative_control_accept_count", -1)) == 0
        and seen == expected_reason_classes
    )


def _fact_bundle(report: Mapping[str, Any]) -> dict[str, int]:
    search = _search(report)
    linked = search.get("linked_witness_merkle_summary", {})
    replay = report.get("deterministic_replay", {})
    non_claims_text = " ".join(str(item) for item in report.get("non_claims", []))

    source_report_ok = (
        bool(report.get("ok")) is True
        and report.get("schema") == EXPECTED_SCHEMA
        and search.get("schema") == EXPECTED_SEARCH_SCHEMA
    )
    n7_zero_min_scope_ok = _contains_all(
        non_claims_text,
        (
            "bounded to the committed n=7 randomized corpus",
            "zero-min exact-in cases",
            "does not prove child-frontier generation in lean",
            "does not cover nonzero min_amount_out behavior",
        ),
    )
    transition_counts_complete = (
        int(search.get("case_count", -1)) == EXPECTED_CASE_COUNT
        and int(search.get("valid_case_count", -1)) == EXPECTED_CASE_COUNT
        and int(search.get("child_mask_count", -1)) == EXPECTED_CHILD_MASK_COUNT
        and int(search.get("transition_row_count", -1)) == EXPECTED_TRANSITION_ROW_COUNT
        and int(search.get("expected_transition_count", -1)) == EXPECTED_TRANSITION_ROW_COUNT
        and int(search.get("covered_transition_count", -1)) == EXPECTED_TRANSITION_ROW_COUNT
        and int(search.get("unique_transition_count", -1)) == EXPECTED_TRANSITION_ROW_COUNT
        and int(search.get("missing_transition_count", -1)) == 0
        and int(search.get("extra_transition_count", -1)) == 0
        and int(search.get("invalid_transition_row_count", -1)) == 0
        and int(search.get("duplicate_transition_row_count", -1)) == 0
    )
    generated_child_count_ok = (
        int(search.get("unique_generated_child_count", -1))
        == EXPECTED_GENERATED_CHILD_COUNT
        and int(search.get("linked_child_coverage_witness_count", -1))
        == EXPECTED_LINKED_CHILD_COVERAGE_COUNT
    )
    linked_child_coverage_ok = (
        isinstance(linked, Mapping)
        and bool(linked.get("available")) is True
        and bool(linked.get("ok")) is True
        and linked.get("schema")
        == "zenodex.ab_reserve_state_child_frontier_witness_merkle_report.v1"
        and int(linked.get("case_count", -1)) == EXPECTED_CASE_COUNT
        and int(linked.get("valid_case_count", -1)) == EXPECTED_CASE_COUNT
        and int(linked.get("child_mask_count", -1)) == EXPECTED_CHILD_MASK_COUNT
        and int(linked.get("bound_row_count", -1)) == EXPECTED_GENERATED_CHILD_COUNT
        and int(linked.get("witness_count", -1)) == EXPECTED_GENERATED_CHILD_COUNT
        and int(linked.get("membership_count", -1)) == EXPECTED_GENERATED_CHILD_COUNT
        and int(linked.get("negative_control_accept_count", -1)) == 0
    )
    transition_digest_pinned = (
        search.get("transition_rows_digest") == EXPECTED_TRANSITION_ROWS_DIGEST
    )
    linked_digest_pinned = (
        isinstance(linked, Mapping)
        and linked.get("bound_rows_digest") == EXPECTED_LINKED_BOUND_ROWS_DIGEST
    )
    deterministic_replay_ok = (
        isinstance(replay, Mapping)
        and bool(replay.get("ok")) is True
        and replay.get("first_hash") == EXPECTED_DETERMINISTIC_HASH
        and replay.get("second_hash") == EXPECTED_DETERMINISTIC_HASH
    )
    corpus_nonvacuous = (
        int(search.get("case_count", 0)) > 0
        and int(search.get("transition_row_count", 0)) > 0
        and int(search.get("unique_generated_child_count", 0)) > 0
        and int(search.get("linked_child_coverage_witness_count", 0)) > 0
    )
    return {
        "source_report_ok": int(source_report_ok),
        "n7_zero_min_scope_ok": int(n7_zero_min_scope_ok),
        "transition_counts_complete": int(transition_counts_complete),
        "generated_child_count_ok": int(generated_child_count_ok),
        "linked_child_coverage_ok": int(linked_child_coverage_ok),
        "transition_digest_pinned": int(transition_digest_pinned),
        "linked_digest_pinned": int(linked_digest_pinned),
        "deterministic_replay_ok": int(deterministic_replay_ok),
        "negative_controls_reject": int(_negative_controls_reject(search)),
        "authority_boundary_ok": int(_authority_boundary_ok(report)),
        "no_authority_effect": 1,
        "corpus_nonvacuous": int(corpus_nonvacuous),
    }


def _tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    pass_step = {
        "i1": 1,
        "i2": int(facts["source_report_ok"]),
        "i3": int(facts["n7_zero_min_scope_ok"]),
        "i4": int(facts["transition_counts_complete"]),
        "i5": int(facts["generated_child_count_ok"]),
        "i6": int(facts["linked_child_coverage_ok"]),
        "i7": int(facts["transition_digest_pinned"]),
        "i8": int(facts["linked_digest_pinned"]),
        "i9": int(facts["deterministic_replay_ok"]),
        "i10": int(facts["negative_controls_reject"]),
        "i11": int(facts["authority_boundary_ok"]),
        "i12": int(facts["no_authority_effect"]),
        "i13": int(facts["corpus_nonvacuous"]),
    }
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauCase(
            "bidirectional_transition_certificate_pass",
            pass_step,
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1, "o7": 1, "o8": 0},
            "All scoped host facts admit the bidirectional transition certificate.",
        ),
        TauCase(
            "missing_source_report_reject",
            {**pass_step, "i2": 0},
            {"o1": 0, "o7": 0},
            "The source bidirectional report must be present, valid, and successful.",
        ),
        TauCase(
            "wrong_scope_reject",
            {**pass_step, "i3": 0},
            {"o1": 0, "o7": 0},
            "The source report must remain scoped to the bounded n=7 zero-min corpus.",
        ),
        TauCase(
            "transition_counts_reject",
            {**pass_step, "i4": 0},
            {"o2": 0, "o7": 0},
            "The 2,777 transition rows must exactly cover all expected transitions.",
        ),
        TauCase(
            "generated_child_count_reject",
            {**pass_step, "i5": 0},
            {"o2": 0, "o7": 0},
            "The transition rows must bind the 864 generated child states.",
        ),
        TauCase(
            "linked_child_coverage_reject",
            {**pass_step, "i6": 0},
            {"o3": 0, "o7": 0},
            "The child coverage direction must remain linked to the witness+Merkle report.",
        ),
        TauCase(
            "transition_digest_reject",
            {**pass_step, "i7": 0},
            {"o5": 0, "o7": 0},
            "The transition-row digest must remain pinned.",
        ),
        TauCase(
            "linked_digest_reject",
            {**pass_step, "i8": 0},
            {"o3": 0, "o5": 0, "o7": 0},
            "The linked witness+Merkle digest must remain pinned.",
        ),
        TauCase(
            "nondeterministic_replay_reject",
            {**pass_step, "i9": 0},
            {"o4": 0, "o7": 0},
            "The bidirectional checker replay must remain deterministic.",
        ),
        TauCase(
            "negative_controls_missing_reject",
            {**pass_step, "i10": 0},
            {"o4": 0, "o7": 0},
            "The mutation suite must keep rejecting malformed packets.",
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
    search = _search(source_report)
    linked = search.get("linked_witness_merkle_summary", {})
    facts = _fact_bundle(source_report)
    tau = _run_tau(facts)
    return {
        "schema": "zenodex.ab_child_frontier_bidirectional_transition_tau_certificate_report.v1",
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
            "ok": bool(source_report.get("ok")),
            "schema": source_report.get("schema"),
            "replay_command": source_report.get("replay_command"),
        },
        "transition_corpus": {
            "case_count": search.get("case_count"),
            "child_mask_count": search.get("child_mask_count"),
            "transition_row_count": search.get("transition_row_count"),
            "expected_transition_count": search.get("expected_transition_count"),
            "covered_transition_count": search.get("covered_transition_count"),
            "unique_transition_count": search.get("unique_transition_count"),
            "unique_generated_child_count": search.get("unique_generated_child_count"),
            "linked_child_coverage_witness_count": search.get(
                "linked_child_coverage_witness_count"
            ),
            "transition_rows_digest": search.get("transition_rows_digest"),
            "linked_bound_rows_digest": linked.get("bound_rows_digest")
            if isinstance(linked, Mapping)
            else None,
            "deterministic_replay_hash": source_report.get("deterministic_replay", {}).get(
                "first_hash"
            ),
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
        },
        "facts": facts,
        "tau": tau,
        "breakthrough": {
            "name": "AB child-frontier bidirectional transition Tau certificate",
            "spec_id": SPEC_ID,
            "tau_cases": len(tau["case_results"]),
            "invalid_accepts": tau["invalid_accepts"],
            "scoped_claims": [
                "the n=7 bidirectional transition source report is present and successful",
                "2,777 transition rows exactly cover all expected predecessor transitions",
                "864 generated child states are linked to the existing witness+Merkle child-coverage report",
                "transition and linked witness+Merkle digests are pinned",
                "9 mutation controls reject with zero accepts",
                "the Tau envelope carries no settlement or state authority",
            ],
        },
        "non_claims": [
            "This certificate is bounded to the committed n=7 zero-min bidirectional transition report.",
            "This certificate links the child coverage direction to the existing witness+Merkle report.",
            "This certificate does not prove Python-to-Lean refinement.",
            "This certificate does not prove child-frontier generation in Lean.",
            "This certificate does not replace the host Merkle verifier or transition checker.",
            "This certificate does not cover nonzero min_amount_out behavior.",
            "This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.",
        ],
        "hypothesis_card": {
            "hypothesis_id": "H-AB-N7-BIDIR-TRANSITION-TAU-20260629",
            "status": "supported_bounded",
            "mechanism_change": "Add a versioned Tau scope certificate over the bidirectional transition closure evidence.",
            "null_hypothesis": "A Tau envelope gives no additional falsifiable boundary beyond the Python bidirectional transition checker.",
            "support_recipe": "Host checks the source report and pinned digests, Tau rejects every missing-fact negative case.",
            "falsification_recipe": "Clear each required fact bit, mutate digest pins, or remove the no-authority rail and require Tau rejection.",
            "formal_obligations": "Production use still needs a deterministic generated-image producer or a deeper Lean refinement of the child-frontier generation relation.",
        },
        "replay_command": "python3 tools/check_ab_child_frontier_bidirectional_transition_tau_certificate_20260629.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX AB Child-Frontier Bidirectional Transition Tau Certificate - 2026-06-29",
        "",
        "## Executive Result",
        "",
        "`ab_child_frontier_bidirectional_transition_scope_certificate_v1` admits the bidirectional transition research bundle only when the source report, n=7 zero-min scope, transition-row coverage, generated-child count, linked child-coverage evidence, digest pins, deterministic replay, negative controls, and no-authority rail are all present.",
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
            "## Transition Pins",
            "",
            f"- Transition rows: `{report['transition_corpus']['transition_row_count']}`",
            f"- Expected transitions: `{report['transition_corpus']['expected_transition_count']}`",
            f"- Covered transitions: `{report['transition_corpus']['covered_transition_count']}`",
            f"- Unique generated child states: `{report['transition_corpus']['unique_generated_child_count']}`",
            f"- Linked child coverage witnesses: `{report['transition_corpus']['linked_child_coverage_witness_count']}`",
            f"- Transition digest: `{report['transition_corpus']['transition_rows_digest']}`",
            f"- Linked witness+Merkle digest: `{report['transition_corpus']['linked_bound_rows_digest']}`",
            f"- Deterministic replay hash: `{report['transition_corpus']['deterministic_replay_hash']}`",
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
                "breakthrough": report["breakthrough"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

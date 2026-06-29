#!/usr/bin/env python3
"""Replay the AB child-frontier corpus-root Tau scope certificate."""

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

SPEC_ID = "ab_child_frontier_corpus_root_scope_certificate_v1"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / f"{SPEC_ID}.tau"
SOURCE_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_corpus_root_20260629"
    / "report.json"
)
OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_child_frontier_corpus_root_tau_certificate_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_CHILD_FRONTIER_CORPUS_ROOT_TAU_CERTIFICATE_20260629.md"

EXPECTED_SCHEMA = "zenodex.ab_reserve_state_child_frontier_corpus_root_report.v1"
EXPECTED_CORPUS_ROOT = "8f4a1a08cf51215cdc9fd382dd2538cc199db35b87597aa9c468358925dfd3b0"
EXPECTED_CASE_SUMMARIES_DIGEST = "afd7706fd7ea10cee0df44d7578dabf44fc82a26d238f814d717c5fee3b5bc28"
EXPECTED_ROW_RECEIPTS_DIGEST = "d52f8c24411e841ae777999d6bfd3ec3fef5bb0a26cd98887f4e0a5902c0f092"
EXPECTED_LINKED_CROSS_BINDING_DIGEST = "0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551"
EXPECTED_DETERMINISTIC_HASH = "b857b66aa96007bda748ae9489ee10f972248eaa30af25fd5ac7dffca73f4591"
EXPECTED_CASE_COUNT = 4
EXPECTED_ROW_RECEIPT_COUNT = 864
EXPECTED_NEGATIVE_CONTROL_COUNT = 10
EXPECTED_LINKED_CHILD_MASK_COUNT = 508


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
        "research_only_no_settlement_or_state_authority" in text
        and "no settlement" in text
        and "state-root" in text
        and "production" in text
        and "governance" in text
        and "pool-mutation" in text
    )


def _negative_controls_reject(search: Mapping[str, Any]) -> bool:
    controls = search.get("negative_controls")
    if not isinstance(controls, list):
        return False
    expected_reason_classes = {
        "packet_hash_mismatch",
        "row_hash_mismatch",
        "row_membership_hash_mismatch",
        "case_row_root_mismatch",
        "case_membership_hash_mismatch",
        "missing_row_receipt",
        "duplicate_row_receipt",
        "case_index_out_of_range",
        "linked_cross_binding_bound_row_count_mismatch",
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
        seen.add(str(control.get("mutation_id")))
    return (
        int(search.get("negative_control_count", -1)) == EXPECTED_NEGATIVE_CONTROL_COUNT
        and int(search.get("negative_control_accept_count", -1)) == 0
        and seen == expected_reason_classes
    )


def _fact_bundle(report: Mapping[str, Any]) -> dict[str, int]:
    search = _search(report)
    coverage = search.get("coverage", {})
    linked = search.get("linked_cross_binding_summary", {})
    replay = report.get("deterministic_replay", {})
    non_claims_text = " ".join(str(item) for item in report.get("non_claims", []))

    source_report_ok = (
        bool(report.get("ok")) is True
        and report.get("schema") == EXPECTED_SCHEMA
        and bool(search.get("verification", {}).get("ok")) is True
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
    corpus_root_pinned = (
        search.get("corpus_root") == EXPECTED_CORPUS_ROOT
        and search.get("expected_corpus_root") == EXPECTED_CORPUS_ROOT
        and bool(search.get("corpus_root_matches")) is True
    )
    case_roots_covered = (
        int(search.get("case_count", -1)) == EXPECTED_CASE_COUNT
        and int(search.get("expected_case_count", -2)) == EXPECTED_CASE_COUNT
        and len(search.get("case_summaries", [])) == EXPECTED_CASE_COUNT
        and int(search.get("max_case_row_count", 0)) == 320
        and search.get("coverage", {}).get("n_counts") == {"7": EXPECTED_CASE_COUNT}
        and coverage.get("case_row_count_histogram") == {"127": 2, "290": 1, "320": 1}
    )
    row_receipts_complete = (
        int(search.get("row_receipt_count", -1)) == EXPECTED_ROW_RECEIPT_COUNT
        and int(search.get("expected_row_receipt_count", -2)) == EXPECTED_ROW_RECEIPT_COUNT
        and int(search.get("covered_row_receipt_count", -3)) == EXPECTED_ROW_RECEIPT_COUNT
        and int(search.get("missing_row_receipt_count", -1)) == 0
        and int(search.get("extra_row_receipt_count", -1)) == 0
        and int(search.get("invalid_row_receipt_count", -1)) == 0
        and int(search.get("duplicate_row_receipt_count", -1)) == 0
    )
    membership_proofs_clean = (
        int(search.get("case_root_mismatch_count", -1)) == 0
        and int(search.get("corpus_root_mismatch_count", -1)) == 0
        and int(search.get("row_membership_mismatch_count", -1)) == 0
    )
    negative_controls_reject = _negative_controls_reject(search)
    deterministic_replay_ok = (
        isinstance(replay, Mapping)
        and bool(replay.get("ok")) is True
        and replay.get("first_hash") == EXPECTED_DETERMINISTIC_HASH
        and replay.get("second_hash") == EXPECTED_DETERMINISTIC_HASH
    )
    linked_cross_binding_ok = (
        isinstance(linked, Mapping)
        and bool(linked.get("available")) is True
        and bool(linked.get("ok")) is True
        and linked.get("schema") == "zenodex.ab_reserve_state_child_frontier_witness_merkle_report.v1"
        and int(linked.get("case_count", -1)) == EXPECTED_CASE_COUNT
        and int(linked.get("valid_case_count", -1)) == EXPECTED_CASE_COUNT
        and int(linked.get("child_mask_count", -1)) == EXPECTED_LINKED_CHILD_MASK_COUNT
        and int(linked.get("bound_row_count", -1)) == EXPECTED_ROW_RECEIPT_COUNT
        and int(linked.get("witness_count", -1)) == EXPECTED_ROW_RECEIPT_COUNT
        and int(linked.get("membership_count", -1)) == EXPECTED_ROW_RECEIPT_COUNT
        and int(linked.get("negative_control_accept_count", -1)) == 0
        and linked.get("bound_rows_digest") == EXPECTED_LINKED_CROSS_BINDING_DIGEST
    )
    digest_pins_ok = (
        search.get("case_summaries_digest") == EXPECTED_CASE_SUMMARIES_DIGEST
        and search.get("row_receipts_digest") == EXPECTED_ROW_RECEIPTS_DIGEST
        and linked.get("bound_rows_digest") == EXPECTED_LINKED_CROSS_BINDING_DIGEST
        and replay.get("first_hash") == EXPECTED_DETERMINISTIC_HASH
    )
    corpus_nonvacuous = (
        int(search.get("case_count", 0)) > 0
        and int(search.get("row_receipt_count", 0)) > 0
        and int(search.get("covered_row_receipt_count", 0)) > 0
        and int(linked.get("child_mask_count", 0)) > 0
    )
    return {
        "source_report_ok": int(source_report_ok),
        "n7_zero_min_scope_ok": int(n7_zero_min_scope_ok),
        "corpus_root_pinned": int(corpus_root_pinned),
        "case_roots_covered": int(case_roots_covered),
        "row_receipts_complete": int(row_receipts_complete),
        "membership_proofs_clean": int(membership_proofs_clean),
        "negative_controls_reject": int(negative_controls_reject),
        "deterministic_replay_ok": int(deterministic_replay_ok),
        "linked_cross_binding_ok": int(linked_cross_binding_ok),
        "digest_pins_ok": int(digest_pins_ok),
        "authority_boundary_ok": int(_authority_boundary_ok(report)),
        "no_authority_effect": 1,
        "corpus_nonvacuous": int(corpus_nonvacuous),
    }


def _tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    pass_step = {
        "i1": 1,
        "i2": int(facts["source_report_ok"]),
        "i3": int(facts["n7_zero_min_scope_ok"]),
        "i4": int(facts["corpus_root_pinned"]),
        "i5": int(facts["case_roots_covered"]),
        "i6": int(facts["row_receipts_complete"]),
        "i7": int(facts["membership_proofs_clean"]),
        "i8": int(facts["negative_controls_reject"]),
        "i9": int(facts["deterministic_replay_ok"]),
        "i10": int(facts["linked_cross_binding_ok"]),
        "i11": int(facts["digest_pins_ok"]),
        "i12": int(facts["authority_boundary_ok"]),
        "i13": int(facts["no_authority_effect"]),
        "i14": int(facts["corpus_nonvacuous"]),
    }
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauCase(
            "corpus_root_certificate_pass",
            pass_step,
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1, "o7": 1, "o8": 0},
            "All scoped host facts admit the corpus-root research certificate.",
        ),
        TauCase(
            "missing_source_report_reject",
            {**pass_step, "i2": 0},
            {"o1": 0, "o7": 0},
            "The source corpus-root report must be present, valid, and successful.",
        ),
        TauCase(
            "wrong_scope_reject",
            {**pass_step, "i3": 0},
            {"o1": 0, "o7": 0},
            "The source report must remain scoped to the bounded n=7 zero-min corpus.",
        ),
        TauCase(
            "wrong_corpus_root_reject",
            {**pass_step, "i4": 0},
            {"o2": 0, "o7": 0},
            "The pinned corpus root must match the expected digest.",
        ),
        TauCase(
            "missing_case_roots_reject",
            {**pass_step, "i5": 0},
            {"o2": 0, "o7": 0},
            "All four case roots must remain covered.",
        ),
        TauCase(
            "missing_row_receipts_reject",
            {**pass_step, "i6": 0},
            {"o3": 0, "o7": 0},
            "All 864 row receipts must remain complete.",
        ),
        TauCase(
            "membership_mismatch_reject",
            {**pass_step, "i7": 0},
            {"o3": 0, "o7": 0},
            "Row, case, and corpus membership proofs must remain clean.",
        ),
        TauCase(
            "negative_controls_missing_reject",
            {**pass_step, "i8": 0},
            {"o4": 0, "o7": 0},
            "The mutation suite must keep rejecting malformed packets.",
        ),
        TauCase(
            "nondeterministic_replay_reject",
            {**pass_step, "i9": 0},
            {"o4": 0, "o7": 0},
            "The parent corpus-root replay must remain deterministic.",
        ),
        TauCase(
            "linked_cross_binding_reject",
            {**pass_step, "i10": 0},
            {"o5": 0, "o7": 0},
            "The corpus root must remain linked to the witness+Merkle cross-binding report.",
        ),
        TauCase(
            "digest_pin_reject",
            {**pass_step, "i11": 0},
            {"o2": 0, "o5": 0, "o7": 0},
            "The row, case, linked, and deterministic replay digests must remain pinned.",
        ),
        TauCase(
            "authority_boundary_reject",
            {**pass_step, "i12": 0},
            {"o6": 0, "o7": 0},
            "The research-only authority boundary must remain explicit.",
        ),
        TauCase(
            "authority_effect_reject",
            {**pass_step, "i13": 0},
            {"o6": 0, "o7": 0},
            "The certificate cannot carry settlement, state-root, governance, or pool-mutation authority.",
        ),
        TauCase(
            "empty_corpus_reject",
            {**pass_step, "i14": 0},
            {"o1": 0, "o7": 0},
            "The certificate must bind a nonempty row and case corpus.",
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
    linked = search.get("linked_cross_binding_summary", {})
    facts = _fact_bundle(source_report)
    tau = _run_tau(facts)
    return {
        "schema": "zenodex.ab_child_frontier_corpus_root_tau_certificate_report.v1",
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
        "corpus": {
            "case_count": search.get("case_count"),
            "row_receipt_count": search.get("row_receipt_count"),
            "covered_row_receipt_count": search.get("covered_row_receipt_count"),
            "corpus_root": search.get("corpus_root"),
            "case_summaries_digest": search.get("case_summaries_digest"),
            "row_receipts_digest": search.get("row_receipts_digest"),
            "linked_cross_binding_digest": linked.get("bound_rows_digest") if isinstance(linked, Mapping) else None,
            "deterministic_replay_hash": source_report.get("deterministic_replay", {}).get("first_hash"),
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
        },
        "facts": facts,
        "tau": tau,
        "breakthrough": {
            "name": "AB child-frontier corpus-root Tau certificate",
            "spec_id": SPEC_ID,
            "tau_cases": len(tau["case_results"]),
            "invalid_accepts": tau["invalid_accepts"],
            "scoped_claims": [
                "the n=7 corpus-root source report is present and successful",
                "the corpus root, row digest, case digest, linked digest, and deterministic replay digest are pinned",
                "864 row receipts are complete across four case roots",
                "row, case, and corpus membership mismatches are zero",
                "10 mutation controls reject with zero accepts",
                "the Tau envelope carries no settlement or state authority",
            ],
        },
        "non_claims": [
            "This certificate is bounded to the committed n=7 zero-min corpus-root report.",
            "This certificate does not prove Python-to-Lean refinement.",
            "This certificate does not prove child-frontier generation in Lean.",
            "This certificate does not replace the host Merkle verifier.",
            "This certificate does not cover nonzero min_amount_out behavior.",
            "This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.",
        ],
        "hypothesis_card": {
            "hypothesis_id": "H-AB-N7-CORPUS-ROOT-TAU-20260629",
            "status": "supported_bounded",
            "mechanism_change": "Add a versioned Tau scope certificate over the corpus-root membership evidence.",
            "null_hypothesis": "A Tau envelope gives no additional falsifiable boundary beyond the Python corpus-root checker.",
            "support_recipe": "Host checks the source report and pinned digests, Tau rejects every missing-fact negative case.",
            "falsification_recipe": "Clear each required fact bit, mutate digest pins, or remove the no-authority rail and require Tau rejection.",
            "formal_obligations": "Production use still needs a deterministic generated-image producer or a deeper Lean refinement of the corpus-root membership relation.",
        },
        "replay_command": "python3 tools/check_ab_child_frontier_corpus_root_tau_certificate_20260629.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX AB Child-Frontier Corpus-Root Tau Certificate - 2026-06-29",
        "",
        "## Executive Result",
        "",
        "`ab_child_frontier_corpus_root_scope_certificate_v1` admits the corpus-root research bundle only when the source report, n=7 zero-min scope, pinned corpus root, case roots, row receipts, membership checks, linked cross-binding digest, deterministic replay, negative controls, and no-authority rail are all present.",
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
            "## Corpus Pins",
            "",
            f"- Corpus root: `{report['corpus']['corpus_root']}`",
            f"- Case summaries digest: `{report['corpus']['case_summaries_digest']}`",
            f"- Row receipts digest: `{report['corpus']['row_receipts_digest']}`",
            f"- Linked cross-binding digest: `{report['corpus']['linked_cross_binding_digest']}`",
            f"- Deterministic replay hash: `{report['corpus']['deterministic_replay_hash']}`",
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

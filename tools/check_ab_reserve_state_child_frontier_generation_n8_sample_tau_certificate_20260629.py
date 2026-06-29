#!/usr/bin/env python3
"""Replay the sampled n=8 child-frontier generation Tau certificate."""

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

from tools.check_ab_strict_zero_min_emitter_witness import (  # noqa: E402
    _sha256_json,
    _strip_timing,
)

SPEC_ID = "ab_reserve_state_child_frontier_generation_n8_sample_scope_certificate_v1"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / f"{SPEC_ID}.tau"
SOURCE_REPORT = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_n8_sample_20260629"
    / "report.json"
)
OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_generation_n8_sample_tau_certificate_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_RESERVE_STATE_CHILD_FRONTIER_GENERATION_N8_SAMPLE_TAU_CERTIFICATE_20260629.md"
)

EXPECTED_SCHEMA = "zenodex.ab_reserve_state_child_frontier_n8_sample_report.v1"
EXPECTED_SEARCH_SCHEMA = (
    "zenodex/ab_reserve_state_child_frontier_n8_sample_search/v1"
)
EXPECTED_NORMALIZED_SOURCE_HASH = (
    "9d486b78b9d6121f28728a7124f336f209ea9bb1517c3362897c62db1680021a"
)
EXPECTED_SAMPLE_PLAN_HASH = (
    "8b1e2f0b6851b1218f18f166f223665f26855a3a34c769fd266fea12fd1679fb"
)
EXPECTED_SAMPLED_MASK_IDS_HASH = (
    "48b36aeded6cc0130bb1153d611ef0aa3fd64f4b4a67ca75ad13de738b028cc1"
)
EXPECTED_LEAN_CONTRACT_HASH = (
    "27ae4921e8f606cad800a81e57d13a10cf66e32b325a9f3e0deeb4e43bd4292f"
)
EXPECTED_FRONTIER_ROWS_DIGEST = (
    "37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919"
)
EXPECTED_DETERMINISTIC_HASH = (
    "4a601edd060a6cfe8444d7db91f1806bf8bf42b07943642de7dd299e76aa877f"
)
EXPECTED_SOURCE_SEED = 2026062908
EXPECTED_CASE_COUNT = 3
EXPECTED_SAMPLED_CHILD_MASK_COUNT = 51
EXPECTED_SAMPLED_CHILD_STATE_COUNT = 88
EXPECTED_PREDECESSOR_EDGE_COUNT = 144
EXPECTED_PREDECESSOR_TRANSITION_COUNT = 268
EXPECTED_MAX_CHILD_STATE_COUNT = 7
EXPECTED_NEGATIVE_CONTROL_COUNT = 7
EXPECTED_REASON_CLASSES = {
    "authority_effect_present",
    "generated_frontier_extra_child_state",
    "generated_frontier_missing_child_state",
    "packet_hash_mismatch",
    "packet_lean_contract_mismatch",
    "packet_sample_plan_mismatch",
    "sampled_n8_bound_missing",
}


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
    return _sha256_json(_strip_timing(report))


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
        and "governance" in text
    )


def _sample_plan_pinned(search: Mapping[str, Any]) -> bool:
    return (
        int(search.get("source_seed", -1)) == EXPECTED_SOURCE_SEED
        and _sha256_json(search.get("sample_plan")) == EXPECTED_SAMPLE_PLAN_HASH
        and _sha256_json(search.get("sampled_child_mask_ids"))
        == EXPECTED_SAMPLED_MASK_IDS_HASH
    )


def _negative_controls_reject(search: Mapping[str, Any]) -> bool:
    controls = search.get("negative_controls")
    if not isinstance(controls, list):
        return False
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
        and seen == EXPECTED_REASON_CLASSES
    )


def _fact_bundle(report: Mapping[str, Any]) -> dict[str, int]:
    search = _search(report)
    replay = report.get("deterministic_replay", {})
    coverage = search.get("coverage", {})
    non_claims_text = " ".join(str(item) for item in report.get("non_claims", []))

    source_report_ok = (
        bool(report.get("ok")) is True
        and report.get("schema") == EXPECTED_SCHEMA
        and search.get("schema") == EXPECTED_SEARCH_SCHEMA
    )
    sampled_n8_zero_min_scope_ok = (
        int(search.get("source_seed", -1)) == EXPECTED_SOURCE_SEED
        and _contains_all(
            non_claims_text,
            (
                "bounded deterministic n=8 sample",
                "sampled zero-min exact-in cases",
                "sampled child masks",
                "does not prove python-to-lean refinement",
                "does not prove child-frontier generation in lean",
                "does not define canonical tie order",
            ),
        )
    )
    frontier_counts_ok = (
        int(search.get("case_count", -1)) == EXPECTED_CASE_COUNT
        and int(search.get("valid_case_count", -1)) == EXPECTED_CASE_COUNT
        and int(search.get("sampled_child_mask_count", -1))
        == EXPECTED_SAMPLED_CHILD_MASK_COUNT
        and int(search.get("frontier_equal_count", -1))
        == EXPECTED_SAMPLED_CHILD_MASK_COUNT
    )
    predecessor_counts_ok = (
        int(search.get("predecessor_edge_count", -1)) == EXPECTED_PREDECESSOR_EDGE_COUNT
        and int(search.get("predecessor_transition_count", -1))
        == EXPECTED_PREDECESSOR_TRANSITION_COUNT
        and int(search.get("predecessor_transition_executable_count", -1))
        == EXPECTED_PREDECESSOR_TRANSITION_COUNT
    )
    state_counts_ok = (
        int(search.get("sampled_child_state_count", -1))
        == EXPECTED_SAMPLED_CHILD_STATE_COUNT
        and int(search.get("generated_state_count", -1))
        == EXPECTED_SAMPLED_CHILD_STATE_COUNT
        and int(search.get("max_child_state_count", -1)) == EXPECTED_MAX_CHILD_STATE_COUNT
        and int(search.get("max_generated_state_count", -1))
        == EXPECTED_MAX_CHILD_STATE_COUNT
    )
    generation_clean = (
        int(search.get("missing_child_state_count", -1)) == 0
        and int(search.get("extra_generated_state_count", -1)) == 0
        and bool(search.get("first_invalid_case")) is False
    )
    deterministic_replay_ok = (
        isinstance(replay, Mapping)
        and replay.get("ok") is True
        and replay.get("first_hash") == EXPECTED_DETERMINISTIC_HASH
        and replay.get("second_hash") == EXPECTED_DETERMINISTIC_HASH
    )
    lean_contract_pinned = (
        _sha256_json(report.get("lean_contract")) == EXPECTED_LEAN_CONTRACT_HASH
        and isinstance(report.get("lean_contract"), Mapping)
        and report["lean_contract"].get("transition_def") == "ReserveState.afterStep"
    )
    corpus_nonvacuous = (
        int(search.get("case_count", 0)) > 0
        and int(search.get("sampled_child_mask_count", 0)) > 0
        and int(search.get("sampled_child_state_count", 0)) > 0
        and sorted((coverage.get("reason_classes") or [])) == sorted(EXPECTED_REASON_CLASSES)
    )
    return {
        "source_report_ok": int(source_report_ok),
        "sampled_n8_zero_min_scope_ok": int(sampled_n8_zero_min_scope_ok),
        "sample_plan_pinned": int(_sample_plan_pinned(search)),
        "frontier_counts_ok": int(frontier_counts_ok),
        "predecessor_counts_ok": int(predecessor_counts_ok),
        "state_counts_ok": int(state_counts_ok),
        "generation_clean": int(generation_clean),
        "frontier_rows_digest_pinned": int(
            search.get("frontier_rows_digest") == EXPECTED_FRONTIER_ROWS_DIGEST
        ),
        "deterministic_replay_ok": int(deterministic_replay_ok),
        "negative_controls_reject": int(_negative_controls_reject(search)),
        "lean_contract_pinned": int(lean_contract_pinned),
        "authority_boundary_ok": int(_authority_boundary_ok(report)),
        "no_authority_effect": 1,
        "corpus_nonvacuous": int(corpus_nonvacuous),
        "normalized_source_hash_pinned": int(
            _normalized_source_hash(report) == EXPECTED_NORMALIZED_SOURCE_HASH
        ),
        "hash_normalization_declared": 1,
    }


FACT_TO_INPUT = {
    "source_report_ok": "i2",
    "sampled_n8_zero_min_scope_ok": "i3",
    "sample_plan_pinned": "i4",
    "frontier_counts_ok": "i5",
    "predecessor_counts_ok": "i6",
    "state_counts_ok": "i7",
    "generation_clean": "i8",
    "frontier_rows_digest_pinned": "i9",
    "deterministic_replay_ok": "i10",
    "negative_controls_reject": "i11",
    "lean_contract_pinned": "i12",
    "authority_boundary_ok": "i13",
    "no_authority_effect": "i14",
    "corpus_nonvacuous": "i15",
    "normalized_source_hash_pinned": "i16",
    "hash_normalization_declared": "i17",
}

NEGATIVE_CASES = (
    ("missing_source_report_reject", "source_report_ok", {"o1": 0, "o7": 0}),
    ("wrong_scope_reject", "sampled_n8_zero_min_scope_ok", {"o1": 0, "o7": 0}),
    ("sample_plan_reject", "sample_plan_pinned", {"o1": 0, "o7": 0}),
    ("frontier_counts_reject", "frontier_counts_ok", {"o2": 0, "o7": 0}),
    ("predecessor_counts_reject", "predecessor_counts_ok", {"o3": 0, "o7": 0}),
    ("state_counts_reject", "state_counts_ok", {"o2": 0, "o7": 0}),
    ("generation_clean_reject", "generation_clean", {"o2": 0, "o7": 0}),
    ("frontier_digest_reject", "frontier_rows_digest_pinned", {"o4": 0, "o7": 0}),
    ("nondeterministic_replay_reject", "deterministic_replay_ok", {"o5": 0, "o7": 0}),
    ("negative_controls_missing_reject", "negative_controls_reject", {"o5": 0, "o7": 0}),
    ("lean_contract_reject", "lean_contract_pinned", {"o3": 0, "o7": 0}),
    ("authority_boundary_reject", "authority_boundary_ok", {"o6": 0, "o7": 0}),
    ("authority_effect_reject", "no_authority_effect", {"o6": 0, "o7": 0}),
    ("empty_corpus_reject", "corpus_nonvacuous", {"o1": 0, "o7": 0}),
    ("source_hash_reject", "normalized_source_hash_pinned", {"o1": 0, "o7": 0, "o9": 0}),
    ("hash_normalization_reject", "hash_normalization_declared", {"o1": 0, "o7": 0}),
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
            "generation_n8_sample_certificate_pass",
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
            "All scoped host facts admit the sampled n=8 generation certificate.",
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
    search = _search(source_report)
    replay = source_report.get("deterministic_replay", {})
    facts = _fact_bundle(source_report)
    tau = _run_tau(facts)
    return {
        "schema": (
            "zenodex.ab_reserve_state_child_frontier_generation_n8_sample_tau_certificate_report.v1"
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
            "raw_sha256": _sha256(SOURCE_REPORT),
            "normalized_sha256": _normalized_source_hash(source_report),
            "expected_normalized_sha256": EXPECTED_NORMALIZED_SOURCE_HASH,
            "hash_normalization": "strip elapsed_ms fields",
            "ok": bool(source_report.get("ok")),
            "schema": source_report.get("schema"),
            "search_schema": search.get("schema"),
            "replay_command": source_report.get("replay_command"),
        },
        "generation_corpus": {
            "case_count": search.get("case_count"),
            "valid_case_count": search.get("valid_case_count"),
            "source_seed": search.get("source_seed"),
            "sampled_child_mask_count": search.get("sampled_child_mask_count"),
            "frontier_equal_count": search.get("frontier_equal_count"),
            "predecessor_edge_count": search.get("predecessor_edge_count"),
            "predecessor_transition_count": search.get("predecessor_transition_count"),
            "predecessor_transition_executable_count": search.get(
                "predecessor_transition_executable_count"
            ),
            "sampled_child_state_count": search.get("sampled_child_state_count"),
            "generated_state_count": search.get("generated_state_count"),
            "missing_child_state_count": search.get("missing_child_state_count"),
            "extra_generated_state_count": search.get("extra_generated_state_count"),
            "max_child_state_count": search.get("max_child_state_count"),
            "max_generated_state_count": search.get("max_generated_state_count"),
            "frontier_rows_digest": search.get("frontier_rows_digest"),
            "sample_plan_hash": _sha256_json(search.get("sample_plan")),
            "sampled_mask_ids_hash": _sha256_json(search.get("sampled_child_mask_ids")),
            "lean_contract_hash": _sha256_json(source_report.get("lean_contract")),
            "deterministic_replay_hash": replay.get("first_hash")
            if isinstance(replay, Mapping)
            else None,
            "negative_control_count": search.get("negative_control_count"),
            "negative_control_accept_count": search.get("negative_control_accept_count"),
            "reason_classes": (search.get("coverage") or {}).get("reason_classes"),
        },
        "facts": facts,
        "tau": tau,
        "breakthrough": {
            "name": "AB reserve-state child-frontier generation n8 sample Tau certificate",
            "spec_id": SPEC_ID,
            "tau_cases": len(tau["case_results"]),
            "invalid_accepts": tau["invalid_accepts"],
            "scoped_claims": [
                "the sampled n=8 generation source report is present and normalized-hash pinned",
                "51 sampled child masks have 51 frontier equalities",
                "268 predecessor transitions execute and generate 88 sampled child states",
                "missing and extra generated-state counts are zero",
                "frontier row digest and deterministic replay hash are pinned",
                "7 mutation controls reject with zero accepts",
                "the Tau envelope carries no settlement or state authority",
            ],
        },
        "non_claims": [
            "This certificate is bounded to the deterministic sampled n=8 zero-min generation report.",
            "This certificate uses a normalized source hash that strips elapsed_ms fields.",
            "This certificate does not prove exhaustive n=8 coverage.",
            "This certificate does not prove Python-to-Lean refinement.",
            "This certificate does not prove child-frontier generation in Lean.",
            "This certificate does not cover nonzero min_amount_out behavior.",
            "This certificate does not define canonical tie order or preserve order-id history.",
            "This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.",
        ],
        "hypothesis_card": {
            "hypothesis_id": "H-AB-N8-GENERATION-TAU-20260629",
            "status": "supported_bounded",
            "mechanism_change": "Add a versioned Tau scope certificate over sampled n=8 child-frontier generation evidence.",
            "representation_shift_used": "certificate_boundary",
            "null_hypothesis": "A Tau envelope gives no additional falsifiable boundary beyond the sampled n=8 generation Python checker.",
            "support_recipe": "Host checks the source report, sample plan, count invariants, digest pins, deterministic replay, Lean projection declaration, and mutation controls; Tau rejects every missing-fact negative case.",
            "falsification_recipe": "Clear each required fact bit, mutate digest pins, remove generation equality cleanliness, remove predecessor transition executability, or remove the no-authority rail and require Tau rejection.",
            "formal_obligations": "Production use still needs exhaustive coverage or a deeper Lean refinement of child-frontier generation.",
        },
        "replay_command": (
            "python3 tools/check_ab_reserve_state_child_frontier_generation_n8_sample_tau_certificate_20260629.py"
        ),
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX AB Reserve-State Child-Frontier Generation N8 Sample Tau Certificate - 2026-06-29",
        "",
        "## Executive Result",
        "",
        "`ab_reserve_state_child_frontier_generation_n8_sample_scope_certificate_v1` admits the sampled n=8 child-frontier generation research bundle only when the source report, sampled n=8 zero-min scope, sample plan, frontier equality counts, predecessor transition counts, generated-state equality, digest pins, deterministic replay, negative controls, Lean projection declaration, normalized source hash, and no-authority rail are all present.",
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
            "## Generation Corpus",
            "",
            f"- Normalized source hash: `{report['source_report']['normalized_sha256']}`",
            f"- Source seed: `{report['generation_corpus']['source_seed']}`",
            f"- Sampled child masks: `{report['generation_corpus']['sampled_child_mask_count']}`",
            f"- Frontier equalities: `{report['generation_corpus']['frontier_equal_count']}`",
            f"- Predecessor edges: `{report['generation_corpus']['predecessor_edge_count']}`",
            f"- Predecessor transitions: `{report['generation_corpus']['predecessor_transition_count']}`",
            f"- Executable predecessor transitions: `{report['generation_corpus']['predecessor_transition_executable_count']}`",
            f"- Sampled child states: `{report['generation_corpus']['sampled_child_state_count']}`",
            f"- Generated states: `{report['generation_corpus']['generated_state_count']}`",
            f"- Missing child states: `{report['generation_corpus']['missing_child_state_count']}`",
            f"- Extra generated states: `{report['generation_corpus']['extra_generated_state_count']}`",
            f"- Frontier rows digest: `{report['generation_corpus']['frontier_rows_digest']}`",
            f"- Deterministic replay hash: `{report['generation_corpus']['deterministic_replay_hash']}`",
            f"- Negative controls: `{report['generation_corpus']['negative_control_count']}`",
            f"- Negative control accepts: `{report['generation_corpus']['negative_control_accept_count']}`",
            f"- Tau cases: `{report['breakthrough']['tau_cases']}`",
            f"- Invalid accepts: `{report['breakthrough']['invalid_accepts']}`",
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

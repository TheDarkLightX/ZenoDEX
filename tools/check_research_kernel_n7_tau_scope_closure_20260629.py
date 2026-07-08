#!/usr/bin/env python3
"""Build a Research Kernel closure receipt for the n7 Tau scope risk."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = REPO_ROOT / "generated" / "zenodex_research_kernel_n7_tau_scope_closure_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_RESEARCH_KERNEL_N7_TAU_SCOPE_CLOSURE_20260629.md"

SOURCE_REPORT = "generated/zenodex_ab_child_frontier_bidirectional_transition_tau_certificate_20260629/report.json"
SOURCE_DOC = "docs/research/ZENODEX_AB_CHILD_FRONTIER_BIDIRECTIONAL_TRANSITION_TAU_CERTIFICATE_20260629.md"
SOURCE_TOOL = "tools/check_ab_child_frontier_bidirectional_transition_tau_certificate_20260629.py"
SOURCE_TEST = "tests/tau/test_ab_child_frontier_bidirectional_transition_tau_certificate_20260629.py"
SOURCE_SPEC = "src/tau_specs/recommended/ab_child_frontier_bidirectional_transition_scope_certificate_v1.tau"

TARGET_RISK_ATOM = "atom_f16f64e92cd14d74"
SOURCE_ATOM = "atom_zenodex_research_kernel_n7_tau_scope_closure_20260629"

EXPECTED_SCHEMA = "zenodex.ab_child_frontier_bidirectional_transition_tau_certificate_report.v1"
EXPECTED_SPEC_ID = "ab_child_frontier_bidirectional_transition_scope_certificate_v1"
EXPECTED_REPORT_HASH = "5a75754c4a631c4e8f5dd5b3a24eda1497e42ce24e69d5705494d69e2f8c6981"
EXPECTED_TOOL_HASH = "80c39784829519d3acd3aeb2f1092bbca698fbbbfd77480309e4c71d485ca95c"
EXPECTED_TEST_HASH = "1e6aabace368861b7190b8064a63669f3d7ba4923279b713429abdcf83075d38"
EXPECTED_DOC_HASH = "bca15222bb311571b5a7dfb09ab45b53e0a8d17e700cdd53dd6973aa97058b40"
EXPECTED_SPEC_HASH = "7a8085d766f205399d5aadf7aa920c7c9a4c1c03dcab03361baa89a0965ea92f"
EXPECTED_TRANSITION_ROWS_DIGEST = "fccc26b63521b510776546e4663cecabcf58849af42bcda799484bf092a81f82"
EXPECTED_LINKED_BOUND_ROWS_DIGEST = "0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551"
EXPECTED_REPLAY_HASH = "54e80016a0c0dc4eb629d22b43265091b3b1c4dc75324320107b17dbd42668b7"

EXPECTED_FACTS = (
    "source_report_ok",
    "n7_zero_min_scope_ok",
    "transition_counts_complete",
    "generated_child_count_ok",
    "linked_child_coverage_ok",
    "transition_digest_pinned",
    "linked_digest_pinned",
    "deterministic_replay_ok",
    "negative_controls_reject",
    "authority_boundary_ok",
    "no_authority_effect",
    "corpus_nonvacuous",
)
EXPECTED_CASES = (
    "bidirectional_transition_certificate_pass",
    "missing_source_report_reject",
    "wrong_scope_reject",
    "transition_counts_reject",
    "generated_child_count_reject",
    "linked_child_coverage_reject",
    "transition_digest_reject",
    "linked_digest_reject",
    "nondeterministic_replay_reject",
    "negative_controls_missing_reject",
    "authority_boundary_reject",
    "authority_effect_reject",
    "empty_corpus_reject",
    "inactive_safe",
)


class ClosureError(ValueError):
    """Raised when the n7 Tau closure receipt cannot be trusted."""


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _repo_path(path: str) -> Path:
    full = (REPO_ROOT / path).resolve()
    if full != REPO_ROOT and REPO_ROOT not in full.parents:
        raise ClosureError(f"path escapes repo: {path}")
    return full


def _read_text(path: str) -> str:
    return _repo_path(path).read_text(encoding="utf-8")


def _read_json(path: str) -> dict[str, Any]:
    data = json.loads(_read_text(path))
    if not isinstance(data, dict):
        raise ClosureError(f"JSON report is not an object: {path}")
    return data


def _require(condition: bool, reason: str, checks: dict[str, bool]) -> None:
    checks[reason] = bool(condition)
    if not condition:
        raise ClosureError(reason)


def _require_tracked(path: str) -> dict[str, str]:
    full = _repo_path(path)
    if not full.exists():
        raise ClosureError(f"missing artifact: {path}")
    proc = subprocess.run(
        ["git", "ls-files", "--error-unmatch", path],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise ClosureError(f"artifact is not tracked by git: {path}")
    return {"path": path, "sha256": _sha256(full)}


def _display_command_arg(arg: str) -> str:
    path = Path(arg)
    if not path.is_absolute():
        return arg
    resolved = path.resolve()
    home = Path.home().resolve()
    if resolved == REPO_ROOT or REPO_ROOT in resolved.parents:
        return str(resolved.relative_to(REPO_ROOT))
    if resolved == home or home in resolved.parents:
        return "~/" + str(resolved.relative_to(home))
    return arg


def _run(command: Sequence[str], *, cwd: Path, timeout_s: float) -> dict[str, Any]:
    proc = subprocess.run(
        list(command),
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout_s,
    )
    return {
        "command": " ".join(_display_command_arg(arg) for arg in command),
        "cwd": str(cwd.relative_to(REPO_ROOT)) if cwd != REPO_ROOT else ".",
        "ok": proc.returncode == 0,
        "returncode": proc.returncode,
        "stdout_tail": proc.stdout[-800:],
        "stderr_tail": proc.stderr[-800:],
    }


def _joined_scope_text(report: Mapping[str, Any], doc_text: str) -> str:
    return (
        " ".join(str(item) for item in report.get("non_claims", []))
        + " "
        + str(report.get("authority_boundary", ""))
        + "\n"
        + doc_text
    ).lower()


def validate_n7_tau_scope_state(
    *,
    report: Mapping[str, Any],
    doc_text: str,
    live_commands: Mapping[str, Any] | None = None,
) -> dict[str, bool]:
    checks: dict[str, bool] = {}
    _require(report.get("schema") == EXPECTED_SCHEMA, "source_schema_ok", checks)
    _require(report.get("breakthrough", {}).get("spec_id") == EXPECTED_SPEC_ID, "spec_id_ok", checks)
    _require(report.get("tau", {}).get("ok") is True, "tau_ok", checks)
    _require(report.get("tau", {}).get("invalid_accepts") == 0, "invalid_accepts_zero", checks)
    _require(report.get("breakthrough", {}).get("tau_cases") == len(EXPECTED_CASES), "tau_case_count_ok", checks)

    _require(_sha256(_repo_path(SOURCE_REPORT)) == EXPECTED_REPORT_HASH, "source_report_hash_ok", checks)
    _require(_sha256(_repo_path(SOURCE_TOOL)) == EXPECTED_TOOL_HASH, "source_tool_hash_ok", checks)
    _require(_sha256(_repo_path(SOURCE_TEST)) == EXPECTED_TEST_HASH, "source_test_hash_ok", checks)
    _require(_sha256(_repo_path(SOURCE_DOC)) == EXPECTED_DOC_HASH, "source_doc_hash_ok", checks)
    _require(_sha256(_repo_path(SOURCE_SPEC)) == EXPECTED_SPEC_HASH, "source_spec_hash_ok", checks)

    facts = report.get("facts", {})
    for fact in EXPECTED_FACTS:
        _require(facts.get(fact) == 1, f"{fact}_present", checks)
    _require(set(facts) == set(EXPECTED_FACTS), "fact_set_exact", checks)

    cases = {case.get("case_id"): case for case in report.get("tau", {}).get("case_results", [])}
    for case_id in EXPECTED_CASES:
        _require(case_id in cases, f"{case_id}_case_present", checks)
        _require(cases[case_id].get("ok") is True, f"{case_id}_case_ok", checks)
    _require(cases["bidirectional_transition_certificate_pass"].get("got", {}).get("o7") == 1, "positive_case_admits", checks)
    for case_id in EXPECTED_CASES[1:]:
        _require(cases[case_id].get("got", {}).get("o7") == 0, f"{case_id}_rejects", checks)
    _require(cases["inactive_safe"].get("got", {}).get("o8") == 1, "inactive_safe_no_authority", checks)

    transition = report.get("transition_corpus", {})
    _require(transition.get("case_count") == 4, "case_count_ok", checks)
    _require(transition.get("child_mask_count") == 508, "child_mask_count_ok", checks)
    _require(transition.get("transition_row_count") == 2777, "transition_row_count_ok", checks)
    _require(transition.get("expected_transition_count") == 2777, "expected_transition_count_ok", checks)
    _require(transition.get("covered_transition_count") == 2777, "covered_transition_count_ok", checks)
    _require(transition.get("unique_transition_count") == 2777, "unique_transition_count_ok", checks)
    _require(transition.get("unique_generated_child_count") == 864, "generated_child_count_ok", checks)
    _require(transition.get("linked_child_coverage_witness_count") == 864, "linked_child_coverage_witness_count_ok", checks)
    _require(transition.get("negative_control_count") == 9, "negative_control_count_ok", checks)
    _require(transition.get("negative_control_accept_count") == 0, "negative_control_accepts_zero", checks)
    _require(transition.get("transition_rows_digest") == EXPECTED_TRANSITION_ROWS_DIGEST, "transition_digest_ok", checks)
    _require(transition.get("linked_bound_rows_digest") == EXPECTED_LINKED_BOUND_ROWS_DIGEST, "linked_digest_ok", checks)
    _require(transition.get("deterministic_replay_hash") == EXPECTED_REPLAY_HASH, "replay_hash_ok", checks)

    joined = _joined_scope_text(report, doc_text)
    _require("bounded to the committed n=7 zero-min bidirectional transition report" in joined, "n7_scope_nonclaim_ok", checks)
    _require("does not prove python-to-lean refinement" in joined, "python_refinement_nonclaim_ok", checks)
    _require("does not prove child-frontier generation in lean" in joined, "lean_generation_nonclaim_ok", checks)
    _require("does not replace the host merkle verifier or transition checker" in joined, "host_verifier_nonclaim_ok", checks)
    _require("does not cover nonzero min_amount_out" in joined, "nonzero_min_nonclaim_ok", checks)
    _require("does not authorize settlement" in joined and "state roots" in joined and "production" in joined, "authority_nonclaim_ok", checks)
    for phrase in (
        "tau replaces the host verifier",
        "proves python-to-lean refinement",
        "proves lean refinement",
        "covers nonzero min_amount_out",
        "authorizes settlement",
        "grants production authority",
        "authorizes production",
    ):
        _require(phrase not in joined, f"forbidden_{phrase.replace(' ', '_')}", checks)

    if live_commands is not None:
        for command_id, result in live_commands.items():
            _require(result.get("ok") is True, f"live_{command_id}_ok", checks)
    return checks


def run_live_commands() -> dict[str, Any]:
    return {
        "source_replay": _run([sys.executable, SOURCE_TOOL], cwd=REPO_ROOT, timeout_s=120),
        "focused_pytest": _run([sys.executable, "-m", "pytest", "-q", SOURCE_TEST], cwd=REPO_ROOT, timeout_s=120),
        "public_claim_scope": _run([sys.executable, "tools/check_public_claim_scope.py", "--root", ".", "--json"], cwd=REPO_ROOT, timeout_s=60),
        "claims_registry": _run([sys.executable, "tools/check_claims_registry.py"], cwd=REPO_ROOT, timeout_s=60),
    }


def build_report(*, live_replay: bool = False) -> dict[str, Any]:
    source_report = _read_json(SOURCE_REPORT)
    doc_text = _read_text(SOURCE_DOC)
    live_commands = run_live_commands() if live_replay else None
    checks = validate_n7_tau_scope_state(report=source_report, doc_text=doc_text, live_commands=live_commands)
    artifacts = [_require_tracked(path) for path in (SOURCE_REPORT, SOURCE_DOC, SOURCE_TOOL, SOURCE_TEST, SOURCE_SPEC)]
    return {
        "schema": "zenodex.research_kernel_n7_tau_scope_closure_20260629.v1",
        "date": "2026-06-29",
        "ok": True,
        "closure": {
            "closure_id": "n7_tau_scope_certificate_resolves_risk",
            "closure_kind": "resolves",
            "source_atom_id": SOURCE_ATOM,
            "target_atom_id": TARGET_RISK_ATOM,
            "edge_type": "SUPERSEDES",
            "summary": (
                "The n7 Tau scope certificate resolves the RK risk for the bounded AB child-frontier "
                "bidirectional-transition scope surface: all required host facts are present, every "
                "missing-fact Tau case rejects, digest pins and deterministic replay match, and the no-authority "
                "rail remains explicit."
            ),
            "checks": checks,
            "resolver_artifacts": artifacts,
            "source_report_path": SOURCE_REPORT,
            "source_report_sha256": _sha256(_repo_path(SOURCE_REPORT)),
            "live_commands": live_commands or {},
        },
        "hypothesis_card": {
            "hypothesis_id": "H-RK-N7-TAU-SCOPE-CLOSURE-20260629",
            "mechanism_change": "Close the RK n7 Tau scope risk after validating the bounded Tau certificate and scope limits.",
            "representation_shift_used": "reduce",
            "expected_metric_delta": {
                "safety": "+frontier hygiene",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "-closure/live-replay check overhead",
                "determinism_simplicity": "+explicit Tau fact envelope boundary",
            },
            "null_hypothesis": "The Tau certificate admits a missing host fact, stale digest, nondeterministic replay, or authority overclaim.",
            "falsification_recipe": "Clear required facts, mutate Tau cases, digest pins, counts, replay hash, and non-claims; require stable reject reasons.",
            "support_recipe": "Validate the source Tau certificate report, current artifact hashes, focused Tau tests, claim gates, and optional live replay.",
            "formal_obligations": "Tau composes host facts only; this receipt closes the RK tracking risk, not host-verifier or Lean-refinement obligations.",
            "risk_modes": [
                "stale source certificate hash",
                "missing Tau negative case",
                "missing required host fact",
                "stale digest or deterministic replay hash",
                "authority leakage",
            ],
            "status": "supported",
        },
        "research_kernel_edges_to_add": [
            {
                "source_atom_id": SOURCE_ATOM,
                "target_atom_id": TARGET_RISK_ATOM,
                "edge_type": "SUPERSEDES",
                "closure_kind": "resolves",
                "rationale": "The n7 Tau scope certificate passes the exact missing-fact and scope-boundary checks in the RK risk.",
            }
        ],
        "residual_open_frontier": [
            "n7 bidirectional transition mutation risk",
            "reserve-state observed-summary bridge risk",
            "sampled n8 canonical-index Merkle certificate risk",
            "sampled n8 bidirectional transition certificate risk",
            "full subset-mask DP construction and Python-to-Lean refinement",
        ],
        "non_claims": [
            "This receipt closes only the RK tracking risk for the bounded n7 Tau scope certificate.",
            "This receipt does not replace the host Merkle verifier or transition checker.",
            "This receipt does not prove Python-to-Lean refinement.",
            "This receipt does not prove child-frontier generation in Lean.",
            "This receipt does not cover nonzero min_amount_out behavior.",
            "This receipt grants no settlement, governance, state-root, routing, matching, pool-mutation, production, or deployment authority.",
        ],
        "replay_command": "python3 tools/check_research_kernel_n7_tau_scope_closure_20260629.py",
        "live_replay_command": "python3 tools/check_research_kernel_n7_tau_scope_closure_20260629.py --live-replay",
    }


def write_json_report(report: Mapping[str, Any]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_markdown_report(report: Mapping[str, Any]) -> None:
    closure = report["closure"]
    lines = [
        "# ZenoDEX Research Kernel n7 Tau Scope Closure - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(closure["summary"]),
        "",
        f"- Target RK atom: `{closure['target_atom_id']}`",
        f"- Closure kind: `{closure['closure_kind']}`",
        f"- Edge type: `{closure['edge_type']}`",
        f"- Source report: `{closure['source_report_path']}`",
        "",
        "## Checks",
        "",
        "| check | value |",
        "| --- | ---: |",
    ]
    for key, value in closure["checks"].items():
        lines.append(f"| `{key}` | `{value}` |")
    lines.extend(["", "## Research Kernel Edge To Add", "", "| source atom | target atom | edge type |", "| --- | --- | --- |"])
    for edge in report["research_kernel_edges_to_add"]:
        lines.append(f"| `{edge['source_atom_id']}` | `{edge['target_atom_id']}` | `{edge['edge_type']}` |")
    lines.extend(["", "## Residual Open Frontier", ""])
    lines.extend(f"- {item}" for item in report["residual_open_frontier"])
    lines.extend(["", "## Non-Claims", ""])
    lines.extend(f"- {item}" for item in report["non_claims"])
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", "", "Live replay:", "", "```bash", str(report["live_replay_command"]), "```", ""])
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--live-replay", action="store_true", help="run the source Tau checker, focused pytest, and claim gates")
    parser.add_argument("--json-only", action="store_true", help="write JSON only and suppress markdown/stdout summary")
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        report = build_report(live_replay=args.live_replay)
        write_json_report(report)
        if not args.json_only:
            write_markdown_report(report)
    except ClosureError as exc:
        print(f"n7 Tau RK closure check failed: {exc}", file=sys.stderr)
        return 1
    if not args.json_only:
        print(
            json.dumps(
                {
                    "ok": report["ok"],
                    "target_atom": report["closure"]["target_atom_id"],
                    "edge_type": report["closure"]["edge_type"],
                    "report": str(REPORT_JSON.relative_to(REPO_ROOT)),
                },
                indent=2,
                sort_keys=True,
            )
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

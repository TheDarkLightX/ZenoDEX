#!/usr/bin/env python3
"""Build a Research Kernel closure receipt for the AB observed-summary risk."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = REPO_ROOT / "generated" / "zenodex_research_kernel_observed_summary_closure_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_RESEARCH_KERNEL_OBSERVED_SUMMARY_CLOSURE_20260629.md"
)

LEAN_FILE = "lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean"
FORMAL_TEST = "tests/formal/test_lean_ab_strict_zero_min_monotone.py"
OBSERVED_DOC = "docs/research/ZENODEX_AB_STRICT_ZERO_MIN_OBSERVED_SUMMARY_LEAN_20260629.md"
OBSERVED_REPORT = "generated/zenodex_ab_strict_zero_min_observed_summary_lean_20260629/report.json"

TARGET_RISK_ATOM = "atom_5e7aa160e5604f79"
SOURCE_ATOM = "atom_zenodex_research_kernel_observed_summary_closure_20260629"

EXPECTED_REPORT_SCHEMA = "zenodex.ab_strict_zero_min_observed_summary_lean_report.v1"
EXPECTED_LEAN_HASH = "0d9787f60b655a59c5ab3f6395eebf013d7827b3e5f51c974c180cfe3a1ae1e6"
EXPECTED_TEST_HASH = "eb9e1af42c1e854baf73fb2f892dd4466c5730d81529d7788ac1f4746c9ba081"
EXPECTED_THEOREMS = (
    "StrictSubsetInductionObservedSummary",
    "strictSubsetInductionObservedSummaryValid",
    "strictSubsetInductionObservedSummaryFullKey",
    "strictSubsetInductionObservedSummarySelectedKey",
    "strictSubsetInductionObservedSummary_to_aggregateRangePathTableValid",
    "strictSubsetInductionObservedSummary_validates",
    "witness_strictSubsetInductionObservedSummary_validates",
)


class ClosureError(ValueError):
    """Raised when the observed-summary closure receipt cannot be trusted."""


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


def _require(condition: bool, reason: str, checks: dict[str, bool]) -> None:
    checks[reason] = bool(condition)
    if not condition:
        raise ClosureError(reason)


def _extract_decl(text: str, name: str) -> str:
    pattern = re.compile(rf"^(?:structure|def|theorem)\s+{re.escape(name)}\b", re.M)
    match = pattern.search(text)
    if not match:
        return ""
    start = match.start()
    next_decl = re.search(r"^(?:structure|def|theorem)\s+\w+\b", text[match.end() :], re.M)
    if not next_decl:
        return text[start:]
    return text[start : match.end() + next_decl.start()]


def _non_claim_text(report: Mapping[str, Any], doc_text: str) -> str:
    return "\n".join(str(item) for item in report.get("non_claims", [])).lower() + "\n" + doc_text.lower()


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


def validate_observed_summary_state(
    *,
    lean_text: str,
    doc_text: str,
    report: Mapping[str, Any],
    live_commands: Mapping[str, Any] | None = None,
) -> dict[str, bool]:
    checks: dict[str, bool] = {}
    _require(report.get("schema") == EXPECTED_REPORT_SCHEMA, "report_schema_ok", checks)
    _require(report.get("ok") is True, "report_ok", checks)
    _require(report.get("proof_role", "").lower().startswith("bind host-visible"), "proof_role_ok", checks)
    _require("Research-only formal proof component" in report.get("authority_boundary", ""), "authority_boundary_ok", checks)

    artifact_hashes = report.get("artifact_hashes", {})
    _require(artifact_hashes.get(LEAN_FILE) == EXPECTED_LEAN_HASH, "report_lean_hash_pinned", checks)
    _require(artifact_hashes.get(FORMAL_TEST) == EXPECTED_TEST_HASH, "report_test_hash_pinned", checks)
    _require(_sha256(_repo_path(LEAN_FILE)) == EXPECTED_LEAN_HASH, "current_lean_hash_ok", checks)
    _require(_sha256(_repo_path(FORMAL_TEST)) == EXPECTED_TEST_HASH, "current_test_hash_ok", checks)

    theorem_set = set(report.get("new_lean_theorems", []))
    for theorem in EXPECTED_THEOREMS:
        _require(theorem in theorem_set, f"{theorem}_listed", checks)
        _require(theorem in lean_text, f"{theorem}_present", checks)
    _require(len(report.get("new_lean_theorems", [])) == len(EXPECTED_THEOREMS), "theorem_count_ok", checks)

    valid_decl = _extract_decl(lean_text, "strictSubsetInductionObservedSummaryValid")
    endpoint_decl = _extract_decl(lean_text, "strictSubsetInductionObservedSummary_validates")
    witness_decl = _extract_decl(lean_text, "witness_strictSubsetInductionObservedSummary_validates")
    _require("summary.observedMaskCount = summary.table.masks.length" in valid_decl, "observed_mask_count_bound", checks)
    _require("summary.observedWinnerMaskId = summary.table.winner.maskId" in valid_decl, "observed_winner_bound", checks)
    _require("summary.observedExecutedInput = summary.table.executedInput" in valid_decl, "observed_executed_input_bound", checks)
    _require(
        "summary.observedInitialReserveOut = summary.table.initialReserveOut" in valid_decl,
        "observed_initial_reserve_bound",
        checks,
    )
    _require("summary.table.packetHashBound = true" in endpoint_decl, "packet_hash_bound_inherited", checks)
    _require("summary.table.noAuthorityEffect = true" in endpoint_decl, "no_authority_inherited", checks)
    _require("summary.table.winnerMembershipBound = true" in endpoint_decl, "winner_membership_inherited", checks)
    _require("allBitsBelowSet summary.table.winner.maskId summary.table.bitCount" in endpoint_decl, "coverage_inherited", checks)
    _require("zeroMinEconomicKeyDominated" in endpoint_decl, "economic_dominance_inherited", checks)
    _require("suffixExecutable summary.table.winner.selected.processedReserveIn" in endpoint_decl, "suffix_exec_inherited", checks)
    _require("strictSubsetInductionObservedSummaryValid summary" in witness_decl, "witness_nonvacuous", checks)

    verification = report.get("verification", {})
    for gate in {
        "lake_env_lean",
        "lake_build_module",
        "focused_pytest",
        "placeholder_scan",
        "json_validation",
        "public_claim_scope",
        "claims_registry",
        "diff_check",
    }:
        _require(verification.get(gate, {}).get("status") in {"pass", "ok"}, f"{gate}_reported_ok", checks)

    joined = _non_claim_text(report, doc_text)
    _require("does not construct a subset dp table" in joined, "subset_dp_nonclaim_ok", checks)
    _require("does not prove python-to-lean refinement" in joined, "python_refinement_nonclaim_ok", checks)
    _require("does not prove json canonicalization" in joined, "json_nonclaim_ok", checks)
    _require("does not define canonical tie order" in joined, "tie_order_nonclaim_ok", checks)
    _require("does not cover nonzero" in joined and "min_amount_out" in joined, "nonzero_min_nonclaim_ok", checks)
    _require("no settlement" in joined and "state-root" in joined and "production" in joined, "authority_nonclaim_ok", checks)
    forbidden = (
        "proves host/python emitter construction",
        "proves json canonicalization",
        "proves full subset dp exactness",
        "authorizes settlement",
        "grants production authority",
        "authorizes production",
    )
    for phrase in forbidden:
        _require(phrase not in joined, f"forbidden_{phrase.replace(' ', '_')}", checks)

    if live_commands is not None:
        for command_id, result in live_commands.items():
            _require(result.get("ok") is True, f"live_{command_id}_ok", checks)
    return checks


def run_live_commands() -> dict[str, Any]:
    proof_scan = REPO_ROOT.parent.parent / ".codex" / "skills" / "proof-engineering" / "scripts" / "scan_proof_placeholders.py"
    commands: dict[str, Any] = {
        "lake_env_lean": _run(["lake", "env", "lean", "Proofs/ABStrictZeroMinMonotone.lean"], cwd=REPO_ROOT / "lean-mathlib", timeout_s=120),
        "focused_pytest": _run([sys.executable, "-m", "pytest", "-q", FORMAL_TEST], cwd=REPO_ROOT, timeout_s=120),
        "public_claim_scope": _run([sys.executable, "tools/check_public_claim_scope.py", "--root", ".", "--json"], cwd=REPO_ROOT, timeout_s=60),
        "claims_registry": _run([sys.executable, "tools/check_claims_registry.py"], cwd=REPO_ROOT, timeout_s=60),
    }
    if proof_scan.exists():
        commands["placeholder_scan"] = _run([sys.executable, str(proof_scan), LEAN_FILE], cwd=REPO_ROOT, timeout_s=60)
    return commands


def build_report(*, live_proof: bool = False) -> dict[str, Any]:
    lean_text = _read_text(LEAN_FILE)
    doc_text = _read_text(OBSERVED_DOC)
    source_report = _read_json(OBSERVED_REPORT)
    live_commands = run_live_commands() if live_proof else None
    checks = validate_observed_summary_state(
        lean_text=lean_text,
        doc_text=doc_text,
        report=source_report,
        live_commands=live_commands,
    )
    if not all(checks.values()):
        raise ClosureError("observed-summary closure checks failed")
    artifacts = [_require_tracked(path) for path in (LEAN_FILE, FORMAL_TEST, OBSERVED_DOC, OBSERVED_REPORT)]
    return {
        "schema": "zenodex.research_kernel_observed_summary_closure_20260629.v1",
        "date": "2026-06-29",
        "ok": True,
        "closure": {
            "closure_id": "observed_summary_lean_bridge_resolves_risk",
            "closure_kind": "resolves",
            "source_atom_id": SOURCE_ATOM,
            "target_atom_id": TARGET_RISK_ATOM,
            "edge_type": "SUPERSEDES",
            "summary": (
                "The observed-summary Lean bridge resolves the RK risk for the scoped checker-boundary surface: "
                "host-visible count/key fields are bound to the validated aggregate range-path table, and the "
                "endpoint inherits packet rails, full-mask coverage, zero-min economic-key dominance, and selected suffix executability."
            ),
            "checks": checks,
            "resolver_artifacts": artifacts,
            "observed_report_path": OBSERVED_REPORT,
            "observed_report_sha256": _sha256(_repo_path(OBSERVED_REPORT)),
            "live_commands": live_commands or {},
        },
        "hypothesis_card": {
            "hypothesis_id": "H-RK-OBSERVED-SUMMARY-CLOSURE-20260629",
            "mechanism_change": "Close the RK observed-summary risk after validating the Lean checker-boundary artifact and scope limits.",
            "representation_shift_used": "reduce",
            "expected_metric_delta": {
                "safety": "+frontier hygiene",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "-closure/live-proof check overhead",
                "determinism_simplicity": "+explicit observed-summary checker boundary",
            },
            "null_hypothesis": "The observed-summary bridge fails to bind host-visible fields, misses inherited endpoint guarantees, or overclaims emitter/production authority.",
            "falsification_recipe": "Mutate theorem listings, field-binding markers, inherited endpoint markers, report gates, and non-claims; require stable reject reasons.",
            "support_recipe": "Validate the generated observed-summary report, current Lean/test hashes, focused formal tests, claim gates, and optional live Lean proof commands.",
            "formal_obligations": "Lean remains the proof authority; this receipt closes only the RK tracking risk for the scoped observed-summary checker boundary.",
            "risk_modes": [
                "stale Lean/report hash",
                "missing host-visible field binding",
                "missing inherited endpoint predicate",
                "overclaim to host/Python emitter construction",
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
                "rationale": "The observed-summary Lean bridge and current report pass the exact predicates in the RK risk.",
            }
        ],
        "residual_open_frontier": [
            "reserve-state observed-summary bridge risk",
            "n7 Tau scope certificate risk",
            "n7 bidirectional transition mutation risk",
            "full subset-mask DP construction and Python-to-Lean refinement",
            "host/Python emitter construction and JSON canonicalization",
        ],
        "non_claims": [
            "This receipt closes only the RK tracking risk for the scoped AB observed-summary Lean checker boundary.",
            "This receipt does not prove host/Python emitter construction.",
            "This receipt does not prove Python-to-Lean refinement.",
            "This receipt does not construct a subset DP table, define canonical tie order, or cover nonzero min_amount_out behavior.",
            "This receipt does not close reserve-state observed-summary, n7, full subset-mask, emitter-construction, or JSON-canonicalization risks.",
            "This receipt grants no settlement, governance, state-root, routing, matching, pool-mutation, or production authority.",
        ],
        "replay_command": "python3 tools/check_research_kernel_observed_summary_closure_20260629.py",
        "live_proof_command": "python3 tools/check_research_kernel_observed_summary_closure_20260629.py --live-proof",
    }


def write_json_report(report: Mapping[str, Any]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_markdown_report(report: Mapping[str, Any]) -> None:
    closure = report["closure"]
    lines = [
        "# ZenoDEX Research Kernel Observed-Summary Closure - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(closure["summary"]),
        "",
        f"- Target RK atom: `{closure['target_atom_id']}`",
        f"- Closure kind: `{closure['closure_kind']}`",
        f"- Edge type: `{closure['edge_type']}`",
        f"- Source report: `{closure['observed_report_path']}`",
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
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", "", "Live Lean checkpoint:", "", "```bash", str(report["live_proof_command"]), "```", ""])
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--live-proof", action="store_true", help="run the Lean/focused-test checkpoint commands")
    parser.add_argument("--json-only", action="store_true", help="write JSON only and suppress markdown/stdout summary")
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        report = build_report(live_proof=args.live_proof)
        write_json_report(report)
        if not args.json_only:
            write_markdown_report(report)
    except ClosureError as exc:
        print(f"observed-summary RK closure check failed: {exc}", file=sys.stderr)
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

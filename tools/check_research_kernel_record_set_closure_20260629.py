#!/usr/bin/env python3
"""Build a Research Kernel closure receipt for the AB record-set pruning risk."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))
OUT_DIR = REPO_ROOT / "generated" / "zenodex_research_kernel_record_set_closure_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT / "docs" / "research" / "ZENODEX_RESEARCH_KERNEL_RECORD_SET_CLOSURE_20260629.md"
)

AUDIT_REPORT = "generated/zenodex_ab_record_set_pruning_refutation_audit_20260629/report.json"
AUDIT_TOOL = "tools/check_ab_record_set_pruning_refutation_audit_20260629.py"
AUDIT_TEST = "tests/formal/test_ab_record_set_pruning_refutation_audit_20260629.py"
AUDIT_DOC = "docs/research/ZENODEX_AB_RECORD_SET_PRUNING_REFUTATION_AUDIT_20260629.md"
LEAN_FILE = "lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean"

TARGET_RISK_ATOM = "atom_c0f2558fe81046cf"
SOURCE_ATOM = "atom_zenodex_research_kernel_record_set_closure_20260629"

EXPECTED_AUDIT_SCHEMA = "zenodex.ab_record_set_pruning_refutation_audit_report.v1"
EXPECTED_REPLAY_HASH = "3bb033dcad8d1bd40aa772e9663ba35320a3edfc3c8d51a99f582c3959c5fef6"
EXPECTED_CERT_DECL_HASH = "6645dd7981cb6fe084bb9c0abd0f8e5b67c22bc2d149c34ccfa44acc85a1cbe9"
EXPECTED_VALIDATES_DECL_HASH = "315f15cce3cffee1d80dd8cd664536afa717926f6fff3f91c1f9edee2dc81fd4"
EXPECTED_NEGATIVE_CONTROLS = 8


class ClosureError(ValueError):
    """Raised when the closure receipt cannot be trusted."""


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


def _load_generated_audit_report() -> dict[str, Any]:
    path = _repo_path(AUDIT_REPORT)
    if not path.exists():
        raise ClosureError(f"missing generated audit report: {AUDIT_REPORT}")
    report = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(report, dict):
        raise ClosureError("audit report is not a JSON object")
    return report


def _load_live_audit_report() -> dict[str, Any]:
    from tools.check_ab_record_set_pruning_refutation_audit_20260629 import build_report

    return build_report()


def _require(condition: bool, reason: str, checks: dict[str, bool]) -> None:
    checks[reason] = bool(condition)
    if not condition:
        raise ClosureError(reason)


def _non_claim_text(report: Mapping[str, Any]) -> str:
    return "\n".join(str(item) for item in report.get("non_claims", [])).lower()


def _validate_audit_report(report: Mapping[str, Any]) -> dict[str, bool]:
    checks: dict[str, bool] = {}
    _require(report.get("schema") == EXPECTED_AUDIT_SCHEMA, "audit_schema_ok", checks)
    _require(report.get("ok") is True, "audit_ok", checks)
    _require(report.get("search", {}).get("ok") is True, "search_ok", checks)
    _require(report.get("search", {}).get("reasons") == [], "no_search_reasons", checks)
    _require(
        report.get("search", {}).get("negative_control_count") == EXPECTED_NEGATIVE_CONTROLS,
        "negative_control_count_ok",
        checks,
    )
    _require(
        report.get("search", {}).get("negative_control_accept_count") == 0,
        "negative_control_accepts_zero",
        checks,
    )
    deterministic = report.get("deterministic_replay", {})
    _require(deterministic.get("ok") is True, "deterministic_replay_ok", checks)
    _require(deterministic.get("first_hash") == EXPECTED_REPLAY_HASH, "first_replay_hash_ok", checks)
    _require(deterministic.get("second_hash") == EXPECTED_REPLAY_HASH, "second_replay_hash_ok", checks)

    lean_surface = report.get("search", {}).get("lean_surface", {})
    _require(lean_surface.get("placeholder_free") is True, "lean_placeholder_free", checks)
    _require(lean_surface.get("required_theorem_count") == 8, "lean_theorem_count_ok", checks)
    _require(
        lean_surface.get("strict_record_set_certificate_decl_hash") == EXPECTED_CERT_DECL_HASH,
        "certificate_decl_hash_ok",
        checks,
    )
    _require(
        lean_surface.get("strict_record_set_validates_decl_hash") == EXPECTED_VALIDATES_DECL_HASH,
        "validates_decl_hash_ok",
        checks,
    )

    bindings = report.get("search", {}).get("report_bindings", {})
    _require(bindings.get("record_key_ok") is True, "record_key_report_ok", checks)
    _require(bindings.get("record_set_status") == "pass", "record_set_report_ok", checks)
    _require(bindings.get("record_key_theorem_count") == 6, "record_key_theorem_count_ok", checks)
    _require(bindings.get("record_set_theorem_count") == 4, "record_set_theorem_count_ok", checks)

    commands = report.get("search", {}).get("verification_commands", {})
    _require(bool(commands), "verification_commands_present", checks)
    for command_id in {
        "lake_env_lean",
        "lake_build_module",
        "focused_pytest",
        "public_claim_scope",
        "claims_registry",
    }:
        result = commands.get(command_id, {})
        _require(result.get("ok") is True, f"{command_id}_ok", checks)

    non_claims = _non_claim_text(report)
    _require("does not prove python-to-lean refinement" in non_claims, "python_refinement_nonclaim_ok", checks)
    _require("does not construct a subset dp table" in non_claims, "subset_dp_nonclaim_ok", checks)
    _require("does not define canonical tie order" in non_claims, "tie_order_nonclaim_ok", checks)
    _require("does not cover nonzero min_amount_out" in non_claims, "nonzero_min_nonclaim_ok", checks)
    _require("no settlement" in non_claims and "state-root" in non_claims, "authority_nonclaim_ok", checks)
    return checks


def build_report(*, live_audit: bool = False) -> dict[str, Any]:
    audit_report = _load_live_audit_report() if live_audit else _load_generated_audit_report()
    artifacts = [_require_tracked(path) for path in (AUDIT_TOOL, AUDIT_TEST, AUDIT_DOC, AUDIT_REPORT, LEAN_FILE)]
    checks = _validate_audit_report(audit_report)
    closed = all(checks.values())
    if not closed:
        raise ClosureError("record-set closure checks failed")
    return {
        "schema": "zenodex.research_kernel_record_set_closure_20260629.v1",
        "date": "2026-06-29",
        "ok": True,
        "closure": {
            "closure_id": "record_set_pruning_refutation_audit_resolves_risk",
            "closure_kind": "resolves",
            "source_atom_id": SOURCE_ATOM,
            "target_atom_id": TARGET_RISK_ATOM,
            "edge_type": "SUPERSEDES",
            "summary": (
                "The current AB record-set pruning refutation audit resolves the RK risk "
                "for the scoped Lean/record-set claim surface: theorem premises, generated "
                "report bindings, negative controls, deterministic replay, and non-claims all pass."
            ),
            "checks": checks,
            "resolver_artifacts": artifacts,
            "audit_report_path": AUDIT_REPORT,
            "audit_report_sha256": _sha256(_repo_path(AUDIT_REPORT)),
            "audit_deterministic_replay_hash": EXPECTED_REPLAY_HASH,
        },
        "hypothesis_card": {
            "hypothesis_id": "H-RK-RECORD-SET-CLOSURE-20260629",
            "mechanism_change": "Close the open RK record-set risk only after replaying the dedicated falsify-first audit.",
            "representation_shift_used": "counterexample_boundary",
            "expected_metric_delta": {
                "safety": "+frontier hygiene",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "-closure check overhead",
                "determinism_simplicity": "+explicit edge and residual-open set",
            },
            "null_hypothesis": "The existing record-set audit is stale, fails a gate, misses a load-bearing premise, or overclaims authority.",
            "falsification_recipe": "Validate stable audit invariants, negative controls, theorem/report bindings, and public non-claims.",
            "support_recipe": "Pass the audit checker, focused pytest, claim-scope gates, and this RK closure checker.",
            "formal_obligations": "Lean remains the proof authority; this receipt closes only the RK tracking risk for the scoped audit surface.",
            "risk_modes": [
                "outer audit JSON timing drift",
                "stale generated report",
                "missing Lean premise",
                "broad RK edge overclaim",
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
                "rationale": "The dedicated falsify-first audit passes and covers the exact record-set risk predicates.",
            }
        ],
        "residual_open_frontier": [
            "n7 Tau scope certificate risk",
            "n7 bidirectional transition mutation risk",
            "observed-summary bridge risks",
            "reserve-state observed-summary bridge risks",
            "full subset-mask DP construction and Python-to-Lean refinement",
        ],
        "non_claims": [
            "This receipt closes only the RK tracking risk for the scoped AB record-set pruning audit.",
            "This receipt does not prove Python-to-Lean refinement.",
            "This receipt does not construct a subset DP table or define canonical tie order.",
            "This receipt does not cover nonzero min_amount_out behavior.",
            "This receipt does not close n7, observed-summary, reserve-state observed-summary, or full subset-mask frontier risks.",
            "This receipt grants no settlement, governance, state-root, routing, matching, pool-mutation, or production authority.",
        ],
        "replay_command": "python3 tools/check_research_kernel_record_set_closure_20260629.py",
        "live_audit_command": "python3 tools/check_research_kernel_record_set_closure_20260629.py --live-audit",
    }


def write_json_report(report: Mapping[str, Any]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_markdown_report(report: Mapping[str, Any]) -> None:
    closure = report["closure"]
    lines = [
        "# ZenoDEX Research Kernel Record-Set Closure - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(closure["summary"]),
        "",
        f"- Target RK atom: `{closure['target_atom_id']}`",
        f"- Closure kind: `{closure['closure_kind']}`",
        f"- Edge type: `{closure['edge_type']}`",
        f"- Audit deterministic replay hash: `{closure['audit_deterministic_replay_hash']}`",
        "",
        "## Checks",
        "",
        "| check | value |",
        "| --- | ---: |",
    ]
    for key, value in closure["checks"].items():
        lines.append(f"| `{key}` | `{value}` |")
    lines.extend(
        [
            "",
            "## Research Kernel Edge To Add",
            "",
            "| source atom | target atom | edge type |",
            "| --- | --- | --- |",
        ]
    )
    for edge in report["research_kernel_edges_to_add"]:
        lines.append(f"| `{edge['source_atom_id']}` | `{edge['target_atom_id']}` | `{edge['edge_type']}` |")
    lines.extend(["", "## Residual Open Frontier", ""])
    lines.extend(f"- {item}" for item in report["residual_open_frontier"])
    lines.extend(["", "## Non-Claims", ""])
    lines.extend(f"- {item}" for item in report["non_claims"])
    lines.extend(
        [
            "",
            "## Replay",
            "",
            "```bash",
            str(report["replay_command"]),
            "```",
            "",
            "Live audit mode recomputes the audit in memory:",
            "",
            "```bash",
            str(report["live_audit_command"]),
            "```",
            "",
        ]
    )
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--live-audit", action="store_true", help="recompute the audit in memory before closure")
    parser.add_argument("--json-only", action="store_true", help="write JSON only and suppress markdown/stdout summary")
    args = parser.parse_args(list(argv) if argv is not None else None)

    try:
        report = build_report(live_audit=args.live_audit)
        write_json_report(report)
        if not args.json_only:
            write_markdown_report(report)
    except ClosureError as exc:
        print(f"record-set RK closure check failed: {exc}", file=sys.stderr)
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

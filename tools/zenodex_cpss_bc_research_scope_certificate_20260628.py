#!/usr/bin/env python3
"""Replay the CPSS-BC research-scope certificate."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time
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


OUT_DIR = REPO_ROOT / "generated" / "zenodex_cpss_bc_research_scope_certificate_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_CPSS_BC_RESEARCH_SCOPE_CERTIFICATE_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "cpss_bc_research_scope_certificate_v1.tau"

LEAN_FILES = (
    REPO_ROOT / "lean-mathlib" / "Proofs" / "CompressedStateSubsetDP.lean",
    REPO_ROOT / "lean-mathlib" / "Proofs" / "CommitRevealStrategyproof.lean",
    REPO_ROOT / "lean-mathlib" / "Proofs" / "CommitRevealBothParamsSP.lean",
    REPO_ROOT / "lean-mathlib" / "Proofs" / "WindowBound.lean",
    REPO_ROOT / "lean-mathlib" / "Proofs" / "StrongConcavityWindowBound.lean",
)

RESEARCH_DOCS = (
    REPO_ROOT / "docs" / "research" / "BREAKTHROUGH_REPORT.md",
    REPO_ROOT / "docs" / "research" / "CPSS_BC_BREAKTHROUGH.md",
    REPO_ROOT / "docs" / "research" / "PRODUCTION_IMPLEMENTATION_GUIDE.md",
)

REPLAY_SCRIPTS = (
    REPO_ROOT / "docs" / "research" / "cpss_bc_witness.py",
    REPO_ROOT / "docs" / "research" / "precommit_collusion_test.py",
    REPO_ROOT / "docs" / "research" / "commit_reveal_both_params.py",
    REPO_ROOT / "docs" / "research" / "stress_test_commit_reveal.py",
    REPO_ROOT / "docs" / "research" / "collusion_resistance_test.py",
)


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _contains_all(text: str, needles: tuple[str, ...]) -> bool:
    lowered = text.lower()
    return all(needle.lower() in lowered for needle in needles)


def _lean_compile(path: Path) -> dict[str, Any]:
    started = time.monotonic()
    proc = subprocess.run(
        ["lake", "env", "lean", str(path.relative_to(REPO_ROOT / "lean-mathlib"))],
        cwd=REPO_ROOT / "lean-mathlib",
        capture_output=True,
        text=True,
        timeout=60,
        check=False,
    )
    return {
        "path": str(path.relative_to(REPO_ROOT)),
        "ok": proc.returncode == 0,
        "returncode": proc.returncode,
        "elapsed_s": round(time.monotonic() - started, 6),
        "stdout": proc.stdout[-2000:],
        "stderr": proc.stderr[-2000:],
        "sha256": _sha256(path),
    }


def _lean_forbidden_scan(path: Path) -> dict[str, Any]:
    text = _read(path)
    matches = []
    for pattern in (r"\bsorry\b", r"\badmit\b", r"\baxiom\b"):
        if re.search(pattern, text):
            matches.append(pattern)
    return {
        "path": str(path.relative_to(REPO_ROOT)),
        "ok": not matches,
        "matches": matches,
    }


def _fact_bundle(lean_results: list[dict[str, Any]], forbidden_results: list[dict[str, Any]]) -> dict[str, int]:
    breakthrough = _read(RESEARCH_DOCS[0])
    cpss = _read(RESEARCH_DOCS[1])
    guide = _read(RESEARCH_DOCS[2])
    both_params = _read(REPO_ROOT / "lean-mathlib" / "Proofs" / "CommitRevealBothParamsSP.lean")
    return {
        "artifacts_present": int(all(path.exists() for path in (*LEAN_FILES, *RESEARCH_DOCS, *REPLAY_SCRIPTS))),
        "lean_compile_ok": int(all(row["ok"] for row in lean_results)),
        "lean_no_forbidden_tokens": int(all(row["ok"] for row in forbidden_results)),
        "compressed_state_scope_ok": int(
            _contains_all(
                breakthrough,
                (
                    "compressed-state sufficiency",
                    "formally proven in lean",
                    "zero sorries",
                ),
            )
        ),
        "adaptive_window_empirical_only": int(
            _contains_all(
                guide,
                (
                    "empirical validation for the adaptive-window implementation",
                    "ternary-search exactness and lipschitz window sufficiency remain empirical",
                    "next proof targets",
                ),
            )
        ),
        "single_user_sp_proven": int(
            _contains_all(
                both_params,
                (
                    "proves only single-user sp",
                    "does not prevent precommit collusion",
                    "cr_both_params_single_user_complete_sp",
                ),
            )
        ),
        "group_sp_falsified": int(
            _contains_all(
                breakthrough,
                (
                    "group sp was falsified",
                    "precommit sacrifice attack",
                    "42.1% violation rate",
                ),
            )
        ),
        "precommit_collusion_documented": int(
            _contains_all(
                guide,
                (
                    "precommit collusion",
                    "off-protocol side payments",
                    "does not prevent precommit collusion",
                ),
            )
        ),
        "cpss_greedy_dominance_falsified": int(
            _contains_all(
                cpss,
                (
                    "status: falsified",
                    "greedy sequential dominance does not hold",
                    "adversarial suite",
                ),
            )
        ),
        "production_nonclaims_bound": int(
            _contains_all(
                guide,
                (
                    "inclusion, censorship, reveal-withholding, and batch-boundary games are non-claims",
                    "does not prevent precommit collusion",
                    "integration checklist",
                ),
            )
        ),
        "replay_scripts_present": int(all(path.exists() and path.stat().st_size > 0 for path in REPLAY_SCRIPTS)),
        "no_authority_effect": 1,
    }


def _tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    pass_step = {
        "i1": 1,
        "i2": int(facts["artifacts_present"]),
        "i3": int(facts["lean_compile_ok"]),
        "i4": int(facts["lean_no_forbidden_tokens"]),
        "i5": int(facts["compressed_state_scope_ok"]),
        "i6": int(facts["adaptive_window_empirical_only"]),
        "i7": int(facts["single_user_sp_proven"]),
        "i8": int(facts["group_sp_falsified"]),
        "i9": int(facts["precommit_collusion_documented"]),
        "i10": int(facts["cpss_greedy_dominance_falsified"]),
        "i11": int(facts["production_nonclaims_bound"]),
        "i12": int(facts["replay_scripts_present"]),
        "i13": int(facts["no_authority_effect"]),
    }
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauCase(
            "research_scope_certificate_pass",
            pass_step,
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 0},
            "All formal, falsification, replay, and no-authority facts admit the research-scope certificate.",
        ),
        TauCase(
            "missing_window_scope_reject",
            {**pass_step, "i6": 0},
            {"o2": 0, "o5": 0},
            "Adaptive-window evidence must be scoped as empirical.",
        ),
        TauCase(
            "missing_group_sp_falsification_reject",
            {**pass_step, "i8": 0},
            {"o2": 0, "o5": 0},
            "Group strategyproofness falsification must be recorded.",
        ),
        TauCase(
            "missing_precommit_collusion_reject",
            {**pass_step, "i9": 0},
            {"o2": 0, "o5": 0},
            "Precommit collusion must remain a documented limitation.",
        ),
        TauCase(
            "missing_cpss_falsification_reject",
            {**pass_step, "i10": 0},
            {"o2": 0, "o5": 0},
            "The CPSS greedy dominance falsification must remain recorded.",
        ),
        TauCase(
            "authority_reject",
            {**pass_step, "i13": 0},
            {"o4": 0, "o5": 0},
            "The research bundle cannot carry production or settlement authority.",
        ),
        TauCase(
            "inactive_safe",
            inactive,
            {"o5": 0, "o6": 1},
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
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    version = (proc.stdout + proc.stderr).strip()
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
        if case.expected.get("o5") == 0 and got.get("o5") == 1:
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
        "tau_bin": tau_bin,
        "tau_version": version,
    }


def _build_report() -> dict[str, Any]:
    lean_results = [_lean_compile(path) for path in LEAN_FILES]
    forbidden_results = [_lean_forbidden_scan(path) for path in LEAN_FILES]
    facts = _fact_bundle(lean_results, forbidden_results)
    tau = _run_tau(facts)
    return {
        "schema": "zenodex.cpss_bc_research_scope_certificate_report.v1",
        "date": "2026-06-28",
        "authority_boundary": "research evidence only; no production, settlement, oracle, governance, pool-mutation, or state-root authority",
        "spec": {
            "path": str(TAU_SPEC.relative_to(REPO_ROOT)),
            "sha256": _sha256(TAU_SPEC),
        },
        "lean": {
            "files": lean_results,
            "forbidden_scan": forbidden_results,
            "compile_ok": all(row["ok"] for row in lean_results),
            "no_forbidden_tokens": all(row["ok"] for row in forbidden_results),
        },
        "research_docs": [
            {"path": str(path.relative_to(REPO_ROOT)), "sha256": _sha256(path)}
            for path in RESEARCH_DOCS
        ],
        "replay_scripts": [
            {"path": str(path.relative_to(REPO_ROOT)), "sha256": _sha256(path)}
            for path in REPLAY_SCRIPTS
        ],
        "facts": facts,
        "tau": tau,
        "breakthrough": {
            "name": "CPSS-BC research-scope certificate",
            "spec_id": "cpss_bc_research_scope_certificate_v1",
            "lean_files": len(LEAN_FILES),
            "tau_cases": len(tau["case_results"]),
            "invalid_accepts": tau["invalid_accepts"],
            "scoped_claims": [
                "compressed-state DP pruning proof compiles",
                "commit-reveal both params proves single-user SP only",
                "adaptive-window implementation remains empirical",
                "group SP is falsified by precommit collusion",
                "CPSS greedy dominance is falsified under adversarial search",
            ],
        },
        "non_claims": [
            "This certificate does not implement production batch clearing.",
            "This certificate does not prove group strategyproofness.",
            "This certificate does not prove universal CPSS greedy dominance.",
            "This certificate does not promote adaptive-window exactness beyond the recorded empirical scope.",
        ],
        "replay_command": "python3 tools/zenodex_cpss_bc_research_scope_certificate_20260628.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX CPSS-BC Research Scope Certificate - 2026-06-28",
        "",
        "## Executive Result",
        "",
        "`cpss_bc_research_scope_certificate_v1` admits the CPSS-BC research bundle only when its formal claims, falsifications, replay artifacts, and no-authority boundary are all present.",
        "The certificate is deliberately scoped as research evidence. It does not implement production clearing or authorize settlement.",
        "",
        "## Facts",
        "",
    ]
    for key, value in report["facts"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(
        [
            "",
            "## Lean Verification",
            "",
            "| file | compile | seconds |",
            "| --- | --- | ---: |",
        ]
    )
    for row in report["lean"]["files"]:
        lines.append(f"| `{row['path']}` | `{row['ok']}` | `{row['elapsed_s']}` |")
    lines.extend(
        [
            "",
            "## Tau Cases",
            "",
            "| case | ok | admitted |",
            "| --- | --- | ---: |",
        ]
    )
    for case in report["tau"]["case_results"]:
        lines.append(f"| `{case['case_id']}` | `{case['ok']}` | `{case['got'].get('o5')}` |")
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```"])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    report = _build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    ok = (
        all(value == 1 for value in report["facts"].values())
        and bool(report["lean"]["compile_ok"])
        and bool(report["lean"]["no_forbidden_tokens"])
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

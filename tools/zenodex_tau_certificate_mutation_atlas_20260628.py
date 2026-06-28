#!/usr/bin/env python3
"""Replay mutation coverage for promoted Tau frontier certificates."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tau_certificate_mutation_atlas_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_TAU_CERTIFICATE_MUTATION_ATLAS_20260628.md"
SPEC_ROOT = REPO_ROOT / "src" / "tau_specs" / "recommended"


@dataclass(frozen=True)
class MutationCase:
    case_id: str
    step: dict[str, int]
    expected_primary: int
    rationale: str


@dataclass(frozen=True)
class CertificateSurface:
    surface_id: str
    spec_id: str
    spec_path: Path
    primary_output: str
    base_step: dict[str, int]
    required_inputs: tuple[str, ...]
    custom_mutations: tuple[MutationCase, ...] = field(default_factory=tuple)
    benefit: str = ""
    non_claims: tuple[str, ...] = field(default_factory=tuple)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _with(base: Mapping[str, int], **overrides: int) -> dict[str, int]:
    step = {str(key): int(value) for key, value in base.items()}
    step.update({str(key): int(value) for key, value in overrides.items()})
    return step


def _zero_mutations(surface: CertificateSurface) -> tuple[MutationCase, ...]:
    cases: list[MutationCase] = []
    for input_name in surface.required_inputs:
        if int(surface.base_step[input_name]) != 1:
            raise ValueError(f"{surface.surface_id}.{input_name} is not a true required input")
        cases.append(
            MutationCase(
                case_id=f"flip_{input_name}_reject",
                step=_with(surface.base_step, **{input_name: 0}),
                expected_primary=0,
                rationale=f"Required input {input_name} is missing, so {surface.primary_output} must reject.",
            )
        )
    return tuple(cases)


def _surface_cases(surface: CertificateSurface) -> tuple[MutationCase, ...]:
    return (
        MutationCase(
            case_id="positive_accept",
            step=dict(surface.base_step),
            expected_primary=1,
            rationale=f"All required facts for {surface.surface_id} are present.",
        ),
        *_zero_mutations(surface),
        *surface.custom_mutations,
    )


def _surfaces() -> tuple[CertificateSurface, ...]:
    frontier_route = {
        "i1": 1,
        "i2": 1,
        "i3": 1,
        "i4": 1,
        "i5": 1,
        "i6": 1,
        "i7": 1,
        "i8": 1,
        "i9": 1,
        "i10": 1,
        "i11": 0,
        "i12": 0,
    }
    ab_mode = {
        "i1": 1,
        "i2": 1,
        "i3": 0,
        "i4": 1,
        "i5": 1,
        "i6": 1,
        "i7": 1,
        "i8": 1,
        "i9": 1,
        "i10": 1,
        "i11": 1,
    }
    cow_mode = _with(ab_mode, i2=0, i3=1)
    route_split = {f"i{idx}": 1 for idx in range(1, 12)}
    oracle_polytope = {f"i{idx}": 1 for idx in range(1, 12)}
    solver_portfolio = {f"i{idx}": 1 for idx in range(1, 16)}
    ebrm_selector = {f"i{idx}": 1 for idx in range(1, 12)}

    return (
        CertificateSurface(
            surface_id="frontier_menu_route_mode",
            spec_id="frontier_certificate_menu_v1",
            spec_path=SPEC_ROOT / "frontier_certificate_menu_v1.tau",
            primary_output="o4",
            base_step=frontier_route,
            required_inputs=("i1", "i2", "i3", "i4", "i5", "i6", "i7", "i8", "i9", "i10"),
            custom_mutations=(
                MutationCase(
                    "oracle_mode_collision_reject",
                    _with(frontier_route, i11=1),
                    0,
                    "Adding a second optimizer mode violates one-hot mode selection.",
                ),
                MutationCase(
                    "ab_cow_mode_collision_reject",
                    _with(frontier_route, i12=1),
                    0,
                    "Adding a second optimizer mode violates one-hot mode selection.",
                ),
            ),
            benefit="Shared one-hot certificate menu rejects missing host facts and mixed optimizer modes.",
            non_claims=("Does not prove the underlying route, oracle, AB, or CoW optimizer.",),
        ),
        CertificateSurface(
            surface_id="ab_cow_exact_solver_ab_mode",
            spec_id="ab_cow_exact_solver_envelope_v1",
            spec_path=SPEC_ROOT / "ab_cow_exact_solver_envelope_v1.tau",
            primary_output="o6",
            base_step=ab_mode,
            required_inputs=("i1", "i2", "i4", "i5", "i6", "i7", "i8", "i9", "i10", "i11"),
            custom_mutations=(
                MutationCase(
                    "two_modes_reject",
                    _with(ab_mode, i3=1),
                    0,
                    "AB and CoW modes cannot both be active.",
                ),
            ),
            benefit="AB ordering certificates reject missing full-state scope, parity, fallback, budget, or no-authority facts.",
            non_claims=("Does not claim compressed one-record Held-Karp state is sound.",),
        ),
        CertificateSurface(
            surface_id="ab_cow_exact_solver_cow_mode",
            spec_id="ab_cow_exact_solver_envelope_v1",
            spec_path=SPEC_ROOT / "ab_cow_exact_solver_envelope_v1.tau",
            primary_output="o6",
            base_step=cow_mode,
            required_inputs=("i1", "i3", "i4", "i5", "i6", "i7", "i8", "i9", "i10", "i11"),
            custom_mutations=(
                MutationCase(
                    "two_modes_reject",
                    _with(cow_mode, i2=1),
                    0,
                    "AB and CoW modes cannot both be active.",
                ),
            ),
            benefit="CoW certificates reject missing uncoupled-capacity scope, parity, fallback, budget, or no-authority facts.",
            non_claims=("Does not claim arbitrary grouped-capacity CoW matching is polynomial.",),
        ),
        CertificateSurface(
            surface_id="route_split_window_certificate",
            spec_id="route_split_window_certificate_v1",
            spec_path=SPEC_ROOT / "route_split_window_certificate_v1.tau",
            primary_output="o4",
            base_step=route_split,
            required_inputs=tuple(f"i{idx}" for idx in range(1, 12)),
            benefit="Route split certificates reject missing local-window, parity, quote replay, budget, fallback, exact-out, or no-authority facts.",
            non_claims=("Does not rely on naive discrete-convex first-difference monotonicity.",),
        ),
        CertificateSurface(
            surface_id="oracle_polytope_certificate",
            spec_id="oracle_polytope_frontier_envelope_v1",
            spec_path=SPEC_ROOT / "oracle_polytope_frontier_envelope_v1.tau",
            primary_output="o5",
            base_step=oracle_polytope,
            required_inputs=tuple(f"i{idx}" for idx in range(1, 12)),
            benefit="Oracle interval certificates reject missing interval, boundary, assumption, fail-closed, or no-authority facts.",
            non_claims=("Does not promote one-field intervals to a Cartesian product box.",),
        ),
        CertificateSurface(
            surface_id="solver_portfolio_upgrade_certificate",
            spec_id="solver_portfolio_upgrade_certificate_v1",
            spec_path=SPEC_ROOT / "solver_portfolio_upgrade_certificate_v1.tau",
            primary_output="o6",
            base_step=solver_portfolio,
            required_inputs=tuple(f"i{idx}" for idx in range(1, 16)),
            benefit="Solver portfolio certificates reject missing AB/CoW evidence, performance, rollback, fallback, or no-authority facts.",
            non_claims=("Does not authorize settlement or state transitions.",),
        ),
        CertificateSurface(
            surface_id="tauspec_ebrm_frontier_selector",
            spec_id="tauspec_ebrm_frontier_selection_certificate_v1",
            spec_path=SPEC_ROOT / "tauspec_ebrm_frontier_selection_certificate_v1.tau",
            primary_output="o5",
            base_step=ebrm_selector,
            required_inputs=tuple(f"i{idx}" for idx in range(1, 12)),
            benefit="TauSpecEBRM selector certificates reject missing replay, invalid-accept, coverage, budget, advisory, or no-authority facts.",
            non_claims=("Does not rank unbounded Tau specification pools.",),
        ),
    )


def _run_surface(surface: CertificateSurface, tau_bin: str) -> dict[str, Any]:
    cases = _surface_cases(surface)
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=surface.spec_path,
        steps=[case.step for case in cases],
        timeout_s=25.0,
    )
    rows: list[dict[str, Any]] = []
    invalid_accepts = 0
    false_rejects = 0
    for idx, case in enumerate(cases):
        got = {str(key): int(value) for key, value in outputs.get(idx, {}).items()}
        got_primary = got.get(surface.primary_output)
        ok = got_primary == int(case.expected_primary)
        if int(case.expected_primary) == 0 and got_primary == 1:
            invalid_accepts += 1
        if int(case.expected_primary) == 1 and got_primary != 1:
            false_rejects += 1
        rows.append(
            {
                "case_id": case.case_id,
                "ok": ok,
                "expected_primary": int(case.expected_primary),
                "got_primary": got_primary,
                "primary_output": surface.primary_output,
                "got": got,
                "step": dict(case.step),
                "rationale": case.rationale,
            }
        )
    return {
        "surface_id": surface.surface_id,
        "spec_id": surface.spec_id,
        "spec_path": str(surface.spec_path.relative_to(REPO_ROOT)),
        "sha256": _sha256(surface.spec_path),
        "primary_output": surface.primary_output,
        "required_input_count": len(surface.required_inputs),
        "custom_mutation_count": len(surface.custom_mutations),
        "case_count": len(cases),
        "mutation_count": len(cases) - 1,
        "invalid_accepts": invalid_accepts,
        "false_rejects": false_rejects,
        "ok": invalid_accepts == 0 and false_rejects == 0 and all(row["ok"] for row in rows),
        "benefit": surface.benefit,
        "non_claims": list(surface.non_claims),
        "cases": rows,
    }


def build_report(tau_bin: str | None = None) -> dict[str, Any]:
    resolved_tau_bin = tau_bin or find_tau_bin(REPO_ROOT, profile="latest")
    if not resolved_tau_bin:
        return {
            "schema": "zenodex.tau_certificate_mutation_atlas_report.v1",
            "date": "2026-06-28",
            "ok": False,
            "error": "latest Tau binary not found",
            "surfaces": [],
        }
    surfaces = [_run_surface(surface, resolved_tau_bin) for surface in _surfaces()]
    total_cases = sum(int(surface["case_count"]) for surface in surfaces)
    total_mutations = sum(int(surface["mutation_count"]) for surface in surfaces)
    total_required_inputs = sum(int(surface["required_input_count"]) for surface in surfaces)
    invalid_accepts = sum(int(surface["invalid_accepts"]) for surface in surfaces)
    false_rejects = sum(int(surface["false_rejects"]) for surface in surfaces)
    ok = all(bool(surface["ok"]) for surface in surfaces) and invalid_accepts == 0 and false_rejects == 0
    return {
        "schema": "zenodex.tau_certificate_mutation_atlas_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "breakthrough": {
            "name": "Tau certificate mutation atlas",
            "summary": "A reusable mutation-replay atlas for promoted Tau frontier certificates. Every required host-projected fact is flipped at least once and must make the primary certificate output reject.",
            "authority_boundary": "Tau validates certificate facts only; host/kernel verifiers remain authoritative for arithmetic, matching, routing, oracle updates, settlement, and state transitions.",
        },
        "tau": {
            "tau_bin": resolved_tau_bin,
            "tau_version": _tau_version(resolved_tau_bin),
        },
        "totals": {
            "surface_count": len(surfaces),
            "case_count": total_cases,
            "mutation_count": total_mutations,
            "required_input_mutations": total_required_inputs,
            "invalid_accepts": invalid_accepts,
            "false_rejects": false_rejects,
        },
        "surfaces": surfaces,
        "new_spec_pattern": {
            "pattern": "required_fact_mutation_atlas",
            "benefit": "Turns promoted Tau specs into executable fail-closed checklists. Missing evidence, hidden authority, mode collisions, and budget/profile gaps become replayed rejects.",
        },
        "non_claims": [
            "The atlas does not prove the host-computed facts are true; it verifies Tau rejects when those facts are absent.",
            "The atlas does not authorize settlement, oracle updates, governance, or state roots.",
            "The atlas covers the declared promoted frontier certificate surfaces, not every Tau file in the repository.",
        ],
        "replay_command": "python3 tools/zenodex_tau_certificate_mutation_atlas_20260628.py",
    }


def _write_markdown(report: Mapping[str, Any], output: Path) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Tau Certificate Mutation Atlas - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(str(report["breakthrough"]["summary"]))
    lines.append("")
    lines.append(str(report["breakthrough"]["authority_boundary"]))
    lines.append("")
    totals = report["totals"]
    lines.append("## Mutation Coverage")
    lines.append("")
    lines.append(f"- Surfaces: `{totals['surface_count']}`")
    lines.append(f"- Cases: `{totals['case_count']}`")
    lines.append(f"- Mutations: `{totals['mutation_count']}`")
    lines.append(f"- Required input flips: `{totals['required_input_mutations']}`")
    lines.append(f"- Invalid accepts: `{totals['invalid_accepts']}`")
    lines.append(f"- False rejects: `{totals['false_rejects']}`")
    lines.append("")
    lines.append("## Surfaces")
    lines.append("")
    lines.append("| surface | spec | primary | mutations | invalid accepts |")
    lines.append("| --- | --- | --- | ---: | ---: |")
    for surface in report["surfaces"]:
        lines.append(
            f"| `{surface['surface_id']}` | `{surface['spec_id']}` | `{surface['primary_output']}` | `{surface['mutation_count']}` | `{surface['invalid_accepts']}` |"
        )
    lines.append("")
    lines.append("## Design Pattern")
    lines.append("")
    pattern = report["new_spec_pattern"]
    lines.append(f"`{pattern['pattern']}`: {pattern['benefit']}")
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(str(report["replay_command"]))
    lines.append("```")
    lines.append("")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path, output_md: Path, tau_bin: str | None = None) -> dict[str, Any]:
    report = build_report(tau_bin=tau_bin)
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if report.get("ok"):
        _write_markdown(report, output_md)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(REPORT_JSON))
    parser.add_argument("--output-md", default=str(REPORT_MD))
    parser.add_argument("--tau-bin", default=None)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json), Path(args.output_md), tau_bin=args.tau_bin)
    print(
        json.dumps(
            {
                "ok": bool(report.get("ok")),
                "json": str(Path(args.output_json)),
                "report": str(Path(args.output_md)),
                "surface_count": int(report.get("totals", {}).get("surface_count", 0)),
                "mutation_count": int(report.get("totals", {}).get("mutation_count", 0)),
                "invalid_accepts": int(report.get("totals", {}).get("invalid_accepts", 0)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if bool(report.get("ok")) else 1


if __name__ == "__main__":
    raise SystemExit(main())

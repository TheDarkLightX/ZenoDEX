#!/usr/bin/env python3
"""Replay a Tau-gated Research Kernel frontier selector certificate."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import sys
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_rk_frontier_spec_selector_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_RK_FRONTIER_SPEC_SELECTOR_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "rk_frontier_spec_selector_v1.tau"

RUN_ID = "tau-spec-frontier-ebrm-20260626"
BUDGET = 7
MAX_CANDIDATES = 12
MAX_AXIS_COUNT = 8

AXES: tuple[str, ...] = (
    "host_projection",
    "counterexample_synthesis",
    "performance_frontier",
    "compiler_search",
    "energy_model",
    "state_space_reformulation",
    "ab_ordering",
    "cow_matching",
)


@dataclass(frozen=True)
class FrontierCandidate:
    candidate_id: str
    title: str
    cost: int
    value: int
    rk_priority: float
    axes: tuple[str, ...]
    parent_refs: tuple[str, ...]
    negative_control_count: int
    replay_command: str
    non_claim: str


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def frontier_candidates() -> tuple[FrontierCandidate, ...]:
    """Return the bounded RK-frontier-derived candidate pool for this receipt."""

    return (
        FrontierCandidate(
            candidate_id="rk_host_projection_perf_energy_selector",
            title="Host-projected Tau frontier selector",
            cost=2,
            value=33,
            rk_priority=2.50,
            axes=("host_projection", "performance_frontier", "energy_model"),
            parent_refs=(
                "atom_86644e461ecd41cd",
                "atom_3d38c5d1362f4f9c",
                "atom_bd3382a9c3ea4b4e",
                "claim-tau-ebrm-architecture",
            ),
            negative_control_count=3,
            replay_command="python3 tools/check_rk_frontier_spec_selector.py",
            non_claim="Advisory selection only; deterministic Tau, host, and kernel checks decide acceptance.",
        ),
        FrontierCandidate(
            candidate_id="rk_counterexample_compiler_synthesis",
            title="Counterexample-driven Tau-spec synthesis lane",
            cost=2,
            value=31,
            rk_priority=2.47,
            axes=("counterexample_synthesis", "compiler_search"),
            parent_refs=("atom_cf063839e779437f", "atom_965e4ac324314e9e"),
            negative_control_count=4,
            replay_command="python3 tools/check_rk_frontier_spec_selector.py --mutation-only",
            non_claim="Generated specs remain candidates until replay, lint, host projection, and negative controls pass.",
        ),
        FrontierCandidate(
            candidate_id="rk_state_ab_ordering_witness",
            title="AB ordering state-space witness lane",
            cost=2,
            value=28,
            rk_priority=2.21,
            axes=("state_space_reformulation", "ab_ordering"),
            parent_refs=("atom_40f28785d5f94303", "atom_33f7d03f5c9b42de", "atom_9870aff28a0841f6"),
            negative_control_count=3,
            replay_command="python3 tools/check_ab_subset_dp_dominance_certificate.py",
            non_claim="AB exactness claims stay bounded to their declared integer CPMM domain and replay corpus.",
        ),
        FrontierCandidate(
            candidate_id="rk_cow_capacity_extension",
            title="CoW capacity matching extension lane",
            cost=1,
            value=18,
            rk_priority=2.18,
            axes=("cow_matching", "counterexample_synthesis"),
            parent_refs=(
                "docs/research/ZENODEX_COW_CAPACITY_DP_CERTIFICATE_20260628.md",
                "src/tau_specs/recommended/cow_capacity_dp_certificate_v1.tau",
            ),
            negative_control_count=2,
            replay_command="python3 tools/check_cow_capacity_dp_certificate.py",
            non_claim="CoW capacity certificates do not authorize settlement materialization.",
        ),
        FrontierCandidate(
            candidate_id="rk_route_split_window_promotion_audit",
            title="Route split-window promotion audit",
            cost=1,
            value=12,
            rk_priority=2.37,
            axes=("performance_frontier", "host_projection"),
            parent_refs=("src/tau_specs/recommended/route_split_window_certificate_v1.tau",),
            negative_control_count=2,
            replay_command="python3 tools/zenodex_tau_route_split_window_breakthrough_20260628.py",
            non_claim="Route certificates remain certificate-lane evidence, not route or settlement authority.",
        ),
        FrontierCandidate(
            candidate_id="rk_compiler_profile_smoke",
            title="Tau compiler/profile smoke selector",
            cost=1,
            value=10,
            rk_priority=2.05,
            axes=("compiler_search",),
            parent_refs=("src/tau_specs/recommended/spec_profiles.json", "tools/check_tau_supported_runtime_subset.py"),
            negative_control_count=1,
            replay_command="bash tests/tau/test_specs_syntax.sh",
            non_claim="Syntax/profile evidence is necessary context, not semantic proof.",
        ),
        FrontierCandidate(
            candidate_id="rk_energy_only_ranker",
            title="Energy-model-only ranker lane",
            cost=2,
            value=15,
            rk_priority=2.38,
            axes=("energy_model",),
            parent_refs=("claim-tau-ebrm-architecture", "tools/tau_spec_frontier_20260626.py"),
            negative_control_count=2,
            replay_command="python3 tools/tau_spec_frontier_20260626.py",
            non_claim="Energy scores are advisory rankings and cannot promote specs by themselves.",
        ),
        FrontierCandidate(
            candidate_id="rk_claim_scope_hygiene",
            title="Claim-scope hygiene lane",
            cost=1,
            value=8,
            rk_priority=1.95,
            axes=("host_projection",),
            parent_refs=("tools/check_research_kernel_frontier_hygiene_20260628.py",),
            negative_control_count=2,
            replay_command="python3 tools/check_research_kernel_frontier_hygiene_20260628.py",
            non_claim="Hygiene receipts reduce stale-claim risk; they do not prove algorithmic correctness.",
        ),
    )


def _axis_mask(axes: Sequence[str]) -> int:
    mask = 0
    for axis in axes:
        if axis not in AXES:
            raise ValueError(f"unknown axis: {axis}")
        mask |= 1 << AXES.index(axis)
    return mask


def _selection_mask(selection: Sequence[FrontierCandidate]) -> int:
    mask = 0
    for candidate in selection:
        mask |= _axis_mask(candidate.axes)
    return mask


def _selection_ids(selection: Sequence[FrontierCandidate]) -> tuple[str, ...]:
    return tuple(sorted(candidate.candidate_id for candidate in selection))


def _selection_key(selection: Sequence[FrontierCandidate]) -> tuple[int, int, int, int, int, int]:
    mask = _selection_mask(selection)
    total_cost = sum(candidate.cost for candidate in selection)
    return (
        int(mask == (1 << len(AXES)) - 1),
        mask.bit_count(),
        sum(candidate.value for candidate in selection),
        sum(candidate.negative_control_count for candidate in selection),
        len({parent for candidate in selection for parent in candidate.parent_refs}),
        -total_cost,
    )


def _is_better(left: Sequence[FrontierCandidate], right: Sequence[FrontierCandidate] | None) -> bool:
    if right is None:
        return True
    left_key = _selection_key(left)
    right_key = _selection_key(right)
    return left_key > right_key or (left_key == right_key and _selection_ids(left) < _selection_ids(right))


def exact_dp_select(candidates: Sequence[FrontierCandidate], *, budget: int = BUDGET) -> dict[str, Any]:
    """Solve the budgeted max-coverage selector with bitmask DP."""

    dp: dict[tuple[int, int], tuple[FrontierCandidate, ...]] = {(0, 0): tuple()}
    transition_count = 0
    for candidate in candidates:
        updates = dict(dp)
        candidate_mask = _axis_mask(candidate.axes)
        for (spent, mask), selection in dp.items():
            transition_count += 1
            next_spent = spent + int(candidate.cost)
            if next_spent > budget:
                continue
            next_mask = mask | candidate_mask
            next_selection = tuple(sorted((*selection, candidate), key=lambda item: item.candidate_id))
            state = (next_spent, next_mask)
            if _is_better(next_selection, updates.get(state)):
                updates[state] = next_selection
        dp = updates

    best: tuple[FrontierCandidate, ...] | None = None
    for selection in dp.values():
        if _is_better(selection, best):
            best = selection
    selected = best or tuple()
    return {
        "selection": selected,
        "states": len(dp),
        "transition_count": transition_count,
        "complexity": "O(n * B * 2^m) time, O(B * 2^m) space",
    }


def brute_force_select(candidates: Sequence[FrontierCandidate], *, budget: int = BUDGET) -> tuple[tuple[FrontierCandidate, ...], int]:
    best: tuple[FrontierCandidate, ...] | None = None
    evaluated = 0
    for size in range(len(candidates) + 1):
        for combo in combinations(candidates, size):
            evaluated += 1
            if sum(candidate.cost for candidate in combo) > budget:
                continue
            selection = tuple(sorted(combo, key=lambda item: item.candidate_id))
            if _is_better(selection, best):
                best = selection
    return best or tuple(), evaluated


def priority_baseline(candidates: Sequence[FrontierCandidate], *, budget: int = BUDGET) -> tuple[FrontierCandidate, ...]:
    selected: list[FrontierCandidate] = []
    spent = 0
    for candidate in sorted(candidates, key=lambda item: (-item.rk_priority, item.cost, item.candidate_id)):
        if spent + candidate.cost <= budget:
            selected.append(candidate)
            spent += candidate.cost
    return tuple(sorted(selected, key=lambda item: item.candidate_id))


def single_lens_baseline(candidates: Sequence[FrontierCandidate], *, budget: int = BUDGET) -> tuple[FrontierCandidate, ...]:
    selected: list[FrontierCandidate] = []
    spent = 0
    used_ids: set[str] = set()
    for axis in AXES:
        ranked = sorted(
            (candidate for candidate in candidates if axis in candidate.axes and candidate.candidate_id not in used_ids),
            key=lambda item: (-item.rk_priority, item.cost, item.candidate_id),
        )
        if not ranked:
            continue
        candidate = ranked[0]
        if spent + candidate.cost <= budget:
            selected.append(candidate)
            used_ids.add(candidate.candidate_id)
            spent += candidate.cost
    return tuple(sorted(selected, key=lambda item: item.candidate_id))


def _selection_row(selection: Sequence[FrontierCandidate]) -> dict[str, Any]:
    mask = _selection_mask(selection)
    return {
        "candidate_ids": list(_selection_ids(selection)),
        "total_cost": sum(candidate.cost for candidate in selection),
        "total_value": sum(candidate.value for candidate in selection),
        "negative_control_count": sum(candidate.negative_control_count for candidate in selection),
        "dependency_count": len({parent for candidate in selection for parent in candidate.parent_refs}),
        "covered_axes": [axis for index, axis in enumerate(AXES) if mask & (1 << index)],
        "missing_axes": [axis for index, axis in enumerate(AXES) if not mask & (1 << index)],
        "objective_key": list(_selection_key(selection)),
    }


def _candidate_row(candidate: FrontierCandidate) -> dict[str, Any]:
    return {
        "candidate_id": candidate.candidate_id,
        "title": candidate.title,
        "cost": candidate.cost,
        "value": candidate.value,
        "rk_priority": candidate.rk_priority,
        "axes": list(candidate.axes),
        "parent_refs": list(candidate.parent_refs),
        "negative_control_count": candidate.negative_control_count,
        "replay_command": candidate.replay_command,
        "non_claim": candidate.non_claim,
    }


def build_selector_report() -> dict[str, Any]:
    candidates = frontier_candidates()
    dp_result = exact_dp_select(candidates)
    exact = dp_result["selection"]
    brute, brute_evaluated = brute_force_select(candidates)
    priority = priority_baseline(candidates)
    single_lens = single_lens_baseline(candidates)
    exact_row = _selection_row(exact)
    priority_row = _selection_row(priority)
    single_lens_row = _selection_row(single_lens)
    full_mask = (1 << len(AXES)) - 1

    return {
        "run_id": RUN_ID,
        "budget": BUDGET,
        "axis_count": len(AXES),
        "axes": list(AXES),
        "candidate_count": len(candidates),
        "candidate_pool": [_candidate_row(candidate) for candidate in candidates],
        "dp": {
            "selection": exact_row,
            "states": int(dp_result["states"]),
            "transition_count": int(dp_result["transition_count"]),
            "complexity": dp_result["complexity"],
        },
        "bruteforce_oracle": {
            "selection": _selection_row(brute),
            "evaluated_subsets": brute_evaluated,
            "matches_dp": _selection_ids(brute) == _selection_ids(exact),
        },
        "baselines": {
            "priority_order": priority_row,
            "single_lens": single_lens_row,
        },
        "selector_checks": {
            "all_required_axes_covered": int(_selection_mask(exact) == full_mask),
            "dp_matches_bruteforce": int(_selection_ids(brute) == _selection_ids(exact)),
            "dominates_priority_baseline": int(_selection_key(exact) > _selection_key(priority)),
            "dominates_single_lens_baseline": int(_selection_key(exact) > _selection_key(single_lens)),
            "selected_have_parent_refs": int(all(candidate.parent_refs for candidate in exact)),
            "selected_have_negative_controls": int(all(candidate.negative_control_count > 0 for candidate in exact)),
            "nonvacuous_selection": int(bool(exact)),
        },
    }


def _tau_step(flags: Mapping[str, int], *, active: int = 1, overrides: Mapping[str, int] | None = None) -> dict[str, int]:
    values = {
        "i1": int(active),
        "i2": int(flags.get("deterministic_replay_ok", 0)),
        "i3": int(flags.get("exact_dp_complete", 0)),
        "i4": int(flags.get("required_axes_covered", 0)),
        "i5": int(flags.get("dominates_priority_baseline", 0)),
        "i6": int(flags.get("dominates_single_lens_baseline", 0)),
        "i7": int(flags.get("negative_controls_ok", 0)),
        "i8": int(flags.get("tau_runtime_subset_ok", 0)),
        "i9": int(flags.get("resource_budget_ok", 0)),
        "i10": int(flags.get("rk_dependencies_ok", 0)),
        "i11": int(flags.get("no_authority_effect", 0)),
        "i12": int(flags.get("nonvacuous_selection", 0)),
        "i13": int(flags.get("replay_evidence_ok", 0)),
    }
    if overrides:
        values.update({key: int(value) for key, value in overrides.items()})
    return values


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _run_tau_cases(flags: Mapping[str, int]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "cases": []}

    cases = (
        TauCase(
            "rk_frontier_selector_pass",
            _tau_step(flags),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0},
            "All host-computed selector facts admit the advisory certificate.",
        ),
        TauCase(
            "missing_dp_reject",
            _tau_step(flags, overrides={"i3": 0}),
            {"o1": 0, "o4": 0},
            "Missing exact DP completeness rejects.",
        ),
        TauCase(
            "missing_axis_coverage_reject",
            _tau_step(flags, overrides={"i4": 0}),
            {"o2": 0, "o4": 0},
            "Missing frontier-axis coverage rejects.",
        ),
        TauCase(
            "priority_baseline_reject",
            _tau_step(flags, overrides={"i5": 0}),
            {"o2": 0, "o4": 0},
            "Missing priority-baseline dominance rejects.",
        ),
        TauCase(
            "single_lens_baseline_reject",
            _tau_step(flags, overrides={"i6": 0}),
            {"o2": 0, "o4": 0},
            "Missing single-lens-baseline dominance rejects.",
        ),
        TauCase(
            "authority_reject",
            _tau_step(flags, overrides={"i11": 0}),
            {"o3": 0, "o4": 0},
            "Authority effects are rejected.",
        ),
        TauCase(
            "inactive_safe",
            _tau_step(flags, active=0),
            {"o4": 0, "o5": 1},
            "Inactive requests remain non-admitting while preserving the no-authority rail.",
        ),
    )
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=TAU_SPEC, steps=[case.step for case in cases], timeout_s=15.0)
    rows: list[dict[str, Any]] = []
    ok = True
    for index, case in enumerate(cases):
        got = outputs.get(index, {})
        mismatches = {
            key: {"expected": value, "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != value
        }
        if mismatches:
            ok = False
        rows.append(
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
        "ok": ok,
        "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
        "tau_bin": tau_bin,
        "tau_version": _tau_version(tau_bin),
        "cases": rows,
    }


def _mutation_checks(flags: Mapping[str, int]) -> list[dict[str, Any]]:
    mutations = (
        ("missing_exact_dp", {"i3": 0}, "exact DP completeness is load-bearing"),
        ("missing_axis_coverage", {"i4": 0}, "frontier-axis coverage is load-bearing"),
        ("missing_priority_dominance", {"i5": 0}, "priority-baseline dominance is load-bearing"),
        ("missing_single_lens_dominance", {"i6": 0}, "single-lens-baseline dominance is load-bearing"),
        ("missing_negative_controls", {"i7": 0}, "negative controls are load-bearing"),
        ("missing_rk_dependencies", {"i10": 0}, "Research Kernel dependency refs are load-bearing"),
        ("authority_effect", {"i11": 0}, "the selector must not carry authority effects"),
    )
    rows: list[dict[str, Any]] = []
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    for mutation_id, overrides, rationale in mutations:
        if not tau_bin:
            rows.append({"mutation_id": mutation_id, "accepted": False, "skipped": True, "rationale": rationale})
            continue
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=TAU_SPEC,
            steps=[_tau_step(flags, overrides=overrides)],
            timeout_s=15.0,
        )
        rows.append(
            {
                "mutation_id": mutation_id,
                "accepted": bool(outputs.get(0, {}).get("o4") == 1),
                "skipped": False,
                "got": outputs.get(0, {}),
                "rationale": rationale,
            }
        )
    return rows


def _fingerprint(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _tau_runtime_subset_check() -> dict[str, Any]:
    proc = subprocess.run(
        [sys.executable, "tools/check_tau_supported_runtime_subset.py", str(TAU_SPEC.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )
    return {
        "ok": proc.returncode == 0,
        "command": f"python3 tools/check_tau_supported_runtime_subset.py {TAU_SPEC.relative_to(REPO_ROOT)}",
        "returncode": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def build_report() -> dict[str, Any]:
    selector = build_selector_report()
    replay_again = build_selector_report()
    selector_checks = selector["selector_checks"]
    runtime_subset = _tau_runtime_subset_check()
    selected_commands = [
        row["replay_command"]
        for row in selector["candidate_pool"]
        if row["candidate_id"] in set(selector["dp"]["selection"]["candidate_ids"])
    ]
    flags = {
        "deterministic_replay_ok": int(_fingerprint(selector) == _fingerprint(replay_again)),
        "exact_dp_complete": int(selector_checks["dp_matches_bruteforce"] == 1),
        "required_axes_covered": int(selector_checks["all_required_axes_covered"] == 1),
        "dominates_priority_baseline": int(selector_checks["dominates_priority_baseline"] == 1),
        "dominates_single_lens_baseline": int(selector_checks["dominates_single_lens_baseline"] == 1),
        "negative_controls_ok": int(selector_checks["selected_have_negative_controls"] == 1),
        "tau_runtime_subset_ok": int(bool(runtime_subset["ok"])),
        "resource_budget_ok": int(
            selector["candidate_count"] <= MAX_CANDIDATES
            and selector["axis_count"] <= MAX_AXIS_COUNT
            and selector["dp"]["states"] <= (BUDGET + 1) * (2 ** len(AXES))
        ),
        "rk_dependencies_ok": int(selector_checks["selected_have_parent_refs"] == 1),
        "no_authority_effect": 1,
        "nonvacuous_selection": int(selector_checks["nonvacuous_selection"] == 1),
        "replay_evidence_ok": int(bool(selected_commands) and all(command.startswith("python3 tools/") for command in selected_commands)),
    }
    tau = _run_tau_cases(flags)
    mutation_rows = _mutation_checks(flags)
    if any(bool(row["accepted"]) for row in mutation_rows):
        flags = copy.deepcopy(flags)
        flags["negative_controls_ok"] = 0
        tau = _run_tau_cases(flags)
    ok = all(value == 1 for value in flags.values()) and bool(tau["ok"]) and all(
        not bool(row["accepted"]) for row in mutation_rows
    )
    return {
        "schema": "zenodex.rk_frontier_spec_selector_report.v1",
        "date": "2026-06-28",
        "ok": bool(ok),
        "spec_id": "rk_frontier_spec_selector_v1",
        "selector": selector,
        "flags": flags,
        "runtime_subset": runtime_subset,
        "selected_replay_commands": selected_commands,
        "tau": tau,
        "mutation_checks": mutation_rows,
        "claim": (
            "A bounded host-side DP can convert the current-branch Research Kernel Tau frontier snapshot into a nonvacuous "
            "next-spec queue that covers host projection, counterexample synthesis, performance, compiler/search, "
            "energy-model, state-space, AB-ordering, and CoW-matching axes while dominating priority-order and "
            "single-lens baselines under the declared objective."
        ),
        "non_claims": [
            "This is an advisory research selector, not a settlement, oracle, governance, release, or repository authority.",
            "The candidate pool is the declared Research Kernel frontier snapshot in this receipt.",
            "This receipt does not supersede the broader TauSpecEBRM compounding-frontier certificate on the tokenomics POL branch.",
            "Tau does not query Research Kernel, score candidates, solve the DP, run tests, or promote claims.",
            "Selected experiments still require their own replay, proof, fuzzing, and review gates before promotion.",
        ],
        "replay_command": "python3 tools/check_rk_frontier_spec_selector.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    selector = report["selector"]
    exact = selector["dp"]["selection"]
    priority = selector["baselines"]["priority_order"]
    single_lens = selector["baselines"]["single_lens"]
    lines = [
        "# ZenoDEX Research Kernel Frontier Spec Selector - 2026-06-28",
        "",
        "## Executive Result",
        "",
        str(report["claim"]),
        "",
        f"- Research Kernel run: `{selector['run_id']}`",
        f"- Candidate pool: `{selector['candidate_count']}`",
        f"- Budget: `{selector['budget']}`",
        f"- Axis count: `{selector['axis_count']}`",
        f"- DP states: `{selector['dp']['states']}`",
        f"- DP/bruteforce parity: `{selector['bruteforce_oracle']['matches_dp']}`",
        f"- Tau replay ok: `{report['tau']['ok']}`",
        "",
        "## Selected Queue",
        "",
        "| selected candidate |",
        "| --- |",
    ]
    for candidate_id in exact["candidate_ids"]:
        lines.append(f"| `{candidate_id}` |")
    lines.extend(
        [
            "",
            "## Coverage Comparison",
            "",
            "| selector | cost | value | axes covered | missing axes |",
            "| --- | ---: | ---: | ---: | --- |",
            f"| exact DP | `{exact['total_cost']}` | `{exact['total_value']}` | `{len(exact['covered_axes'])}` | `{', '.join(exact['missing_axes']) or 'none'}` |",
            f"| priority order | `{priority['total_cost']}` | `{priority['total_value']}` | `{len(priority['covered_axes'])}` | `{', '.join(priority['missing_axes']) or 'none'}` |",
            f"| single lens | `{single_lens['total_cost']}` | `{single_lens['total_value']}` | `{len(single_lens['covered_axes'])}` | `{', '.join(single_lens['missing_axes']) or 'none'}` |",
            "",
            "## Algorithm",
            "",
            "The host solves a budgeted max-coverage problem by DP over `(spent, axis_mask)`. The exact objective is `(all axes covered, axis count, value, negative-control count, dependency count, -cost)` with deterministic candidate-id tie-breaks.",
            "",
            "Complexity: `O(n * B * 2^m)` time and `O(B * 2^m)` space, where `n` is candidate count, `B` is budget, and `m` is the number of frontier axes.",
            "",
            "## Tau Boundary",
            "",
            "`src/tau_specs/recommended/rk_frontier_spec_selector_v1.tau` admits only host-projected facts: deterministic replay, exact-DP completeness, frontier-axis coverage, baseline dominance, negative controls, runtime-subset compatibility, resource budget, Research Kernel dependencies, nonvacuity, replay evidence, and no authority effects.",
            "",
            "## Mutation Checks",
            "",
            "| mutation | accepted | rationale |",
            "| --- | --- | --- |",
        ]
    )
    for row in report["mutation_checks"]:
        lines.append(f"| `{row['mutation_id']}` | `{row['accepted']}` | {row['rationale']} |")
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path = REPORT_JSON) -> dict[str, Any]:
    report = build_report()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(REPORT_JSON))
    parser.add_argument(
        "--mutation-only",
        action="store_true",
        help="Return the selector report without writing artifacts; used as a stable candidate replay command.",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = build_report() if args.mutation_only else run(Path(args.output_json))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "spec_id": report["spec_id"],
                "candidate_count": report["selector"]["candidate_count"],
                "selected": report["selector"]["dp"]["selection"]["candidate_ids"],
                "missing_axes": report["selector"]["dp"]["selection"]["missing_axes"],
                "tau_ok": report["tau"]["ok"],
                "report": str(REPORT_MD),
                "json": str(Path(args.output_json)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

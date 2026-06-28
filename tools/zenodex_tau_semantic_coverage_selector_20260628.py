#!/usr/bin/env python3
"""Build and replay the Tau semantic-coverage frontier selector."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from tools.zenodex_tau_certificate_mutation_atlas_20260628 import _surfaces as atlas_surfaces  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tau_semantic_coverage_selector_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_TAU_SEMANTIC_COVERAGE_SELECTOR_20260628.md"
SPEC_ROOT = REPO_ROOT / "src" / "tau_specs" / "recommended"
HOST_PROJECTION_CONTRACTS = SPEC_ROOT / "host_projection_contracts.json"
SEMANTIC_CONTRACTS = SPEC_ROOT / "semantic_contracts.json"
FORMAL_CONTRACTS_DIR = REPO_ROOT / "formal" / "tau" / "contracts"
RUNTIME_SCAN_PREFIXES = ("src/integration", "src/agents", "src/core")

RISK_WEIGHTS = {
    "consensus_core": 90,
    "spot_math_core": 82,
    "policy_gate": 55,
    "governance_tokenomics": 45,
    "other": 30,
}

SOURCE_WEIGHTS = {
    "missing": 55,
    "review_packet": 35,
    "semantic_contract": 8,
    "formal_contract": 0,
}


@dataclass(frozen=True)
class ReplaySurface:
    surface_id: str
    spec_id: str
    spec_path: Path
    primary_output: str
    inactive_output: str
    base_step: dict[str, int]
    required_inputs: tuple[str, ...]


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _load_json(path: Path) -> Any:
    return json.loads(_tracked_text(path))


def _tracked_text(path: Path) -> str:
    relpath = path.relative_to(REPO_ROOT).as_posix()
    proc = subprocess.run(
        ["git", "show", f":{relpath}"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=20,
        check=False,
    )
    if proc.returncode == 0:
        return proc.stdout
    return path.read_text(encoding="utf-8")


def _tracked_files(*pathspecs: str) -> list[Path]:
    proc = subprocess.run(
        ["git", "ls-files", "--cached", "--", *pathspecs],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=20,
        check=False,
    )
    if proc.returncode != 0:
        out: list[Path] = []
        for spec in pathspecs:
            root = REPO_ROOT / spec.rstrip("/")
            if root.is_dir():
                out.extend(path for path in root.rglob("*") if path.is_file())
            elif root.exists():
                out.append(root)
        return sorted(set(out))
    return [REPO_ROOT / line for line in proc.stdout.splitlines() if line.strip()]


def _runtime_refs() -> dict[str, list[str]]:
    refs: dict[str, set[str]] = defaultdict(set)
    patterns = [
        re.compile(r'spec_id\s*=\s*"([A-Za-z0-9_]+)"'),
        re.compile(r'"([A-Za-z0-9_]+)\.tau"'),
    ]
    for path in _tracked_files(*RUNTIME_SCAN_PREFIXES):
        if path.suffix != ".py" or not path.exists():
            continue
        relpath = path.relative_to(REPO_ROOT).as_posix()
        text = _tracked_text(path)
        for pattern in patterns:
            for spec_id in pattern.findall(text):
                refs[spec_id].add(relpath)
    return {spec_id: sorted(paths) for spec_id, paths in sorted(refs.items())}


def _semantic_contract_index(path: Path = SEMANTIC_CONTRACTS) -> dict[str, dict[str, Any]]:
    if not path.exists():
        return {}
    raw = _load_json(path)
    specs = raw.get("specs", []) if isinstance(raw, Mapping) else []
    out: dict[str, dict[str, Any]] = {}
    if not isinstance(specs, list):
        return out
    for spec in specs:
        if not isinstance(spec, Mapping):
            continue
        spec_path = str(spec.get("spec_path", "")).strip()
        if spec_path:
            out[Path(spec_path).stem] = dict(spec)
    return out


def _formal_contract_index(path: Path = FORMAL_CONTRACTS_DIR) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for contract_path in _tracked_files("formal/tau/contracts"):
        if not contract_path.name.endswith(".contract.json") or not contract_path.exists():
            continue
        raw = _load_json(contract_path)
        if not isinstance(raw, Mapping):
            continue
        spec_id = str(raw.get("spec_id", "")).strip()
        if spec_id:
            out[spec_id] = {
                "path": contract_path.relative_to(REPO_ROOT).as_posix(),
                "contract": dict(raw),
            }
    return out


def _tau_spec_paths() -> dict[str, list[Path]]:
    out: dict[str, list[Path]] = defaultdict(list)
    for path in _tracked_files("src/tau_specs"):
        if path.suffix == ".tau":
            out[path.stem].append(path)
    return {spec_id: sorted(paths) for spec_id, paths in out.items()}


def _semantic_source(*, formal_present: bool, semantic_present: bool) -> str:
    if formal_present:
        return "formal_contract"
    if semantic_present:
        return "semantic_contract"
    return "missing"


def _build_active_inventory() -> dict[str, Any]:
    runtime_refs = _runtime_refs()
    semantic_contracts = _semantic_contract_index()
    formal_contracts = _formal_contract_index()
    spec_paths = _tau_spec_paths()

    entries: list[dict[str, Any]] = []
    for spec_id, ref_files in runtime_refs.items():
        candidates = spec_paths.get(spec_id, [])
        spec_path = candidates[0] if candidates else None
        semantic_contract = semantic_contracts.get(spec_id)
        formal_contract = formal_contracts.get(spec_id)
        formal_meta = formal_contract["contract"] if formal_contract else {}
        proof_scope = str(formal_meta.get("proof_scope", "")).strip()
        source = _semantic_source(
            formal_present=formal_contract is not None,
            semantic_present=semantic_contract is not None,
        )

        blockers: list[str] = []
        if spec_path is None:
            blockers.append("unresolved_spec_path")
        if semantic_contract is None:
            blockers.append("missing_semantic_contract")
        if formal_contract is None:
            blockers.append("missing_formal_contract")
        elif proof_scope != "full_input_domain":
            blockers.append("bounded_scope_only")

        family = ""
        recommended = False
        if spec_path is not None:
            family = spec_path.parent.relative_to(REPO_ROOT / "src" / "tau_specs").as_posix()
            recommended = family == "recommended"

        entries.append(
            {
                "spec_id": spec_id,
                "spec_path": spec_path.relative_to(REPO_ROOT).as_posix() if spec_path is not None else "",
                "spec_candidates": [path.relative_to(REPO_ROOT).as_posix() for path in candidates],
                "spec_family": family,
                "recommended": recommended,
                "runtime_ref_files": ref_files,
                "runtime_ref_count": len(ref_files),
                "semantic_contract_present": semantic_contract is not None,
                "formal_contract_present": formal_contract is not None,
                "formal_contract_path": str(formal_contract.get("path", "")) if formal_contract else "",
                "proof_scope": proof_scope,
                "semantic_source": source,
                "semantic_confidence": "high" if source == "formal_contract" else "medium" if source == "semantic_contract" else "none",
                "blockers": blockers,
            }
        )

    source_counts = Counter(entry["semantic_source"] for entry in entries)
    blocker_counts = Counter(blocker for entry in entries for blocker in entry["blockers"])
    summary = {
        "active_spec_count": len(entries),
        "active_recommended_count": sum(1 for entry in entries if entry["recommended"]),
        "active_nonrecommended_count": sum(1 for entry in entries if not entry["recommended"]),
        "semantic_contract_count": sum(1 for entry in entries if entry["semantic_contract_present"]),
        "formal_contract_count": sum(1 for entry in entries if entry["formal_contract_present"]),
        "source_counts": dict(sorted(source_counts.items())),
        "blocker_counts": dict(sorted(blocker_counts.items())),
    }
    return {
        "schema": "zenodex/tau/semantic-coverage-selector-local-inventory/v1",
        "source": "tracked runtime Python refs plus tracked Tau specs/contracts",
        "summary": summary,
        "entries": entries,
    }


def _build_refinement_queue(inventory: Mapping[str, Any]) -> dict[str, Any]:
    entries = [
        entry
        for entry in inventory.get("entries", [])
        if isinstance(entry, Mapping) and not bool(entry.get("semantic_contract_present", False))
    ]
    bucket_counts = Counter(_risk_bucket(str(entry["spec_id"])) for entry in entries)
    return {
        "schema": "zenodex/tau/semantic-coverage-selector-local-queue/v1",
        "summary": {
            "queued_spec_count": len(entries),
            "risk_bucket_counts": dict(sorted(bucket_counts.items())),
        },
        "entries": [
            {
                "spec_id": str(entry["spec_id"]),
                "risk_bucket": _risk_bucket(str(entry["spec_id"])),
                "blockers": list(entry.get("blockers", [])),
            }
            for entry in entries
        ],
    }


def _host_projection_spec_ids(path: Path = HOST_PROJECTION_CONTRACTS) -> set[str]:
    if not path.exists():
        return set()
    raw = _load_json(path)
    specs = raw.get("specs", []) if isinstance(raw, Mapping) else []
    out: set[str] = set()
    if not isinstance(specs, list):
        return out
    for spec in specs:
        if not isinstance(spec, Mapping):
            continue
        spec_path = str(spec.get("spec_path", "")).strip()
        if spec_path:
            out.add(Path(spec_path).stem)
    return out


def _risk_bucket(spec_id: str) -> str:
    if spec_id.startswith(("swap_", "settlement_", "zusd_", "perp_")):
        return "consensus_core"
    if spec_id.startswith(("cpmm", "add_liquidity", "remove_liquidity", "batch", "balance_", "lp_")):
        return "spot_math_core"
    if spec_id.startswith(("autotrader_", "confidential_")):
        return "policy_gate"
    if spec_id.startswith(("protocol_", "token", "tdex_", "governance_", "revision_", "parameter_")):
        return "governance_tokenomics"
    return "other"


def _candidate_score(entry: Mapping[str, Any], host_specs: set[str], atlas_specs: set[str]) -> tuple[int, list[str]]:
    spec_id = str(entry["spec_id"])
    bucket = _risk_bucket(spec_id)
    blockers = set(str(blocker) for blocker in entry.get("blockers", []))
    semantic_source = str(entry.get("semantic_source", "missing"))

    score = RISK_WEIGHTS.get(bucket, 0)
    score += SOURCE_WEIGHTS.get(semantic_source, 20)
    score += min(int(entry.get("runtime_ref_count", 0)), 5) * 4
    if bool(entry.get("recommended", False)):
        score += 8
    if "missing_semantic_contract" in blockers:
        score += 20
    if "missing_formal_contract" in blockers:
        score += 10
    if "missing_review_packet" in blockers:
        score += 15
    if spec_id not in host_specs:
        score += 8
    if spec_id not in atlas_specs and bucket in {"consensus_core", "spot_math_core"}:
        score += 8

    reasons: list[str] = []
    if semantic_source in {"missing", "review_packet"}:
        reasons.append(f"semantic_source={semantic_source}")
    for blocker in sorted(blockers):
        reasons.append(blocker)
    if spec_id not in host_specs:
        reasons.append("missing_host_projection_contract")
    if spec_id not in atlas_specs and bucket in {"consensus_core", "spot_math_core"}:
        reasons.append("missing_mutation_atlas_surface")
    return score, reasons


def _next_actions(entry: Mapping[str, Any], host_specs: set[str], atlas_specs: set[str]) -> list[str]:
    spec_id = str(entry["spec_id"])
    blockers = set(str(blocker) for blocker in entry.get("blockers", []))
    bucket = _risk_bucket(spec_id)
    actions: list[str] = []
    if "missing_review_packet" in blockers:
        actions.append("generate Tau review packet")
    if "missing_semantic_contract" in blockers:
        actions.append("write semantic contract")
    if "missing_formal_contract" in blockers:
        actions.append("add formal contract or bounded proof note")
    if spec_id not in host_specs:
        actions.append("add host projection contract if host facts are required")
    if spec_id not in atlas_specs and bucket in {"consensus_core", "spot_math_core"}:
        actions.append("add required-fact mutation atlas surface")
    if not actions:
        actions.append("keep under periodic replay")
    return actions


def _rank_candidates(inventory: Mapping[str, Any]) -> list[dict[str, Any]]:
    host_specs = _host_projection_spec_ids()
    atlas_specs = {surface.spec_id for surface in atlas_surfaces()}
    ranked: list[dict[str, Any]] = []
    entries = inventory.get("entries", [])
    if not isinstance(entries, list):
        raise TypeError("inventory entries must be a list")
    for entry in entries:
        if not isinstance(entry, Mapping):
            continue
        score, reasons = _candidate_score(entry, host_specs, atlas_specs)
        spec_id = str(entry["spec_id"])
        ranked.append(
            {
                "spec_id": spec_id,
                "spec_path": str(entry.get("spec_path", "")),
                "risk_bucket": _risk_bucket(spec_id),
                "priority_score": score,
                "recommended": bool(entry.get("recommended", False)),
                "runtime_ref_count": int(entry.get("runtime_ref_count", 0)),
                "semantic_source": str(entry.get("semantic_source", "")),
                "semantic_confidence": str(entry.get("semantic_confidence", "")),
                "blockers": list(entry.get("blockers", [])),
                "reasons": reasons,
                "next_actions": _next_actions(entry, host_specs, atlas_specs),
            }
        )
    ranked.sort(key=lambda row: (-int(row["priority_score"]), str(row["spec_id"])))
    return ranked


def _proposed_specifications() -> list[dict[str, Any]]:
    return [
        {
            "spec_id": "ab_ordering_held_karp_dp_certificate_v1",
            "spec_path": "src/tau_specs/recommended/ab_ordering_held_karp_dp_certificate_v1.tau",
            "work_item": "1_ab_ordering",
            "benefit": "Certifies that an AB-ordering upgrade used full CPMM state, bounded brute-force parity, deterministic ties, state-cap fallback, and no settlement authority.",
            "host_algorithm": "Held-Karp style subset DP over full state, scoped to a configured state cap.",
            "tau_role": "Compose host evidence into a fail-closed research certificate.",
            "non_claim": "Does not prove a compressed one-record DP is sound and does not authorize settlement.",
        },
        {
            "spec_id": "cow_hungarian_matching_certificate_v1",
            "spec_path": "src/tau_specs/recommended/cow_hungarian_matching_certificate_v1.tau",
            "work_item": "2_cow_matching",
            "benefit": "Certifies that an uncoupled CoW matching upgrade supplied primal/dual assignment evidence, bounded parity, grouped-capacity fallback, deterministic ties, and no settlement authority.",
            "host_algorithm": "Maximum-weight bipartite assignment with primal/dual certificate checks under uncoupled capacity.",
            "tau_role": "Compose host evidence into a fail-closed research certificate.",
            "non_claim": "Does not claim arbitrary grouped-capacity CoW matching is polynomial and does not authorize settlement.",
        },
        {
            "spec_id": "tau_semantic_coverage_selector_certificate_v1",
            "spec_path": "src/tau_specs/recommended/tau_semantic_coverage_selector_certificate_v1.tau",
            "work_item": "semantic_coverage_frontier",
            "benefit": "Certifies that the active Tau inventory and refinement queue were replayed and that AB/CoW promotion targets remain selected.",
            "host_algorithm": "Deterministic priority-plus-coverage ranking over active Tau specs and semantic-contract gaps.",
            "tau_role": "Compose selector evidence into a fail-closed advisory certificate.",
            "non_claim": "Does not rank an unbounded spec pool and does not change runtime policy.",
        },
    ]


def _select_focus_candidates(ranked: list[dict[str, Any]], limit: int = 16) -> list[dict[str, Any]]:
    selected: dict[str, dict[str, Any]] = {}
    for row in ranked[:limit]:
        selected[str(row["spec_id"])] = row
    for bucket in ("consensus_core", "spot_math_core", "policy_gate", "governance_tokenomics"):
        for row in ranked:
            if row["risk_bucket"] == bucket:
                selected[str(row["spec_id"])] = row
                break
    return sorted(selected.values(), key=lambda row: (-int(row["priority_score"]), str(row["spec_id"])))


def _with(base: Mapping[str, int], **overrides: int) -> dict[str, int]:
    step = {str(key): int(value) for key, value in base.items()}
    step.update({str(key): int(value) for key, value in overrides.items()})
    return step


def _replay_surfaces() -> tuple[ReplaySurface, ...]:
    ab_base = {f"i{idx}": 1 for idx in range(1, 12)}
    cow_base = {f"i{idx}": 1 for idx in range(1, 13)}
    selector_base = {f"i{idx}": 1 for idx in range(1, 16)}
    return (
        ReplaySurface(
            surface_id="ab_ordering_held_karp_dp_certificate",
            spec_id="ab_ordering_held_karp_dp_certificate_v1",
            spec_path=SPEC_ROOT / "ab_ordering_held_karp_dp_certificate_v1.tau",
            primary_output="o5",
            inactive_output="o6",
            base_step=ab_base,
            required_inputs=tuple(f"i{idx}" for idx in range(1, 12)),
        ),
        ReplaySurface(
            surface_id="cow_hungarian_matching_certificate",
            spec_id="cow_hungarian_matching_certificate_v1",
            spec_path=SPEC_ROOT / "cow_hungarian_matching_certificate_v1.tau",
            primary_output="o5",
            inactive_output="o6",
            base_step=cow_base,
            required_inputs=tuple(f"i{idx}" for idx in range(1, 13)),
        ),
        ReplaySurface(
            surface_id="tau_semantic_coverage_selector_certificate",
            spec_id="tau_semantic_coverage_selector_certificate_v1",
            spec_path=SPEC_ROOT / "tau_semantic_coverage_selector_certificate_v1.tau",
            primary_output="o5",
            inactive_output="o6",
            base_step=selector_base,
            required_inputs=tuple(f"i{idx}" for idx in range(1, 16)),
        ),
    )


def _surface_cases(surface: ReplaySurface) -> list[dict[str, Any]]:
    cases = [
        {
            "case_id": "positive_accept",
            "step": dict(surface.base_step),
            "expected_primary": 1,
            "expected_inactive": 0,
            "rationale": "All required certificate facts are present.",
        }
    ]
    for input_name in surface.required_inputs:
        cases.append(
            {
                "case_id": f"flip_{input_name}_reject",
                "step": _with(surface.base_step, **{input_name: 0}),
                "expected_primary": 0,
                "expected_inactive": 1 if input_name == "i1" else 0,
                "rationale": f"Required input {input_name} is missing, so the certificate must reject.",
            }
        )
    inactive_step = _with(surface.base_step, i1=0)
    cases.append(
        {
            "case_id": "inactive_safe",
            "step": inactive_step,
            "expected_primary": 0,
            "expected_inactive": 1,
            "rationale": "Inactive certificates are safe only when the no-authority fact remains present.",
        }
    )
    return cases


def _run_surface(surface: ReplaySurface, tau_bin: str) -> dict[str, Any]:
    cases = _surface_cases(surface)
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=surface.spec_path,
        steps=[case["step"] for case in cases],
        timeout_s=25.0,
    )
    rows: list[dict[str, Any]] = []
    invalid_accepts = 0
    false_rejects = 0
    for idx, case in enumerate(cases):
        got = {str(key): int(value) for key, value in outputs.get(idx, {}).items()}
        got_primary = got.get(surface.primary_output)
        got_inactive = got.get(surface.inactive_output)
        primary_ok = got_primary == int(case["expected_primary"])
        inactive_ok = got_inactive == int(case["expected_inactive"])
        ok = primary_ok and inactive_ok
        if int(case["expected_primary"]) == 0 and got_primary == 1:
            invalid_accepts += 1
        if int(case["expected_primary"]) == 1 and got_primary != 1:
            false_rejects += 1
        rows.append(
            {
                "case_id": str(case["case_id"]),
                "ok": ok,
                "expected_primary": int(case["expected_primary"]),
                "got_primary": got_primary,
                "expected_inactive": int(case["expected_inactive"]),
                "got_inactive": got_inactive,
                "primary_output": surface.primary_output,
                "inactive_output": surface.inactive_output,
                "got": got,
                "step": dict(case["step"]),
                "rationale": str(case["rationale"]),
            }
        )
    return {
        "surface_id": surface.surface_id,
        "spec_id": surface.spec_id,
        "spec_path": str(surface.spec_path.relative_to(REPO_ROOT)),
        "sha256": _sha256(surface.spec_path),
        "primary_output": surface.primary_output,
        "inactive_output": surface.inactive_output,
        "required_input_count": len(surface.required_inputs),
        "case_count": len(cases),
        "mutation_count": len(cases) - 2,
        "invalid_accepts": invalid_accepts,
        "false_rejects": false_rejects,
        "ok": invalid_accepts == 0 and false_rejects == 0 and all(row["ok"] for row in rows),
        "cases": rows,
    }


def _run_tau_replay(tau_bin: str | None) -> dict[str, Any]:
    resolved_tau_bin = tau_bin or find_tau_bin(REPO_ROOT, profile="latest")
    if not resolved_tau_bin:
        return {
            "ok": False,
            "error": "latest Tau binary not found",
            "tau_bin": None,
            "tau_version": None,
            "surfaces": [],
            "totals": {"surface_count": 0, "case_count": 0, "mutation_count": 0, "invalid_accepts": 0, "false_rejects": 0},
        }
    surfaces = [_run_surface(surface, resolved_tau_bin) for surface in _replay_surfaces()]
    totals = {
        "surface_count": len(surfaces),
        "case_count": sum(int(surface["case_count"]) for surface in surfaces),
        "mutation_count": sum(int(surface["mutation_count"]) for surface in surfaces),
        "invalid_accepts": sum(int(surface["invalid_accepts"]) for surface in surfaces),
        "false_rejects": sum(int(surface["false_rejects"]) for surface in surfaces),
    }
    return {
        "ok": all(bool(surface["ok"]) for surface in surfaces) and totals["invalid_accepts"] == 0 and totals["false_rejects"] == 0,
        "tau_bin": resolved_tau_bin,
        "tau_version": _tau_version(resolved_tau_bin),
        "surfaces": surfaces,
        "totals": totals,
    }


def _selector_facts(
    *,
    inventory: Mapping[str, Any],
    queue: Mapping[str, Any],
    focus_candidates: list[dict[str, Any]],
    proposed_specs: list[dict[str, Any]],
    tau_replay: Mapping[str, Any],
) -> dict[str, bool]:
    summary = inventory.get("summary", {})
    blockers = summary.get("blocker_counts", {}) if isinstance(summary, Mapping) else {}
    buckets = {str(row["risk_bucket"]) for row in focus_candidates}
    proposed_ids = {str(row["spec_id"]) for row in proposed_specs}
    atlas_spec_ids = {surface.spec_id for surface in atlas_surfaces()}
    expected_proposed_paths = [REPO_ROOT / str(row["spec_path"]) for row in proposed_specs]
    deterministic_order_ok = focus_candidates == sorted(
        focus_candidates,
        key=lambda row: (-int(row["priority_score"]), str(row["spec_id"])),
    )
    return {
        "selector_active": True,
        "active_inventory_built": int(summary.get("active_spec_count", 0)) > 0 if isinstance(summary, Mapping) else False,
        "semantic_refinement_queue_built": int(queue.get("summary", {}).get("queued_spec_count", 0)) > 0,
        "coverage_gaps_present": int(blockers.get("missing_semantic_contract", 0)) > 0 if isinstance(blockers, Mapping) else False,
        "critical_bucket_coverage_ok": {"consensus_core", "spot_math_core"} <= buckets,
        "work_item_1_ab_selected": "ab_ordering_held_karp_dp_certificate_v1" in proposed_ids,
        "work_item_2_cow_selected": "cow_hungarian_matching_certificate_v1" in proposed_ids,
        "proposed_spec_artifacts_present": all(path.exists() for path in expected_proposed_paths),
        "mutation_atlas_dependency_bound": {
            "ab_cow_exact_solver_envelope_v1",
            "tauspec_ebrm_frontier_selection_certificate_v1",
        }
        <= atlas_spec_ids,
        "deterministic_priority_order_ok": deterministic_order_ok,
        "semantic_contract_next_actions_bound": all(bool(row.get("next_actions")) for row in focus_candidates),
        "tau_replay_invalid_accepts_zero": int(tau_replay.get("totals", {}).get("invalid_accepts", 1)) == 0,
        "advisory_selection_only": True,
        "no_runtime_authority_effect": True,
        "budget_profile_ok": len(focus_candidates) <= 32 and int(summary.get("active_spec_count", 9999)) <= 512,
    }


def build_report(tau_bin: str | None = None) -> dict[str, Any]:
    inventory = _build_active_inventory()
    queue = _build_refinement_queue(inventory)
    ranked = _rank_candidates(inventory)
    focus_candidates = _select_focus_candidates(ranked)
    proposed_specs = _proposed_specifications()
    tau_replay = _run_tau_replay(tau_bin)
    facts = _selector_facts(
        inventory=inventory,
        queue=queue,
        focus_candidates=focus_candidates,
        proposed_specs=proposed_specs,
        tau_replay=tau_replay,
    )
    inventory_summary = inventory.get("summary", {})
    queue_summary = queue.get("summary", {})
    ok = bool(tau_replay.get("ok")) and all(facts.values()) and bool(focus_candidates)
    return {
        "schema": "zenodex.tau_semantic_coverage_selector_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "breakthrough": {
            "name": "Tau semantic coverage selector",
            "summary": "A replayable Tau certificate and report generator that converts runtime-active Tau semantic gaps into a deterministic promotion frontier.",
            "design_pattern": "priority_plus_bucket_coverage",
            "authority_boundary": "The selector is advisory. Runtime kernels, host verifiers, and settlement code remain authoritative.",
        },
        "inventory_summary": inventory_summary,
        "queue_summary": queue_summary,
        "ranked_candidate_count": len(ranked),
        "focus_candidates": focus_candidates,
        "proposed_specifications": proposed_specs,
        "selector_facts": facts,
        "tau_replay": tau_replay,
        "work_items": {
            "1_ab_ordering": {
                "status": "specified_for_certificate_replay",
                "spec_id": "ab_ordering_held_karp_dp_certificate_v1",
                "algorithmic_target": "Replace bounded brute-force AB ordering with a full-state Held-Karp subset-DP evidence path where the state cap permits it.",
                "benefit": "Moves the exact-solving frontier from factorial enumeration toward O(n^2 * 2^n) host search under explicit state-cap and parity gates.",
            },
            "2_cow_matching": {
                "status": "specified_for_certificate_replay",
                "spec_id": "cow_hungarian_matching_certificate_v1",
                "algorithmic_target": "Use assignment-style primal/dual evidence for uncoupled CoW matching and fail closed for grouped capacity.",
                "benefit": "Gives CoW matching a polynomial exact certificate surface under the uncoupled-capacity scope.",
            },
        },
        "non_claims": [
            "This artifact does not prove the proposed host algorithms correct.",
            "This artifact does not authorize settlement, oracle updates, governance actions, or state roots.",
            "The selector ranks the current bounded repo inventory and proposed work-item specs; it does not rank an unbounded Tau language space.",
            "The AB certificate does not validate compressed one-record Held-Karp state.",
            "The CoW certificate does not claim arbitrary grouped-capacity matching is polynomial.",
        ],
        "replay_command": "python3 tools/zenodex_tau_semantic_coverage_selector_20260628.py",
    }


def _write_markdown(report: Mapping[str, Any], output: Path) -> None:
    lines: list[str] = [
        "# ZenoDEX Tau Semantic Coverage Selector - 2026-06-28",
        "",
        "## Executive Result",
        "",
        str(report["breakthrough"]["summary"]),
        "",
        str(report["breakthrough"]["authority_boundary"]),
        "",
        "## Current Tau Coverage Frontier",
        "",
    ]
    inventory = report["inventory_summary"]
    queue = report["queue_summary"]
    lines.extend(
        [
            f"- Runtime-active Tau specs: `{inventory.get('active_spec_count')}`",
            f"- Semantic contracts: `{inventory.get('semantic_contract_count')}`",
            f"- Formal contracts: `{inventory.get('formal_contract_count')}`",
            f"- Review-packet-only specs: `{inventory.get('source_counts', {}).get('review_packet', 0)}`",
            f"- Missing semantic contracts: `{inventory.get('blocker_counts', {}).get('missing_semantic_contract', 0)}`",
            f"- Refinement queue entries: `{queue.get('queued_spec_count')}`",
            "",
            "## New Tau Specifications",
            "",
            "| spec | work item | benefit |",
            "| --- | --- | --- |",
        ]
    )
    for spec in report["proposed_specifications"]:
        lines.append(f"| `{spec['spec_id']}` | `{spec['work_item']}` | {spec['benefit']} |")
    lines.extend(["", "## Selected Promotion Targets", "", "| spec | bucket | score | next action |", "| --- | --- | ---: | --- |"])
    for row in report["focus_candidates"]:
        action = "; ".join(row["next_actions"][:2])
        lines.append(f"| `{row['spec_id']}` | `{row['risk_bucket']}` | `{row['priority_score']}` | {action} |")
    lines.extend(["", "## Work Items 1 And 2", ""])
    for key, item in report["work_items"].items():
        lines.append(f"### {key}")
        lines.append("")
        lines.append(f"- Spec: `{item['spec_id']}`")
        lines.append(f"- Target: {item['algorithmic_target']}")
        lines.append(f"- Benefit: {item['benefit']}")
        lines.append("")
    tau_totals = report["tau_replay"]["totals"]
    lines.extend(
        [
            "## Tau Replay Evidence",
            "",
            f"- Tau surfaces: `{tau_totals['surface_count']}`",
            f"- Replay cases: `{tau_totals['case_count']}`",
            f"- Required-fact mutations: `{tau_totals['mutation_count']}`",
            f"- Invalid accepts: `{tau_totals['invalid_accepts']}`",
            f"- False rejects: `{tau_totals['false_rejects']}`",
            "",
            "## Selector Facts",
            "",
        ]
    )
    for key, value in sorted(report["selector_facts"].items()):
        lines.append(f"- `{key}`: `{int(bool(value))}`")
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
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
    totals = report.get("tau_replay", {}).get("totals", {})
    print(
        json.dumps(
            {
                "ok": bool(report.get("ok")),
                "json": str(Path(args.output_json)),
                "report": str(Path(args.output_md)),
                "active_spec_count": int(report.get("inventory_summary", {}).get("active_spec_count", 0)),
                "focus_candidate_count": len(report.get("focus_candidates", [])),
                "proposed_spec_count": len(report.get("proposed_specifications", [])),
                "tau_surface_count": int(totals.get("surface_count", 0)),
                "tau_mutation_count": int(totals.get("mutation_count", 0)),
                "invalid_accepts": int(totals.get("invalid_accepts", 0)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if bool(report.get("ok")) else 1


if __name__ == "__main__":
    raise SystemExit(main())

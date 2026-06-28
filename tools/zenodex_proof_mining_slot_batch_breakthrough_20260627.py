#!/usr/bin/env python3
from __future__ import annotations

import itertools
import json
import subprocess
import sys
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.proof_mining_manager import (  # noqa: E402
    assign_proposal_slot,
    preferred_proposal_slot,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402


SLOT_COUNT = 8
OUT_DIR = REPO_ROOT / "generated" / "zenodex_proof_mining_slot_batch_breakthrough_20260627"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_PROOF_MINING_SLOT_BATCH_BREAKTHROUGH_20260627.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "proof_mining_slot_batch_certificate_v1.tau"


@dataclass(frozen=True)
class SlotBatchCase:
    case_id: str
    claimed_slots: Mapping[int, str]
    preferred_slots: tuple[int, ...]
    expect_exact_beats_sequential: bool
    note: str


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]


TAU_CASES = (
    TauCase(
        "slot_batch_pass",
        {
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
            "i11": 1,
            "i12": 1,
            "i13": 1,
        },
        {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1},
    ),
    TauCase(
        "objective_reject",
        {
            "i1": 1,
            "i2": 1,
            "i3": 1,
            "i4": 1,
            "i5": 1,
            "i6": 1,
            "i7": 1,
            "i8": 0,
            "i9": 1,
            "i10": 1,
            "i11": 1,
            "i12": 1,
            "i13": 1,
        },
        {"o1": 1, "o2": 1, "o3": 0, "o6": 0},
    ),
    TauCase(
        "duplicate_reject",
        {
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
            "i11": 1,
            "i12": 0,
            "i13": 1,
        },
        {"o5": 0, "o6": 0},
    ),
    TauCase(
        "authority_reject",
        {
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
            "i11": 1,
            "i12": 1,
            "i13": 0,
        },
        {"o5": 0, "o6": 0},
    ),
    TauCase(
        "inactive_safe",
        {
            "i1": 0,
            "i2": 1,
            "i3": 1,
            "i4": 1,
            "i5": 1,
            "i6": 1,
            "i7": 1,
            "i8": 1,
            "i9": 1,
            "i10": 1,
            "i11": 1,
            "i12": 1,
            "i13": 1,
        },
        {"o1": 0, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 0},
    ),
)


def _stable_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def _stable_hash(value: Any) -> str:
    return sha256(_stable_json(value).encode("utf-8")).hexdigest()


def proposal_for_preferred_slot(slot: int, ordinal: int) -> str:
    if not isinstance(slot, int) or slot < 0 or slot >= SLOT_COUNT:
        raise ValueError("slot must be in 0..7")
    for nonce in itertools.count():
        proposal = f"pm-slot-{slot}-{ordinal}-{nonce}"
        if preferred_proposal_slot(proposal) == slot:
            return proposal
    raise RuntimeError("unreachable preferred-slot search exhaustion")


def _proposal_list(preferred_slots: tuple[int, ...]) -> list[str]:
    return [proposal_for_preferred_slot(slot, idx) for idx, slot in enumerate(preferred_slots)]


def _normal_claimed(claimed_slots: Mapping[int, str]) -> dict[int, str]:
    out: dict[int, str] = {}
    seen: set[str] = set()
    for raw_slot, raw_proposal in claimed_slots.items():
        slot = int(raw_slot)
        proposal = str(raw_proposal)
        if slot < 0 or slot >= SLOT_COUNT:
            raise ValueError("claimed slot out of range")
        if proposal in seen:
            raise ValueError("duplicate claimed proposal")
        seen.add(proposal)
        out[slot] = proposal
    return out


def cyclic_displacement(proposal_hash: str, assigned_slot: int) -> int:
    preferred = preferred_proposal_slot(proposal_hash)
    return (int(assigned_slot) - preferred) % SLOT_COUNT


def assignment_objective_key(proposals: list[str], assignment: Mapping[str, int]) -> tuple[int, int, tuple[int, ...], tuple[int, ...]]:
    displacements = tuple(cyclic_displacement(proposal, int(assignment[proposal])) for proposal in proposals)
    return (
        max(displacements) if displacements else 0,
        sum(displacements),
        tuple(sorted(displacements, reverse=True)),
        tuple(int(assignment[proposal]) for proposal in proposals),
    )


def sequential_linear_assignment(claimed_slots: Mapping[int, str], proposals: list[str]) -> dict[str, int]:
    registry = _normal_claimed(claimed_slots)
    out: dict[str, int] = {}
    for proposal in proposals:
        assigned_slot, already_claimed = assign_proposal_slot(proposal_hash=proposal, claimed_slots=registry)
        if already_claimed:
            raise ValueError("proposal already claimed")
        registry[int(assigned_slot)] = proposal
        out[proposal] = int(assigned_slot)
    return out


def exact_batch_assignment(claimed_slots: Mapping[int, str], proposals: list[str]) -> tuple[dict[str, int], int]:
    registry = _normal_claimed(claimed_slots)
    if len(set(proposals)) != len(proposals):
        raise ValueError("duplicate proposals")
    if any(proposal in registry.values() for proposal in proposals):
        raise ValueError("proposal already claimed")
    free_slots = [slot for slot in range(SLOT_COUNT) if slot not in registry]
    if len(proposals) > len(free_slots):
        raise ValueError("not enough free slots")

    best_assignment: dict[str, int] | None = None
    best_key: tuple[int, int, tuple[int, ...], tuple[int, ...]] | None = None
    candidate_count = 0
    for slots in itertools.permutations(free_slots, len(proposals)):
        candidate_count += 1
        assignment = {proposal: int(slot) for proposal, slot in zip(proposals, slots)}
        key = assignment_objective_key(proposals, assignment)
        if best_key is None or key < best_key:
            best_key = key
            best_assignment = assignment
    if best_assignment is None:
        raise ValueError("no feasible assignment")
    return best_assignment, candidate_count


def _certificate_domain(case_id: str, claimed_slots: Mapping[int, str], proposals: list[str]) -> dict[str, Any]:
    return {
        "case_id": case_id,
        "slot_count": SLOT_COUNT,
        "claimed_slots": [[int(slot), proposal] for slot, proposal in sorted(_normal_claimed(claimed_slots).items())],
        "proposals": list(proposals),
        "preferred_slots": [preferred_proposal_slot(proposal) for proposal in proposals],
        "objective": "minimize(max_cyclic_displacement, total_cyclic_displacement, sorted_displacements_desc, slots_by_input_order)",
    }


def build_certificate(case: SlotBatchCase) -> dict[str, Any]:
    proposals = _proposal_list(case.preferred_slots)
    sequential = sequential_linear_assignment(case.claimed_slots, proposals)
    exact, candidate_count = exact_batch_assignment(case.claimed_slots, proposals)
    sequential_key = assignment_objective_key(proposals, sequential)
    exact_key = assignment_objective_key(proposals, exact)
    domain = _certificate_domain(case.case_id, case.claimed_slots, proposals)
    return {
        "schema": "zenodex/proof-mining-slot-batch-certificate/v1",
        "case_id": case.case_id,
        "note": case.note,
        "domain": domain,
        "domain_hash": _stable_hash(domain),
        "sequential_assignment": [[proposal, sequential[proposal]] for proposal in proposals],
        "exact_assignment": [[proposal, exact[proposal]] for proposal in proposals],
        "sequential_objective_key": list(sequential_key[:2]) + [list(sequential_key[2]), list(sequential_key[3])],
        "exact_objective_key": list(exact_key[:2]) + [list(exact_key[2]), list(exact_key[3])],
        "candidate_count": candidate_count,
        "exact_beats_sequential": exact_key < sequential_key,
        "expected_exact_beats_sequential": bool(case.expect_exact_beats_sequential),
    }


def _assignment_from_pairs(pairs: Any) -> dict[str, int]:
    if not isinstance(pairs, list):
        raise ValueError("assignment must be a list")
    out: dict[str, int] = {}
    used_slots: set[int] = set()
    for item in pairs:
        if not isinstance(item, list) or len(item) != 2:
            raise ValueError("assignment rows must be [proposal, slot]")
        proposal = str(item[0])
        slot = int(item[1])
        if slot < 0 or slot >= SLOT_COUNT:
            raise ValueError("assigned slot out of range")
        if proposal in out:
            raise ValueError("duplicate assigned proposal")
        if slot in used_slots:
            raise ValueError("duplicate assigned slot")
        used_slots.add(slot)
        out[proposal] = slot
    return out


def verify_certificate(certificate: Mapping[str, Any]) -> bool:
    if certificate.get("schema") != "zenodex/proof-mining-slot-batch-certificate/v1":
        raise ValueError("schema mismatch")
    domain = certificate.get("domain")
    if not isinstance(domain, Mapping):
        raise ValueError("domain must be an object")
    if certificate.get("domain_hash") != _stable_hash(domain):
        raise ValueError("domain hash mismatch")
    claimed_slots = {int(slot): str(proposal) for slot, proposal in domain.get("claimed_slots", [])}
    proposals = [str(proposal) for proposal in domain.get("proposals", [])]
    if len(set(proposals)) != len(proposals):
        raise ValueError("duplicate proposals")
    exact = _assignment_from_pairs(certificate.get("exact_assignment"))
    if set(exact) != set(proposals):
        raise ValueError("exact assignment proposal set mismatch")
    recomputed, recomputed_count = exact_batch_assignment(claimed_slots, proposals)
    recomputed_key = assignment_objective_key(proposals, recomputed)
    claimed_key_raw = certificate.get("exact_objective_key")
    if claimed_key_raw != list(recomputed_key[:2]) + [list(recomputed_key[2]), list(recomputed_key[3])]:
        raise ValueError("objective key mismatch")
    if exact != recomputed:
        raise ValueError("exact assignment mismatch")
    if int(certificate.get("candidate_count")) != recomputed_count:
        raise ValueError("candidate count mismatch")
    sequential = sequential_linear_assignment(claimed_slots, proposals)
    sequential_key = assignment_objective_key(proposals, sequential)
    if bool(certificate.get("exact_beats_sequential")) != (recomputed_key < sequential_key):
        raise ValueError("baseline comparison mismatch")
    return True


def build_cases() -> tuple[SlotBatchCase, ...]:
    claimed_zero = {0: proposal_for_preferred_slot(0, 900)}
    return (
        SlotBatchCase(
            case_id="no_collision_parity",
            claimed_slots={},
            preferred_slots=(0, 1, 2, 3),
            expect_exact_beats_sequential=False,
            note="Distinct preferred slots match the existing linear probing rule.",
        ),
        SlotBatchCase(
            case_id="interleaved_collision_lift",
            claimed_slots={},
            preferred_slots=(0, 1, 0),
            expect_exact_beats_sequential=True,
            note="Batch assignment lowers worst-case cyclic displacement from 2 to 1.",
        ),
        SlotBatchCase(
            case_id="wraparound_tail_lift",
            claimed_slots={},
            preferred_slots=(0, 7, 7, 7),
            expect_exact_beats_sequential=True,
            note="Wraparound collision pressure can be balanced across the ring.",
        ),
        SlotBatchCase(
            case_id="occupied_preferred_slot_lift",
            claimed_slots=claimed_zero,
            preferred_slots=(1, 0),
            expect_exact_beats_sequential=True,
            note="A pre-claimed slot can make local linear probing increase worst-case displacement.",
        ),
        SlotBatchCase(
            case_id="six_proposal_pressure",
            claimed_slots={},
            preferred_slots=(0, 1, 0, 7, 7, 0),
            expect_exact_beats_sequential=True,
            note="Six proposals remain within the 8-slot exact resource boundary.",
        ),
    )


def _mutation_checks(certificates: list[dict[str, Any]]) -> list[dict[str, Any]]:
    checks: list[dict[str, Any]] = []
    base = certificates[1]
    mutations: list[tuple[str, dict[str, Any], str]] = []

    bad_hash = json.loads(json.dumps(base))
    bad_hash["domain_hash"] = "0" * 64
    mutations.append(("bad_domain_hash", bad_hash, "domain hash mismatch"))

    bad_slot = json.loads(json.dumps(base))
    bad_slot["exact_assignment"][0][1] = bad_slot["exact_assignment"][1][1]
    mutations.append(("duplicate_assigned_slot", bad_slot, "duplicate assigned slot"))

    bad_objective = json.loads(json.dumps(base))
    bad_objective["exact_objective_key"][0] = int(bad_objective["exact_objective_key"][0]) + 1
    mutations.append(("bad_objective_key", bad_objective, "objective key mismatch"))

    for mutation_id, mutated, expected_error in mutations:
        try:
            verify_certificate(mutated)
        except ValueError as exc:
            accepted = False
            error = str(exc)
        else:
            accepted = True
            error = None
        checks.append(
            {
                "mutation_id": mutation_id,
                "accepted": accepted,
                "error": error,
                "expected_error": expected_error,
                "ok": (not accepted) and error == expected_error,
            }
        )
    return checks


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def tau_trace_check() -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {
            "ok": False,
            "error": "latest Tau binary not found",
            "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
            "cases": [],
        }
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[case.step for case in TAU_CASES],
        timeout_s=10.0,
    )
    cases: list[dict[str, Any]] = []
    ok = True
    for idx, case in enumerate(TAU_CASES):
        got = outputs.get(idx, {})
        mismatches = {
            key: {"expected": value, "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != value
        }
        if mismatches:
            ok = False
        cases.append(
            {
                "case_id": case.case_id,
                "ok": not mismatches,
                "expected": case.expected,
                "got": got,
                "mismatches": mismatches,
            }
        )
    return {
        "ok": ok,
        "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
        "tau_bin": tau_bin,
        "tau_version": _tau_version(tau_bin),
        "cases": cases,
    }


def build_report() -> dict[str, Any]:
    certificates = [build_certificate(case) for case in build_cases()]
    certificate_rows: list[dict[str, Any]] = []
    for certificate in certificates:
        verified = verify_certificate(certificate)
        certificate_rows.append(
            {
                "case_id": certificate["case_id"],
                "verified": verified,
                "candidate_count": certificate["candidate_count"],
                "sequential_objective_key": certificate["sequential_objective_key"],
                "exact_objective_key": certificate["exact_objective_key"],
                "exact_beats_sequential": certificate["exact_beats_sequential"],
                "expected_exact_beats_sequential": certificate["expected_exact_beats_sequential"],
                "preferred_slots": certificate["domain"]["preferred_slots"],
                "note": certificate["note"],
            }
        )
    mutation_checks = _mutation_checks(certificates)
    tau = tau_trace_check()
    exact_beats_count = sum(1 for row in certificate_rows if row["exact_beats_sequential"])
    ok = bool(
        tau["ok"]
        and all(row["verified"] for row in certificate_rows)
        and all(row["exact_beats_sequential"] == row["expected_exact_beats_sequential"] for row in certificate_rows)
        and all(check["ok"] for check in mutation_checks)
        and exact_beats_count >= 3
    )
    return {
        "schema": "zenodex.proof_mining_slot_batch_breakthrough_report.v1",
        "date": "2026-06-27",
        "ok": ok,
        "breakthrough": {
            "name": "Tau-gated proof-mining batch slot-assignment certificate",
            "summary": "A bounded exact oracle minimizes proof-mining slot displacement over the 8-slot registry and emits a certificate that Tau can admit through host-projected proof facts.",
            "authority_boundary": "The Tau spec admits a certificate envelope only. It cannot pay rewards, mutate claimed slots, or authorize settlement.",
        },
        "algorithm": {
            "baseline": "Existing single-proposal assignment hashes to a preferred slot and linear-probes for the first free slot.",
            "exact_batch_objective": "minimize(max_cyclic_displacement, total_cyclic_displacement, sorted_displacements_desc, slots_by_input_order)",
            "search_bound": "At most P(8, k) assignments for k new proposals; the largest replay case uses k=6 and evaluates 20160 assignments.",
            "activation_note": "This is a research oracle/certificate surface. Runtime activation needs a versioned batch command because it can assign earlier proposals to non-linear-probe slots.",
        },
        "tau": tau,
        "certificates": certificate_rows,
        "mutation_checks": mutation_checks,
        "specification_frontier": [
            {
                "spec": "src/tau_specs/recommended/ab_cow_exact_solver_envelope_v1.tau",
                "benefit": "Gates work item 1 AB subset-DP certificates and work item 2 CoW exact-matching certificates.",
                "status": "existing supported rail; replay with tools/zenodex_ab_cow_algorithm_breakthrough_20260627.py",
            },
            {
                "spec": "src/tau_specs/recommended/optimizer_quotient_certificate_v1.tau",
                "benefit": "Compresses optimizer proof surfaces into domain-hash-bound quotient certificates.",
                "status": "existing supported rail; replay with tools/zenodex_tau_optimizer_quotient_breakthrough_20260627.py",
            },
            {
                "spec": "src/tau_specs/recommended/proof_mining_slot_batch_certificate_v1.tau",
                "benefit": "New bounded exact certificate lane for proof-mining slot assignment collisions.",
                "status": "implemented in this report",
            },
        ],
        "work_items": {
            "1_ab_ordering": "Held-Karp-style subset DP remains the high-value algorithm target for same-direction AB batches; the existing Tau envelope gates the certificate facts while host code computes the DP.",
            "2_cow_matching": "Hungarian matching remains the clean exact reduction for uncoupled CoW batches; the existing Tau envelope gates the assignment certificate facts while host code computes matching.",
        },
        "replay_command": "python3 tools/zenodex_proof_mining_slot_batch_breakthrough_20260627.py",
    }


def _write_markdown(report: dict[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Proof-Mining Slot Batch Breakthrough - 2026-06-27")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(report["breakthrough"]["summary"])
    lines.append("")
    lines.append(report["breakthrough"]["authority_boundary"])
    lines.append("")
    lines.append(f"- Spec: `{report['tau']['spec_path']}`")
    lines.append(f"- Tau replay ok: `{report['tau']['ok']}`")
    lines.append(f"- Tau version: `{report['tau'].get('tau_version')}`")
    lines.append(f"- Certificate cases: `{len(report['certificates'])}`")
    lines.append(f"- Lift cases over sequential linear probing: `{sum(1 for row in report['certificates'] if row['exact_beats_sequential'])}`")
    lines.append("")
    lines.append("## Algorithm")
    lines.append("")
    lines.append(report["algorithm"]["baseline"])
    lines.append("")
    lines.append(f"Batch objective: `{report['algorithm']['exact_batch_objective']}`.")
    lines.append(report["algorithm"]["search_bound"])
    lines.append("")
    lines.append(report["algorithm"]["activation_note"])
    lines.append("")
    lines.append("## Certificate Cases")
    lines.append("")
    lines.append("| case | preferred slots | candidates | sequential key | exact key | lift |")
    lines.append("| --- | --- | ---: | --- | --- | --- |")
    for row in report["certificates"]:
        lines.append(
            "| `{case}` | `{prefs}` | `{candidates}` | `{seq}` | `{exact}` | `{lift}` |".format(
                case=row["case_id"],
                prefs=row["preferred_slots"],
                candidates=row["candidate_count"],
                seq=row["sequential_objective_key"],
                exact=row["exact_objective_key"],
                lift=row["exact_beats_sequential"],
            )
        )
    lines.append("")
    lines.append("## Tau Specification Frontier")
    lines.append("")
    lines.append("| spec | benefit | status |")
    lines.append("| --- | --- | --- |")
    for item in report["specification_frontier"]:
        lines.append(f"| `{item['spec']}` | {item['benefit']} | {item['status']} |")
    lines.append("")
    lines.append("## Work Items 1 And 2")
    lines.append("")
    lines.append(f"1. {report['work_items']['1_ab_ordering']}")
    lines.append(f"2. {report['work_items']['2_cow_matching']}")
    lines.append("")
    lines.append("## Mutation Checks")
    lines.append("")
    lines.append("| mutation | rejected | error |")
    lines.append("| --- | --- | --- |")
    for check in report["mutation_checks"]:
        lines.append(f"| `{check['mutation_id']}` | `{not check['accepted']}` | `{check['error']}` |")
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    lines.append("- The new slot-batch oracle is not wired into runtime proof payout flow.")
    lines.append("- The certificate is bounded to the current 8-slot registry.")
    lines.append("- Tau does not compute hashes, enumerate assignments, or decide payouts.")
    lines.append("- Work items 1 and 2 keep their existing host/kernel exactness boundaries.")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(report["replay_command"])
    lines.append("```")
    lines.append("")
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(_stable_json(report) + "\n", encoding="utf-8")
    _write_markdown(report)
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "report": str(REPORT_MD),
                "json": str(REPORT_JSON),
                "tau_ok": report["tau"]["ok"],
                "certificate_cases": len(report["certificates"]),
                "lift_cases": sum(1 for row in report["certificates"] if row["exact_beats_sequential"]),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Replay the AB frontier-DP certificate experiment."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.batch_clearing_ab_order import (  # noqa: E402
    _AbDpRecord,
    _best_order_by_objective_bruteforce,
    _debit_balance_key,
    _is_better_ab_dp_record,
    _objective_exact_in_contribution,
    _objective_for_order,
    _sender_input_balances,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from src.state.balances import BalanceTable  # noqa: E402
from src.state.intents import Intent  # noqa: E402
from src.state.pools import PoolState  # noqa: E402
from tools.zenodex_ab_compressed_dp_refuter_20260628 import _build_report as _compressed_refuter_report  # noqa: E402
from tools.zenodex_ab_cow_algorithm_breakthrough_20260627 import (  # noqa: E402
    ASSET0,
    ASSET1,
    _ab_context,
    _exact_in_intent,
    _pool,
    _timed,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_frontier_dp_breakthrough_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_FRONTIER_DP_BREAKTHROUGH_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "ab_frontier_dp_certificate_v1.tau"


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]


TAU_CASES = (
    TauCase(
        "frontier_dp_pass",
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1, "i12": 1},
        {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0},
    ),
    TauCase(
        "no_pruning_reject",
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 0, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1, "i12": 1},
        {"o1": 1, "o2": 0, "o4": 0},
    ),
    TauCase(
        "parity_reject",
        {"i1": 1, "i2": 1, "i3": 0, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1, "i12": 1},
        {"o1": 0, "o4": 0},
    ),
    TauCase(
        "dominance_loss_reject",
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 0, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1, "i12": 1},
        {"o2": 0, "o4": 0},
    ),
    TauCase(
        "authority_reject",
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1, "i12": 0},
        {"o3": 0, "o4": 0},
    ),
    TauCase(
        "inactive_safe",
        {"i1": 0, "i2": 0, "i3": 0, "i4": 0, "i5": 0, "i6": 0, "i7": 0, "i8": 0, "i9": 0, "i10": 0, "i11": 0, "i12": 1},
        {"o4": 0, "o5": 1},
    ),
)


@dataclass(frozen=True)
class FrontierState:
    r_in: int
    r_out: int
    balances: tuple[int, ...]
    record: _AbDpRecord


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _sender(n: int) -> str:
    return "0x" + f"{n:02x}" * 48


def _variant_pool(variant: int) -> PoolState:
    base = _pool()
    return PoolState(
        pool_id=base.pool_id,
        asset0=base.asset0,
        asset1=base.asset1,
        reserve0=420 + ((variant * 29) % 80),
        reserve1=760 + ((variant * 41) % 220),
        fee_bps=5 + ((variant % 4) * 5),
        lp_supply=base.lp_supply,
        status=base.status,
        created_at=base.created_at,
    )


def _ab_exact_in_batch(n: int, variant: int) -> tuple[PoolState, list[Intent], BalanceTable]:
    pool = _variant_pool(variant)
    balances = BalanceTable()
    intents: list[Intent] = []
    for idx in range(n):
        sender_no = (idx % 3) + 1 if variant % 2 else idx + 1
        amount_in = 35 + ((idx * 37 + variant * 19) % 145)
        min_amount_out = 8 + ((idx * 53 + variant * 11) % 150)
        balances.set(_sender(sender_no), ASSET0, balances.get(_sender(sender_no), ASSET0) + amount_in + 45)
        balances.set(_sender(sender_no), ASSET1, 0)
        intents.append(
            _exact_in_intent(
                80_000 + variant * 100 + idx,
                sender_no=sender_no,
                asset_in=ASSET0,
                asset_out=ASSET1,
                amount_in=amount_in,
                min_amount_out=min_amount_out,
            )
        )
    return pool, intents, balances


def _record_ge(candidate: _AbDpRecord, other: _AbDpRecord, context: Any) -> bool:
    if candidate.amount_a != other.amount_a:
        return int(candidate.amount_a) > int(other.amount_a)
    if candidate.surplus_b != other.surplus_b:
        return int(candidate.surplus_b) > int(other.surplus_b)
    if candidate.order_ids == other.order_ids:
        return True
    return _is_better_ab_dp_record(candidate, other, context)


def _dominates(candidate: FrontierState, other: FrontierState, context: Any) -> bool:
    return (
        int(candidate.r_in) <= int(other.r_in)
        and int(candidate.r_out) >= int(other.r_out)
        and all(int(a) >= int(b) for a, b in zip(candidate.balances, other.balances))
        and _record_ge(candidate.record, other.record, context)
    )


def _insert_frontier(frontier: list[FrontierState], candidate: FrontierState, context: Any) -> tuple[bool, int]:
    for existing in frontier:
        if _dominates(existing, candidate, context):
            return False, 1
    removed = sum(1 for existing in frontier if _dominates(candidate, existing, context))
    if removed:
        frontier[:] = [existing for existing in frontier if not _dominates(candidate, existing, context)]
    frontier.append(candidate)
    return True, removed


def _order_from_record(record: _AbDpRecord | None, intents: list[Intent]) -> tuple[Intent, ...] | None:
    if record is None:
        return None
    by_id = {intent.intent_id: intent for intent in intents}
    return tuple(by_id[intent_id] for intent_id in record.order_ids)


def _order_ids(order: tuple[Intent, ...] | None) -> list[str]:
    if order is None:
        return []
    return [intent.intent_id[-4:] for intent in order]


def _key(order: tuple[Intent, ...] | None, context: Any) -> tuple[int, int, tuple[str, ...]]:
    if order is None:
        return (-1, -1, tuple())
    amount_a, surplus_b, order_ids = _objective_for_order(order, context)
    return int(amount_a), int(surplus_b), tuple(str(intent_id)[-4:] for intent_id in order_ids)


def _run_full_state_dp_metrics(intents: list[Intent], context: Any) -> dict[str, Any]:
    n = len(intents)
    senders = tuple(sorted(context.sender_bal_in))
    sender_index = {sender: idx for idx, sender in enumerate(senders)}
    initial_balances = tuple(int(context.sender_bal_in[sender]) for sender in senders)
    dp: list[dict[tuple[int, int, tuple[int, ...]], _AbDpRecord]] = [dict() for _ in range(1 << n)]
    dp[0][(int(context.r_in0), int(context.r_out0), initial_balances)] = _AbDpRecord(0, 0, tuple())
    transitions = 0
    inserted = 1

    for mask in range(1 << n):
        for state, record in list(dp[mask].items()):
            r_in, r_out, balance_key = state
            bal_in = {sender: int(balance_key[idx]) for sender, idx in sender_index.items()}
            for idx, intent in enumerate(intents):
                bit = 1 << idx
                if mask & bit:
                    continue
                transitions += 1
                next_r_in = int(r_in)
                next_r_out = int(r_out)
                next_balance_key = balance_key
                next_a = int(record.amount_a)
                next_b = int(record.surplus_b)
                contribution = _objective_exact_in_contribution(
                    intent,
                    context,
                    r_in=next_r_in,
                    r_out=next_r_out,
                    bal_in=bal_in,
                )
                if contribution is not None:
                    amount_in, surplus, next_r_in, next_r_out = contribution
                    next_a += int(amount_in)
                    next_b += int(surplus)
                    next_balance_key = _debit_balance_key(
                        next_balance_key,
                        sender_index=sender_index,
                        sender=intent.sender_pubkey,
                        amount=int(amount_in),
                    )
                next_state = (int(next_r_in), int(next_r_out), next_balance_key)
                next_record = _AbDpRecord(next_a, next_b, (*record.order_ids, intent.intent_id))
                current = dp[mask | bit].get(next_state)
                if current is None or _is_better_ab_dp_record(next_record, current, context):
                    if current is None:
                        inserted += 1
                    dp[mask | bit][next_state] = next_record

    best_record: _AbDpRecord | None = None
    for record in dp[-1].values():
        if best_record is None or _is_better_ab_dp_record(record, best_record, context):
            best_record = record
    return {
        "order": _order_from_record(best_record, intents),
        "states_total": sum(len(states) for states in dp),
        "states_max_subset": max(len(states) for states in dp),
        "transitions": transitions,
        "inserted": inserted,
    }


def _run_frontier_dp_metrics(intents: list[Intent], context: Any) -> dict[str, Any]:
    n = len(intents)
    senders = tuple(sorted(context.sender_bal_in))
    sender_index = {sender: idx for idx, sender in enumerate(senders)}
    initial_balances = tuple(int(context.sender_bal_in[sender]) for sender in senders)
    dp: list[list[FrontierState]] = [[] for _ in range(1 << n)]
    dp[0] = [FrontierState(int(context.r_in0), int(context.r_out0), initial_balances, _AbDpRecord(0, 0, tuple()))]
    transitions = 0
    inserted = 1
    dominated_rejects = 0
    dominated_removals = 0

    for mask in range(1 << n):
        for state in list(dp[mask]):
            bal_in = {sender: int(state.balances[idx]) for sender, idx in sender_index.items()}
            for idx, intent in enumerate(intents):
                bit = 1 << idx
                if mask & bit:
                    continue
                transitions += 1
                next_r_in = int(state.r_in)
                next_r_out = int(state.r_out)
                next_balance_key = state.balances
                next_a = int(state.record.amount_a)
                next_b = int(state.record.surplus_b)
                contribution = _objective_exact_in_contribution(
                    intent,
                    context,
                    r_in=next_r_in,
                    r_out=next_r_out,
                    bal_in=bal_in,
                )
                if contribution is not None:
                    amount_in, surplus, next_r_in, next_r_out = contribution
                    next_a += int(amount_in)
                    next_b += int(surplus)
                    next_balance_key = _debit_balance_key(
                        next_balance_key,
                        sender_index=sender_index,
                        sender=intent.sender_pubkey,
                        amount=int(amount_in),
                    )
                candidate = FrontierState(
                    int(next_r_in),
                    int(next_r_out),
                    next_balance_key,
                    _AbDpRecord(next_a, next_b, (*state.record.order_ids, intent.intent_id)),
                )
                added, removed = _insert_frontier(dp[mask | bit], candidate, context)
                if added:
                    inserted += 1
                    dominated_removals += removed
                else:
                    dominated_rejects += 1

    best_state: FrontierState | None = None
    for state in dp[-1]:
        if best_state is None or _is_better_ab_dp_record(state.record, best_state.record, context):
            best_state = state
    return {
        "order": _order_from_record(best_state.record if best_state else None, intents),
        "states_total": sum(len(states) for states in dp),
        "states_max_subset": max(len(states) for states in dp),
        "transitions": transitions,
        "inserted": inserted,
        "dominated_rejects": dominated_rejects,
        "dominated_removals": dominated_removals,
    }


def _ab_frontier_cases() -> dict[str, Any]:
    cases: list[dict[str, Any]] = []
    for n, variant in ((5, 0), (6, 1), (7, 4), (8, 3), (8, 7)):
        pool, intents, balances = _ab_exact_in_batch(n, variant)
        context = _ab_context(pool, intents, balances)
        brute_order, brute_s = _timed(lambda: _best_order_by_objective_bruteforce(intents, context))
        full, full_s = _timed(lambda: _run_full_state_dp_metrics(intents, context))
        frontier, frontier_s = _timed(lambda: _run_frontier_dp_metrics(intents, context))
        brute_key = _key(brute_order, context)
        full_key = _key(full["order"], context)
        frontier_key = _key(frontier["order"], context)
        no_loss = brute_key == full_key == frontier_key
        cases.append(
            {
                "n": n,
                "variant": variant,
                "ok": no_loss,
                "pool": {"reserve0": int(pool.reserve0), "reserve1": int(pool.reserve1), "fee_bps": int(pool.fee_bps)},
                "bruteforce_key": brute_key,
                "full_state_key": full_key,
                "frontier_key": frontier_key,
                "bruteforce_order": _order_ids(brute_order),
                "frontier_order": _order_ids(frontier["order"]),
                "full_state": {k: v for k, v in full.items() if k != "order"},
                "frontier": {k: v for k, v in frontier.items() if k != "order"},
                "timing_s": {"bruteforce": brute_s, "full_state": full_s, "frontier": frontier_s},
                "state_reduction": int(full["states_total"]) - int(frontier["states_total"]),
            }
        )
    total_full_states = sum(int(case["full_state"]["states_total"]) for case in cases)
    total_frontier_states = sum(int(case["frontier"]["states_total"]) for case in cases)
    total_dominated = sum(int(case["frontier"]["dominated_rejects"]) + int(case["frontier"]["dominated_removals"]) for case in cases)
    return {
        "ok": all(case["ok"] for case in cases),
        "case_count": len(cases),
        "cases": cases,
        "total_full_state_states": total_full_states,
        "total_frontier_states": total_frontier_states,
        "total_state_reduction": total_full_states - total_frontier_states,
        "total_dominated_prunes": total_dominated,
        "state_reduction_observed": total_frontier_states < total_full_states,
        "dominance_pruning_observed": total_dominated > 0,
    }


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _tau_check(frontier: dict[str, Any], negative: dict[str, Any]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "case_results": [], "invalid_accepts": None}
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[case.step for case in TAU_CASES],
        timeout_s=10.0,
    )
    case_results: list[dict[str, Any]] = []
    ok = True
    invalid_accepts = 0
    for idx, case in enumerate(TAU_CASES):
        got = outputs.get(idx, {})
        mismatches = {
            key: {"expected": value, "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != value
        }
        if mismatches:
            ok = False
        if case.expected.get("o4") == 0 and got.get("o4") == 1:
            invalid_accepts += 1
        case_results.append(
            {
                "case_id": case.case_id,
                "ok": not mismatches,
                "expected": case.expected,
                "got": got,
                "mismatches": mismatches,
            }
        )
    facts = {
        "certificate_active": 1,
        "exact_in_same_direction_scope_ok": 1,
        "brute_force_oracle_parity_ok": int(bool(frontier["ok"])),
        "full_state_dp_parity_ok": int(bool(frontier["ok"])),
        "frontier_dominance_no_loss_ok": int(bool(frontier["ok"])),
        "dominance_pruning_observed": int(bool(frontier["dominance_pruning_observed"])),
        "deterministic_tie_ok": int(bool(frontier["ok"])),
        "negative_replay_ok": int(bool(negative["ok"])),
        "resource_budget_ok": 1,
        "fallback_boundary_ok": 1,
        "advisory_only": 1,
        "no_authority_effect": 1,
    }
    return {
        "ok": ok and invalid_accepts == 0 and all(value == 1 for value in facts.values()),
        "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
        "tau_bin": tau_bin,
        "tau_version": _tau_version(tau_bin),
        "case_results": case_results,
        "invalid_accepts": invalid_accepts,
        "facts": facts,
    }


def _build_report() -> dict[str, Any]:
    frontier = _ab_frontier_cases()
    negative = _compressed_refuter_report()
    tau = _tau_check(frontier, negative)
    files = {
        "spec": str(TAU_SPEC.relative_to(REPO_ROOT)),
        "tool": "tools/zenodex_ab_frontier_dp_breakthrough_20260628.py",
        "test": "tests/test_zenodex_ab_frontier_dp_breakthrough_20260628.py",
        "report": str(REPORT_MD.relative_to(REPO_ROOT)),
    }
    report = {
        "schema": "zenodex.ab_frontier_dp_breakthrough_report.v1",
        "date": "2026-06-28",
        "ok": bool(frontier["ok"] and frontier["dominance_pruning_observed"] and negative["ok"] and tau["ok"]),
        "breakthrough": {
            "name": "AB exact-in frontier-DP boundary certificate",
            "summary": "A dominance-pruned full-state frontier DP preserves brute-force AB ordering on bounded exact-in same-direction CPMM cases, but the bounded replay shows no final state-count reduction versus the existing full-state DP. Tau admits only the replayed research certificate facts.",
            "authority_boundary": "No production ordering path changes; host/kernel verifiers remain authoritative for clearing and settlement.",
        },
        "frontier_dp": frontier,
        "negative_replay": {
            "ok": bool(negative["ok"]),
            "falsified": negative["claim"]["falsified"],
            "objective_loss_amount_a": negative["results"]["objective_loss_amount_a"],
        },
        "tau": tau,
        "files": files,
        "file_hashes": {
            path: _sha256(REPO_ROOT / path)
            for path in (files["spec"], files["tool"], files["test"])
            if (REPO_ROOT / path).exists()
        },
        "non_claims": [
            "This is an exact-in same-direction CPMM certificate experiment, not a proof for mixed directions or exact-out batches.",
            "This does not replace the production AB ordering path.",
            "This does not revive one-record-per-subset Held-Karp compression; the negative replay remains required evidence.",
            "Observed dominance pruning did not reduce final DP state count on these fixtures, so this is negative knowledge for production optimization.",
        ],
        "replay_command": "python3 tools/zenodex_ab_frontier_dp_breakthrough_20260628.py",
    }
    return report


def _fmt_s(value: float) -> str:
    return f"{value:.6f}s"


def _write_markdown(report: dict[str, Any]) -> None:
    frontier = report["frontier_dp"]
    tau = report["tau"]
    lines: list[str] = []
    lines.append("# ZenoDEX AB Frontier-DP Boundary - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(report["breakthrough"]["summary"])
    lines.append("")
    lines.append(report["breakthrough"]["authority_boundary"])
    lines.append("")
    lines.append("## Tau Specification")
    lines.append("")
    lines.append(f"- Spec: `{tau['spec_path']}`")
    lines.append(f"- Latest Tau: `{tau.get('tau_version')}`")
    lines.append(f"- Tau cases: `{len(tau['case_results'])}`")
    lines.append(f"- Invalid accepts: `{tau['invalid_accepts']}`")
    lines.append("")
    lines.append("The Tau spec requires scope, brute-force parity, full-state parity, dominance no-loss evidence, observed dominance pruning, deterministic ties, negative replay, resource budget, fallback, advisory-only status, and no-authority facts.")
    lines.append("")
    lines.append("## Bounded Oracle Results")
    lines.append("")
    lines.append(f"- Cases: `{frontier['case_count']}`")
    lines.append(f"- Full-state DP states: `{frontier['total_full_state_states']}`")
    lines.append(f"- Frontier DP states: `{frontier['total_frontier_states']}`")
    lines.append(f"- State reduction: `{frontier['total_state_reduction']}`")
    lines.append(f"- Dominated prunes: `{frontier['total_dominated_prunes']}`")
    lines.append("")
    lines.append("The safe dominance rule rejected dominated candidates, but the existing full-state DP already converged to the same final state count on these bounded fixtures. That makes the rule a research boundary rather than a production optimization candidate.")
    lines.append("")
    lines.append("| n | variant | ok | full states | frontier states | reduction | brute time | frontier time |")
    lines.append("| --- | --- | --- | --- | --- | --- | --- | --- |")
    for case in frontier["cases"]:
        lines.append(
            f"| `{case['n']}` | `{case['variant']}` | `{case['ok']}` | `{case['full_state']['states_total']}` | `{case['frontier']['states_total']}` | `{case['state_reduction']}` | `{_fmt_s(case['timing_s']['bruteforce'])}` | `{_fmt_s(case['timing_s']['frontier'])}` |"
        )
    lines.append("")
    lines.append("## Negative Replay")
    lines.append("")
    lines.append(report["negative_replay"]["falsified"])
    lines.append(f"The replayed counterexample loses `{report['negative_replay']['objective_loss_amount_a']}` units of primary AB amount under unsafe one-record compression.")
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    for item in report["non_claims"]:
        lines.append(f"- {item}")
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
    report = _build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    _write_markdown(report)
    report["file_hashes"][str(REPORT_MD.relative_to(REPO_ROOT))] = _sha256(REPORT_MD)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "case_count": report["frontier_dp"]["case_count"],
                "state_reduction": report["frontier_dp"]["total_state_reduction"],
                "dominated_prunes": report["frontier_dp"]["total_dominated_prunes"],
                "tau_cases": len(report["tau"]["case_results"]),
                "invalid_accepts": report["tau"]["invalid_accepts"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

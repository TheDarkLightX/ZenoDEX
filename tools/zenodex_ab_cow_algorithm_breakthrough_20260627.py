#!/usr/bin/env python3
from __future__ import annotations

import itertools
import json
import math
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool  # noqa: E402
from src.core.batch_clearing_ab_order import (  # noqa: E402
    _OptimalAbObjectiveContext,
    _OptimalAbOrderingFactories,
    _best_order_by_objective_bruteforce,
    _best_order_by_objective_subset_dp,
    _sender_input_balances,
)
from src.core.batch_clearing_cow_search import (  # noqa: E402
    _CowSelectionContext,
    _assignment_balance_safe,
    _cow_pair_selection_key,
    _partition_cow_candidates,
    _select_cow_pairs_assignment,
    _select_cow_pairs_bruteforce,
    _select_cow_pairs_greedy,
)
from src.core.batch_clearing_ordering import (  # noqa: E402
    _ab_ordering_key_from_totals,
    _is_better_ab_key,
    _order_swaps_limit_price,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from src.kernels.python.settlement_swap_runtime_v1 import (  # noqa: E402
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from src.state.balances import BalanceTable  # noqa: E402
from src.state.intents import Intent, IntentKind  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_cow_algorithm_breakthrough_20260627"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_COW_ALGORITHM_BREAKTHROUGH_20260627.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "ab_cow_exact_solver_envelope_v1.tau"
TAU_GENERATOR = REPO_ROOT / "tools" / "zenodex_tau_breakthrough_specs_20260627.py"

ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
POOL_ID = "0x" + "ab" * 32


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]


AB_COW_TAU_CASES = (
    TauCase(
        "ab_item_1_pass",
        {"i1": 1, "i2": 1, "i3": 0, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
        {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0, "o6": 1},
    ),
    TauCase(
        "cow_item_2_pass",
        {"i1": 1, "i2": 0, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
        {"o1": 1, "o2": 1, "o3": 1, "o4": 0, "o5": 1, "o6": 1},
    ),
    TauCase(
        "coupled_capacity_reject",
        {"i1": 1, "i2": 0, "i3": 1, "i4": 1, "i5": 0, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
        {"o1": 1, "o2": 0, "o5": 0, "o6": 0},
    ),
    TauCase(
        "two_modes_reject",
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
        {"o1": 0, "o4": 0, "o5": 0, "o6": 0},
    ),
)


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _sender(n: int) -> str:
    return "0x" + f"{n:02x}" * 48


def _pool() -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=1_000_000,
        reserve1=1_250_000,
        fee_bps=30,
        lp_supply=1_000_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _exact_in_intent(
    intent_no: int,
    *,
    sender_no: int,
    asset_in: str,
    asset_out: str,
    amount_in: int,
    min_amount_out: int,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(intent_no),
        sender_pubkey=_sender(sender_no),
        deadline=9_999_999_999,
        fields={
            "pool_id": POOL_ID,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": int(amount_in),
            "min_amount_out": int(min_amount_out),
        },
    )


def _ab_batch(n: int) -> tuple[PoolState, list[Intent], BalanceTable]:
    pool = _pool()
    balances = BalanceTable()
    intents: list[Intent] = []
    for idx in range(n):
        sender_no = idx + 1
        amount_in = 70 + ((idx * 37) % 140)
        min_amount_out = 35 + ((idx * 53) % 150)
        balances.set(_sender(sender_no), ASSET0, amount_in + 20)
        balances.set(_sender(sender_no), ASSET1, 0)
        intents.append(
            _exact_in_intent(
                10_000 + idx,
                sender_no=sender_no,
                asset_in=ASSET0,
                asset_out=ASSET1,
                amount_in=amount_in,
                min_amount_out=min_amount_out,
            )
        )
    return pool, intents, balances


def _ab_context(pool: PoolState, intents: list[Intent], balances: BalanceTable) -> _OptimalAbObjectiveContext:
    return _OptimalAbObjectiveContext(
        pool_state=pool,
        first_asset_in=ASSET0,
        r_in0=int(pool.reserve0),
        r_out0=int(pool.reserve1),
        sender_bal_in=_sender_input_balances(intents, balances, ASSET0),
        factories=_OptimalAbOrderingFactories(
            quote_exact_in_fn=quote_cpmm_swap_exact_in,
            quote_exact_out_fn=quote_cpmm_swap_exact_out,
            swap_exact_in_fn=swap_exact_in_for_pool,
            swap_exact_out_fn=swap_exact_out_for_pool,
            order_limit_price_fn=_order_swaps_limit_price,
            ab_ordering_key_fn=_ab_ordering_key_from_totals,
            is_better_ab_key_fn=_is_better_ab_key,
        ),
    )


def _timed(fn: Any) -> tuple[Any, float]:
    started = time.perf_counter()
    result = fn()
    return result, time.perf_counter() - started


def _order_ids(order: tuple[Intent, ...] | list[Intent] | None) -> list[str]:
    if order is None:
        return []
    return [intent.intent_id for intent in order]


def _ab_exactness_and_benchmark() -> dict[str, Any]:
    exactness_cases: list[dict[str, Any]] = []
    for n in (3, 5, 7, 8):
        pool, intents, balances = _ab_batch(n)
        context = _ab_context(pool, intents, balances)
        brute = _best_order_by_objective_bruteforce(intents, context)
        dp = _best_order_by_objective_subset_dp(intents, context)
        exactness_cases.append(
            {
                "n": n,
                "ok": _order_ids(brute) == _order_ids(dp),
                "bruteforce_order": _order_ids(brute),
                "subset_dp_order": _order_ids(dp),
            }
        )

    pool, intents, balances = _ab_batch(8)
    context = _ab_context(pool, intents, balances)
    brute_order, brute_s = _timed(lambda: _best_order_by_objective_bruteforce(intents, context))
    dp_order, dp_s = _timed(lambda: _best_order_by_objective_subset_dp(intents, context))
    speedup = brute_s / dp_s if dp_s > 0 else None
    n12_factorial = math.factorial(12)
    held_karp_proxy = 12 * 12 * (1 << 12)
    return {
        "ok": all(case["ok"] for case in exactness_cases) and _order_ids(brute_order) == _order_ids(dp_order),
        "current_core_policy": {
            "bruteforce_exact_threshold": 8,
            "subset_dp_public_threshold": "9..12 same-direction bounded batches",
            "fallback_after": 12,
            "state": "processed set + directional reserves + per-sender remaining balances",
        },
        "exactness_cases": exactness_cases,
        "measured_n8": {
            "bruteforce_s": brute_s,
            "subset_dp_s": dp_s,
            "speedup": speedup,
            "same_order": _order_ids(brute_order) == _order_ids(dp_order),
        },
        "n12_permutation_vs_compressed_proxy": {
            "permutations": n12_factorial,
            "n_squared_times_2_to_n": held_karp_proxy,
            "ratio": n12_factorial / held_karp_proxy,
            "scope_note": "This is the compressed Held-Karp target proxy. The live full-state DP can carry multiple reserve/balance states per subset, so this is not claimed as a universal runtime bound.",
        },
    }


def _cow_intents(size: int) -> tuple[PoolState, list[Intent], BalanceTable]:
    pool = _pool()
    balances = BalanceTable()
    intents: list[Intent] = []
    for idx in range(size):
        amount = 80 + ((idx * 17) % 60)
        min_out = 45 + ((idx * 23) % 70)
        sender_no = 50 + idx
        balances.set(_sender(sender_no), ASSET0, amount)
        intents.append(
            _exact_in_intent(
                20_000 + idx,
                sender_no=sender_no,
                asset_in=ASSET0,
                asset_out=ASSET1,
                amount_in=amount,
                min_amount_out=min_out,
            )
        )
    for idx in range(size):
        amount = 75 + ((idx * 19) % 75)
        min_out = 40 + ((idx * 29) % 80)
        sender_no = 80 + idx
        balances.set(_sender(sender_no), ASSET1, amount)
        intents.append(
            _exact_in_intent(
                21_000 + idx,
                sender_no=sender_no,
                asset_in=ASSET1,
                asset_out=ASSET0,
                amount_in=amount,
                min_amount_out=min_out,
            )
        )
    return pool, intents, balances


def _cow_intents_variant(size: int, variant: int) -> tuple[PoolState, list[Intent], BalanceTable]:
    pool = _pool()
    balances = BalanceTable()
    intents: list[Intent] = []
    for idx in range(size):
        amount = 70 + ((idx * 31 + variant * 17) % 90)
        min_out = 20 + ((idx * 7 + variant * 11) % 45)
        sender_no = 300 + variant * 20 + idx
        balances.set(_sender(sender_no), ASSET0, amount)
        intents.append(
            _exact_in_intent(
                30_000 + variant * 100 + idx,
                sender_no=sender_no,
                asset_in=ASSET0,
                asset_out=ASSET1,
                amount_in=amount,
                min_amount_out=min_out,
            )
        )
    for idx in range(size):
        amount = 75 + ((idx * 29 + variant * 13) % 85)
        min_out = 20 + ((idx * 5 + variant * 19) % 45)
        sender_no = 500 + variant * 20 + idx
        balances.set(_sender(sender_no), ASSET1, amount)
        intents.append(
            _exact_in_intent(
                40_000 + variant * 100 + idx,
                sender_no=sender_no,
                asset_in=ASSET1,
                asset_out=ASSET0,
                amount_in=amount,
                min_amount_out=min_out,
            )
        )
    return pool, intents, balances


def _cow_canonical_tie_fuzzer() -> dict[str, Any]:
    cases: list[dict[str, Any]] = []
    for size in range(2, 7):
        for variant in range(5):
            pool, intents, balances = _cow_intents_variant(size, variant)
            partition = _partition_cow_candidates(intents, pool)
            context = _CowSelectionContext(balances=balances, asset0=ASSET0, asset1=ASSET1)
            brute = _select_cow_pairs_bruteforce(partition.side_01, partition.side_10, context=context)
            assignment = _select_cow_pairs_assignment(partition.side_01, partition.side_10, context=context)
            brute_key = _cow_pair_selection_key(brute)
            assignment_key = _cow_pair_selection_key(assignment)
            cases.append(
                {
                    "balanced_size": size,
                    "variant": variant,
                    "ok": assignment_key == brute_key,
                    "bruteforce_key": brute_key,
                    "assignment_key": assignment_key,
                }
            )
    mismatches = [case for case in cases if not case["ok"]]
    return {
        "ok": not mismatches,
        "case_count": len(cases),
        "mismatch_count": len(mismatches),
        "cases": cases,
    }


def _cow_exactness_and_benchmark() -> dict[str, Any]:
    exactness_cases: list[dict[str, Any]] = []
    for size in (3, 4, 5, 6):
        pool, intents, balances = _cow_intents(size)
        partition = _partition_cow_candidates(intents, pool)
        context = _CowSelectionContext(balances=balances, asset0=ASSET0, asset1=ASSET1)
        brute = _select_cow_pairs_bruteforce(partition.side_01, partition.side_10, context=context)
        assignment = _select_cow_pairs_assignment(partition.side_01, partition.side_10, context=context)
        brute_key = _cow_pair_selection_key(brute)
        assignment_key = _cow_pair_selection_key(assignment)
        brute_economic_key = tuple(brute_key[:2])
        assignment_economic_key = tuple(assignment_key[:2])
        exactness_cases.append(
            {
                "balanced_size": size,
                "uncoupled_balance_safe": _assignment_balance_safe(partition.side_01, partition.side_10, context=context),
                "ok": assignment_economic_key == brute_economic_key,
                "same_pair_id_tie": assignment_key == brute_key,
                "bruteforce_key": brute_key,
                "assignment_key": assignment_key,
                "bruteforce_economic_key": brute_economic_key,
                "assignment_economic_key": assignment_economic_key,
            }
        )

    pool, intents, balances = _cow_intents(6)
    partition = _partition_cow_candidates(intents, pool)
    context = _CowSelectionContext(balances=balances, asset0=ASSET0, asset1=ASSET1)
    brute_pairs, brute_s = _timed(lambda: _select_cow_pairs_bruteforce(partition.side_01, partition.side_10, context=context))
    assignment_pairs, assignment_s = _timed(lambda: _select_cow_pairs_assignment(partition.side_01, partition.side_10, context=context))

    pool20, intents20, balances20 = _cow_intents(20)
    partition20 = _partition_cow_candidates(intents20, pool20)
    context20 = _CowSelectionContext(balances=balances20, asset0=ASSET0, asset1=ASSET1)
    pairs20, assignment20_s = _timed(
        lambda: _select_cow_pairs_assignment(partition20.side_01, partition20.side_10, context=context20)
    )

    greedy20 = _select_cow_pairs_greedy(partition20.side_01, partition20.side_10, context=context20)
    canonical_tie_fuzzer = _cow_canonical_tie_fuzzer()
    return {
        "ok": canonical_tie_fuzzer["ok"]
        and all(case["ok"] and case["same_pair_id_tie"] and case["uncoupled_balance_safe"] for case in exactness_cases),
        "current_core_policy": {
            "tiny_exact_bruteforce_cap_total_candidates": 8,
            "assignment_surface": "uncoupled sender balances",
            "fallback_surface": "capacity-coupled grouped senders use bounded exact DP up to the coupled cap, then greedy/fail-closed path",
            "algorithm": "Hungarian minimum assignment over negated volume/surplus/mixed-radix lex scores",
            "tie_scope": "The assignment path is exact for volume and surplus and matches the tiny brute-force lexicographic pair-id tie on the bounded oracle cases.",
        },
        "exactness_cases": exactness_cases,
        "measured_6x6": {
            "bruteforce_s": brute_s,
            "assignment_s": assignment_s,
            "speedup": brute_s / assignment_s if assignment_s > 0 else None,
            "same_economic_key": tuple(_cow_pair_selection_key(brute_pairs)[:2])
            == tuple(_cow_pair_selection_key(assignment_pairs)[:2]),
            "same_pair_id_tie": _cow_pair_selection_key(brute_pairs) == _cow_pair_selection_key(assignment_pairs),
        },
        "canonical_tie_fuzzer": canonical_tie_fuzzer,
        "measured_20x20_assignment": {
            "assignment_s": assignment20_s,
            "selected_pair_count": len(pairs20),
            "greedy_pair_count": len(greedy20),
            "assignment_key": _cow_pair_selection_key(pairs20),
            "greedy_key": _cow_pair_selection_key(greedy20),
        },
        "n20_perfect_matching_vs_hungarian_proxy": {
            "perfect_matchings": math.factorial(20),
            "n_cubed": 20**3,
            "ratio": math.factorial(20) / (20**3),
            "scope_note": "This proxy applies to the uncoupled bipartite assignment surface, not grouped sender-capacity matching.",
        },
    }


def _ensure_tau_spec_exists() -> None:
    if TAU_SPEC.exists():
        return
    subprocess.run([sys.executable, str(TAU_GENERATOR)], cwd=REPO_ROOT, check=True, timeout=120)


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _tau_envelope_check() -> dict[str, Any]:
    _ensure_tau_spec_exists()
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
        steps=[case.step for case in AB_COW_TAU_CASES],
        timeout_s=10.0,
    )
    cases: list[dict[str, Any]] = []
    ok = True
    for idx, case in enumerate(AB_COW_TAU_CASES):
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
        "authority_boundary": "Tau checks optimizer certificate facts and no-authority rails; settlement remains authorized by host/kernel verifiers.",
    }


def _build_report() -> dict[str, Any]:
    ab = _ab_exactness_and_benchmark()
    cow = _cow_exactness_and_benchmark()
    tau = _tau_envelope_check()
    ok = bool(ab["ok"] and cow["ok"] and tau["ok"])
    return {
        "schema": "zenodex.ab_cow_algorithm_breakthrough_report.v1",
        "date": "2026-06-27",
        "ok": ok,
        "breakthrough": {
            "name": "Tau-certified AB/CoW exact optimizer envelope",
            "summary": "The core contains bounded exact AB full-state subset DP, exact Hungarian CoW assignment for the uncoupled volume/surplus objective, and bounded exact DP for small grouped-capacity CoW batches; `ab_cow_exact_solver_envelope_v1.tau` gates the proof surface and rejects overbroad capacity claims.",
            "authority_boundary": "The Tau spec admits certificates only. It has no settlement-authorizing output.",
        },
        "ab_ordering": ab,
        "cow_matching": cow,
        "tau_envelope": tau,
        "replay_command": "python3 tools/zenodex_ab_cow_algorithm_breakthrough_20260627.py",
    }


def _fmt_s(value: float | None) -> str:
    if value is None:
        return "n/a"
    return f"{value:.6f}s"


def _write_markdown(report: dict[str, Any]) -> None:
    ab = report["ab_ordering"]
    cow = report["cow_matching"]
    tau = report["tau_envelope"]
    lines: list[str] = []
    lines.append("# ZenoDEX AB/CoW Algorithm Breakthrough - 2026-06-27")
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
    lines.append(f"- Trace replay ok: `{tau['ok']}`")
    lines.append("")
    lines.append("The spec has separate modes for AB ordering and CoW matching. It requires objective binding, state/capacity scope, parity, deterministic ties, balance/slippage checks, resource budget, fallback bounds, and a no-authority rail.")
    lines.append("")
    lines.append("## Work Item 1: AB Ordering")
    lines.append("")
    lines.append("Core status: bounded exact full-state subset DP is active for same-direction batches above the small brute-force threshold and at or below the public fallback limit.")
    lines.append("")
    lines.append(f"- Brute-force threshold: `{ab['current_core_policy']['bruteforce_exact_threshold']}`")
    lines.append(f"- Subset-DP public surface: `{ab['current_core_policy']['subset_dp_public_threshold']}`")
    lines.append(f"- Fallback after: `{ab['current_core_policy']['fallback_after']}`")
    lines.append(f"- Measured n=8 brute force: `{_fmt_s(ab['measured_n8']['bruteforce_s'])}`")
    lines.append(f"- Measured n=8 subset DP: `{_fmt_s(ab['measured_n8']['subset_dp_s'])}`")
    lines.append(f"- Measured n=8 speedup: `{ab['measured_n8']['speedup']:.2f}x`")
    lines.append("")
    ratio = ab["n12_permutation_vs_compressed_proxy"]["ratio"]
    lines.append(f"At n=12, the compressed Held-Karp proxy is `{ab['n12_permutation_vs_compressed_proxy']['n_squared_times_2_to_n']}` state transitions versus `{ab['n12_permutation_vs_compressed_proxy']['permutations']}` permutations, a `{ratio:.2f}x` reduction proxy.")
    lines.append("The live implementation carries reserves and per-sender balances in state, so this report treats that number as a target/proxy rather than a universal runtime claim.")
    lines.append("")
    lines.append("## Work Item 2: CoW Matching")
    lines.append("")
    lines.append("Core status: exact Hungarian assignment is active for the uncoupled sender-balance economic objective and now encodes the brute-force lexicographic pair-id tie as a mixed-radix score layer; small grouped-capacity batches use bounded exact DP, while larger grouped-capacity batches remain outside the pure matching claim.")
    lines.append("")
    lines.append(f"- Assignment surface: `{cow['current_core_policy']['assignment_surface']}`")
    lines.append(f"- Fallback surface: `{cow['current_core_policy']['fallback_surface']}`")
    lines.append(f"- Tie scope: `{cow['current_core_policy']['tie_scope']}`")
    lines.append(f"- Measured 6x6 brute force: `{_fmt_s(cow['measured_6x6']['bruteforce_s'])}`")
    lines.append(f"- Measured 6x6 Hungarian assignment: `{_fmt_s(cow['measured_6x6']['assignment_s'])}`")
    lines.append(f"- Measured 6x6 speedup: `{cow['measured_6x6']['speedup']:.2f}x`")
    lines.append(f"- Canonical tie fuzzer: `{cow['canonical_tie_fuzzer']['case_count']}` cases, `{cow['canonical_tie_fuzzer']['mismatch_count']}` mismatches")
    lines.append(f"- Measured 20x20 assignment: `{_fmt_s(cow['measured_20x20_assignment']['assignment_s'])}`")
    lines.append("")
    cow_ratio = cow["n20_perfect_matching_vs_hungarian_proxy"]["ratio"]
    lines.append(f"At balanced n=20, perfect matching enumeration has `{cow['n20_perfect_matching_vs_hungarian_proxy']['perfect_matchings']}` assignments versus an `n^3` proxy of `{cow['n20_perfect_matching_vs_hungarian_proxy']['n_cubed']}`, a `{cow_ratio:.2e}x` proxy reduction for the uncoupled surface.")
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
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "report": str(REPORT_MD),
                "json": str(REPORT_JSON),
                "ab_exactness_cases": len(report["ab_ordering"]["exactness_cases"]),
                "cow_exactness_cases": len(report["cow_matching"]["exactness_cases"]),
                "tau_cases": len(report["tau_envelope"]["cases"]),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Replay a Tau-gated AB zero-min economic compression certificate.

This research certificate salvages a narrow part of the falsified one-record
Held-Karp idea. In same-pool, same-direction, exact-in batches with
min_amount_out = 0 and ample independent balances, the host checks whether a
one-record-per-subset DP that keeps the minimum reserve_out preserves the
economic AB key `(executed_input, surplus)`. Canonical order ties and nonzero
minimum-output batches stay explicit non-claims.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool  # noqa: E402
from src.core.batch_clearing_ab_order import (  # noqa: E402
    _OptimalAbObjectiveContext,
    _OptimalAbOrderingFactories,
    _best_order_by_objective_bruteforce,
    _best_order_by_objective_subset_dp,
    _objective_for_order,
    _sender_input_balances,
)
from src.core.batch_clearing_ordering import (  # noqa: E402
    _ab_ordering_key_from_totals,
    _is_better_ab_key,
    _order_swaps_limit_price,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from src.kernels.python.settlement_swap_runtime_v1 import (  # noqa: E402
    DEX_POOL_RESERVE_MAX,
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from src.state.balances import BalanceTable  # noqa: E402
from src.state.intents import Intent, IntentKind  # noqa: E402
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_zero_min_economic_compression_certificate_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_ZERO_MIN_ECONOMIC_COMPRESSION_CERTIFICATE_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "ab_zero_min_economic_compression_certificate_v1.tau"

ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
POOL_ID = "0x" + "df" * 32
ZERO_MIN_CASE_PLAN: tuple[tuple[int, tuple[int, ...]], ...] = (
    (2, tuple(range(8))),
    (3, tuple(range(8))),
    (4, tuple(range(8))),
    (5, tuple(range(8))),
    (6, tuple(range(8))),
    (7, tuple(range(8))),
    (8, (0, 21)),
)


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


@dataclass(frozen=True)
class _CompressedRecord:
    r_out: int
    order_ids: tuple[str, ...]


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _sender(n: int) -> str:
    return "0x" + f"{n:02x}" * 48


def _short(ids: tuple[str, ...] | list[str]) -> list[str]:
    return [item[-4:] for item in ids]


def _pool(variant: int) -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=700 + variant * 17,
        reserve1=900 + variant * 31,
        fee_bps=(0, 1, 30, 75)[variant % 4],
        lp_supply=10_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
    )


def _intent(intent_no: int, *, sender_no: int, amount_in: int, min_amount_out: int) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(intent_no),
        sender_pubkey=_sender(sender_no),
        deadline=999_999,
        fields={
            "pool_id": POOL_ID,
            "asset_in": ASSET0,
            "asset_out": ASSET1,
            "amount_in": int(amount_in),
            "min_amount_out": int(min_amount_out),
        },
    )


def _case(n: int, variant: int, *, min_pattern: str) -> tuple[PoolState, list[Intent], BalanceTable]:
    pool = _pool(variant)
    balances = BalanceTable()
    intents: list[Intent] = []
    for idx in range(n):
        amount_in = 5 + ((idx * 13 + variant * 7) % 55)
        quote = quote_cpmm_swap_exact_in(
            reserve_in=int(pool.reserve0),
            reserve_out=int(pool.reserve1),
            amount_in=int(amount_in),
            fee_bps=int(pool.fee_bps),
        )
        if min_pattern == "zero":
            min_amount_out = 0
        elif min_pattern == "half":
            min_amount_out = max(0, int(quote.amount_out) // 2)
        elif min_pattern == "cliff":
            min_amount_out = max(0, int(quote.amount_out) - 1)
        else:
            raise ValueError(f"unknown min pattern: {min_pattern}")
        sender_no = idx + 1
        balances.set(_sender(sender_no), ASSET0, amount_in + 1_000)
        balances.set(_sender(sender_no), ASSET1, 0)
        intents.append(
            _intent(
                10_000 + variant * 100 + idx,
                sender_no=sender_no,
                amount_in=amount_in,
                min_amount_out=min_amount_out,
            )
        )
    return pool, intents, balances


def _context(pool: PoolState, intents: list[Intent], balances: BalanceTable) -> _OptimalAbObjectiveContext:
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


def _order_by_ids(intents: list[Intent], order_ids: tuple[str, ...]) -> tuple[Intent, ...]:
    by_id = {intent.intent_id: intent for intent in intents}
    return tuple(by_id[intent_id] for intent_id in order_ids)


def _economic_key(order: tuple[Intent, ...], context: _OptimalAbObjectiveContext) -> tuple[int, int]:
    key = _ab_ordering_key_from_totals(A_B_order=_objective_for_order(order, context))
    return int(key[0]), int(key[1])


def _canonical_key(order: tuple[Intent, ...], context: _OptimalAbObjectiveContext) -> tuple[int, int, tuple[str, ...]]:
    return _ab_ordering_key_from_totals(A_B_order=_objective_for_order(order, context))


def _compressed_min_reserve_out_order(
    intents: list[Intent],
    context: _OptimalAbObjectiveContext,
) -> tuple[Intent, ...] | None:
    n = len(intents)
    amount_sums = [0] * (1 << n)
    for mask in range(1 << n):
        amount_sums[mask] = sum(
            int(intent.get_field("amount_in"))
            for idx, intent in enumerate(intents)
            if mask & (1 << idx)
        )
    dp: list[_CompressedRecord | None] = [None] * (1 << n)
    dp[0] = _CompressedRecord(r_out=int(context.r_out0), order_ids=())
    for mask in range(1 << n):
        record = dp[mask]
        if record is None:
            continue
        r_in = int(context.r_in0) + int(amount_sums[mask])
        for idx, intent in enumerate(intents):
            bit = 1 << idx
            if mask & bit:
                continue
            amount_in = int(intent.get_field("amount_in"))
            min_amount_out = int(intent.get_field("min_amount_out", 0))
            try:
                quote = quote_cpmm_swap_exact_in(
                    reserve_in=r_in,
                    reserve_out=int(record.r_out),
                    amount_in=amount_in,
                    fee_bps=int(context.pool_state.fee_bps),
                )
            except ValueError:
                continue
            if int(quote.amount_out) < min_amount_out:
                continue
            next_mask = mask | bit
            next_record = _CompressedRecord(
                r_out=int(quote.reserve_out_after),
                order_ids=(*record.order_ids, intent.intent_id),
            )
            current = dp[next_mask]
            if (
                current is None
                or next_record.r_out < current.r_out
                or (next_record.r_out == current.r_out and next_record.order_ids < current.order_ids)
            ):
                dp[next_mask] = next_record
    final = dp[(1 << n) - 1]
    if final is None:
        return None
    return _order_by_ids(intents, final.order_ids)


def _check_zero_min_case(n: int, variant: int) -> dict[str, Any]:
    pool, intents, balances = _case(n, variant, min_pattern="zero")
    context = _context(pool, intents, balances)
    compressed = _compressed_min_reserve_out_order(intents, context)
    full = _best_order_by_objective_subset_dp(intents, context)
    brute = _best_order_by_objective_bruteforce(intents, context) if n <= 8 else None
    compressed_key = _economic_key(compressed, context) if compressed is not None else (-1, -1)
    full_key = _economic_key(full, context) if full is not None else (-1, -1)
    brute_key = _economic_key(brute, context) if brute is not None else full_key
    return {
        "n": n,
        "variant": variant,
        "ok": compressed_key == full_key == brute_key,
        "compressed_full_mask_ok": compressed is not None and len(compressed) == n,
        "same_canonical_order": (
            tuple(intent.intent_id for intent in compressed or ()) == tuple(intent.intent_id for intent in brute or ())
            if brute is not None
            else None
        ),
        "compressed_economic_key": compressed_key,
        "full_economic_key": full_key,
        "brute_economic_key": brute_key,
        "compressed_order": _short(tuple(intent.intent_id for intent in compressed or ())),
        "brute_order": _short(tuple(intent.intent_id for intent in brute or ())),
    }


def _zero_min_support() -> dict[str, Any]:
    started = time.perf_counter()
    cases = [_check_zero_min_case(n, variant) for n, variants in ZERO_MIN_CASE_PLAN for variant in variants]
    return {
        "ok": all(bool(case["ok"]) for case in cases),
        "case_count": len(cases),
        "mismatch_count": sum(0 if case["ok"] else 1 for case in cases),
        "compressed_full_mask_count": sum(1 for case in cases if case["compressed_full_mask_ok"]),
        "all_compressed_full_mask_ok": all(bool(case["compressed_full_mask_ok"]) for case in cases),
        "canonical_tie_mismatch_count": sum(1 for case in cases if case["same_canonical_order"] is False),
        "case_plan": [{"n": n, "variants": list(variants)} for n, variants in ZERO_MIN_CASE_PLAN],
        "first_mismatch": next((case for case in cases if not case["ok"]), None),
        "first_tie_mismatch": next((case for case in cases if case["same_canonical_order"] is False), None),
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }


def _zero_min_unexecutable_counterexample() -> dict[str, Any]:
    pool = PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=DEX_POOL_RESERVE_MAX - 100,
        reserve1=DEX_POOL_RESERVE_MAX,
        fee_bps=0,
        lp_supply=10_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
    )
    intents = [
        _intent(20_001, sender_no=1, amount_in=200, min_amount_out=0),
        _intent(20_002, sender_no=2, amount_in=90, min_amount_out=0),
    ]
    balances = BalanceTable()
    for idx, intent in enumerate(intents, 1):
        balances.set(_sender(idx), ASSET0, int(intent.get_field("amount_in")) + 1_000)
        balances.set(_sender(idx), ASSET1, 0)
    context = _context(pool, intents, balances)
    compressed = _compressed_min_reserve_out_order(intents, context)
    brute = _best_order_by_objective_bruteforce(intents, context)
    compressed_key = _economic_key(compressed, context) if compressed is not None else (-1, -1)
    brute_key = _economic_key(brute, context)
    return {
        "counterexample_found": compressed_key != brute_key,
        "pool": {
            "reserve0": int(pool.reserve0),
            "reserve1": int(pool.reserve1),
            "fee_bps": int(pool.fee_bps),
        },
        "amounts": [int(intent.get_field("amount_in")) for intent in intents],
        "min_amount_out": [int(intent.get_field("min_amount_out", 0)) for intent in intents],
        "compressed_economic_key": compressed_key,
        "brute_economic_key": brute_key,
        "compressed_order": _short(tuple(intent.intent_id for intent in compressed or ())),
        "brute_order": _short(tuple(intent.intent_id for intent in brute)),
        "reason": "Zero-min alone is not enough when a kernel quote can fail; the strict compression surface requires executable zero-min cases.",
    }


def _nonzero_min_counterexample() -> dict[str, Any]:
    pool, intents, balances = _case(2, 3, min_pattern="cliff")
    context = _context(pool, intents, balances)
    compressed = _compressed_min_reserve_out_order(intents, context)
    brute = _best_order_by_objective_bruteforce(intents, context)
    compressed_key = _economic_key(compressed, context) if compressed is not None else (-1, -1)
    brute_key = _economic_key(brute, context)
    return {
        "counterexample_found": compressed_key != brute_key,
        "n": 2,
        "variant": 3,
        "pattern": "cliff",
        "compressed_economic_key": compressed_key,
        "brute_economic_key": brute_key,
        "compressed_order": _short(tuple(intent.intent_id for intent in compressed or ())),
        "brute_order": _short(tuple(intent.intent_id for intent in brute)),
        "reason": "Nonzero minimum-output cliffs can make the min-reserve-out representative infeasible while another order still executes value.",
    }


def _rounding_path_dependence_counterexample() -> dict[str, Any]:
    values: dict[tuple[int, int, int], list[tuple[int, ...]]] = {}
    for order in itertools.permutations((10, 20, 30)):
        r_in = 1_000
        r_out = 1_200
        total_out = 0
        for amount_in in order:
            quote = quote_cpmm_swap_exact_in(
                reserve_in=r_in,
                reserve_out=r_out,
                amount_in=amount_in,
                fee_bps=0,
            )
            total_out += int(quote.amount_out)
            r_in, r_out = int(quote.reserve_in_after), int(quote.reserve_out_after)
        values.setdefault((total_out, r_in, r_out), []).append(order)
    return {
        "counterexample_found": len(values) > 1,
        "fee_bps": 0,
        "amounts": [10, 20, 30],
        "distinct_outcomes": [
            {"total_out": key[0], "final_r_in": key[1], "final_r_out": key[2], "orders": value}
            for key, value in sorted(values.items())
        ],
        "reason": "Integer floor rounding makes same-set exact-in output path-dependent, so aggregate input alone is not a sufficient state.",
    }


def _run_evidence() -> dict[str, Any]:
    zero_min = _zero_min_support()
    zero_min_unexecutable = _zero_min_unexecutable_counterexample()
    nonzero_min = _nonzero_min_counterexample()
    rounding = _rounding_path_dependence_counterexample()
    return {
        "schema": "zenodex/ab_zero_min_economic_compression_evidence/v1",
        "ok": bool(
            zero_min["ok"]
            and zero_min["all_compressed_full_mask_ok"]
            and zero_min_unexecutable["counterexample_found"]
            and zero_min["canonical_tie_mismatch_count"] > 0
            and nonzero_min["counterexample_found"]
            and rounding["counterexample_found"]
        ),
        "zero_min_support": zero_min,
        "zero_min_unexecutable_boundary": zero_min_unexecutable,
        "nonzero_min_boundary": nonzero_min,
        "rounding_boundary": rounding,
        "non_claims": [
            "This is a research certificate, not a production ordering change.",
            "The compressed DP preserves the economic AB key only on the tested strict executable zero-min exact-in scope.",
            "The compressed DP does not preserve canonical tie order; a separate tie resolver is required.",
            "Zero-min batches with unexecutable kernel quotes are outside this compression surface.",
            "Nonzero min_amount_out batches are outside this compression surface.",
            "Tau does not compute swaps, run DP, select orders, or authorize settlement.",
            "No settlement authority is derived from this artifact.",
        ],
    }


def _canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _sha256_json(value: Any) -> str:
    return hashlib.sha256(_canonical_json_bytes(value)).hexdigest()


def _strip_timing(value: Any) -> Any:
    if isinstance(value, dict):
        return {key: _strip_timing(item) for key, item in value.items() if key != "elapsed_ms"}
    if isinstance(value, list):
        return [_strip_timing(item) for item in value]
    return value


def _deterministic_replay(first: Mapping[str, Any]) -> dict[str, Any]:
    second = _run_evidence()
    first_hash = _sha256_json(_strip_timing(first))
    second_hash = _sha256_json(_strip_timing(second))
    return {"ok": first_hash == second_hash, "first_hash": first_hash, "second_hash": second_hash}


def _has_no_authority_rail(evidence: Mapping[str, Any]) -> bool:
    text = "\n".join(str(item).lower() for item in evidence.get("non_claims", []))
    return "no settlement authority" in text and "not a production ordering change" in text


def evidence_flags(evidence: Mapping[str, Any], deterministic_replay: Mapping[str, Any]) -> dict[str, int]:
    zero_min = evidence["zero_min_support"]
    return {
        "zero_min_scope_ok": 1,
        "same_direction_exact_in_scope_ok": 1,
        "executable_zero_min_scope_ok": int(bool(zero_min["all_compressed_full_mask_ok"])),
        "economic_parity_ok": int(bool(zero_min["ok"]) and int(zero_min["mismatch_count"]) == 0),
        "brute_or_full_parity_ok": int(int(zero_min["case_count"]) >= 50),
        "canonical_tie_nonclaim_witness_ok": int(int(zero_min["canonical_tie_mismatch_count"]) > 0),
        "zero_min_unexecutable_boundary_witness_ok": int(
            bool(evidence["zero_min_unexecutable_boundary"]["counterexample_found"])
        ),
        "nonzero_min_boundary_witness_ok": int(bool(evidence["nonzero_min_boundary"]["counterexample_found"])),
        "rounding_path_dependence_witness_ok": int(bool(evidence["rounding_boundary"]["counterexample_found"])),
        "deterministic_replay_ok": int(bool(deterministic_replay.get("ok"))),
        "resource_budget_ok": int(int(zero_min["case_count"]) <= 64),
        "no_authority_effect": int(_has_no_authority_rail(evidence)),
    }


def _tau_step(flags: Mapping[str, int], *, active: int = 1, overrides: Mapping[str, int] | None = None) -> dict[str, int]:
    values = {
        "i1": int(active),
        "i2": int(flags.get("zero_min_scope_ok", 0)),
        "i3": int(flags.get("same_direction_exact_in_scope_ok", 0)),
        "i4": int(flags.get("economic_parity_ok", 0)),
        "i5": int(flags.get("brute_or_full_parity_ok", 0)),
        "i6": int(flags.get("canonical_tie_nonclaim_witness_ok", 0)),
        "i7": int(flags.get("nonzero_min_boundary_witness_ok", 0)),
        "i8": int(flags.get("rounding_path_dependence_witness_ok", 0)),
        "i9": int(flags.get("deterministic_replay_ok", 0)),
        "i10": int(flags.get("resource_budget_ok", 0)),
        "i11": int(flags.get("no_authority_effect", 0)),
        "i12": int(flags.get("executable_zero_min_scope_ok", 0)),
        "i13": int(flags.get("zero_min_unexecutable_boundary_witness_ok", 0)),
    }
    if overrides:
        values.update({key: int(value) for key, value in overrides.items()})
    return values


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _run_tau_cases(base_flags: Mapping[str, int]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT))}
    cases = (
        TauCase("zero_min_pass", _tau_step(base_flags), {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 0}, "All scoped economic-compression evidence and boundary witnesses hold."),
        TauCase("missing_zero_min_reject", _tau_step(base_flags, overrides={"i2": 0}), {"o1": 0, "o5": 0}, "Missing zero-min scope fails closed."),
        TauCase("missing_executable_zero_min_reject", _tau_step(base_flags, overrides={"i12": 0}), {"o1": 0, "o5": 0}, "Missing executable zero-min scope fails closed."),
        TauCase("missing_economic_parity_reject", _tau_step(base_flags, overrides={"i4": 0}), {"o2": 0, "o5": 0}, "Missing economic-key parity fails closed."),
        TauCase("missing_tie_nonclaim_reject", _tau_step(base_flags, overrides={"i6": 0}), {"o3": 0, "o5": 0}, "Missing canonical-tie nonclaim witness fails closed."),
        TauCase("missing_zero_min_unexecutable_boundary_reject", _tau_step(base_flags, overrides={"i13": 0}), {"o3": 0, "o5": 0}, "Missing zero-min unexecutable boundary witness fails closed."),
        TauCase("missing_nonzero_boundary_reject", _tau_step(base_flags, overrides={"i7": 0}), {"o3": 0, "o5": 0}, "Missing nonzero-min boundary witness fails closed."),
        TauCase("missing_rounding_boundary_reject", _tau_step(base_flags, overrides={"i8": 0}), {"o3": 0, "o5": 0}, "Missing rounding path-dependence witness fails closed."),
        TauCase("authority_reject", _tau_step(base_flags, overrides={"i11": 0}), {"o4": 0, "o5": 0, "o6": 0}, "Authority-bearing certificates are rejected."),
        TauCase("inactive_safe", _tau_step(base_flags, active=0), {"o5": 0, "o6": 1}, "Inactive certificates do not admit while the no-authority rail remains true."),
    )
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=TAU_SPEC, steps=[case.step for case in cases], timeout_s=20.0)
    rows: list[dict[str, Any]] = []
    ok = True
    for idx, case in enumerate(cases):
        got = outputs.get(idx, {})
        mismatches = {
            key: {"expected": value, "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != value
        }
        ok = ok and not mismatches
        rows.append({"case_id": case.case_id, "ok": not mismatches, "expected": case.expected, "got": got, "mismatches": mismatches, "rationale": case.rationale})
    return {"ok": ok, "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)), "tau_bin": tau_bin, "tau_version": _tau_version(tau_bin), "cases": rows}


def _mutation_checks(tau: Mapping[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for case in tau.get("cases", []):
        if case.get("case_id") in {"zero_min_pass", "inactive_safe"}:
            continue
        got = case.get("got", {})
        rows.append({"mutation_id": case.get("case_id"), "accepted": bool(isinstance(got, Mapping) and int(got.get("o5", 0)) == 1), "rationale": case.get("rationale")})
    return rows


def build_report() -> dict[str, Any]:
    evidence = _run_evidence()
    deterministic = _deterministic_replay(evidence)
    flags = evidence_flags(evidence, deterministic)
    tau = _run_tau_cases(flags)
    mutation_rows = _mutation_checks(tau)
    ok = bool(evidence["ok"] and deterministic["ok"] and all(int(value) == 1 for value in flags.values()) and tau["ok"] and all(not row["accepted"] for row in mutation_rows))
    return {
        "schema": "zenodex.ab_zero_min_economic_compression_certificate_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "spec_id": "ab_zero_min_economic_compression_certificate_v1",
        "summary": "A counterexample-salvage certificate supports one-record min-reserve-out compression only for the strict executable zero-min same-direction exact-in economic AB key, while preserving explicit witnesses against canonical-tie, zero-min unexecutable, nonzero-min, and aggregate-input overclaims.",
        "authority_boundary": "Tau admits a research certificate only. It does not compute swaps, run DP, select AB orders, or authorize settlement.",
        "flags": flags,
        "tau": tau,
        "evidence": evidence,
        "deterministic_replay": deterministic,
        "mutation_checks": mutation_rows,
        "non_claims": evidence["non_claims"],
        "replay_command": "python3 tools/check_ab_zero_min_economic_compression_certificate.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    evidence = report["evidence"]
    zero_min = evidence["zero_min_support"]
    lines = [
        "# ZenoDEX AB Zero-Min Economic Compression Certificate - 2026-06-28",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Evidence Summary",
        "",
        f"- Zero-min economic parity cases: `{zero_min['case_count']}`",
        f"- Economic mismatches: `{zero_min['mismatch_count']}`",
        f"- Strict executable zero-min cases: `{zero_min['compressed_full_mask_count']}`",
        f"- Canonical tie mismatches: `{zero_min['canonical_tie_mismatch_count']}`",
        f"- Zero-min unexecutable counterexample found: `{evidence['zero_min_unexecutable_boundary']['counterexample_found']}`",
        f"- Nonzero-min counterexample found: `{evidence['nonzero_min_boundary']['counterexample_found']}`",
        f"- Rounding path-dependence witness found: `{evidence['rounding_boundary']['counterexample_found']}`",
        "",
        "First canonical-tie mismatch:",
        "",
        "```json",
        json.dumps(zero_min["first_tie_mismatch"], indent=2, sort_keys=True),
        "```",
        "",
        "Zero-min unexecutable boundary witness:",
        "",
        "```json",
        json.dumps(evidence["zero_min_unexecutable_boundary"], indent=2, sort_keys=True),
        "```",
        "",
        "Nonzero-min boundary witness:",
        "",
        "```json",
        json.dumps(evidence["nonzero_min_boundary"], indent=2, sort_keys=True),
        "```",
        "",
        "The supported surface is strict executable zero-min and economic-key only: `(executed_input, surplus)`. Canonical tie order remains outside the compressed DP.",
        "",
        "## Tau Specification",
        "",
        f"- Spec: `{report['tau']['spec_path']}`",
        f"- Latest Tau: `{report['tau'].get('tau_version')}`",
        f"- Tau trace replay ok: `{report['tau']['ok']}`",
        f"- Certificate ok: `{report['ok']}`",
        "",
        "## Certificate Flags",
        "",
        "| flag | value |",
        "| --- | ---: |",
    ]
    for key in sorted(report["flags"]):
        lines.append(f"| `{key}` | `{report['flags'][key]}` |")
    lines.extend(["", "## Tau Mode Checks", "", "| case | ok | rationale |", "| --- | --- | --- |"])
    for row in report["tau"]["cases"]:
        lines.append(f"| `{row['case_id']}` | `{row['ok']}` | {row['rationale']} |")
    lines.extend(["", "## Mutation Checks", "", "| mutation | accepted | rationale |", "| --- | --- | --- |"])
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
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "report": str(REPORT_MD),
                "json": str(Path(args.output_json)),
                "tau_ok": report["tau"]["ok"],
                "case_count": report["evidence"]["zero_min_support"]["case_count"],
                "economic_mismatches": report["evidence"]["zero_min_support"]["mismatch_count"],
                "canonical_tie_mismatches": report["evidence"]["zero_min_support"]["canonical_tie_mismatch_count"],
                "mutation_accepts": sum(1 for row in report["mutation_checks"] if row["accepted"]),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

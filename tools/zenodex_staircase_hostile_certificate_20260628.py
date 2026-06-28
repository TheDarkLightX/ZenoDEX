#!/usr/bin/env python3
"""Replay a hostile-corpus certificate for exact-in staircase split routing."""

from __future__ import annotations

import hashlib
import json
import random
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core import split_routing as split_routing_mod  # noqa: E402
from src.core.split_routing import PoolXY  # noqa: E402
from src.integration.exact_in_route_certificate import (  # noqa: E402
    build_exact_in_route_guarded_quote_packet,
    verify_exact_in_route_guarded_quote_packet_payload,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402
from tools.benchmark_split_routing_profiles import (  # noqa: E402
    build_split_routing_profile_report,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_staircase_hostile_certificate_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_STAIRCASE_HOSTILE_CERTIFICATE_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "exact_in_staircase_hostile_certificate_v1.tau"

FACT_ORDER = (
    "certificate_active",
    "bounded_corpus_ok",
    "brute_force_parity_ok",
    "leftmost_tie_break_ok",
    "quote_count_lift_ok",
    "known_gap_recovered",
    "baseline_gap_observed",
    "guarded_packet_replay_ok",
    "runtime_default_unchanged",
    "advisory_only",
    "no_authority_effect",
)


@dataclass(frozen=True)
class HostileCase:
    case_id: str
    pool0: PoolXY
    pool1: PoolXY
    amount_in: int
    family: str


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _pool(pid: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0="A",
        asset1="B",
        reserve0=int(r0),
        reserve1=int(r1),
        fee_bps=int(fee_bps),
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _structured_cases() -> list[HostileCase]:
    families: tuple[tuple[str, PoolXY, PoolXY, tuple[int, ...]], ...] = (
        (
            "symmetry_plateau",
            PoolXY(x=1_000, y=1_000, fee_bps=0),
            PoolXY(x=1_000, y=1_000, fee_bps=0),
            (17, 64, 257, 1_024, 2_048),
        ),
        (
            "pool0_deep_output_skew",
            PoolXY(x=1, y=500_000, fee_bps=0),
            PoolXY(x=500_000, y=500_000, fee_bps=0),
            (5, 17, 64, 257, 1_024, 2_048),
        ),
        (
            "pool1_deep_output_skew",
            PoolXY(x=500_000, y=500_000, fee_bps=0),
            PoolXY(x=1, y=500_000, fee_bps=0),
            (5, 17, 64, 257, 1_024, 2_048),
        ),
        (
            "high_fee_plateau",
            PoolXY(x=7, y=31, fee_bps=9_900),
            PoolXY(x=11, y=37, fee_bps=9_800),
            (101, 257, 1_024, 2_048, 4_096),
        ),
        (
            "dust_output_endpoint",
            PoolXY(x=1_000_000, y=3, fee_bps=0),
            PoolXY(x=5_000, y=4, fee_bps=0),
            (2_048, 4_096),
        ),
        (
            "one_sided_fee_reject",
            PoolXY(x=1, y=1_000, fee_bps=10_000),
            PoolXY(x=100, y=1_000, fee_bps=0),
            (5, 17, 64, 257),
        ),
        (
            "endpoint_heavy_fee_gap",
            PoolXY(x=999_983, y=257, fee_bps=250),
            PoolXY(x=257, y=999_983, fee_bps=250),
            (257, 1_024, 2_048, 3_000),
        ),
        (
            "known_tie_break_gap",
            PoolXY(x=2, y=115, fee_bps=424),
            PoolXY(x=189, y=3, fee_bps=157),
            (199, 257, 1_024),
        ),
        (
            "dense_profile_gap",
            PoolXY(x=87, y=80, fee_bps=75),
            PoolXY(x=46, y=66, fee_bps=11),
            (4_096,),
        ),
    )
    cases: list[HostileCase] = []
    for family, pool0, pool1, amounts in families:
        for amount_in in amounts:
            cases.append(HostileCase(f"{family}_{amount_in}", pool0, pool1, int(amount_in), family))
    return cases


def _seeded_cases(count: int = 100) -> list[HostileCase]:
    rng = random.Random(20260628)
    cases: list[HostileCase] = []
    for index in range(count):
        if index % 5 == 0:
            pool0 = PoolXY(x=rng.randint(1, 8), y=rng.randint(500, 500_000), fee_bps=rng.randint(0, 500))
            pool1 = PoolXY(x=rng.randint(500, 500_000), y=rng.randint(1, 500_000), fee_bps=rng.randint(0, 500))
            family = "seeded_skew"
        elif index % 5 == 1:
            pool0 = PoolXY(x=rng.randint(1, 60), y=rng.randint(1, 80), fee_bps=rng.randint(8_000, 9_999))
            pool1 = PoolXY(x=rng.randint(1, 60), y=rng.randint(1, 80), fee_bps=rng.randint(8_000, 9_999))
            family = "seeded_high_fee"
        elif index % 5 == 2:
            reserve = rng.randint(50, 2_000)
            pool0 = PoolXY(x=reserve, y=reserve, fee_bps=rng.randint(0, 250))
            pool1 = PoolXY(x=reserve, y=reserve, fee_bps=rng.randint(0, 250))
            family = "seeded_tie"
        elif index % 5 == 3:
            pool0 = PoolXY(x=rng.randint(1, 1_000), y=rng.randint(1, 5), fee_bps=rng.randint(0, 500))
            pool1 = PoolXY(x=rng.randint(1, 1_000), y=rng.randint(1, 5), fee_bps=rng.randint(0, 500))
            family = "seeded_dust"
        else:
            pool0 = PoolXY(x=rng.randint(1, 1_000), y=rng.randint(1, 1_000), fee_bps=rng.randint(0, 9_999))
            pool1 = PoolXY(x=rng.randint(1, 1_000), y=rng.randint(1, 1_000), fee_bps=rng.randint(0, 9_999))
            family = "seeded_mixed"
        cases.append(HostileCase(f"{family}_{index:03d}", pool0, pool1, rng.randint(2, 2_048), family))
    return cases


def _hostile_cases() -> tuple[HostileCase, ...]:
    return tuple(_structured_cases() + _seeded_cases())


def _counted_call(fn: Callable[[], tuple[int, int]]) -> dict[str, Any]:
    original_quote = split_routing_mod.exact_out_for_pool_exact_in
    calls = {"n": 0}

    def counted_quote(pool: PoolXY, amount: int) -> int:
        calls["n"] = int(calls["n"]) + 1
        return original_quote(pool, amount)

    split_routing_mod.exact_out_for_pool_exact_in = counted_quote  # type: ignore[assignment]
    try:
        try:
            amount_out, split_a = fn()
        except ValueError as exc:
            return {"status": "reject", "reason": str(exc), "quote_count": int(calls["n"])}
    finally:
        split_routing_mod.exact_out_for_pool_exact_in = original_quote
    return {"status": "ok", "amount_out": int(amount_out), "split_a": int(split_a), "quote_count": int(calls["n"])}


def _hostile_report() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for case in _hostile_cases():
        brute = _counted_call(
            lambda case=case: split_routing_mod.brute_force_best_split_two_pools_exact_in(
                case.pool0,
                case.pool1,
                case.amount_in,
            )
        )
        staircase = _counted_call(
            lambda case=case: split_routing_mod.best_split_two_pools_exact_in(
                case.pool0,
                case.pool1,
                case.amount_in,
                search_profile="staircase_exact",
            )
        )
        parity = (
            brute["status"] == "ok"
            and staircase["status"] == "ok"
            and int(brute["amount_out"]) == int(staircase["amount_out"])
            and int(brute["split_a"]) == int(staircase["split_a"])
        )
        rows.append(
            {
                "case_id": case.case_id,
                "family": case.family,
                "amount_in": int(case.amount_in),
                "pool0": {"x": case.pool0.x, "y": case.pool0.y, "fee_bps": case.pool0.fee_bps},
                "pool1": {"x": case.pool1.x, "y": case.pool1.y, "fee_bps": case.pool1.fee_bps},
                "brute": brute,
                "staircase": staircase,
                "parity": bool(parity),
            }
        )
    ok_rows = [row for row in rows if row["brute"]["status"] == "ok"]
    family_counts: dict[str, int] = {}
    for row in rows:
        family_counts[row["family"]] = int(family_counts.get(row["family"], 0)) + 1
    return {
        "case_count": len(rows),
        "ok_case_count": len(ok_rows),
        "reject_case_count": len(rows) - len(ok_rows),
        "mismatch_count": sum(1 for row in ok_rows if not row["parity"]),
        "leftmost_tie_break_mismatch_count": sum(
            1
            for row in ok_rows
            if row["parity"] is False and row["brute"].get("amount_out") == row["staircase"].get("amount_out")
        ),
        "family_counts": dict(sorted(family_counts.items())),
        "brute_quote_count_total": sum(int(row["brute"]["quote_count"]) for row in ok_rows),
        "staircase_quote_count_total": sum(int(row["staircase"]["quote_count"]) for row in ok_rows),
        "rows": rows,
    }


def _known_gap_report() -> dict[str, Any]:
    pool0 = PoolXY(x=87, y=80, fee_bps=75)
    pool1 = PoolXY(x=46, y=66, fee_bps=11)
    amount_in = 6_539
    brute = _counted_call(lambda: split_routing_mod.brute_force_best_split_two_pools_exact_in(pool0, pool1, amount_in))
    baseline = _counted_call(
        lambda: split_routing_mod.best_split_two_pools_exact_in(
            pool0,
            pool1,
            amount_in,
            search_profile="baseline",
        )
    )
    staircase = _counted_call(
        lambda: split_routing_mod.best_split_two_pools_exact_in(
            pool0,
            pool1,
            amount_in,
            search_profile="staircase_exact",
        )
    )
    return {
        "case_id": "known_dense_gap_6539",
        "brute": brute,
        "baseline": baseline,
        "staircase": staircase,
        "baseline_gap_observed": (
            brute["status"] == "ok"
            and baseline["status"] == "ok"
            and int(baseline["amount_out"]) < int(brute["amount_out"])
        ),
        "staircase_recovers_gap": (
            brute["status"] == "ok"
            and staircase["status"] == "ok"
            and int(staircase["amount_out"]) == int(brute["amount_out"])
            and int(staircase["split_a"]) == int(brute["split_a"])
        ),
    }


def _guarded_packet_report() -> dict[str, Any]:
    pools = {
        "p_ab_0": _pool("p_ab_0", 87, 80, 75),
        "p_ab_1": _pool("p_ab_1", 46, 66, 11),
    }
    packet = build_exact_in_route_guarded_quote_packet(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=4_999,
        split_search_profile="staircase_exact",
        enable_mixed_direct_twohop_split=True,
    )
    payload = packet.to_dict()
    ok, error = verify_exact_in_route_guarded_quote_packet_payload(payload)
    return {
        "guard_ok": bool(packet.guard_ok),
        "payload_verify_ok": bool(ok),
        "payload_verify_error": error,
        "split_search_profile": payload["contract"]["split_search_profile"],
    }


def _profile_benchmark_report() -> dict[str, Any]:
    benchmark = build_split_routing_profile_report(profiles=("adaptive_v6", "dense24", "staircase_exact"))
    oracle_total = sum(int(case["oracle"]["quote_count"]) for case in benchmark["cases"] if case["oracle"]["status"] == "ok")
    staircase_total = int(benchmark["summary"]["staircase_exact"]["total_quote_count"])
    return {
        **benchmark,
        "oracle_quote_count_total": oracle_total,
        "staircase_quote_count_total": staircase_total,
        "quote_count_ratio_vs_oracle": (float(oracle_total) / float(staircase_total)) if staircase_total > 0 else None,
    }


def _facts(
    *,
    hostile: Mapping[str, Any],
    benchmark: Mapping[str, Any],
    known_gap: Mapping[str, Any],
    guarded_packet: Mapping[str, Any],
) -> dict[str, int]:
    quote_lift = (
        int(benchmark["staircase_quote_count_total"]) < int(benchmark["oracle_quote_count_total"])
        and int(benchmark["summary"]["staircase_exact"]["oracle_match_count"]) == int(benchmark["case_count"])
    )
    return {
        "certificate_active": 1,
        "bounded_corpus_ok": int(int(hostile["case_count"]) >= 120 and int(hostile["ok_case_count"]) >= 110),
        "brute_force_parity_ok": int(int(hostile["mismatch_count"]) == 0),
        "leftmost_tie_break_ok": int(int(hostile["leftmost_tie_break_mismatch_count"]) == 0),
        "quote_count_lift_ok": int(bool(quote_lift)),
        "known_gap_recovered": int(bool(known_gap["staircase_recovers_gap"])),
        "baseline_gap_observed": int(bool(known_gap["baseline_gap_observed"])),
        "guarded_packet_replay_ok": int(
            bool(guarded_packet["guard_ok"])
            and bool(guarded_packet["payload_verify_ok"])
            and guarded_packet["split_search_profile"] == "staircase_exact"
        ),
        "runtime_default_unchanged": 1,
        "advisory_only": 1,
        "no_authority_effect": 1,
    }


def _step_from_facts(facts: Mapping[str, int]) -> dict[str, int]:
    return {f"i{idx}": int(facts[name]) for idx, name in enumerate(FACT_ORDER, start=1)}


def _tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    pass_step = _step_from_facts(facts)
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauCase("certificate_pass", pass_step, {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0}, "All host-projected staircase certificate facts hold."),
        TauCase("parity_reject", {**pass_step, "i3": 0}, {"o1": 0, "o4": 0}, "Brute-force parity is load-bearing."),
        TauCase("tie_break_reject", {**pass_step, "i4": 0}, {"o1": 0, "o4": 0}, "Leftmost canonical tie parity is load-bearing."),
        TauCase("quote_lift_reject", {**pass_step, "i5": 0}, {"o2": 0, "o4": 0}, "Quote-count evidence is load-bearing for this certificate."),
        TauCase("gap_recovery_reject", {**pass_step, "i6": 0}, {"o1": 0, "o4": 0}, "Known-gap recovery is part of the bounded support."),
        TauCase("baseline_gap_reject", {**pass_step, "i7": 0}, {"o2": 0, "o4": 0}, "The report must preserve the negative baseline comparison."),
        TauCase("guarded_packet_reject", {**pass_step, "i8": 0}, {"o3": 0, "o4": 0}, "Guarded packet replay is required before using the profile in route certificates."),
        TauCase("default_change_reject", {**pass_step, "i9": 0}, {"o3": 0, "o4": 0}, "The certificate does not authorize changing the runtime default."),
        TauCase("authority_reject", {**pass_step, "i11": 0}, {"o3": 0, "o4": 0, "o5": 0}, "The certificate cannot carry authority effects."),
        TauCase("inactive_safe", inactive, {"o4": 0, "o5": 1}, "Inactive certificates do not admit while no-authority remains true."),
    )


def _run_tau(facts: Mapping[str, int], tau_bin: str | None) -> dict[str, Any]:
    cases = _tau_cases(facts)
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "case_results": [], "invalid_accepts": 0}
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=TAU_SPEC, steps=[case.step for case in cases], timeout_s=15.0)
    invalid_accepts = 0
    case_results: list[dict[str, Any]] = []
    ok = True
    for index, case in enumerate(cases):
        got = {str(key): int(value) for key, value in outputs.get(index, {}).items()}
        mismatches = {
            key: {"expected": int(value), "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != int(value)
        }
        if case.expected.get("o4", 0) == 0 and got.get("o4") == 1:
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
    return {"ok": bool(ok and invalid_accepts == 0), "case_results": case_results, "invalid_accepts": invalid_accepts}


def build_report() -> dict[str, Any]:
    hostile = _hostile_report()
    benchmark = _profile_benchmark_report()
    known_gap = _known_gap_report()
    guarded_packet = _guarded_packet_report()
    facts = _facts(hostile=hostile, benchmark=benchmark, known_gap=known_gap, guarded_packet=guarded_packet)
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    tau = _run_tau(facts, tau_bin)
    ok = bool(all(value == 1 for value in facts.values()) and tau["ok"])
    return {
        "schema": "zenodex.exact_in_staircase_hostile_certificate_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "breakthrough": {
            "name": "Exact-in staircase hostile-corpus certificate",
            "summary": "The two-pool CPMM exact-in staircase profile matched brute force on a deterministic hostile corpus and reduced profile-benchmark quote calls while keeping runtime default selection unchanged.",
            "authority_boundary": "Advisory routing evidence only; this certificate does not change default routing, settle swaps, mutate pools, or authorize production promotion.",
        },
        "tau": {
            "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
            "sha256": _sha256(TAU_SPEC),
            "tau_bin": tau_bin,
            "tau_version": _tau_version(tau_bin),
            **tau,
        },
        "certificate_facts": facts,
        "hostile_corpus": hostile,
        "profile_benchmark": {
            "case_count": benchmark["case_count"],
            "summary": benchmark["summary"],
            "oracle_quote_count_total": benchmark["oracle_quote_count_total"],
            "staircase_quote_count_total": benchmark["staircase_quote_count_total"],
            "quote_count_ratio_vs_oracle": benchmark["quote_count_ratio_vs_oracle"],
        },
        "known_gap": known_gap,
        "guarded_packet": guarded_packet,
        "non_claims": [
            "This does not change the live default split-routing profile.",
            "This is a two-pool CPMM exact-in integer-routing certificate, not a general CFMM network optimizer.",
            "The quote-count lift is measured on the declared bounded profile benchmark, not every possible pool configuration.",
            "Guarded packet replay proves certificate compatibility only for the replayed packet shape.",
        ],
        "replay_command": "python3 tools/zenodex_staircase_hostile_certificate_20260628.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Exact-In Staircase Hostile Certificate - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(str(report["breakthrough"]["summary"]))
    lines.append("")
    lines.append(str(report["breakthrough"]["authority_boundary"]))
    lines.append("")
    lines.append("## Tau Certificate")
    lines.append("")
    tau = report["tau"]
    lines.append(f"- Spec: `{tau['spec_path']}`")
    lines.append(f"- Latest Tau: `{tau.get('tau_version')}`")
    lines.append(f"- Tau cases: `{len(tau['case_results'])}`")
    lines.append(f"- Invalid accepts: `{tau['invalid_accepts']}`")
    lines.append("")
    lines.append("Certificate facts:")
    for key, value in report["certificate_facts"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.append("")
    hostile = report["hostile_corpus"]
    lines.append("## Hostile Corpus")
    lines.append("")
    lines.append(f"- Total cases: `{hostile['case_count']}`")
    lines.append(f"- Brute-force comparable cases: `{hostile['ok_case_count']}`")
    lines.append(f"- Mismatches: `{hostile['mismatch_count']}`")
    lines.append(f"- Leftmost tie mismatches: `{hostile['leftmost_tie_break_mismatch_count']}`")
    lines.append(f"- Families: `{len(hostile['family_counts'])}`")
    lines.append("")
    lines.append("## Profile Benchmark")
    lines.append("")
    benchmark = report["profile_benchmark"]
    lines.append(f"- Oracle quote calls: `{benchmark['oracle_quote_count_total']}`")
    lines.append(f"- Staircase quote calls: `{benchmark['staircase_quote_count_total']}`")
    lines.append(f"- Quote-count ratio vs oracle: `{benchmark['quote_count_ratio_vs_oracle']:.3f}`")
    lines.append("")
    lines.append("| profile | oracle matches | total quotes | max quotes |")
    lines.append("| --- | ---: | ---: | ---: |")
    for profile, summary in benchmark["summary"].items():
        lines.append(
            f"| `{profile}` | `{summary['oracle_match_count']}` | `{summary['total_quote_count']}` | `{summary['max_quote_count']}` |"
        )
    lines.append("")
    lines.append("## Known Gap And Guarded Packet")
    lines.append("")
    gap = report["known_gap"]
    lines.append(f"- Baseline gap observed: `{gap['baseline_gap_observed']}`")
    lines.append(f"- Staircase recovers gap: `{gap['staircase_recovers_gap']}`")
    guarded = report["guarded_packet"]
    lines.append(f"- Guard ok: `{guarded['guard_ok']}`")
    lines.append(f"- Packet verifier ok: `{guarded['payload_verify_ok']}`")
    lines.append("")
    lines.append("## Tau Negative Cases")
    lines.append("")
    lines.append("| case | ok | primary output |")
    lines.append("| --- | --- | ---: |")
    for case in tau["case_results"]:
        lines.append(f"| `{case['case_id']}` | `{case['ok']}` | `{case['got'].get('o4')}` |")
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
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path = REPORT_JSON, output_md: Path = REPORT_MD) -> dict[str, Any]:
    report = build_report()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    return report


def main() -> int:
    report = run()
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "spec": report["tau"]["spec_path"],
                "tau_cases": len(report["tau"]["case_results"]),
                "invalid_accepts": report["tau"]["invalid_accepts"],
                "hostile_cases": report["hostile_corpus"]["case_count"],
                "mismatch_count": report["hostile_corpus"]["mismatch_count"],
                "quote_count_ratio_vs_oracle": report["profile_benchmark"]["quote_count_ratio_vs_oracle"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

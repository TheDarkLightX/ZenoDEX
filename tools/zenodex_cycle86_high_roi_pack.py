#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
RUNS_ROOT = ROOT / "runs" / "manual_morph_supervised"


def _now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _safe_token(text: str, max_len: int = 120) -> str:
    out: list[str] = []
    for ch in str(text):
        if ch.isalnum() or ch in "._-":
            out.append(ch)
        else:
            out.append("_")
    tok = "".join(out).strip("._").lower()
    if not tok:
        tok = "x"
    return tok[:max_len]


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _discover_next_run_id() -> int:
    max_h = 0
    pat = re.compile(r"^h(\d+)_supervised_cycle\d+$")
    for p in RUNS_ROOT.glob("h*_supervised_cycle*"):
        if not p.is_dir():
            continue
        m = pat.match(p.name)
        if not m:
            continue
        max_h = max(max_h, int(m.group(1)))
    return max_h + 1


def _delta(domain: str, transform: str, claim: bool) -> list[int]:
    # [safety, capital_efficiency, execution_quality, performance_cost, determinism_simplicity]
    if transform == "relax":
        return [1, -1, -1, -1, -1]
    if domain == "security":
        return [3, 0, 2, 0, 1] if claim else [2, 0, 1, -1, 1]
    if domain == "automation":
        return [2, 0, 1, -1, 2] if claim else [1, 0, 1, -1, 1]
    if domain == "execution":
        return [1, 1, 3, 1, 2] if claim else [1, 0, 2, 0, 1]
    if domain == "performance":
        return [1, 1, 2, 2, 2] if claim else [1, 1, 1, 1, 1]
    return [1, 1, 2, 1, 2] if claim else [1, 1, 1, 0, 1]


def _mk(
    *,
    cycle: int,
    idx: int,
    sketch_id: str,
    sketch_name: str,
    domain: str,
    check: str,
    claim_type: str,
    mechanism: str,
    timeout_s: int,
) -> dict[str, Any]:
    is_counter = claim_type == "counterclaim"
    if is_counter:
        transform = "relax"
    elif domain in {"security", "automation"}:
        transform = "restrict"
    elif domain == "performance":
        transform = "reduce"
    else:
        transform = "equiv"
    hid = f"H_cycle{cycle}_{_safe_token(sketch_id)}_{idx:03d}_{_safe_token(check, 84)}_v1"
    null = f"{sketch_name} does not hold under `{check}`."
    if is_counter:
        null = f"{sketch_name} remains safe/stable and counterclaim `{check}` is false."
    return {
        "hypothesis_id": hid,
        "mechanism_change": mechanism,
        "representation_shift_used": transform,
        "expected_metric_delta": _delta(domain=domain, transform=transform, claim=(not is_counter)),
        "null_hypothesis": null,
        "falsification_recipe": check,
        "support_recipe": check,
        "formal_obligations": [
            f"`{check}` resolves deterministically",
            "UNKNOWN/TIMEOUT/ERROR remains inconclusive",
            "Promotion requires replayable evidence artifact",
        ],
        "risk_modes": [
            "Bounded checks can miss out-of-distribution edge cases",
            "Solver/test harness posture can influence outcomes",
        ],
        "status": "proposed",
        "timeout_s": int(timeout_s),
        "category": domain,
        "source": "cycle86_high_roi_pack",
        "sketch_id": sketch_id,
        "sketch_name": sketch_name,
        "claim_type": claim_type,
    }


def _ig(row: dict[str, Any]) -> float:
    check = str(row["falsification_recipe"])
    domain = str(row.get("category", ""))
    transform = str(row.get("representation_shift_used", ""))
    timeout_s = int(row.get("timeout_s", 180) or 180)
    claim_type = str(row.get("claim_type", "claim"))

    base = 2.4
    if check.startswith("exact_out_gate_tradeoff::"):
        base = 4.8
    elif check.startswith("split_routing_tradeoff::"):
        base = 4.4
    elif check.startswith("exact_out_split_tradeoff::"):
        base = 4.2
    elif check.startswith("perp_oracle_lp_attack_"):
        base = 4.6
    elif check.startswith("esso_verify_solver_timeout::cvc5,z3::"):
        base = 4.0
    elif check.startswith("esso_repeat2_solver::cvc5,z3::"):
        base = 3.8
    elif check.startswith("lean_repeat3::"):
        base = 3.4
    elif check.startswith("lean_pass::"):
        base = 3.1
    elif check.startswith("pytest_repeat3::"):
        base = 3.2
    elif check.startswith("pytest_pass::"):
        base = 2.9
    elif check.startswith("pytest_fail::"):
        base = 2.8
    elif check in {
        "route_exact_out_2hop_value",
        "route_exact_out_no_2hop_value",
        "split_routing_gap",
        "split_routing_no_gap",
        "perp_lp_fee_share_guard",
        "perp_lp_fee_share_irrelevant",
        "twap_staleness_effect",
    }:
        base = 3.7

    if domain == "security":
        base += 0.2
    if domain == "execution":
        base += 0.2
    if claim_type == "counterclaim":
        base += 0.15
    if transform == "restrict":
        base += 0.1
    if timeout_s >= 330:
        base -= 0.2
    if timeout_s <= 120:
        base += 0.1
    return round(base, 3)


def _ideation_iterations() -> list[dict[str, Any]]:
    notes = [
        ("A1", "Gate-vs-quality frontier extraction", "exact_out gate policies show exploitable capture/call tradeoff"),
        ("A2", "Comparative-topology manifold fit", "tripiece parameters span quality/latency frontier"),
        ("A3", "Counterclaim stress-test lane", "strict thresholds fail near frontier boundaries"),
        ("A4", "Split-router efficiency lens", "adaptive_v2/v3 dominate baseline on match but cost more calls"),
        ("A5", "Split-router latency lens", "baseline_w64 keeps low call budget with quality sacrifice"),
        ("A6", "Exact-out split dispatch lens", "default/w64 already near-optimal on tested ranges"),
        ("A7", "Overfitting risk control", "train/holdout delta required before promotion"),
        ("A8", "Boundary falsifier mining", "threshold-near checks maximize information gain"),
        ("A9", "Oracle-manipulation floor map", "pfs=10000 absence and pfs=9999 presence are stable anchors"),
        ("A10", "MEV guard dual branch", "profit-exists/profit-absent claim pairs expose true regime"),
        ("A11", "Deterministic automation anchors", "state-root and intent normal form remain high-ROI gates"),
        ("A12", "Execution envelope composition", "route-aware worst-case bounds improve submit guarantees"),
        ("A13", "Proof-carrying priority", "Lean replay remains heavy but promotion-critical"),
        ("A14", "Dual-solver posture check", "ESSO dual verification separates semantic from posture failures"),
        ("A15", "Representation-shift scoring", "restrict+reduce dominate relax for promoted lanes"),
        ("A16", "Queue entropy management", "mix dynamic checks with fast regression anchors"),
        ("A17", "Intractability early warning", "high-cost inconclusive checks must be decomposed"),
        ("A18", "Pareto synthesis", "retain non-dominated quality, latency, and security points"),
        ("A19", "Cycle86 sketch consolidation", "five sketches chosen for highest cross-domain ROI"),
        ("A20", "Runnable tranche extraction", "top-20 queue selected for immediate falsify-first execution"),
    ]
    out: list[dict[str, Any]] = []
    for i, (atom, move, insight) in enumerate(notes, 1):
        out.append(
            {
                "iteration": i,
                "atom_id": atom,
                "move": move,
                "insight": insight,
                "transform": "reduce" if i % 3 else "restrict",
            }
        )
    return out


def _build_rows(cycle: int) -> list[dict[str, Any]]:
    specs: list[dict[str, Any]] = [
        {
            "id": "ALG86-EXEC-GATE-MANIFOLD",
            "name": "Comparative Topology Gate Manifold",
            "domain": "execution",
            "checks": [
                ("claim", "exact_out_gate_tradeoff::stress_or_pressure::seed=20260221,n=3000,stress_bp=4000,pressure_bp=16000,capture_bp=9600,avg_calls_milli=2000", 180),
                ("claim", "exact_out_gate_tradeoff::stress_or_pressure_tripiece::seed=20260221,n=3000,stress_bp=4000,pressure_bp=16000,capture_bp=9750,avg_calls_milli=1950", 180),
                ("claim", "exact_out_gate_tradeoff::stress_or_pressure_piecewise_fee::seed=20260221,n=3000,stress_bp=4000,pressure_bp=16000,capture_bp=9750,avg_calls_milli=1950", 180),
                ("counterclaim", "exact_out_gate_tradeoff::stress_or_pressure_tripiece::seed=20260221,n=3000,stress_bp=4532,pressure_bp=12353,capture_bp=9750,avg_calls_milli=1900", 180),
                ("counterclaim", "exact_out_gate_tradeoff::stress_or_pressure_tripiece::seed=20260221,n=3000,stress_bp=5000,pressure_bp=19000,capture_bp=9650,avg_calls_milli=1750", 180),
                ("claim", "route_exact_out_2hop_value", 120),
                ("counterclaim", "route_exact_out_no_2hop_value", 120),
                ("claim", "pytest_pass::tests/core/test_routing_exact_out_gate.py", 180),
                ("counterclaim", "pytest_fail::tests/core/test_routing_exact_out_gate.py", 180),
                ("claim", "pytest_repeat3::tests/core/test_routing_exact_out_gate.py", 240),
                ("claim", "lean_pass::lean-mathlib/Proofs/SplitRoutingArgmaxPlateau.lean", 300),
                ("claim", "lean_repeat3::lean-mathlib/Proofs/SplitRoutingArgmaxPlateau.lean", 360),
                ("claim", "esso_verify_solver_timeout::cvc5,z3::9000::src/kernels/dex/swap_router_optimizer.yaml", 360),
                ("counterclaim", "esso_fail_solver_timeout::cvc5,z3::9000::src/kernels/dex/swap_router_optimizer.yaml", 360),
                ("claim", "esso_repeat2_solver::cvc5,z3::src/kernels/dex/swap_router_optimizer.yaml", 380),
                ("claim", "split_routing_tradeoff::adaptive_v2::seed=20260221,n=80,match_bp=9800,avg_calls_max=11000", 180),
                ("claim", "split_routing_tradeoff::adaptive_v3::seed=20260221,n=80,match_bp=9800,avg_calls_max=11000", 180),
                ("claim", "split_routing_tradeoff::dense32_w64::seed=20260221,n=80,match_bp=9990,avg_calls_max=11500", 180),
                ("claim", "split_routing_tradeoff::dense24_w64::seed=20260221,n=80,match_bp=9700,avg_calls_max=10250", 180),
                ("counterclaim", "split_routing_tradeoff::baseline_w64::seed=20260221,n=80,match_bp=9000,avg_calls_max=3000", 180),
            ],
        },
        {
            "id": "ALG86-EXEC-EXACTOUT-SPLIT",
            "name": "Exact-Out Split Dispatch Frontier",
            "domain": "performance",
            "checks": [
                ("claim", "exact_out_split_tradeoff::default::seed=20260221,n=80,match_bp=9990,avg_calls_max=1900,out_min=700,out_max=2000,bf_max=512,worst_calls_max=2600", 180),
                ("claim", "exact_out_split_tradeoff::w64::seed=20260221,n=80,match_bp=9990,avg_calls_max=1900,out_min=700,out_max=2000,bf_max=512,worst_calls_max=2600", 180),
                ("claim", "exact_out_split_tradeoff::w96::seed=20260221,n=80,match_bp=9990,avg_calls_max=2400,out_min=700,out_max=2000,bf_max=512,worst_calls_max=3600", 180),
                ("claim", "exact_out_split_tradeoff::w128::seed=20260221,n=80,match_bp=9990,avg_calls_max=2800,out_min=700,out_max=2000,bf_max=512,worst_calls_max=5000", 180),
                ("counterclaim", "exact_out_split_tradeoff::default::seed=20260221,n=80,match_bp=9990,avg_calls_max=1700,out_min=700,out_max=2000,bf_max=512,worst_calls_max=2200", 180),
                ("counterclaim", "exact_out_split_tradeoff::w128::seed=20260221,n=80,match_bp=9990,avg_calls_max=2400,out_min=700,out_max=2000,bf_max=512,worst_calls_max=3600", 180),
                ("claim", "route_exact_out_2hop_value", 120),
                ("counterclaim", "route_exact_out_no_2hop_value", 120),
                ("claim", "pytest_pass::tests/core/test_routing_exact_out.py", 180),
                ("counterclaim", "pytest_fail::tests/core/test_routing_exact_out.py", 180),
                ("claim", "pytest_repeat3::tests/core/test_routing_exact_out.py", 240),
                ("claim", "split_routing_gap", 120),
                ("counterclaim", "split_routing_no_gap", 120),
                ("claim", "settlement_normal_form", 120),
                ("counterclaim", "settlement_ordering_nondeterminism_exists", 120),
                ("claim", "esso_verify_solver_timeout::cvc5,z3::9000::src/kernels/dex/swap_router_optimizer_evolvable_v1.yaml", 360),
                ("counterclaim", "esso_fail_solver_timeout::cvc5,z3::9000::src/kernels/dex/swap_router_optimizer_evolvable_v1.yaml", 360),
                ("claim", "esso_repeat2_solver::cvc5,z3::src/kernels/dex/swap_router_optimizer_evolvable_v1.yaml", 380),
                ("claim", "lean_pass::lean-mathlib/Proofs/CPMMSettlement.lean", 300),
                ("claim", "lean_repeat3::lean-mathlib/Proofs/CPMMSettlement.lean", 360),
            ],
        },
        {
            "id": "ALG86-SEC-ORACLE-MEV",
            "name": "Perp Oracle Boundary and MEV Regime Guard",
            "domain": "security",
            "checks": [
                ("claim", "perp_oracle_lp_attack_absent::rb=10000,rq=10000,fee_bps=10,pfs=10000,lp_share_bps=10000,max_r=10000,max_pos_abs=50,max_move_bps=500,target_profit_quote=1,pfr=0", 240),
                ("claim", "perp_oracle_lp_attack_exists::rb=10000,rq=10000,fee_bps=10,pfs=9999,lp_share_bps=10000,max_r=10000,max_pos_abs=50,max_move_bps=500,target_profit_quote=1,pfr=0", 240),
                ("claim", "perp_oracle_lp_attack_absent::rb=10000,rq=10000,fee_bps=30,pfs=10000,lp_share_bps=10000,max_r=10000,max_pos_abs=50,max_move_bps=500,target_profit_quote=1,pfr=0", 240),
                ("claim", "perp_oracle_lp_attack_exists::rb=10000,rq=10000,fee_bps=30,pfs=9999,lp_share_bps=10000,max_r=10000,max_pos_abs=50,max_move_bps=500,target_profit_quote=1,pfr=0", 240),
                ("claim", "perp_oracle_lp_attack_absent::rb=10000,rq=10000,fee_bps=10,pfs=10000,lp_share_bps=10000,max_r=10000,max_pos_abs=50,max_move_bps=100,target_profit_quote=1,pfr=0", 240),
                ("claim", "perp_oracle_lp_attack_exists::rb=10000,rq=10000,fee_bps=10,pfs=0,lp_share_bps=10000,max_r=10000,max_pos_abs=50,max_move_bps=500,target_profit_quote=2,pfr=1", 240),
                ("claim", "perp_oracle_lp_attack_absent::rb=10000,rq=10000,fee_bps=10,pfs=1000,lp_share_bps=10000,max_r=10000,max_pos_abs=50,max_move_bps=500,target_profit_quote=2,pfr=1", 240),
                ("claim", "roundtrip_positive_profit_exists", 120),
                ("counterclaim", "roundtrip_no_positive_profit", 120),
                ("claim", "perp_lp_fee_share_guard", 120),
                ("counterclaim", "perp_lp_fee_share_irrelevant", 120),
                ("claim", "twap_staleness_effect", 120),
                ("claim", "il_insurance_vuln_presence", 120),
                ("counterclaim", "il_insurance_status_quo_safe", 120),
                ("claim", "pytest_pass::tests/core/test_perp_incentive_hazards.py", 180),
                ("counterclaim", "pytest_fail::tests/core/test_perp_incentive_hazards.py", 180),
                ("claim", "pytest_repeat3::tests/core/test_perp_incentive_hazards.py", 240),
                ("claim", "esso_verify_solver_timeout::cvc5,z3::9000::src/kernels/dex/perp_game_theory_v1_fundingfix.yaml", 360),
                ("counterclaim", "esso_fail_solver_timeout::cvc5,z3::9000::src/kernels/dex/perp_game_theory_v1_fundingfix.yaml", 360),
                ("claim", "lean_pass::lean-mathlib/Proofs/PerpGameTheory.lean", 300),
            ],
        },
        {
            "id": "ALG86-AUTO-DETERMINISM",
            "name": "Deterministic Intent Compiler and Receipt Canonicalizer",
            "domain": "automation",
            "checks": [
                ("claim", "state_root_determinism", 120),
                ("counterclaim", "state_root_nondeterminism_exists", 120),
                ("claim", "intent_normal_form_tests", 120),
                ("counterclaim", "intent_normal_form_regression_exists", 120),
                ("claim", "settlement_normal_form", 120),
                ("counterclaim", "settlement_ordering_nondeterminism_exists", 120),
                ("claim", "pytest_pass::tests/integration/test_tau_runner_fake_tau.py", 180),
                ("counterclaim", "pytest_fail::tests/integration/test_tau_runner_fake_tau.py", 180),
                ("claim", "pytest_repeat3::tests/integration/test_tau_runner_fake_tau.py", 240),
                ("claim", "pytest_pass::tests/integration/test_tau_runner_utils.py", 180),
                ("counterclaim", "pytest_fail::tests/integration/test_tau_runner_utils.py", 180),
                ("claim", "pytest_pass::tests/integration/test_tau_gate.py", 180),
                ("counterclaim", "pytest_fail::tests/integration/test_tau_gate.py", 180),
                ("claim", "pytest_repeat3::tests/integration/test_tau_gate.py", 240),
                ("claim", "pytest_pass::tests/state/test_state_root_determinism.py", 180),
                ("counterclaim", "pytest_fail::tests/state/test_state_root_determinism.py", 180),
                ("claim", "esso_verify_solver_timeout::cvc5,z3::9000::src/kernels/dex/spec_quality_assessment_v1.yaml", 360),
                ("counterclaim", "esso_fail_solver_timeout::cvc5,z3::9000::src/kernels/dex/spec_quality_assessment_v1.yaml", 360),
                ("claim", "lean_pass::lean-mathlib/Proofs/DeterministicAgentTieBreakSort.lean", 300),
                ("claim", "lean_repeat3::lean-mathlib/Proofs/DeterministicAgentTieBreakSort.lean", 360),
            ],
        },
        {
            "id": "ALG86-EXEC-ENVELOPE",
            "name": "Price-Impact Envelope and Overdelivery Safety Frontier",
            "domain": "execution",
            "checks": [
                ("claim", "pytest_pass::tests/core/test_price_impact_preview.py", 180),
                ("counterclaim", "pytest_fail::tests/core/test_price_impact_preview.py", 180),
                ("claim", "pytest_repeat3::tests/core/test_price_impact_preview.py", 240),
                ("claim", "pytest_pass::tests/integration/test_api_server_dex_api.py", 180),
                ("counterclaim", "pytest_fail::tests/integration/test_api_server_dex_api.py", 180),
                ("claim", "pytest_repeat3::tests/integration/test_api_server_dex_api.py", 240),
                ("claim", "cpmm_no_overdelivery_guarded", 120),
                ("counterclaim", "cpmm_overdelivery_witness", 120),
                ("claim", "cpmm_ref_parity", 120),
                ("counterclaim", "cpmm_ref_parity_broken", 120),
                ("claim", "dex_v8_ref_parity", 120),
                ("counterclaim", "dex_v8_ref_parity_broken", 120),
                ("claim", "split_routing_regression", 120),
                ("counterclaim", "split_routing_regression_exists", 120),
                ("claim", "batch_clearing_gap_exists", 120),
                ("counterclaim", "batch_clearing_no_gap", 120),
                ("claim", "esso_verify_solver_timeout::cvc5,z3::9000::src/kernels/dex/cpmm_swap_v8.yaml", 360),
                ("counterclaim", "esso_fail_solver_timeout::cvc5,z3::9000::src/kernels/dex/cpmm_swap_v8.yaml", 360),
                ("claim", "lean_pass::lean-mathlib/Proofs/BatchAuctionCanonical.lean", 300),
                ("claim", "lean_repeat3::lean-mathlib/Proofs/BatchAuctionCanonical.lean", 360),
            ],
        },
    ]

    rows: list[dict[str, Any]] = []
    idx = 1
    for spec in specs:
        sid = str(spec["id"])
        sname = str(spec["name"])
        domain = str(spec["domain"])
        checks = list(spec["checks"])
        if len(checks) != 20:
            raise RuntimeError(f"{sid}: expected 20 checks, got {len(checks)}")
        for claim_type, check, timeout_s in checks:
            mechanism = (
                f"{sname}: evaluate `{check}` under supervised falsification-first gate "
                f"(claim_type={claim_type}) with replayable evidence."
            )
            rows.append(
                _mk(
                    cycle=cycle,
                    idx=idx,
                    sketch_id=sid,
                    sketch_name=sname,
                    domain=domain,
                    check=str(check),
                    claim_type=str(claim_type),
                    mechanism=mechanism,
                    timeout_s=int(timeout_s),
                )
            )
            idx += 1
    if len(rows) != 100:
        raise RuntimeError(f"expected 100 hypotheses, got {len(rows)}")
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description="Build cycle86 high-ROI algorithm hypothesis pack (100).")
    ap.add_argument("--cycle", type=int, default=86)
    ap.add_argument("--run-name", type=str, default="")
    ap.add_argument("--top-k", type=int, default=20)
    args = ap.parse_args()

    cycle = int(args.cycle)
    if args.run_name:
        run_name = str(args.run_name)
    else:
        run_name = f"h{_discover_next_run_id():03d}_supervised_cycle{cycle}"
    out_dir = RUNS_ROOT / run_name
    out_dir.mkdir(parents=True, exist_ok=True)

    iterations = _ideation_iterations()
    rows = _build_rows(cycle)

    queue = [
        {
            "hypothesis_id": r["hypothesis_id"],
            "check": r["falsification_recipe"],
            "status": "proposed",
            "transform": r["representation_shift_used"],
            "category": r["category"],
            "duration_s": int(r["timeout_s"]),
            "expected_information_gain": _ig(r),
            "sketch_id": r["sketch_id"],
            "claim_type": r["claim_type"],
        }
        for r in rows
    ]
    queue.sort(
        key=lambda x: (
            -float(x["expected_information_gain"]),
            str(x["sketch_id"]),
            str(x["claim_type"]),
            str(x["check"]),
        )
    )

    top_k = max(1, min(int(args.top_k), len(queue)))
    by_id = {str(r["hypothesis_id"]): r for r in rows}
    top_rows = [by_id[str(q["hypothesis_id"])] for q in queue[:top_k]]

    _write_json(
        out_dir / "ideation_iterations_cycle86.json",
        {
            "schema": "zenodex/cycle86-ideation/v1",
            "generated_at": _now_iso(),
            "cycle": cycle,
            "iterations": iterations,
        },
    )
    _write_json(out_dir / "hypothesis_pack_100_high_roi.json", {"count": len(rows), "hypotheses": rows})
    _write_json(out_dir / "next_experiment_queue_high_roi.json", {"count": len(queue), "queue": queue})
    _write_json(out_dir / "hypothesis_pack_top20_high_roi.json", {"count": len(top_rows), "hypotheses": top_rows})
    _write_json(
        out_dir / "cycle86_high_roi_manifest.json",
        {
            "schema": "zenodex/cycle86-high-roi-manifest/v1",
            "generated_at": _now_iso(),
            "cycle": cycle,
            "run_name": run_name,
            "artifacts": {
                "ideation": str(out_dir / "ideation_iterations_cycle86.json"),
                "pack_100": str(out_dir / "hypothesis_pack_100_high_roi.json"),
                "queue": str(out_dir / "next_experiment_queue_high_roi.json"),
                "top20": str(out_dir / "hypothesis_pack_top20_high_roi.json"),
            },
            "sketches": [
                "ALG86-EXEC-GATE-MANIFOLD",
                "ALG86-EXEC-EXACTOUT-SPLIT",
                "ALG86-SEC-ORACLE-MEV",
                "ALG86-AUTO-DETERMINISM",
                "ALG86-EXEC-ENVELOPE",
            ],
        },
    )

    print(
        json.dumps(
            {
                "ok": True,
                "cycle": cycle,
                "run_name": run_name,
                "out_dir": str(out_dir),
                "count": len(rows),
                "top_k": top_k,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


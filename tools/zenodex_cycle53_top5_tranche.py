#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = ROOT / "runs" / "manual_morph_supervised" / "h067_supervised_cycle53"


def _now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _safe_token(text: str, max_len: int = 84) -> str:
    out: list[str] = []
    for ch in str(text):
        if ch.isalnum() or ch in "._-":
            out.append(ch)
        else:
            out.append("_")
    token = "".join(out).strip("._").lower()
    if not token:
        token = "x"
    return token[:max_len]


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _delta(*, domain: str, transform: str, claim: bool) -> list[int]:
    # [safety, capital_efficiency, execution_quality, performance_cost, determinism_simplicity]
    if transform == "relax":
        return [1, -1, -1, -1, -1]
    if domain == "ux":
        return [1, 2, 3, 1, 1] if claim else [1, 1, 2, 0, 0]
    if domain == "security":
        return [3, 0, 2, 0, 1] if claim else [2, 0, 1, -1, 1]
    return [2, 0, 1, 1, 3] if claim else [2, 0, 1, 0, 2]


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
    else:
        transform = "reduce" if domain == "ux" else ("restrict" if domain == "security" else "equiv")
    hid = f"H_cycle{cycle}_{_safe_token(sketch_id)}_{idx:03d}_{_safe_token(check)}_v1"
    null = f"{sketch_name} does not hold under `{check}`."
    if is_counter:
        null = f"{sketch_name} remains safe/stable and counterclaim `{check}` is false."

    obligations = [
        f"`{check}` resolves deterministically",
        "UNKNOWN/TIMEOUT/ERROR remains inconclusive",
    ]
    if "repeat" in check:
        obligations.append("Repeated replay remains polarity-stable")
    if check.startswith("lean_"):
        obligations.append("No `sorry`/timeout accepted as proof")
    if check.startswith("esso_"):
        obligations.append("Kernel verification posture is replayable")

    risks = [
        "Bounded checks can miss out-of-distribution failures",
        "Model/test coverage may lag mechanism changes",
    ]
    if is_counter:
        risks.append("Counterclaim failures can be solver/environment sensitive")

    return {
        "hypothesis_id": hid,
        "mechanism_change": mechanism,
        "representation_shift_used": transform,
        "expected_metric_delta": _delta(domain=domain, transform=transform, claim=(not is_counter)),
        "null_hypothesis": null,
        "falsification_recipe": check,
        "support_recipe": check,
        "formal_obligations": obligations,
        "risk_modes": risks,
        "status": "proposed",
        "timeout_s": int(timeout_s),
        "category": domain,
        "source": "cycle53_top5_sketches_tranche",
        "sketch_id": sketch_id,
        "claim_type": claim_type,
    }


def _ig(row: dict[str, Any]) -> float:
    check = str(row["falsification_recipe"])
    domain = str(row.get("category", ""))
    transform = str(row.get("representation_shift_used", ""))
    prefix = check.split("::", 1)[0]

    base = 2.5
    if prefix.startswith("esso_verify_solver_timeout"):
        base = 4.3
    elif prefix.startswith("esso_fail_solver_timeout"):
        base = 4.2
    elif prefix.startswith("esso_repeat2_solver"):
        base = 3.8
    elif prefix.startswith("lean_repeat3"):
        base = 3.2
    elif prefix.startswith("lean_"):
        base = 2.9
    elif prefix.startswith("pytest_repeat3"):
        base = 3.0
    elif prefix.startswith("pytest_"):
        base = 2.7
    elif prefix in {
        "route_exact_out_2hop_value",
        "route_exact_out_no_2hop_value",
        "il_insurance_vuln_presence",
        "il_insurance_status_quo_safe",
        "twap_staleness_effect",
    }:
        base = 3.7
    elif prefix in {
        "settlement_normal_form",
        "batch_greedy_invariants",
        "state_root_determinism",
        "intent_normal_form_tests",
    }:
        base = 3.3
    elif prefix in {
        "settlement_ordering_nondeterminism_exists",
        "state_root_nondeterminism_exists",
        "intent_normal_form_regression_exists",
    }:
        base = 3.5

    if domain == "security":
        base += 0.2
    if domain == "automation":
        base += 0.15
    if transform == "relax":
        base += 0.15
    return round(base, 2)


def build_tranche(cycle: int) -> list[dict[str, Any]]:
    specs: list[dict[str, Any]] = [
        {
            "id": "ALG53-UX-BATCH",
            "name": "Canonical Surplus Gradient Batch Refiner",
            "domain": "ux",
            "checks": [
                ("claim", "batch_clearing_gap_exists", 200),
                ("counterclaim", "batch_clearing_no_gap", 200),
                ("claim", "batch_greedy_invariants", 200),
                ("counterclaim", "settlement_ordering_nondeterminism_exists", 200),
                ("claim", "pytest_pass::tests/core/test_batch_clearing_b_refinement.py", 240),
                ("counterclaim", "pytest_fail::tests/core/test_batch_clearing_b_refinement.py", 240),
                ("claim", "pytest_repeat3::tests/core/test_batch_clearing_b_refinement.py", 280),
                ("claim", "esso_verify_solver_timeout::cvc5,z3::9000::src/kernels/dex/batch_auction_settler_v1.yaml", 380),
                ("counterclaim", "esso_fail_solver_timeout::cvc5,z3::9000::src/kernels/dex/batch_auction_settler_v1.yaml", 380),
                ("claim", "esso_repeat2_solver::cvc5,z3::src/kernels/dex/batch_auction_settler_v1.yaml", 400),
                ("claim", "lean_pass::lean-mathlib/Proofs/BatchRefinementOrder.lean", 340),
                ("claim", "lean_repeat3::lean-mathlib/Proofs/BatchRefinementOrder.lean", 380),
            ],
        },
        {
            "id": "ALG53-SEC-OICSB",
            "name": "Oracle-Insurance Coupled Safety Barrier",
            "domain": "security",
            "checks": [
                ("claim", "twap_staleness_effect", 200),
                ("claim", "il_insurance_vuln_presence", 200),
                ("counterclaim", "il_insurance_status_quo_safe", 200),
                ("counterclaim", "perp_v2_oracle_divergence_exists", 200),
                ("claim", "pytest_pass::tests/core/test_perp_v2/test_oracle_equiv.py", 240),
                ("counterclaim", "pytest_fail::tests/core/test_perp_v2/test_oracle_equiv.py", 240),
                ("claim", "pytest_repeat3::tests/core/test_perp_v2/test_oracle_equiv.py", 280),
                ("claim", "esso_verify_solver_timeout::cvc5,z3::9000::src/kernels/dex/il_insurance_pool_v2.yaml", 380),
                ("counterclaim", "esso_fail_solver_timeout::cvc5,z3::9000::src/kernels/dex/il_insurance_pool_v2.yaml", 380),
                ("claim", "esso_repeat2_solver::cvc5,z3::src/kernels/dex/il_insurance_pool_v2.yaml", 400),
                ("claim", "lean_pass::lean-mathlib/Proofs/PerpInsuranceSafety.lean", 340),
                ("claim", "lean_repeat3::lean-mathlib/Proofs/PerpInsuranceSafety.lean", 380),
            ],
        },
        {
            "id": "ALG53-AUTO-DIRC",
            "name": "Deterministic Intent-to-Receipt Compiler",
            "domain": "automation",
            "checks": [
                ("claim", "state_root_determinism", 200),
                ("counterclaim", "state_root_nondeterminism_exists", 200),
                ("claim", "intent_normal_form_tests", 200),
                ("counterclaim", "intent_normal_form_regression_exists", 200),
                ("claim", "pytest_pass::tests/integration/test_replay_protection.py", 240),
                ("counterclaim", "pytest_fail::tests/integration/test_replay_protection.py", 240),
                ("claim", "pytest_repeat3::tests/integration/test_replay_protection.py", 280),
                ("claim", "esso_verify_solver_timeout::cvc5,z3::9000::src/kernels/dex/execution_receipts_v1.yaml", 380),
                ("counterclaim", "esso_fail_solver_timeout::cvc5,z3::9000::src/kernels/dex/execution_receipts_v1.yaml", 380),
                ("claim", "esso_repeat2_solver::cvc5,z3::src/kernels/dex/execution_receipts_v1.yaml", 400),
                ("claim", "lean_pass::lean-mathlib/Proofs/DeterministicAgentTieBreakSort.lean", 340),
                ("claim", "lean_repeat3::lean-mathlib/Proofs/DeterministicAgentTieBreakSort.lean", 380),
            ],
        },
        {
            "id": "ALG53-UX-TOPO",
            "name": "Stress-Adaptive Comparative Topology Router",
            "domain": "ux",
            "checks": [
                ("claim", "route_exact_out_2hop_value", 200),
                ("counterclaim", "route_exact_out_no_2hop_value", 200),
                ("claim", "split_routing_gap", 200),
                ("counterclaim", "split_routing_no_gap", 200),
                ("claim", "pytest_pass::tests/core/test_routing_exact_out_gate.py", 240),
                ("counterclaim", "pytest_fail::tests/core/test_routing_exact_out_gate.py", 240),
                ("claim", "pytest_repeat3::tests/core/test_routing_exact_out_gate.py", 280),
                ("claim", "esso_verify_solver_timeout::cvc5,z3::9000::src/kernels/dex/swap_router_optimizer.yaml", 380),
                ("counterclaim", "esso_fail_solver_timeout::cvc5,z3::9000::src/kernels/dex/swap_router_optimizer.yaml", 380),
                ("claim", "esso_repeat2_solver::cvc5,z3::src/kernels/dex/swap_router_optimizer.yaml", 400),
                ("claim", "lean_pass::lean-mathlib/Proofs/SplitRoutingArgmaxPlateau.lean", 340),
                ("claim", "lean_repeat3::lean-mathlib/Proofs/SplitRoutingArgmaxPlateau.lean", 380),
            ],
        },
        {
            "id": "ALG53-SEC-RSMG",
            "name": "Regime-Switch MEV Guard for Perps",
            "domain": "security",
            "checks": [
                ("claim", "roundtrip_no_positive_profit", 200),
                ("counterclaim", "roundtrip_positive_profit_exists", 200),
                ("claim", "perp_lp_fee_share_guard", 200),
                ("counterclaim", "perp_lp_fee_share_irrelevant", 200),
                ("claim", "pytest_pass::tests/core/test_perp_incentive_hazards.py", 240),
                ("counterclaim", "pytest_fail::tests/core/test_perp_incentive_hazards.py", 240),
                ("claim", "pytest_repeat3::tests/core/test_perp_incentive_hazards.py", 280),
                ("claim", "esso_verify_solver_timeout::cvc5,z3::9000::src/kernels/dex/perp_game_theory_v1_fundingfix.yaml", 380),
                ("counterclaim", "esso_fail_solver_timeout::cvc5,z3::9000::src/kernels/dex/perp_game_theory_v1_fundingfix.yaml", 380),
                ("claim", "esso_repeat2_solver::cvc5,z3::src/kernels/dex/perp_game_theory_v1_fundingfix.yaml", 400),
                ("claim", "lean_pass::lean-mathlib/Proofs/PerpGameTheory.lean", 340),
                ("claim", "lean_repeat3::lean-mathlib/Proofs/PerpGameTheory.lean", 380),
            ],
        },
    ]

    rows: list[dict[str, Any]] = []
    idx = 1
    for spec in specs:
        sid = str(spec["id"])
        sname = str(spec["name"])
        domain = str(spec["domain"])
        for claim_type, check, timeout_s in spec["checks"]:
            mech = (
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
                    check=check,
                    claim_type=str(claim_type),
                    mechanism=mech,
                    timeout_s=int(timeout_s),
                )
            )
            idx += 1
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description="Build heavy supervised tranche from cycle53 top-5 algorithm sketches.")
    ap.add_argument("--cycle", type=int, default=53)
    ap.add_argument("--out-json", type=Path, default=OUT_DIR / "hypothesis_pack_heavy_top5_sketches.json")
    ap.add_argument("--out-queue", type=Path, default=OUT_DIR / "next_experiment_queue_top5_sketches.json")
    ap.add_argument("--out-manifest", type=Path, default=OUT_DIR / "tranche_manifest_top5_sketches.json")
    args = ap.parse_args()

    cycle = int(args.cycle)
    rows = build_tranche(cycle)
    if len(rows) != 60:
        raise RuntimeError(f"expected 60 hypotheses, got {len(rows)}")

    queue_rows: list[dict[str, Any]] = []
    for row in rows:
        queue_rows.append(
            {
                "hypothesis_id": row["hypothesis_id"],
                "check": row["falsification_recipe"],
                "status": "proposed",
                "transform": row["representation_shift_used"],
                "category": row["category"],
                "duration_s": int(row.get("timeout_s", 0)),
                "expected_information_gain": _ig(row),
                "sketch_id": row["sketch_id"],
                "claim_type": row["claim_type"],
            }
        )
    queue_rows.sort(
        key=lambda x: (
            -float(x["expected_information_gain"]),
            str(x["sketch_id"]),
            str(x["claim_type"]),
            str(x["check"]),
        )
    )

    manifest = {
        "schema": "zenodex/top5-sketches-tranche/v1",
        "created_at": _now_iso(),
        "cycle": cycle,
        "run_name": "h067_supervised_cycle53",
        "selection": {
            "total": len(rows),
            "sketches": 5,
            "per_sketch": 12,
        },
        "budgets": {
            "max_depth": 14,
            "max_width": 24,
            "per_epoch_compute_budget": 320,
            "exploration_ratio": 0.68,
            "exploitation_ratio": 0.32,
        },
        "sources": [
            "runs/manual_morph_supervised/h067_supervised_cycle53/high_roi_algorithm_sketches_cycle53.json",
            "runs/manual_morph_supervised/h067_supervised_cycle53/novel_algo_exploration_cycle53.json",
            "runs/manual_morph_supervised/h067_supervised_cycle53_zag_high_compute_eval/summary.json",
        ],
    }

    pack = {"count": len(rows), "hypotheses": rows}
    queue = {"created_at": int(time.time()), "cycle": "h067_supervised_cycle53_top5_sketches", "queue": queue_rows}

    out_json = args.out_json if args.out_json.is_absolute() else (ROOT / args.out_json)
    out_queue = args.out_queue if args.out_queue.is_absolute() else (ROOT / args.out_queue)
    out_manifest = args.out_manifest if args.out_manifest.is_absolute() else (ROOT / args.out_manifest)
    _write_json(out_json, pack)
    _write_json(out_queue, queue)
    _write_json(out_manifest, manifest)

    print(
        json.dumps(
            {
                "ok": True,
                "pack": str(out_json),
                "queue": str(out_queue),
                "manifest": str(out_manifest),
                "count": len(rows),
                "top_queue": queue_rows[:6],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

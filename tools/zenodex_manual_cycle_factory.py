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
VALID_TRANSFORMS = {"equiv", "reduce", "relax", "restrict", "heuristic"}


def _now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _read_json(path: Path, default: Any) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _safe_token(text: str, *, max_len: int = 120) -> str:
    chars = []
    for ch in str(text):
        if ch.isalnum() or ch in "_.-":
            chars.append(ch)
        else:
            chars.append("_")
    token = "".join(chars).strip("._")
    if not token:
        token = "x"
    return token[:max_len]


def _parse_run_name(name: str) -> tuple[int, int]:
    m = re.match(r"h(\d+)_supervised_cycle(\d+)$", name)
    if not m:
        return (0, 0)
    return (int(m.group(1)), int(m.group(2)))


def _discover_cycle_dirs(runs_root: Path) -> list[Path]:
    out: list[Path] = []
    for p in sorted(runs_root.glob("h*_supervised_cycle*")):
        if not p.is_dir():
            continue
        hid, cyc = _parse_run_name(p.name)
        if hid <= 0 or cyc <= 0:
            continue
        out.append(p)
    out.sort(key=lambda p: _parse_run_name(p.name))
    return out


def _load_rows_for_dir(cycle_dir: Path) -> list[dict[str, Any]]:
    combined = sorted(cycle_dir.glob("summary_cycle*combined.json"))
    if combined:
        obj = _read_json(combined[-1], default={})
        rows = [dict(x) for x in obj.get("rows", []) if isinstance(x, dict)]
        if rows:
            return rows
    summary = cycle_dir / "summary.json"
    if summary.exists():
        obj = _read_json(summary, default={})
        rows = [dict(x) for x in obj.get("rows", []) if isinstance(x, dict)]
        if rows:
            return rows
    rows: list[dict[str, Any]] = []
    for sp in sorted(cycle_dir.glob("tranche_*/summary.json")):
        obj = _read_json(sp, default={})
        rows.extend(dict(x) for x in obj.get("rows", []) if isinstance(x, dict))
    return rows


def _load_status_history(runs_root: Path) -> tuple[dict[str, list[str]], dict[str, int]]:
    history: dict[str, list[str]] = {}
    last_cycle_seen: dict[str, int] = {}
    for cd in _discover_cycle_dirs(runs_root):
        _, cyc = _parse_run_name(cd.name)
        rows = _load_rows_for_dir(cd)
        latest_for_run: dict[str, str] = {}
        for r in rows:
            hid = str(r.get("hypothesis_id", ""))
            st = str(r.get("final_status", ""))
            if not hid or st not in {"supported", "falsified", "inconclusive"}:
                continue
            latest_for_run[hid] = st
        for hid, st in latest_for_run.items():
            history.setdefault(hid, []).append(st)
            last_cycle_seen[hid] = cyc
    return history, last_cycle_seen


def _infer_category_from_recipe(recipe: str) -> str:
    r = str(recipe or "")
    if r.startswith("perp_oracle_lp_attack_"):
        return "game"
    if r.startswith("esso_synth") or r.startswith("esso_spec_debug"):
        return "cegis"
    if r.startswith("lean_"):
        return "lean"
    if r.startswith("pytest_"):
        low = r.lower()
        if any(tok in low for tok in ("tau_", "intent", "dex_snapshot", "state_root", "operations_parsing")):
            return "automation"
        if any(tok in low for tok in ("perp", "funding", "il_futures")):
            return "game"
        return "algo"
    if r.startswith("state_root") or r.startswith("intent_normal_form") or r.startswith("settlement_normal_form"):
        return "automation"
    if r.startswith("perp_") or r.startswith("il_") or r.startswith("roundtrip_") or r.startswith("curve_selection_"):
        return "game"
    if r.startswith("split_routing_") or r.startswith("batch_") or r.startswith("route_exact_out") or r.startswith("cpmm_"):
        return "algo"
    if r.startswith("esso_"):
        return "algo"
    return "misc"


def _mk_hyp(
    *,
    hypothesis_id: str,
    mechanism_change: str,
    transform: str,
    delta: list[int],
    null_hypothesis: str,
    check: str,
    obligations: list[str],
    risks: list[str],
    timeout_s: int,
    category: str,
    source: str,
    carryover_eig: float = 0.0,
) -> dict[str, Any]:
    if transform not in VALID_TRANSFORMS:
        raise ValueError(f"invalid transform: {transform}")
    if len(delta) != 5:
        raise ValueError(f"expected 5-d metric vector: {hypothesis_id}")
    return {
        "hypothesis_id": hypothesis_id,
        "mechanism_change": mechanism_change,
        "representation_shift_used": transform,
        "expected_metric_delta": [int(x) for x in delta],
        "null_hypothesis": null_hypothesis,
        "falsification_recipe": check,
        "support_recipe": check,
        "formal_obligations": obligations,
        "risk_modes": risks,
        "status": "proposed",
        "timeout_s": int(timeout_s),
        "category": category,
        "source": source,
        "carryover_eig": float(carryover_eig),
    }


ALGO_TESTS = [
    "tests/core/test_batch_clearing_global_refinement.py",
    "tests/core/test_batch_clearing_b_refinement.py",
    "tests/core/test_batch_greedy.py",
    "tests/core/test_batch_clearing.py",
    "tests/core/test_split_routing.py",
    "tests/core/test_routing_exact_out_gate.py",
    "tests/core/test_settlement_normal_form.py",
    "tests/core/test_cpmm.py",
]

GAME_TESTS = [
    "tests/core/test_perp_incentive_hazards.py",
    "tests/core/test_perp_math_hazards.py",
    "tests/core/test_funding_rate_market.py",
    "tests/core/test_il_futures.py",
    "tests/core/test_perp_v2/test_invariants.py",
    "tests/core/test_perp_v2/test_oracle_equiv.py",
]

AUTOMATION_TESTS = [
    "tests/integration/test_tau_runner_fake_tau.py",
    "tests/integration/test_tau_runner_utils.py",
    "tests/integration/test_tau_runner_subprocess.py",
    "tests/integration/test_tau_gate.py",
    "tests/integration/test_tau_gate_boundary.py",
    "tests/integration/test_zusd_tau_gate.py",
    "tests/integration/test_tau_testnet_dex_plugin.py",
    "tests/integration/test_tau_net_signing_optional.py",
    "tests/integration/test_intent_signatures.py",
    "tests/integration/test_dex_snapshot.py",
    "tests/integration/test_operations_parsing.py",
    "tests/state/test_state_root_determinism.py",
]

LEAN_FILES = {
    "algo": [
        "lean-mathlib/Proofs/BatchRefinementOrder.lean",
        "lean-mathlib/Proofs/BatchAuctionCanonical.lean",
        "lean-mathlib/Proofs/SplitRoutingArgmaxPlateau.lean",
        "lean-mathlib/Proofs/CPMMSettlement.lean",
    ],
    "game": [
        "lean-mathlib/Proofs/PerpGameTheory.lean",
        "lean-mathlib/Proofs/NoRisklessYieldLaw.lean",
        "lean-mathlib/Proofs/ProtocolFeeShareThreshold.lean",
        "lean-mathlib/Proofs/PerpFundingSymmetry.lean",
    ],
    "automation": [
        "lean-mathlib/Proofs/DeterministicAgentTieBreakSort.lean",
        "lean-mathlib/Proofs/DeterministicAgentTieBreak.lean",
        "lean-mathlib/Proofs/ZenoDEXNonces.lean",
        "lean-mathlib/Proofs/DeterministicEpochWindow.lean",
    ],
}

ALGO_STATIC_CHECKS = [
    "batch_clearing_gap_exists",
    "batch_clearing_no_gap",
    "batch_greedy_invariants",
    "split_routing_gap",
    "split_routing_no_gap",
    "split_routing_regression_exists",
    "route_exact_out_2hop_value",
    "route_exact_out_no_2hop_value",
    "curve_sum_boost_exact_out_advantage",
    "cpmm_overdelivery_witness",
    "cpmm_no_overdelivery_guarded",
    "cpmm_ref_parity",
    "cpmm_ref_parity_broken",
    "dex_v8_ref_parity",
    "dex_v8_ref_parity_broken",
    "settlement_normal_form",
    "settlement_ordering_nondeterminism_exists",
    "batch_clearing_invariant_break_exists",
]

GAME_STATIC_CHECKS = [
    "perp_clamp_profit",
    "perp_lp_fee_share_guard",
    "perp_lp_fee_share_irrelevant",
    "perp_reserve_hardening_effect",
    "il_insurance_vuln_presence",
    "il_insurance_status_quo_safe",
    "roundtrip_positive_profit_exists",
    "roundtrip_no_positive_profit",
    "perp_v2_invariants",
    "perp_v2_invariant_break_exists",
    "perp_v2_oracle_equiv",
    "perp_v2_oracle_divergence_exists",
    "curve_selection_safety",
    "curve_selection_unsafe_exists",
]

AUTOMATION_STATIC_CHECKS = [
    "state_root_determinism",
    "state_root_nondeterminism_exists",
    "intent_normal_form_tests",
    "intent_normal_form_regression_exists",
    "settlement_normal_form",
    "settlement_ordering_nondeterminism_exists",
]

ALGO_KERNELS = [
    "src/kernels/dex/batch_auction_settler_v1.yaml",
    "src/kernels/dex/swap_router_optimizer.yaml",
    "src/kernels/dex/swap_router_optimizer_evolvable_v1.yaml",
    "src/kernels/dex/hybrid_curve_swap_v1.yaml",
    "src/kernels/dex/cpmm_swap_v8.yaml",
    "src/kernels/dex/cpmm_output_amount_v2.yaml",
]

GAME_KERNELS = [
    "src/kernels/dex/perp_game_theory_v1_liqfix.yaml",
    "src/kernels/dex/perp_game_theory_v2.yaml",
    "src/kernels/dex/perp_game_theory_v1_fundingfix.yaml",
    "src/kernels/dex/curve_selection_market_v1.yaml",
    "src/kernels/dex/il_futures_market_v1.yaml",
]

AUTOMATION_KERNELS = [
    "src/kernels/dex/swap_router_optimizer.yaml",
    "src/kernels/dex/swap_router_optimizer_evolvable_v1.yaml",
    "src/kernels/dex/spec_quality_assessment_v1.yaml",
]

SYNTH_MODELS = [
    (
        "src/kernels/dex/simple_fee_multiplier_hole.yaml",
        "src/kernels/dex/simple_fee_multiplier_hole.synth.json",
        "GRAMMAR_UNREALIZABLE",
        False,
    ),
    (
        "src/kernels/dex/cpmm_output_amount_hole_v2.yaml",
        "src/kernels/dex/cpmm_output_amount_hole_v2.synth.json",
        "GRAMMAR_UNREALIZABLE",
        False,
    ),
    (
        "src/kernels/dex/lp_mint_optimal_hole_v2.yaml",
        "src/kernels/dex/lp_mint_optimal_hole_v2.synth.json",
        "GRAMMAR_UNREALIZABLE",
        False,
    ),
    (
        "src/kernels/dex/circuit_breaker_hole.yaml",
        "src/kernels/dex/circuit_breaker_hole.synth.json",
        "GRAMMAR_UNREALIZABLE",
        False,
    ),
    (
        "src/kernels/dex/swap_output_simple_hole.yaml",
        "src/kernels/dex/swap_output_simple_hole.synth.json",
        "GRAMMAR_UNREALIZABLE",
        False,
    ),
    (
        "src/kernels/dex/lp_ratio_calculator_hole.yaml",
        "src/kernels/dex/lp_ratio_calculator_hole.synth.json",
        "GRAMMAR_UNREALIZABLE",
        False,
    ),
    (
        "src/kernels/dex/swap_fee_calculator_hole.yaml",
        "src/kernels/dex/swap_fee_calculator_hole.synth.json",
        "GRAMMAR_UNREALIZABLE",
        False,
    ),
    (
        "src/kernels/dex/fee_calculator_hole.yaml",
        "src/kernels/dex/fee_calculator_hole.synth.json",
        "CONFLICTING_POINTS",
        True,
    ),
    (
        "src/kernels/dex/fee_accumulator_simple_hole.yaml",
        "src/kernels/dex/fee_accumulator_simple_hole.synth.json",
        "CONFLICTING_POINTS",
        True,
    ),
]

GAME_DYNAMIC_MASTER = [
    {
        "name": "floor_p9999_target1_exists",
        "expected_exists": True,
        "params": {
            "rb": 10000,
            "rq": 10000,
            "fee_bps": 10,
            "pfs": 9999,
            "lp_share_bps": 10000,
            "max_r": 10000,
            "max_pos_abs": 50,
            "max_move_bps": 500,
            "target_profit_quote": 1,
            "pfr": 0,
        },
    },
    {
        "name": "floor_p10000_target1_absent",
        "expected_exists": False,
        "params": {
            "rb": 10000,
            "rq": 10000,
            "fee_bps": 10,
            "pfs": 10000,
            "lp_share_bps": 10000,
            "max_r": 10000,
            "max_pos_abs": 50,
            "max_move_bps": 500,
            "target_profit_quote": 1,
            "pfr": 0,
        },
    },
    {
        "name": "floor_move100_target1_absent",
        "expected_exists": False,
        "params": {
            "rb": 10000,
            "rq": 10000,
            "fee_bps": 10,
            "pfs": 0,
            "lp_share_bps": 10000,
            "max_r": 10000,
            "max_pos_abs": 50,
            "max_move_bps": 100,
            "target_profit_quote": 1,
            "pfr": 0,
        },
    },
    {
        "name": "ceil_p0_target2_exists",
        "expected_exists": True,
        "params": {
            "rb": 10000,
            "rq": 10000,
            "fee_bps": 10,
            "pfs": 0,
            "lp_share_bps": 10000,
            "max_r": 10000,
            "max_pos_abs": 50,
            "max_move_bps": 500,
            "target_profit_quote": 2,
            "pfr": 1,
        },
    },
    {
        "name": "ceil_p1000_target2_absent",
        "expected_exists": False,
        "params": {
            "rb": 10000,
            "rq": 10000,
            "fee_bps": 10,
            "pfs": 1000,
            "lp_share_bps": 10000,
            "max_r": 10000,
            "max_pos_abs": 50,
            "max_move_bps": 500,
            "target_profit_quote": 2,
            "pfr": 1,
        },
    },
    {
        "name": "floor_p9999_target3_absent",
        "expected_exists": False,
        "params": {
            "rb": 10000,
            "rq": 10000,
            "fee_bps": 10,
            "pfs": 9999,
            "lp_share_bps": 10000,
            "max_r": 10000,
            "max_pos_abs": 50,
            "max_move_bps": 500,
            "target_profit_quote": 3,
            "pfr": 0,
        },
    },
    {
        "name": "floor_lp5000_p9999_target1_exists",
        "expected_exists": True,
        "params": {
            "rb": 10000,
            "rq": 10000,
            "fee_bps": 10,
            "pfs": 9999,
            "lp_share_bps": 5000,
            "max_r": 10000,
            "max_pos_abs": 50,
            "max_move_bps": 500,
            "target_profit_quote": 1,
            "pfr": 0,
        },
    },
    {
        "name": "floor_fee30_p9999_target1_exists",
        "expected_exists": True,
        "params": {
            "rb": 10000,
            "rq": 10000,
            "fee_bps": 30,
            "pfs": 9999,
            "lp_share_bps": 10000,
            "max_r": 10000,
            "max_pos_abs": 50,
            "max_move_bps": 500,
            "target_profit_quote": 1,
            "pfr": 0,
        },
    },
    {
        "name": "floor_fee30_p10000_target1_absent",
        "expected_exists": False,
        "params": {
            "rb": 10000,
            "rq": 10000,
            "fee_bps": 30,
            "pfs": 10000,
            "lp_share_bps": 10000,
            "max_r": 10000,
            "max_pos_abs": 50,
            "max_move_bps": 500,
            "target_profit_quote": 1,
            "pfr": 0,
        },
    },
    {
        "name": "floor_p0_target2_exists",
        "expected_exists": True,
        "params": {
            "rb": 10000,
            "rq": 10000,
            "fee_bps": 10,
            "pfs": 0,
            "lp_share_bps": 10000,
            "max_r": 10000,
            "max_pos_abs": 50,
            "max_move_bps": 500,
            "target_profit_quote": 2,
            "pfr": 0,
        },
    },
]


def _slice_window(items: list[Any], start: int, count: int) -> list[Any]:
    if not items or count <= 0:
        return []
    n = len(items)
    out: list[Any] = []
    for i in range(count):
        out.append(items[(start + i) % n])
    return out


def _check_id_perp_oracle(kind_exists: bool, params: dict[str, int]) -> str:
    order = [
        "rb",
        "rq",
        "fee_bps",
        "pfs",
        "lp_share_bps",
        "max_r",
        "max_pos_abs",
        "max_move_bps",
        "target_profit_quote",
        "pfr",
    ]
    body = ",".join(f"{k}={int(params[k])}" for k in order)
    suffix = "exists" if kind_exists else "absent"
    return f"perp_oracle_lp_attack_{suffix}::{body}"


def _base_pytest_hypotheses(
    *,
    cycle: int,
    test_paths: list[str],
    category: str,
    index_start: int,
) -> tuple[list[dict[str, Any]], int]:
    out: list[dict[str, Any]] = []
    idx = int(index_start)
    repeat_n = 3 if (cycle % 2 == 0) else 5
    for path in test_paths:
        slug = _safe_token(path.replace("/", "_").replace(".py", ""), max_len=90).lower()
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_{category}_{idx:03d}_{slug}_pytest_pass_v1",
                mechanism_change=f"Use `{path}` as deterministic gate for {category} mechanism changes.",
                transform="restrict" if category in {"automation", "game"} else "reduce",
                delta=[2, 0, 1, -1, 2] if category in {"automation", "game"} else [1, 1, 1, -1, 2],
                null_hypothesis=f"`{path}` is unstable or fails under bounded local replay.",
                check=f"pytest_pass::{path}",
                obligations=[
                    f"`{path}` passes in local deterministic replay",
                    "No timeout/error treated as support",
                ],
                risks=[
                    "Test under-coverage for unseen edge cases",
                    "Local environment can diverge from production",
                ],
                timeout_s=150,
                category=category,
                source="manual_pytest_gate",
            )
        )
        idx += 1
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_{category}_{idx:03d}_{slug}_pytest_fail_v1",
                mechanism_change=f"Counterclaim: `{path}` still exposes bounded regressions.",
                transform="relax",
                delta=[1, -1, -1, -1, -1],
                null_hypothesis=f"Bounded regressions exist in `{path}`.",
                check=f"pytest_fail::{path}",
                obligations=[
                    f"Produce deterministic failing witness for `{path}`",
                    "Treat flaky/timeouts as inconclusive",
                ],
                risks=[
                    "False negatives from fixture assumptions",
                    "Conflating harness failures with mechanism flaws",
                ],
                timeout_s=150,
                category=category,
                source="manual_pytest_counterclaim",
            )
        )
        idx += 1
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_{category}_{idx:03d}_{slug}_pytest_repeat{repeat_n}_v1",
                mechanism_change=f"Require `{repeat_n}x` deterministic replay of `{path}` before promotion.",
                transform="reduce",
                delta=[1, 0, 1, -1, 2],
                null_hypothesis=f"`{path}` is not stable across {repeat_n} deterministic replays.",
                check=f"pytest_repeat{repeat_n}::{path}",
                obligations=[
                    f"All {repeat_n} replays pass for `{path}`",
                    "Any timeout/error remains inconclusive",
                ],
                risks=[
                    "Replay still under-approximates rare events",
                    "Extra runtime cost",
                ],
                timeout_s=210,
                category=category,
                source="manual_pytest_replay",
            )
        )
        idx += 1
    return out, idx


def _lean_hypotheses(
    *,
    cycle: int,
    files: list[str],
    category: str,
    index_start: int,
) -> tuple[list[dict[str, Any]], int]:
    out: list[dict[str, Any]] = []
    idx = int(index_start)
    for path in files:
        slug = _safe_token(path.replace("/", "_").replace(".lean", ""), max_len=90).lower()
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_lean_{category}_{idx:03d}_{slug}_pass_v1",
                mechanism_change=f"Promote theorem-carrying gate: `{path}` must compile before acceptance.",
                transform="restrict",
                delta=[2, 0, 1, -1, 2],
                null_hypothesis=f"`{path}` does not compile in local Mathlib toolchain.",
                check=f"lean_pass::{path}",
                obligations=[
                    f"`{path}` compiles under local lake/mathlib",
                    "No UNKNOWN/TIMEOUT treated as proof",
                ],
                risks=[
                    "Proof/code invariant mapping can still be incomplete",
                    "Toolchain drift",
                ],
                timeout_s=240,
                category="lean",
                source="manual_lean_gate",
            )
        )
        idx += 1
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_lean_{category}_{idx:03d}_{slug}_repeat3_v1",
                mechanism_change=f"Require 3x deterministic replay for `{path}`.",
                transform="reduce",
                delta=[1, 0, 1, -1, 2],
                null_hypothesis=f"`{path}` is unstable across repeated formal replay.",
                check=f"lean_repeat3::{path}",
                obligations=[
                    "Three consecutive proof replays succeed",
                    "Timeout/error is inconclusive",
                ],
                risks=[
                    "Bounded replay still under-approximates full toolchain changes",
                    "Higher runtime cost",
                ],
                timeout_s=360,
                category="lean",
                source="manual_lean_replay",
            )
        )
        idx += 1
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_lean_{category}_{idx:03d}_{slug}_fail_v1",
                mechanism_change=f"Counterclaim: `{path}` is currently unprovable/unbuildable.",
                transform="relax",
                delta=[1, -1, -1, -1, -1],
                null_hypothesis=f"`{path}` is buildable and replayable.",
                check=f"lean_fail::{path}",
                obligations=[
                    f"Produce deterministic compile failure for `{path}`",
                    "Do not classify transient IO errors as proof failures",
                ],
                risks=[
                    "False negative from temporary environment issues",
                    "Misclassification of setup vs theorem failures",
                ],
                timeout_s=240,
                category="lean",
                source="manual_lean_counterclaim",
            )
        )
        idx += 1
    return out, idx


def _kernel_hypotheses(
    *,
    cycle: int,
    kernels: list[str],
    category: str,
    index_start: int,
) -> tuple[list[dict[str, Any]], int]:
    out: list[dict[str, Any]] = []
    idx = int(index_start)
    for kernel in kernels:
        slug = _safe_token(kernel.replace("/", "_").replace(".yaml", ""), max_len=90).lower()
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_{category}_{idx:03d}_{slug}_verify_dual_timeout_v1",
                mechanism_change=f"Gate `{kernel}` with dual-solver timeout posture for deterministic verification.",
                transform="restrict" if category in {"game", "automation"} else "reduce",
                delta=[2, 0, 1, -1, 1] if category in {"game", "automation"} else [1, 1, 1, -1, 1],
                null_hypothesis=f"`{kernel}` does not remain VERIFIED under dual-solver timeout posture.",
                check=f"esso_verify_solver_timeout::cvc5,z3::9000::{kernel}",
                obligations=[
                    "ESSO verify-multi returns VERIFIED",
                    "No inconclusive/timeout treated as support",
                ],
                risks=[
                    "Solver posture sensitivity",
                    "Kernel assumptions may omit production composition details",
                ],
                timeout_s=330,
                category=category,
                source="manual_esso_gate_dual_timeout",
            )
        )
        idx += 1
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_{category}_{idx:03d}_{slug}_fail_dual_timeout_v1",
                mechanism_change=f"Counterclaim: `{kernel}` fails dual-solver timeout verification.",
                transform="relax",
                delta=[1, -1, -1, -1, -1],
                null_hypothesis=f"`{kernel}` is stable under dual-solver timeout posture.",
                check=f"esso_fail_solver_timeout::cvc5,z3::9000::{kernel}",
                obligations=[
                    "Produce deterministic failure witness",
                    "Treat UNKNOWN/TIMEOUT as inconclusive, not support",
                ],
                risks=[
                    "Timeout posture can blur semantic vs posture failures",
                    "False negatives from solver environment drift",
                ],
                timeout_s=330,
                category=category,
                source="manual_esso_counterclaim_dual_timeout",
            )
        )
        idx += 1
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_{category}_{idx:03d}_{slug}_repeat2_dual_v1",
                mechanism_change=f"Require 2x dual-solver replay for `{kernel}` before promotion.",
                transform="reduce",
                delta=[1, 0, 1, -1, 2],
                null_hypothesis=f"`{kernel}` is unstable across dual-solver replays.",
                check=f"esso_repeat2_solver::cvc5,z3::{kernel}",
                obligations=[
                    "Two consecutive dual-solver replays pass",
                    "No timeout/error treated as support",
                ],
                risks=[
                    "Replay bounds do not prove global correctness",
                    "Additional compute cost",
                ],
                timeout_s=330,
                category=category,
                source="manual_esso_replay_dual",
            )
        )
        idx += 1
    return out, idx


def _static_check_hypotheses(
    *,
    cycle: int,
    checks: list[str],
    category: str,
    index_start: int,
) -> tuple[list[dict[str, Any]], int]:
    out: list[dict[str, Any]] = []
    idx = int(index_start)
    for check in checks:
        slug = _safe_token(check, max_len=100).lower()
        tr = "restrict" if any(tok in check for tok in ("determin", "invariant", "safety", "normal_form")) else "reduce"
        delta = [2, 0, 1, -1, 1] if tr == "restrict" else [1, 1, 1, -1, 1]
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_{category}_{idx:03d}_{slug}_v1",
                mechanism_change=f"Promote `{check}` as mechanistic gate in {category} tranche.",
                transform=tr,
                delta=delta,
                null_hypothesis=f"`{check}` does not hold under current bounded check harness.",
                check=check,
                obligations=[
                    f"`{check}` returns deterministic signal",
                    "UNKNOWN/TIMEOUT/ERROR remain inconclusive",
                ],
                risks=[
                    "Bounded harness may miss larger counterexamples",
                    "Signal polarity mistakes can mislead promotions",
                ],
                timeout_s=220,
                category=category,
                source="manual_static_check",
            )
        )
        idx += 1
    return out, idx


def _dynamic_game_hypotheses(*, cycle: int, index_start: int) -> tuple[list[dict[str, Any]], int]:
    out: list[dict[str, Any]] = []
    idx = int(index_start)

    # Rotate deterministic boundary regimes across cycles.
    start = ((cycle - 1) * 2) % len(GAME_DYNAMIC_MASTER)
    regimes = _slice_window(GAME_DYNAMIC_MASTER, start, 5)

    for reg in regimes:
        name = str(reg["name"])
        params = dict(reg["params"])
        expected_exists = bool(reg["expected_exists"])
        main_check = _check_id_perp_oracle(kind_exists=expected_exists, params=params)
        alt_check = _check_id_perp_oracle(kind_exists=not expected_exists, params=params)
        slug = _safe_token(name, max_len=90).lower()

        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_game_dyn_{idx:03d}_{slug}_main_v1",
                mechanism_change=(
                    "Boundary probe for LP-assisted oracle manipulation under "
                    f"regime `{name}` (expected_exists={expected_exists})."
                ),
                transform="reduce",
                delta=[2, 0, 2, -1, 1],
                null_hypothesis=f"Regime `{name}` does not match expected attack classification.",
                check=main_check,
                obligations=[
                    "Dynamic regime check returns deterministic classification",
                    "Witness (if present) is replayable from serialized params",
                ],
                risks=[
                    "Bounded search horizon can under-approximate attack space",
                    "Regime-specific conclusions may not generalize",
                ],
                timeout_s=420,
                category="game",
                source="manual_game_dynamic_boundary",
            )
        )
        idx += 1
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_game_dyn_{idx:03d}_{slug}_counter_v1",
                mechanism_change=(
                    "Counterclaim probe for LP-assisted oracle manipulation under "
                    f"regime `{name}` (opposite classification)."
                ),
                transform="relax",
                delta=[1, -1, -1, -1, -1],
                null_hypothesis=f"Opposite classification holds for regime `{name}`.",
                check=alt_check,
                obligations=[
                    "Counter-branch classification is explicitly tested",
                    "No timeout/error treated as support",
                ],
                risks=[
                    "Opposite branch can be vacuous when regime is near phase boundary",
                    "Higher runtime due to dynamic miner search",
                ],
                timeout_s=420,
                category="game",
                source="manual_game_dynamic_counterclaim",
            )
        )
        idx += 1
    return out, idx


def _cegis_hypotheses(*, cycle: int, index_start: int) -> tuple[list[dict[str, Any]], int]:
    out: list[dict[str, Any]] = []
    idx = int(index_start)
    start = ((cycle - 1) * 3) % len(SYNTH_MODELS)
    selected = _slice_window(SYNTH_MODELS, start, 6)

    for model_yaml, synth_json, expected_class, expected_success in selected:
        slug = _safe_token(model_yaml.replace("/", "_").replace(".yaml", ""), max_len=100).lower()
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_cegis_{idx:03d}_{slug}_synth_cvc5_v1",
                mechanism_change=f"Check SyGuS realizability posture for `{model_yaml}` (cvc5 timeout).",
                transform="reduce",
                delta=[1, 1, 1, -1, 1] if expected_success else [1, 0, 1, -1, 1],
                null_hypothesis=f"`{model_yaml}` does not synthesize under cvc5 timeout posture.",
                check=f"esso_synth_solver_timeout::cvc5::6000::{model_yaml}::{synth_json}",
                obligations=[
                    "Synthesis verdict must be parsed from deterministic JSON payload",
                    "Timeout/error remains inconclusive",
                ],
                risks=[
                    "Synthesis labels can vary across solver posture",
                    "Model success can be brittle to grammar constraints",
                ],
                timeout_s=330,
                category="cegis",
                source="manual_cegis_synth_gate",
            )
        )
        idx += 1
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_cegis_{idx:03d}_{slug}_synth_fail_cvc5_v1",
                mechanism_change=f"Counterclaim: `{model_yaml}` should fail synthesis under cvc5 timeout posture.",
                transform="relax",
                delta=[1, -1, -1, -1, -1],
                null_hypothesis=f"`{model_yaml}` has deterministic cvc5 synthesis failure witness.",
                check=f"esso_synth_fail_solver_timeout::cvc5::6000::{model_yaml}::{synth_json}",
                obligations=[
                    "Counterclaim path emits deterministic failure evidence when true",
                    "Timeout/error remains inconclusive",
                ],
                risks=[
                    "Failure can be posture-specific rather than semantic",
                    "Misclassification of model quality vs solver budget",
                ],
                timeout_s=330,
                category="cegis",
                source="manual_cegis_synth_counterclaim",
            )
        )
        idx += 1
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_cegis_{idx:03d}_{slug}_spec_class_v1",
                mechanism_change=f"Require expected spec-debug class `{expected_class}` for `{model_yaml}`.",
                transform="reduce",
                delta=[1, 0, 1, -1, 2],
                null_hypothesis=f"Spec-debug class for `{model_yaml}` diverges from `{expected_class}`.",
                check=f"esso_spec_debug_class::{expected_class}::{model_yaml}::{synth_json}",
                obligations=[
                    "Class label derived from deterministic ESSO spec-debug report",
                    "Class mismatch must produce replayable counterexample payload",
                ],
                risks=[
                    "Class taxonomy may evolve across ESSO versions",
                    "Class agreement does not imply model realizability",
                ],
                timeout_s=330,
                category="cegis",
                source="manual_cegis_spec_class",
            )
        )
        idx += 1

    # Extra z3 probes for high-information split between fail/success model families.
    z3_extra = [
        (
            "src/kernels/dex/fee_calculator_hole.yaml",
            "src/kernels/dex/fee_calculator_hole.synth.json",
        ),
        (
            "src/kernels/dex/fee_accumulator_simple_hole.yaml",
            "src/kernels/dex/fee_accumulator_simple_hole.synth.json",
        ),
        (
            "src/kernels/dex/cpmm_output_amount_hole_v2.yaml",
            "src/kernels/dex/cpmm_output_amount_hole_v2.synth.json",
        ),
    ]
    for model_yaml, synth_json in z3_extra:
        slug = _safe_token(model_yaml.replace("/", "_").replace(".yaml", ""), max_len=100).lower()
        out.append(
            _mk_hyp(
                hypothesis_id=f"H_cycle{cycle}_manual_cegis_{idx:03d}_{slug}_synth_fail_z3_v1",
                mechanism_change=f"Probe z3 synthesis failure posture for `{model_yaml}`.",
                transform="relax",
                delta=[1, -1, -1, -1, -1],
                null_hypothesis=f"`{model_yaml}` has deterministic z3 synth failure witness.",
                check=f"esso_synth_fail_solver_timeout::z3::6000::{model_yaml}::{synth_json}",
                obligations=[
                    "z3 synth-fail signal must be deterministic under fixed timeout",
                    "No timeout/error treated as support",
                ],
                risks=[
                    "Solver-specific posture mismatch vs cvc5",
                    "Increased inconclusive risk under tight timeout",
                ],
                timeout_s=330,
                category="cegis",
                source="manual_cegis_solver_posture",
            )
        )
        idx += 1
    return out, idx


def _carryover_hypotheses(
    *,
    prev_pack_path: Path | None,
    prev_queue_path: Path | None,
    carryover_n: int,
) -> list[dict[str, Any]]:
    if prev_pack_path is None or prev_queue_path is None:
        return []
    pack_obj = _read_json(prev_pack_path, default={})
    queue_obj = _read_json(prev_queue_path, default={})
    pack_rows = [h for h in pack_obj.get("hypotheses", []) if isinstance(h, dict) and h.get("hypothesis_id")]
    by_id = {str(h["hypothesis_id"]): dict(h) for h in pack_rows}
    out: list[dict[str, Any]] = []
    for row in queue_obj.get("queue", []):
        if len(out) >= carryover_n:
            break
        if not isinstance(row, dict):
            continue
        hid = str(row.get("hypothesis_id", ""))
        if not hid:
            continue
        h = by_id.get(hid)
        if h is None:
            continue
        h = dict(h)
        h["carryover"] = True
        h["carryover_eig"] = float(row.get("expected_information_gain", 0.0) or 0.0)
        h["category"] = str(h.get("category") or _infer_category_from_recipe(str(h.get("support_recipe", ""))))
        out.append(h)
    return out


def _ensure_hyp_schema(rows: list[dict[str, Any]]) -> None:
    required = {
        "hypothesis_id",
        "mechanism_change",
        "representation_shift_used",
        "expected_metric_delta",
        "null_hypothesis",
        "falsification_recipe",
        "support_recipe",
        "formal_obligations",
        "risk_modes",
        "status",
    }
    seen: set[str] = set()
    for r in rows:
        miss = [k for k in required if k not in r]
        if miss:
            raise ValueError(f"missing fields {miss} in {r.get('hypothesis_id')}")
        hid = str(r.get("hypothesis_id", ""))
        if not hid:
            raise ValueError("empty hypothesis_id")
        if hid in seen:
            raise ValueError(f"duplicate hypothesis_id: {hid}")
        seen.add(hid)
        tr = str(r.get("representation_shift_used"))
        if tr not in VALID_TRANSFORMS:
            raise ValueError(f"invalid transform {tr} ({hid})")
        vec = r.get("expected_metric_delta")
        if not isinstance(vec, list) or len(vec) != 5:
            raise ValueError(f"bad expected_metric_delta shape ({hid})")


def _score_hypothesis(
    *,
    h: dict[str, Any],
    history: dict[str, list[str]],
    last_cycle_seen: dict[str, int],
    cycle: int,
) -> float:
    hid = str(h.get("hypothesis_id", ""))
    recipe = str(h.get("support_recipe", ""))
    category = str(h.get("category", _infer_category_from_recipe(recipe)))
    transform = str(h.get("representation_shift_used", "equiv"))
    timeout_s = int(h.get("timeout_s", 180) or 180)

    score = 0.0
    score += float(h.get("carryover_eig", 0.0)) * 0.45

    hist = history.get(hid, [])
    if not hist:
        score += 1.35
    else:
        if hist[-1] == "inconclusive":
            score += 0.75
        if len(hist) >= 3 and all(x == hist[-1] for x in hist[-3:]):
            score -= 0.7
        age = cycle - int(last_cycle_seen.get(hid, cycle))
        if age >= 3:
            score += 0.2

    if category == "game":
        score += 1.1
    elif category == "algo":
        score += 0.85
    elif category == "automation":
        score += 0.8
    elif category == "cegis":
        score += 0.95
    elif category == "lean":
        score += 0.7

    if recipe.startswith("perp_oracle_lp_attack_"):
        score += 1.0
    if recipe.startswith("esso_synth") or recipe.startswith("esso_spec_debug"):
        score += 0.75
    if recipe.startswith("esso_verify_solver_timeout::cvc5,z3::"):
        score += 0.45
    if recipe.startswith("lean_repeat3::"):
        score += 0.35
    if recipe.startswith("pytest_repeat5::"):
        score -= 0.2
    if "counterclaim" in str(h.get("source", "")):
        score += 0.25

    if transform == "restrict":
        score += 0.25
    elif transform == "reduce":
        score += 0.2
    elif transform == "relax":
        score += 0.1

    # Mild cost penalty to avoid overloading heavy lanes with low-value checks.
    score -= min(0.7, float(timeout_s) / 900.0)
    return score


def _is_heavy(h: dict[str, Any]) -> bool:
    recipe = str(h.get("support_recipe", ""))
    timeout_s = int(h.get("timeout_s", 180) or 180)
    if timeout_s >= 330:
        return True
    if recipe.startswith("perp_oracle_lp_attack_"):
        return True
    if "repeat3" in recipe or "repeat5" in recipe:
        return True
    if recipe.startswith("lean_repeat"):
        return True
    if recipe.startswith("esso_verify_solver_timeout::") and "::9000::" in recipe:
        return True
    if recipe.startswith("esso_repeat2_solver::"):
        return True
    return False


def _shard_round_robin(rows: list[dict[str, Any]], shards: int) -> list[list[dict[str, Any]]]:
    n = max(1, int(shards))
    out = [[] for _ in range(n)]
    for i, row in enumerate(rows):
        out[i % n].append(row)
    return out


def _build_manual_candidates(cycle: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    idx = 1

    algo_tests = _slice_window(ALGO_TESTS, ((cycle - 1) * 2) % len(ALGO_TESTS), 5)
    chunk, idx = _base_pytest_hypotheses(cycle=cycle, test_paths=algo_tests, category="algo", index_start=idx)
    rows.extend(chunk)
    algo_checks = _slice_window(ALGO_STATIC_CHECKS, ((cycle - 1) * 4) % len(ALGO_STATIC_CHECKS), 8)
    chunk, idx = _static_check_hypotheses(cycle=cycle, checks=algo_checks, category="algo", index_start=idx)
    rows.extend(chunk)
    algo_kernels = _slice_window(ALGO_KERNELS, ((cycle - 1) * 2) % len(ALGO_KERNELS), 4)
    chunk, idx = _kernel_hypotheses(cycle=cycle, kernels=algo_kernels, category="algo", index_start=idx)
    rows.extend(chunk)

    game_tests = _slice_window(GAME_TESTS, ((cycle - 1) * 2) % len(GAME_TESTS), 4)
    chunk, idx = _base_pytest_hypotheses(cycle=cycle, test_paths=game_tests, category="game", index_start=idx)
    rows.extend(chunk)
    chunk, idx = _dynamic_game_hypotheses(cycle=cycle, index_start=idx)
    rows.extend(chunk)
    game_checks = _slice_window(GAME_STATIC_CHECKS, ((cycle - 1) * 3) % len(GAME_STATIC_CHECKS), 8)
    chunk, idx = _static_check_hypotheses(cycle=cycle, checks=game_checks, category="game", index_start=idx)
    rows.extend(chunk)
    game_kernels = _slice_window(GAME_KERNELS, ((cycle - 1) * 2) % len(GAME_KERNELS), 3)
    chunk, idx = _kernel_hypotheses(cycle=cycle, kernels=game_kernels, category="game", index_start=idx)
    rows.extend(chunk)

    auto_tests = _slice_window(AUTOMATION_TESTS, ((cycle - 1) * 3) % len(AUTOMATION_TESTS), 6)
    chunk, idx = _base_pytest_hypotheses(cycle=cycle, test_paths=auto_tests, category="automation", index_start=idx)
    rows.extend(chunk)
    auto_checks = _slice_window(AUTOMATION_STATIC_CHECKS, ((cycle - 1) * 2) % len(AUTOMATION_STATIC_CHECKS), 6)
    chunk, idx = _static_check_hypotheses(cycle=cycle, checks=auto_checks, category="automation", index_start=idx)
    rows.extend(chunk)
    auto_kernels = _slice_window(AUTOMATION_KERNELS, ((cycle - 1) * 2) % len(AUTOMATION_KERNELS), 2)
    chunk, idx = _kernel_hypotheses(cycle=cycle, kernels=auto_kernels, category="automation", index_start=idx)
    rows.extend(chunk)

    for lean_cat, files in LEAN_FILES.items():
        lean_pick = _slice_window(files, ((cycle - 1) * 2) % len(files), 2 if lean_cat != "automation" else 3)
        chunk, idx = _lean_hypotheses(cycle=cycle, files=lean_pick, category=lean_cat, index_start=idx)
        rows.extend(chunk)

    chunk, idx = _cegis_hypotheses(cycle=cycle, index_start=idx)
    rows.extend(chunk)

    return rows


def _select_hypotheses(
    *,
    cycle: int,
    candidates: list[dict[str, Any]],
    carryover: list[dict[str, Any]],
    history: dict[str, list[str]],
    last_cycle_seen: dict[str, int],
    target: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    by_id: dict[str, dict[str, Any]] = {}
    selected: list[dict[str, Any]] = []

    def add_row(row: dict[str, Any]) -> None:
        hid = str(row.get("hypothesis_id", ""))
        if not hid or hid in by_id:
            return
        rr = dict(row)
        rr["category"] = str(rr.get("category") or _infer_category_from_recipe(str(rr.get("support_recipe", ""))))
        by_id[hid] = rr
        selected.append(rr)

    # Carryover first for supervised exploitation.
    for row in carryover:
        add_row(row)

    # Dedup candidate pool and score.
    pool: list[dict[str, Any]] = []
    for row in candidates:
        hid = str(row.get("hypothesis_id", ""))
        if not hid or hid in by_id:
            continue
        rr = dict(row)
        rr["category"] = str(rr.get("category") or _infer_category_from_recipe(str(rr.get("support_recipe", ""))))
        rr["score"] = _score_hypothesis(h=rr, history=history, last_cycle_seen=last_cycle_seen, cycle=cycle)
        pool.append(rr)

    pool.sort(key=lambda r: (float(r.get("score", 0.0)), r.get("hypothesis_id", "")), reverse=True)

    # Quota-guided fill.
    quotas = {"algo": 20, "game": 24, "automation": 20, "cegis": 16, "lean": 8}

    def counts(rows: list[dict[str, Any]]) -> dict[str, int]:
        c: dict[str, int] = {}
        for x in rows:
            cat = str(x.get("category", "misc"))
            c[cat] = int(c.get(cat, 0)) + 1
        return c

    while len(selected) < target:
        c = counts(selected)
        pending = {k for k, v in quotas.items() if int(c.get(k, 0)) < int(v)}
        pick: dict[str, Any] | None = None
        for row in pool:
            hid = str(row["hypothesis_id"])
            if hid in by_id:
                continue
            cat = str(row.get("category", "misc"))
            if pending and cat not in pending:
                continue
            pick = row
            break
        if pick is None:
            # fallback: ignore pending quota, fill by score.
            for row in pool:
                hid = str(row["hypothesis_id"])
                if hid not in by_id:
                    pick = row
                    break
        if pick is None:
            break
        add_row(pick)

    selected = selected[:target]
    novel = [r for r in selected if not history.get(str(r.get("hypothesis_id", "")))]
    for r in selected:
        r.pop("score", None)
    return selected, novel


def _next_run_id_for_cycle(runs_root: Path, cycle: int) -> int:
    dirs = _discover_cycle_dirs(runs_root)
    max_h = 0
    for d in dirs:
        hid, _ = _parse_run_name(d.name)
        max_h = max(max_h, hid)
    return max_h + 1


def _find_cycle_dir(runs_root: Path, cycle: int) -> Path | None:
    for d in _discover_cycle_dirs(runs_root):
        _, cyc = _parse_run_name(d.name)
        if cyc == cycle:
            return d
    return None


def main() -> int:
    ap = argparse.ArgumentParser(description="Manual high-ROI hypothesis factory for supervised ZenoDEX cycles.")
    ap.add_argument("--cycle", type=int, required=True)
    ap.add_argument("--run-name", type=str, default="")
    ap.add_argument("--runs-root", type=Path, default=Path("runs/manual_morph_supervised"))
    ap.add_argument("--target", type=int, default=100)
    ap.add_argument("--carryover", type=int, default=20)
    ap.add_argument("--fast-shards", type=int, default=3)
    ap.add_argument("--heavy-shards", type=int, default=3)
    ap.add_argument("--exploration-ratio", type=float, default=0.72)
    ap.add_argument("--max-depth", type=int, default=8)
    ap.add_argument("--max-width", type=int, default=14)
    ap.add_argument("--per-epoch-compute-budget", type=int, default=180)
    args = ap.parse_args()

    cycle = int(args.cycle)
    target = max(10, int(args.target))
    runs_root = (ROOT / args.runs_root).resolve() if not args.runs_root.is_absolute() else args.runs_root
    runs_root.mkdir(parents=True, exist_ok=True)

    if args.run_name:
        run_name = str(args.run_name)
    else:
        hid = _next_run_id_for_cycle(runs_root, cycle)
        run_name = f"h{hid:03d}_supervised_cycle{cycle}"
    cycle_dir = runs_root / run_name
    cycle_dir.mkdir(parents=True, exist_ok=True)

    history, last_cycle_seen = _load_status_history(runs_root)

    prev_dir = _find_cycle_dir(runs_root, cycle - 1)
    prev_pack = prev_dir / "hypothesis_pack_100.json" if prev_dir is not None else None
    prev_queue = prev_dir / "next_experiment_queue.json" if prev_dir is not None else None
    carryover = _carryover_hypotheses(prev_pack_path=prev_pack, prev_queue_path=prev_queue, carryover_n=max(0, int(args.carryover)))

    candidates = _build_manual_candidates(cycle=cycle)
    selected, novel = _select_hypotheses(
        cycle=cycle,
        candidates=candidates,
        carryover=carryover,
        history=history,
        last_cycle_seen=last_cycle_seen,
        target=target,
    )
    _ensure_hyp_schema(selected)

    fast = [h for h in selected if not _is_heavy(h)]
    heavy = [h for h in selected if _is_heavy(h)]
    fast_shards = _shard_round_robin(fast, max(1, int(args.fast_shards)))
    heavy_shards = _shard_round_robin(heavy, max(1, int(args.heavy_shards)))

    _write_json(cycle_dir / "hypothesis_pack_raw_manual.json", {"count": len(candidates), "hypotheses": candidates})
    _write_json(cycle_dir / "hypothesis_pack_100.json", {"count": len(selected), "hypotheses": selected})
    _write_json(cycle_dir / "hypothesis_pack_100_novel.json", {"count": len(novel), "hypotheses": novel})
    _write_json(cycle_dir / "hypothesis_pack_fast.json", {"count": len(fast), "hypotheses": fast})
    _write_json(cycle_dir / "hypothesis_pack_heavy.json", {"count": len(heavy), "hypotheses": heavy})

    for i, shard in enumerate(fast_shards, 1):
        _write_json(cycle_dir / f"hypothesis_pack_fast_novel_shard{i}.json", {"count": len(shard), "hypotheses": shard})
    for i, shard in enumerate(heavy_shards, 1):
        _write_json(cycle_dir / f"hypothesis_pack_heavy_novel_shard{i}.json", {"count": len(shard), "hypotheses": shard})

    cat_counts: dict[str, int] = {}
    for h in selected:
        cat = str(h.get("category", "misc"))
        cat_counts[cat] = int(cat_counts.get(cat, 0)) + 1

    _write_json(
        cycle_dir / f"manual_injection_report_cycle{cycle}.json",
        {
            "schema": "zenodex/manual-cycle-injection/v2",
            "created_at": int(time.time()),
            "cycle": run_name,
            "target": target,
            "selected_total": len(selected),
            "novel_selected_actual": len(novel),
            "carryover_selected": len([x for x in selected if bool(x.get("carryover"))]),
            "category_counts": cat_counts,
            "focus": [
                "algorithm_global_refinement",
                "game_theory_boundary_mapping",
                "deterministic_agent_automation",
                "cegis_sygus_failure_classification",
                "manual_lean_formal_gates",
            ],
            "sample_hypothesis_ids": [str(x.get("hypothesis_id")) for x in selected[:20]],
        },
    )

    _write_json(
        cycle_dir / f"shard_plan_cycle{cycle}.json",
        {
            "schema": "zenodex/manual-cycle-shard-plan/v2",
            "created_at": int(time.time()),
            "cycle": run_name,
            "fast_shards": len(fast_shards),
            "heavy_shards": len(heavy_shards),
            "fast_total": len(fast),
            "heavy_total": len(heavy),
            "fast_counts": [len(x) for x in fast_shards],
            "heavy_counts": [len(x) for x in heavy_shards],
        },
    )

    _write_json(
        cycle_dir / "cycle_manifest.json",
        {
            "schema": "zenodex/manual-cycle-manifest/v1",
            "created_at": _now_iso(),
            "cycle": cycle,
            "run_name": run_name,
            "budgets": {
                "max_depth": int(args.max_depth),
                "max_width": int(args.max_width),
                "per_epoch_compute_budget": int(args.per_epoch_compute_budget),
                "exploration_ratio": float(args.exploration_ratio),
                "exploitation_ratio": round(1.0 - float(args.exploration_ratio), 3),
            },
            "selection": {
                "target": target,
                "selected": len(selected),
                "novel": len(novel),
                "carryover": len([x for x in selected if bool(x.get("carryover"))]),
            },
            "inputs": {
                "prev_cycle_dir": None if prev_dir is None else str(prev_dir),
                "prev_pack": None if prev_pack is None else str(prev_pack),
                "prev_queue": None if prev_queue is None else str(prev_queue),
            },
        },
    )

    print(
        json.dumps(
            {
                "ok": True,
                "cycle": cycle,
                "run_name": run_name,
                "cycle_dir": str(cycle_dir),
                "selected": len(selected),
                "novel": len(novel),
                "carryover": len([x for x in selected if bool(x.get("carryover"))]),
                "fast": len(fast),
                "heavy": len(heavy),
                "category_counts": cat_counts,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

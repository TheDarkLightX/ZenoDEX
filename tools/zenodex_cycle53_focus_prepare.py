#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
RUN_DIR = ROOT / "runs" / "manual_morph_supervised" / "h067_supervised_cycle53"

VALID_TRANSFORMS = {"equiv", "reduce", "relax", "restrict", "heuristic"}


def _now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _safe_token(text: str, max_len: int = 80) -> str:
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


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _delta(category: str, transform: str, optimistic: bool) -> list[int]:
    # [safety, capital_efficiency, execution_quality, performance_cost, determinism_simplicity]
    if transform == "relax":
        return [1, -1, -1, -1, -1]
    if category == "ux":
        if optimistic:
            return [1, 2, 3, 1, 1]
        return [1, 1, 2, 0, 0]
    if category == "security":
        if optimistic:
            return [3, 0, 2, 0, 1]
        return [2, 0, 1, -1, 1]
    # automation
    if optimistic:
        return [2, 0, 1, 1, 3]
    return [2, 0, 1, 0, 2]


def _mk_hypothesis(
    *,
    hid: str,
    mechanism_change: str,
    transform: str,
    category: str,
    check: str,
    null_hypothesis: str,
    obligations: list[str],
    risks: list[str],
    timeout_s: int,
    source: str,
    optimistic: bool,
) -> dict[str, Any]:
    if transform not in VALID_TRANSFORMS:
        raise ValueError(f"invalid transform: {transform} ({hid})")
    return {
        "hypothesis_id": hid,
        "mechanism_change": mechanism_change,
        "representation_shift_used": transform,
        "expected_metric_delta": _delta(category, transform, optimistic),
        "null_hypothesis": null_hypothesis,
        "falsification_recipe": check,
        "support_recipe": check,
        "formal_obligations": obligations,
        "risk_modes": risks,
        "status": "proposed",
        "timeout_s": int(timeout_s),
        "category": category,
        "source": source,
    }


def _check_transform(check: str, category: str) -> tuple[str, bool]:
    negative_tokens = [
        "_no_",
        "_broken",
        "_unsafe_exists",
        "_vuln_presence",
        "_positive_profit_exists",
        "_nondeterminism_exists",
        "_divergence_exists",
        "_invariant_break_exists",
        "_regression_exists",
        "_irrelevant",
        "_gap_exists",
    ]
    low = check.lower()
    if any(tok in low for tok in negative_tokens):
        return ("relax", False)
    if category == "security":
        return ("restrict", True)
    if category == "automation":
        return ("equiv", True)
    return ("reduce", True)


def _expected_ig(row: dict[str, Any]) -> float:
    check = str(row.get("falsification_recipe", ""))
    category = str(row.get("category", ""))
    transform = str(row.get("representation_shift_used", ""))
    prefix = check.split("::", 1)[0]

    base = 2.4
    if prefix.startswith("esso_verify_solver_timeout"):
        base = 4.2
    elif prefix.startswith("esso_fail_solver_timeout"):
        base = 4.0
    elif prefix.startswith("esso_repeat2_solver"):
        base = 3.7
    elif prefix.startswith("lean_repeat3"):
        base = 3.1
    elif prefix.startswith("lean_"):
        base = 2.8
    elif prefix.startswith("pytest_repeat3"):
        base = 2.9
    elif prefix.startswith("pytest_"):
        base = 2.6
    elif prefix in {
        "route_exact_out_2hop_value",
        "route_exact_out_no_2hop_value",
        "il_insurance_vuln_presence",
        "il_insurance_status_quo_safe",
        "twap_staleness_effect",
    }:
        base = 3.6
    elif prefix in {
        "settlement_normal_form",
        "batch_greedy_invariants",
        "state_root_determinism",
        "intent_normal_form_tests",
    }:
        base = 3.2
    elif prefix in {
        "settlement_ordering_nondeterminism_exists",
        "state_root_nondeterminism_exists",
        "intent_normal_form_regression_exists",
    }:
        base = 3.4

    if category == "security":
        base += 0.2
    if category == "automation":
        base += 0.15
    if transform == "relax":
        base += 0.15
    if "repeat3" in prefix:
        base -= 0.2
    return round(base, 2)


def _make_pytest_trio(
    *,
    cycle: int,
    start_idx: int,
    category: str,
    algorithm_name: str,
    test_path: str,
    transform_main: str,
    source: str,
) -> tuple[list[dict[str, Any]], int]:
    slug = _safe_token(test_path.replace("/", "_").replace(".py", ""))
    rows: list[dict[str, Any]] = []

    hid_pass = f"H_cycle{cycle}_focus_{category}_{start_idx:03d}_{slug}_pytest_pass_v1"
    rows.append(
        _mk_hypothesis(
            hid=hid_pass,
            mechanism_change=f"{algorithm_name}: promote deterministic regression gate on `{test_path}` as primary acceptance criterion.",
            transform=transform_main,
            category=category,
            check=f"pytest_pass::{test_path}",
            null_hypothesis=f"{algorithm_name} does not preserve expected behavior under `{test_path}`.",
            obligations=[
                f"`{test_path}` passes under deterministic local execution",
                "No timeout/error interpreted as support",
                "Gate remains replay-stable over repeated cycles",
            ],
            risks=[
                "Passing tests may still miss unmodeled adversarial regimes",
                "Coverage can lag mechanism changes",
            ],
            timeout_s=220,
            source=source,
            optimistic=True,
        )
    )
    start_idx += 1

    hid_fail = f"H_cycle{cycle}_focus_{category}_{start_idx:03d}_{slug}_pytest_fail_v1"
    rows.append(
        _mk_hypothesis(
            hid=hid_fail,
            mechanism_change=f"{algorithm_name} counterclaim: the same mechanism should fail `{test_path}` and is not deployment-safe.",
            transform="relax",
            category=category,
            check=f"pytest_fail::{test_path}",
            null_hypothesis=f"{algorithm_name} remains safe and test-stable on `{test_path}`.",
            obligations=[
                f"Produce deterministic failing witness for `{test_path}`",
                "Failure must be semantic, not tooling-transient",
            ],
            risks=[
                "False negatives from environment issues",
                "Failure can be orthogonal to the intended algorithmic claim",
            ],
            timeout_s=220,
            source=source,
            optimistic=False,
        )
    )
    start_idx += 1

    hid_repeat = f"H_cycle{cycle}_focus_{category}_{start_idx:03d}_{slug}_pytest_repeat3_v1"
    rows.append(
        _mk_hypothesis(
            hid=hid_repeat,
            mechanism_change=f"{algorithm_name}: require 3x deterministic replay on `{test_path}` to reduce flake risk.",
            transform="reduce",
            category=category,
            check=f"pytest_repeat3::{test_path}",
            null_hypothesis=f"{algorithm_name} is replay-unstable on `{test_path}`.",
            obligations=[
                "Three consecutive replays succeed",
                "No nondeterministic pass/fail oscillation",
            ],
            risks=[
                "Replay stability can still under-approximate full state-space",
                "Extra compute overhead for little marginal gain on trivial tests",
            ],
            timeout_s=260,
            source=source,
            optimistic=False,
        )
    )
    start_idx += 1
    return rows, start_idx


def _make_static_checks(
    *,
    cycle: int,
    start_idx: int,
    category: str,
    checks: list[tuple[str, str]],
    source: str,
) -> tuple[list[dict[str, Any]], int]:
    rows: list[dict[str, Any]] = []
    for check, algo_name in checks:
        transform, optimistic = _check_transform(check, category)
        hid = f"H_cycle{cycle}_focus_{category}_{start_idx:03d}_{_safe_token(check)}_v1"
        rows.append(
            _mk_hypothesis(
                hid=hid,
                mechanism_change=f"{algo_name}: evaluate mechanism under `{check}` as a direct falsifier/support gate.",
                transform=transform,
                category=category,
                check=check,
                null_hypothesis=f"{algo_name} claim does not hold under `{check}`.",
                obligations=[
                    f"`{check}` resolves deterministically",
                    "UNKNOWN/TIMEOUT/ERROR remains inconclusive",
                    "Outcome is replayable by recipe alone",
                ],
                risks=[
                    "Single check can overfit one failure mode",
                    "Bounded harness may miss out-of-distribution failures",
                ],
                timeout_s=180,
                source=source,
                optimistic=optimistic,
            )
        )
        start_idx += 1
    return rows, start_idx


def _make_esso_triples(
    *,
    cycle: int,
    start_idx: int,
    category: str,
    kernels: list[tuple[str, str]],
    source: str,
) -> tuple[list[dict[str, Any]], int]:
    rows: list[dict[str, Any]] = []
    for kernel_path, algo_name in kernels:
        slug = _safe_token(kernel_path.replace("/", "_").replace(".yaml", ""))

        hid_verify = f"H_cycle{cycle}_focus_{category}_{start_idx:03d}_{slug}_verify_dual_timeout_v1"
        rows.append(
            _mk_hypothesis(
                hid=hid_verify,
                mechanism_change=f"{algo_name}: require dual-solver ESSO verify gate on `{kernel_path}`.",
                transform="reduce" if category == "ux" else "restrict",
                category=category,
                check=f"esso_verify_solver_timeout::cvc5,z3::9000::{kernel_path}",
                null_hypothesis=f"`{kernel_path}` cannot be verified under this deterministic dual-solver posture.",
                obligations=[
                    "Dual-solver verify returns pass outcome",
                    "No timeout/error treated as support",
                    "Kernel remains in ESSO IR boundary",
                ],
                risks=[
                    "Solver posture sensitivity",
                    "Verification model may omit composition-level effects",
                ],
                timeout_s=360,
                source=source,
                optimistic=True,
            )
        )
        start_idx += 1

        hid_fail = f"H_cycle{cycle}_focus_{category}_{start_idx:03d}_{slug}_fail_dual_timeout_v1"
        rows.append(
            _mk_hypothesis(
                hid=hid_fail,
                mechanism_change=f"{algo_name} counterclaim: `{kernel_path}` fails dual-solver verification and should not be promoted.",
                transform="relax",
                category=category,
                check=f"esso_fail_solver_timeout::cvc5,z3::9000::{kernel_path}",
                null_hypothesis=f"`{kernel_path}` is verifiable and failure claims are spurious.",
                obligations=[
                    "Produce deterministic failure/counterexample",
                    "Failure is model-level, not schema/tooling mismatch",
                ],
                risks=[
                    "Counterexamples may be solver-artefacts",
                    "Timeout masquerading as semantic failure",
                ],
                timeout_s=360,
                source=source,
                optimistic=False,
            )
        )
        start_idx += 1

        hid_repeat = f"H_cycle{cycle}_focus_{category}_{start_idx:03d}_{slug}_repeat2_dual_v1"
        rows.append(
            _mk_hypothesis(
                hid=hid_repeat,
                mechanism_change=f"{algo_name}: require two consecutive dual-solver replays on `{kernel_path}` before promotion.",
                transform="reduce",
                category=category,
                check=f"esso_repeat2_solver::cvc5,z3::{kernel_path}",
                null_hypothesis=f"`{kernel_path}` is replay-unstable across dual-solver verification.",
                obligations=[
                    "Two replay runs pass without polarity drift",
                    "No timeout/error interpreted as support",
                ],
                risks=[
                    "Replay2 does not imply full global soundness",
                    "Added compute cost for narrow confidence gain",
                ],
                timeout_s=380,
                source=source,
                optimistic=False,
            )
        )
        start_idx += 1
    return rows, start_idx


def _make_lean_triples(
    *,
    cycle: int,
    start_idx: int,
    category: str,
    files: list[tuple[str, str]],
    source: str,
) -> tuple[list[dict[str, Any]], int]:
    rows: list[dict[str, Any]] = []
    for lean_path, algo_name in files:
        slug = _safe_token(lean_path.replace("/", "_").replace(".lean", ""))

        hid_pass = f"H_cycle{cycle}_focus_{category}_{start_idx:03d}_{slug}_lean_pass_v1"
        rows.append(
            _mk_hypothesis(
                hid=hid_pass,
                mechanism_change=f"{algo_name}: enforce theorem gate `{lean_path}` for formal promotion.",
                transform="equiv" if category != "security" else "restrict",
                category=category,
                check=f"lean_pass::{lean_path}",
                null_hypothesis=f"`{lean_path}` does not compile in local Mathlib posture.",
                obligations=[
                    f"`{lean_path}` compiles deterministically",
                    "No `sorry`/timeout accepted as proof",
                ],
                risks=[
                    "Theorem-code linkage may be incomplete",
                    "Toolchain drift can break previously valid proof scripts",
                ],
                timeout_s=320,
                source=source,
                optimistic=True,
            )
        )
        start_idx += 1

        hid_fail = f"H_cycle{cycle}_focus_{category}_{start_idx:03d}_{slug}_lean_fail_v1"
        rows.append(
            _mk_hypothesis(
                hid=hid_fail,
                mechanism_change=f"{algo_name} counterclaim: `{lean_path}` currently fails and cannot serve as a valid gate.",
                transform="relax",
                category=category,
                check=f"lean_fail::{lean_path}",
                null_hypothesis=f"`{lean_path}` is compilable and the counterclaim is false.",
                obligations=[
                    "Produce deterministic Lean failure witness",
                    "Failure must be theorem/toolchain relevant",
                ],
                risks=[
                    "False negatives from environment setup",
                    "Counterclaim can collapse after minor import repair",
                ],
                timeout_s=320,
                source=source,
                optimistic=False,
            )
        )
        start_idx += 1

        hid_repeat = f"H_cycle{cycle}_focus_{category}_{start_idx:03d}_{slug}_lean_repeat3_v1"
        rows.append(
            _mk_hypothesis(
                hid=hid_repeat,
                mechanism_change=f"{algo_name}: require 3x replay for `{lean_path}` before classifying it as a stable formal gate.",
                transform="reduce",
                category=category,
                check=f"lean_repeat3::{lean_path}",
                null_hypothesis=f"`{lean_path}` is replay-unstable under repeated formal builds.",
                obligations=[
                    "Three sequential Lean builds pass",
                    "No polarity drift across replays",
                ],
                risks=[
                    "Replay determinism does not imply theorem sufficiency",
                    "Longer proof CI duration",
                ],
                timeout_s=360,
                source=source,
                optimistic=False,
            )
        )
        start_idx += 1
    return rows, start_idx


def _build_ideation_log() -> dict[str, Any]:
    rounds = [
        {
            "round": 1,
            "title": "Contradiction Map Bootstrapping",
            "focus": "Extract high-information claim/counterclaim pairs from recent cycle polarity data.",
            "atoms": [
                {"atom_id": "A1.1", "candidate": "2-hop stress gate", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A1.2", "candidate": "no-2-hop-value null", "transform": "relax", "decision": "keep"},
                {"atom_id": "A1.3", "candidate": "settlement nondeterminism alarm", "transform": "relax", "decision": "keep"},
                {"atom_id": "A1.4", "candidate": "state-root nondeterminism alarm", "transform": "relax", "decision": "keep"},
                {"atom_id": "A1.5", "candidate": "low-yield broad solver sweep", "transform": "heuristic", "decision": "drop"},
            ],
        },
        {
            "round": 2,
            "title": "UX Routing Manifold",
            "focus": "Invent route/quote algorithms over stress and topology features.",
            "atoms": [
                {"atom_id": "A2.1", "candidate": "pfr-aware topology map", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A2.2", "candidate": "argmax-plateau split probe", "transform": "equiv", "decision": "keep"},
                {"atom_id": "A2.3", "candidate": "dense probe with canonical tie-break", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A2.4", "candidate": "always-2-hop policy", "transform": "heuristic", "decision": "drop"},
                {"atom_id": "A2.5", "candidate": "randomized tie-break routing", "transform": "heuristic", "decision": "drop"},
            ],
        },
        {
            "round": 3,
            "title": "Batch-Clearing UX Refinement",
            "focus": "Surplus-oriented refinement without sacrificing deterministic ordering.",
            "atoms": [
                {"atom_id": "A3.1", "candidate": "B-refinement pass after greedy A", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A3.2", "candidate": "global pair-swap frontier", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A3.3", "candidate": "canonical settlement normal form", "transform": "equiv", "decision": "keep"},
                {"atom_id": "A3.4", "candidate": "unordered equal-surplus ties", "transform": "heuristic", "decision": "drop"},
                {"atom_id": "A3.5", "candidate": "surplus-only objective", "transform": "relax", "decision": "drop"},
            ],
        },
        {
            "round": 4,
            "title": "Security Game-Theory Adversaries",
            "focus": "Model strategic attacks as paired claims with explicit anti-claims.",
            "atoms": [
                {"atom_id": "A4.1", "candidate": "roundtrip positive-profit detector", "transform": "relax", "decision": "keep"},
                {"atom_id": "A4.2", "candidate": "roundtrip no-profit invariant", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A4.3", "candidate": "LP fee-share guard theorem", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A4.4", "candidate": "fee-share irrelevant claim", "transform": "relax", "decision": "keep"},
                {"atom_id": "A4.5", "candidate": "single-check attack dismissal", "transform": "heuristic", "decision": "drop"},
            ],
        },
        {
            "round": 5,
            "title": "Security Oracle and Insurance Surface",
            "focus": "Probe oracle freshness and insurance fragility as structured duals.",
            "atoms": [
                {"atom_id": "A5.1", "candidate": "TWAP staleness effect", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A5.2", "candidate": "insurance vulnerability witness", "transform": "relax", "decision": "keep"},
                {"atom_id": "A5.3", "candidate": "insurance status-quo safety", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A5.4", "candidate": "oracle freshness as UX-only metric", "transform": "heuristic", "decision": "drop"},
                {"atom_id": "A5.5", "candidate": "unbounded volatility slack", "transform": "heuristic", "decision": "drop"},
            ],
        },
        {
            "round": 6,
            "title": "Automation Determinism Kernel",
            "focus": "Deterministic state roots, intent canonicalization, and replay-safety.",
            "atoms": [
                {"atom_id": "A6.1", "candidate": "state root determinism gate", "transform": "equiv", "decision": "keep"},
                {"atom_id": "A6.2", "candidate": "state root nondeterminism counterclaim", "transform": "relax", "decision": "keep"},
                {"atom_id": "A6.3", "candidate": "intent normal form tests", "transform": "equiv", "decision": "keep"},
                {"atom_id": "A6.4", "candidate": "intent regression existence", "transform": "relax", "decision": "keep"},
                {"atom_id": "A6.5", "candidate": "non-canonical agent ordering", "transform": "heuristic", "decision": "drop"},
            ],
        },
        {
            "round": 7,
            "title": "Tau Automation Contracts",
            "focus": "Automate agent/Tau paths with fail-closed gates and reproducible traces.",
            "atoms": [
                {"atom_id": "A7.1", "candidate": "tau gate replay pass", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A7.2", "candidate": "replay protection regression pass", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A7.3", "candidate": "state root replay triage", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A7.4", "candidate": "nonces without formal replay", "transform": "heuristic", "decision": "drop"},
                {"atom_id": "A7.5", "candidate": "probabilistic tie-break", "transform": "heuristic", "decision": "drop"},
            ],
        },
        {
            "round": 8,
            "title": "ESSO Kernel Selection",
            "focus": "Choose kernels with highest contradiction information gain per minute.",
            "atoms": [
                {"atom_id": "A8.1", "candidate": "swap_router_optimizer dual timeout", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A8.2", "candidate": "batch_auction_settler dual timeout", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A8.3", "candidate": "perp_game_theory_v1_fundingfix dual timeout", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A8.4", "candidate": "il_insurance_pool_v2 dual timeout", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A8.5", "candidate": "broad all-kernel sweep", "transform": "heuristic", "decision": "drop"},
            ],
        },
        {
            "round": 9,
            "title": "Lean Gate Selection",
            "focus": "Manual proof gates for high-leverage arithmetic/game-theory/determinism claims.",
            "atoms": [
                {"atom_id": "A9.1", "candidate": "BatchRefinementOrder theorem gate", "transform": "equiv", "decision": "keep"},
                {"atom_id": "A9.2", "candidate": "PerpGameTheory theorem gate", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A9.3", "candidate": "PerpInsuranceSafety theorem gate", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A9.4", "candidate": "DeterministicAgentTieBreakSort theorem gate", "transform": "equiv", "decision": "keep"},
                {"atom_id": "A9.5", "candidate": "proof-free promotion", "transform": "heuristic", "decision": "drop"},
            ],
        },
        {
            "round": 10,
            "title": "ZAG Operator Integration",
            "focus": "Integrate verified ZAG transfer signal; reject unstable operators.",
            "atoms": [
                {"atom_id": "A10.1", "candidate": "operator=data_structure_array", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A10.2", "candidate": "operator=algebraic_rewrite", "transform": "equiv", "decision": "keep"},
                {"atom_id": "A10.3", "candidate": "operator=invariant_chunking", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A10.4", "candidate": "operator=schema_switch_dc", "transform": "reduce", "decision": "drop"},
                {"atom_id": "A10.5", "candidate": "operator=partition_reduce", "transform": "reduce", "decision": "drop"},
            ],
        },
        {
            "round": 11,
            "title": "Budgeted Queue Policy",
            "focus": "Rank by expected information gain with heavy-first contradiction staging.",
            "atoms": [
                {"atom_id": "A11.1", "candidate": "ESSO timeout families first", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A11.2", "candidate": "static contradiction checks second", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A11.3", "candidate": "pytest/lean replay stabilization third", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A11.4", "candidate": "uniform random queue", "transform": "heuristic", "decision": "drop"},
                {"atom_id": "A11.5", "candidate": "single-family queue lock", "transform": "heuristic", "decision": "drop"},
            ],
        },
        {
            "round": 12,
            "title": "Cycle53 Synthesis",
            "focus": "Freeze top 100 hypotheses across UX/security/automation with deterministic recipes.",
            "atoms": [
                {"atom_id": "A12.1", "candidate": "100-hypothesis pack build", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A12.2", "candidate": "fast/heavy staged shards", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A12.3", "candidate": "queue by expected information gain", "transform": "reduce", "decision": "keep"},
                {"atom_id": "A12.4", "candidate": "manifest with expanded budgets", "transform": "restrict", "decision": "keep"},
                {"atom_id": "A12.5", "candidate": "direct autonomous run without supervision", "transform": "heuristic", "decision": "drop"},
            ],
        },
    ]
    return {
        "schema": "zenodex/cycle-ideation-rounds/v1",
        "created_at": _now_iso(),
        "cycle": 53,
        "source_evidence": {
            "roi_policy_cycle52": "runs/manual_morph_supervised/h066_supervised_cycle52/roi_policy_cycle52.json",
            "deep_insights_cycle52": "runs/manual_morph_supervised/h066_supervised_cycle52/deep_insights_cycle52.json",
            "zag_seed_summary": "external/ZAG/runs/zenodex_cycle53_ideation_seed/summary.json",
            "zag_seed_verify": "external/ZAG/runs/zenodex_cycle53_ideation_seed/run_verify.json (MCP structuredContent in execution log)",
            "zag_bridge_eval": "runs/manual_morph_supervised/h067_supervised_cycle53_zag_seed_eval/summary.json",
        },
        "rounds": rounds,
    }


def _build_hypotheses(cycle: int) -> list[dict[str, Any]]:
    idx = 1
    rows: list[dict[str, Any]] = []

    ux_pytests = [
        ("Comparative topology routing map", "tests/core/test_split_routing.py"),
        ("Exact-out stress-gated hop search", "tests/core/test_routing_exact_out_gate.py"),
        ("Surplus-aware batch local refinement", "tests/core/test_batch_clearing_b_refinement.py"),
        ("Global swap-topology batch refinement", "tests/core/test_batch_clearing_global_refinement.py"),
    ]
    for algo_name, path in ux_pytests:
        out, idx = _make_pytest_trio(
            cycle=cycle,
            start_idx=idx,
            category="ux",
            algorithm_name=algo_name,
            test_path=path,
            transform_main="reduce",
            source="manual_focus_ux_pytest",
        )
        rows.extend(out)

    security_pytests = [
        ("Adverse-selection incentive shield", "tests/core/test_perp_incentive_hazards.py"),
        ("Perp arithmetic hazard guardrail", "tests/core/test_perp_math_hazards.py"),
        ("Funding imbalance stabilizer", "tests/core/test_funding_rate_market.py"),
        ("Insurance-linked IL payout guard", "tests/core/test_il_futures.py"),
        ("CPMM exact-out semantics regression", "tests/core/test_cpmm.py"),
    ]
    for algo_name, path in security_pytests:
        out, idx = _make_pytest_trio(
            cycle=cycle,
            start_idx=idx,
            category="security",
            algorithm_name=algo_name,
            test_path=path,
            transform_main="restrict",
            source="manual_focus_security_pytest",
        )
        rows.extend(out)

    automation_pytests = [
        ("Tau command gate canonicalizer", "tests/integration/test_tau_gate.py"),
        ("Deterministic nonce replay firewall", "tests/integration/test_replay_protection.py"),
        ("State-root canonicalization pipeline", "tests/state/test_state_root_determinism.py"),
        ("Intent normalization automaton", "tests/core/test_intent_normal_form.py"),
    ]
    for algo_name, path in automation_pytests:
        out, idx = _make_pytest_trio(
            cycle=cycle,
            start_idx=idx,
            category="automation",
            algorithm_name=algo_name,
            test_path=path,
            transform_main="equiv",
            source="manual_focus_automation_pytest",
        )
        rows.extend(out)

    ux_static = [
        ("route_exact_out_2hop_value", "pfr-aware topology map"),
        ("route_exact_out_no_2hop_value", "counterclaim: no 2-hop advantage regime"),
        ("split_routing_gap", "argmax plateau split falsifier"),
        ("split_routing_no_gap", "deterministic split optimizer"),
        ("batch_clearing_gap_exists", "surplus-loss witness under naive ordering"),
        ("batch_clearing_no_gap", "global-refined surplus-preserving ordering"),
        ("settlement_normal_form", "algebraic rewrite settlement canonicalizer"),
        ("settlement_ordering_nondeterminism_exists", "counterclaim: ordering nondeterminism detector"),
        ("cpmm_overdelivery_witness", "overdelivery sentinel on exact-out path"),
        ("cpmm_no_overdelivery", "counterclaim: no exact-out overdelivery witness exists (expected false; regression sentinel)"),
    ]
    out, idx = _make_static_checks(
        cycle=cycle,
        start_idx=idx,
        category="ux",
        checks=ux_static,
        source="manual_focus_ux_static_zag_aligned",
    )
    rows.extend(out)

    security_static = [
        ("roundtrip_positive_profit_exists", "sandwich/roundtrip profitability detector"),
        ("roundtrip_no_positive_profit", "fee-protected roundtrip safety invariant"),
        ("il_insurance_vuln_presence", "insurance drain vulnerability witness"),
        ("il_insurance_status_quo_safe", "insurance pool safety equilibrium check"),
        ("perp_lp_fee_share_guard", "LP fee-share guard policy"),
        ("perp_lp_fee_share_irrelevant", "counterclaim: fee-share guard irrelevant"),
        ("perp_reserve_hardening_effect", "reserve hardening effectiveness"),
        ("perp_v2_invariants", "perp v2 invariant envelope"),
        ("perp_v2_invariant_break_exists", "counterclaim: perp v2 invariant break exists"),
        ("perp_v2_oracle_equiv", "oracle equivalence under protected updates"),
        ("perp_v2_oracle_divergence_exists", "counterclaim: oracle divergence witness"),
        ("curve_selection_safety", "curve selection manipulation safety bound"),
        ("curve_selection_unsafe_exists", "counterclaim: curve selection unsafe witness"),
        ("twap_staleness_effect", "twap staleness risk detector"),
    ]
    out, idx = _make_static_checks(
        cycle=cycle,
        start_idx=idx,
        category="security",
        checks=security_static,
        source="manual_focus_security_static",
    )
    rows.extend(out)

    automation_static = [
        ("state_root_determinism", "deterministic state-root constructor"),
        ("state_root_nondeterminism_exists", "counterclaim: state-root nondeterminism detector"),
        ("intent_normal_form_tests", "intent normal-form canonicalization proof gate"),
        ("intent_normal_form_regression_exists", "counterclaim: intent canonicalization regression exists"),
    ]
    out, idx = _make_static_checks(
        cycle=cycle,
        start_idx=idx,
        category="automation",
        checks=automation_static,
        source="manual_focus_automation_static",
    )
    rows.extend(out)

    esso_kernels = [
        ("ux", "src/kernels/dex/swap_router_optimizer.yaml", "topology-aware deterministic router"),
        ("ux", "src/kernels/dex/swap_router_optimizer_evolvable_v1.yaml", "adaptive routing policy envelope"),
        ("ux", "src/kernels/dex/batch_auction_settler_v1.yaml", "canonical AB batch settlement engine"),
        ("security", "src/kernels/dex/perp_game_theory_v1_fundingfix.yaml", "perp incentive anti-extraction fix"),
        ("security", "src/kernels/dex/il_insurance_pool_v2.yaml", "insurance firewall reparameterization"),
        ("security", "src/kernels/dex/volatility_cascade_controller_v1.yaml", "volatility cascade suppression controller"),
        ("automation", "src/kernels/dex/safety_proof_gate_v1.yaml", "proof-gated automation deployment"),
        ("automation", "src/kernels/dex/execution_receipts_v1.yaml", "deterministic receipt/state fold automation"),
    ]
    for cat, kernel, algo_name in esso_kernels:
        out, idx = _make_esso_triples(
            cycle=cycle,
            start_idx=idx,
            category=cat,
            kernels=[(kernel, algo_name)],
            source=f"manual_focus_{cat}_esso",
        )
        rows.extend(out)

    lean_files = [
        ("ux", "lean-mathlib/Proofs/BatchRefinementOrder.lean", "batch refinement canonical order proof"),
        ("security", "lean-mathlib/Proofs/PerpGameTheory.lean", "perp game-theory safety lemma"),
        ("security", "lean-mathlib/Proofs/PerpInsuranceSafety.lean", "insurance safety bound theorem"),
        ("automation", "lean-mathlib/Proofs/DeterministicAgentTieBreakSort.lean", "agent tie-break determinism theorem"),
    ]
    for cat, lean_path, algo_name in lean_files:
        out, idx = _make_lean_triples(
            cycle=cycle,
            start_idx=idx,
            category=cat,
            files=[(lean_path, algo_name)],
            source=f"manual_focus_{cat}_lean",
        )
        rows.extend(out)

    if len(rows) != 100:
        raise RuntimeError(f"expected 100 hypotheses, got {len(rows)}")

    seen: set[str] = set()
    for row in rows:
        hid = str(row.get("hypothesis_id", ""))
        if not hid:
            raise RuntimeError("empty hypothesis_id")
        if hid in seen:
            raise RuntimeError(f"duplicate hypothesis_id: {hid}")
        seen.add(hid)

    return rows


def _build_queue(rows: list[dict[str, Any]], *, cycle_name: str) -> dict[str, Any]:
    qrows: list[dict[str, Any]] = []
    for row in rows:
        qrows.append(
            {
                "hypothesis_id": row["hypothesis_id"],
                "check": row["falsification_recipe"],
                "status": "proposed",
                "transform": row["representation_shift_used"],
                "category": row.get("category", ""),
                "duration_s": int(row.get("timeout_s", 0)),
                "expected_information_gain": _expected_ig(row),
            }
        )
    qrows.sort(
        key=lambda x: (
            -float(x["expected_information_gain"]),
            str(x["category"]),
            str(x["check"]),
        )
    )
    return {
        "created_at": int(time.time()),
        "cycle": cycle_name,
        "queue": qrows,
    }


def _pack(rows: list[dict[str, Any]]) -> dict[str, Any]:
    return {"count": len(rows), "hypotheses": rows}


def _markdown_summary(
    *,
    manifest: dict[str, Any],
    totals: dict[str, int],
    queue: dict[str, Any],
) -> str:
    top = queue.get("queue", [])[:15]
    lines = [
        "# Cycle 53 Focus Preparation Summary",
        "",
        f"- created_at: {manifest.get('created_at')}",
        f"- run_name: {manifest.get('run_name')}",
        f"- hypothesis_count: {sum(totals.values())}",
        f"- category_totals: ux={totals.get('ux', 0)} security={totals.get('security', 0)} automation={totals.get('automation', 0)}",
        "",
        "## Budgets",
        f"- max_depth: {manifest['budgets']['max_depth']}",
        f"- max_width: {manifest['budgets']['max_width']}",
        f"- per_epoch_compute_budget: {manifest['budgets']['per_epoch_compute_budget']}",
        f"- exploration_ratio: {manifest['budgets']['exploration_ratio']}",
        f"- exploitation_ratio: {manifest['budgets']['exploitation_ratio']}",
        "",
        "## Top Queue (by expected information gain)",
    ]
    for row in top:
        lines.append(
            f"- {row['hypothesis_id']} | {row['check']} | eig={row['expected_information_gain']:.2f} | category={row['category']}"
        )
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description="Prepare cycle53 focus artifacts for UX/security/automation algorithm discovery.")
    ap.add_argument("--cycle", type=int, default=53)
    args = ap.parse_args()

    cycle = int(args.cycle)
    cycle_name = f"h{cycle + 14:03d}_supervised_cycle{cycle}" if cycle == 53 else f"supervised_cycle{cycle}"
    # Preserve historical naming for this repo's current run.
    cycle_name = "h067_supervised_cycle53"

    hypotheses = _build_hypotheses(cycle)

    totals = {"ux": 0, "security": 0, "automation": 0}
    for row in hypotheses:
        cat = str(row.get("category", ""))
        totals[cat] = totals.get(cat, 0) + 1

    queue = _build_queue(hypotheses, cycle_name=cycle_name)
    fast_rows = [r for r in hypotheses if not str(r["falsification_recipe"]).startswith("esso_")]
    heavy_rows = [r for r in hypotheses if str(r["falsification_recipe"]).startswith("esso_")]

    ideation = _build_ideation_log()

    manifest = {
        "schema": "zenodex/manual-cycle-manifest/v1",
        "created_at": _now_iso(),
        "run_name": cycle_name,
        "cycle": cycle,
        "selection": {
            "target": 100,
            "selected": len(hypotheses),
            "carryover": 0,
            "novel": len(hypotheses),
        },
        "budgets": {
            "max_depth": 12,
            "max_width": 20,
            "per_epoch_compute_budget": 260,
            "exploration_ratio": 0.76,
            "exploitation_ratio": 0.24,
        },
        "focus": {
            "primary": ["ux_algorithm_innovation", "security_algorithm_innovation", "deterministic_automation_algorithms"],
            "method": "manual_supervised_with_zag_seeded_candidates",
        },
        "inputs": {
            "roi_policy_cycle52": "runs/manual_morph_supervised/h066_supervised_cycle52/roi_policy_cycle52.json",
            "deep_insights_cycle52": "runs/manual_morph_supervised/h066_supervised_cycle52/deep_insights_cycle52.json",
            "zag_seed_run": "external/ZAG/runs/zenodex_cycle53_ideation_seed",
            "zag_seed_bridge_eval": "runs/manual_morph_supervised/h067_supervised_cycle53_zag_seed_eval",
        },
    }

    RUN_DIR.mkdir(parents=True, exist_ok=True)
    _write_json(RUN_DIR / "cycle_manifest_focus.json", manifest)
    _write_json(RUN_DIR / "ideation_iterations_cycle53.json", ideation)
    _write_json(RUN_DIR / "hypothesis_pack_100_focus_ux_security_automation.json", _pack(hypotheses))
    _write_json(RUN_DIR / "hypothesis_pack_fast_focus.json", _pack(fast_rows))
    _write_json(RUN_DIR / "hypothesis_pack_heavy_focus.json", _pack(heavy_rows))
    _write_json(RUN_DIR / "next_experiment_queue_focus.json", queue)
    _write_text(
        RUN_DIR / "prep_summary_cycle53_focus.md",
        _markdown_summary(manifest=manifest, totals=totals, queue=queue),
    )

    print(
        json.dumps(
            {
                "ok": True,
                "run_dir": str(RUN_DIR),
                "cycle": cycle,
                "counts": {
                    "total": len(hypotheses),
                    "ux": totals.get("ux", 0),
                    "security": totals.get("security", 0),
                    "automation": totals.get("automation", 0),
                    "fast": len(fast_rows),
                    "heavy": len(heavy_rows),
                },
                "top_queue": queue.get("queue", [])[:5],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

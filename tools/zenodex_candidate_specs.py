#!/usr/bin/env python3
"""Reusable deterministic ZenoDEX research candidate specifications."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
VALID_TRANSFORMS = {"equiv", "reduce", "relax", "restrict", "heuristic"}


def _safe_token(text: str, *, max_len: int = 120) -> str:
    token = re.sub(r"[^A-Za-z0-9_.-]+", "_", str(text)).strip("._")
    if not token:
        token = "x"
    return token[:max_len]


def _discover_auto_pytest_files(max_files: int) -> list[str]:
    roots = [
        ROOT / "tests" / "core",
        ROOT / "tests" / "state",
        ROOT / "tests" / "formal",
    ]
    files: list[str] = []
    for root in roots:
        if not root.exists():
            continue
        for path in sorted(root.rglob("test_*.py")):
            if not path.is_file():
                continue
            rel = str(path.relative_to(ROOT))
            files.append(rel)
    dedup = sorted(set(files))
    lim = max(0, int(max_files))
    if lim <= 0:
        return []
    return dedup[:lim]


def _transform_for_pytest_file(path: str) -> tuple[str, list[int], list[int]]:
    low = path.lower()
    if any(tok in low for tok in ("invariant", "safety", "hazard", "determin", "parity", "root", "formal", "proof")):
        return ("restrict", [2, 0, 1, -1, 1], [1, 0, 1, -1, 2])
    return ("equiv", [1, 0, 1, -1, 2], [1, 0, 1, -1, 2])


def _auto_pytest_hypothesis_specs(
    *,
    max_auto_pytest_files: int,
    offset_files: int = 0,
    replay_repeats: int = 3,
) -> list[dict[str, Any]]:
    specs: list[dict[str, Any]] = []
    files_all = _discover_auto_pytest_files(max_auto_pytest_files + max(0, int(offset_files)))
    start = max(0, int(offset_files))
    stop = start + max(0, int(max_auto_pytest_files))
    for path in files_all[start:stop]:
        slug = _safe_token(path.replace("/", "_").replace(".py", ""), max_len=80).lower()
        gate_transform, gate_delta, replay_delta = _transform_for_pytest_file(path)
        rep = max(2, int(replay_repeats))

        specs.append(
            {
                "hypothesis_id": f"H_pytest_gate_{slug}_v1",
                "mechanism_change": f"Use `{path}` as a fail-closed acceptance gate for related mechanism edits.",
                "representation_shift_used": gate_transform,
                "expected_metric_delta": gate_delta,
                "null_hypothesis": f"`{path}` is unstable or failing under bounded local replay.",
                "falsification_recipe": f"pytest_pass::{path}",
                "support_recipe": f"pytest_pass::{path}",
                "formal_obligations": [
                    f"`{path}` passes deterministically in local replay",
                    "No UNKNOWN/TIMEOUT is treated as support",
                ],
                "risk_modes": [
                    "Test fixture under-coverage for unseen edge cases",
                    "Local environment skew vs production constraints",
                ],
                "status": "proposed",
                "timeout_s": 90,
            }
        )
        specs.append(
            {
                "hypothesis_id": f"H_pytest_unstable_{slug}_v1",
                "mechanism_change": f"Assume `{path}` still exhibits bounded regressions/flakiness (status-quo fragility claim).",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": f"Bounded regressions exist in `{path}`.",
                "falsification_recipe": f"pytest_fail::{path}",
                "support_recipe": f"pytest_fail::{path}",
                "formal_obligations": [
                    f"Produce deterministic failing witness for `{path}`",
                    "Reject flaky-only failures as inconclusive",
                ],
                "risk_modes": [
                    "False alarms from environment-sensitive tests",
                    "Conflating harness issues with mechanism issues",
                ],
                "status": "proposed",
                "timeout_s": 90,
            }
        )
        specs.append(
            {
                "hypothesis_id": f"H_pytest_replay{rep}_{slug}_v1",
                "mechanism_change": f"Require {rep}x replay stability of `{path}` before promotion of nearby mechanism changes.",
                "representation_shift_used": "reduce",
                "expected_metric_delta": replay_delta,
                "null_hypothesis": f"`{path}` is not stable across {rep} deterministic replays.",
                "falsification_recipe": f"pytest_repeat{rep}::{path}",
                "support_recipe": f"pytest_repeat{rep}::{path}",
                "formal_obligations": [
                    f"All {rep} replays pass with deterministic verdicts",
                    "Any replay timeout/error is inconclusive, not support",
                ],
                "risk_modes": [
                    "Extra CI/runtime cost from repeated checks",
                    "Replay determinism can still miss rare timing edges",
                ],
                "status": "proposed",
                "timeout_s": 120,
            }
        )
    return specs


def _candidate_specs(
    *,
    auto_pytest_hypotheses: bool = False,
    max_auto_pytest_files: int = 0,
    auto_pytest_offset_files: int = 0,
    auto_pytest_replay_repeats: int = 3,
    target_hypotheses: int = 0,
) -> list[dict[str, Any]]:
    # All hypotheses must carry the required schema from the user prompt.
    specs: list[dict[str, Any]] = [
        {
            "hypothesis_id": "H_split_routing_adaptive_bruteforce_v1",
            "mechanism_change": "Use adaptive brute-force fallback for small split-routing windows to eliminate heuristic output gaps.",
            "representation_shift_used": "reduce",
            "expected_metric_delta": [0, 2, 2, -1, 1],
            "null_hypothesis": "Current split routing has no actionable optimality gap under bounded search.",
            "falsification_recipe": "split_routing_gap",
            "support_recipe": "split_routing_gap",
            "formal_obligations": [
                "Deterministic tie-break on equal-route outputs",
                "No negative output amounts",
                "No regression in route validity constraints",
            ],
            "risk_modes": [
                "Search-time blowups for larger pool counts",
                "Overfitting to bounded miner domains",
            ],
            "status": "proposed",
            "timeout_s": 180,
        },
        {
            "hypothesis_id": "H_split_routing_status_quo_sufficient_v1",
            "mechanism_change": "Keep current split-routing heuristic unchanged (status-quo claim: bounded search has no actionable optimality gap).",
            "representation_shift_used": "equiv",
            "expected_metric_delta": [0, 0, 0, 1, 1],
            "null_hypothesis": "Status-quo split routing already has no bounded optimality gap.",
            "falsification_recipe": "split_routing_no_gap",
            "support_recipe": "split_routing_no_gap",
            "formal_obligations": [
                "No witness with positive brute-force minus heuristic gap in bounded domains",
                "Deterministic tie-break stability under status-quo params",
            ],
            "risk_modes": [
                "Hidden execution quality regression if bounded gap exists",
                "Overconfidence from narrow sampling",
            ],
            "status": "proposed",
            "timeout_s": 180,
        },
        {
            "hypothesis_id": "H_twap_staleness_cap_tightening_v1",
            "mechanism_change": "Tighten TWAP staleness windows and enforce stale-state fail-closed gating in price consumers.",
            "representation_shift_used": "restrict",
            "expected_metric_delta": [2, -1, 1, 0, 1],
            "null_hypothesis": "Reducing staleness cap does not materially reduce manipulation deviation.",
            "falsification_recipe": "twap_staleness_effect",
            "support_recipe": "twap_staleness_effect",
            "formal_obligations": [
                "Staleness transitions are deterministic",
                "No read path bypasses stale guards",
                "TWAP monotonic accumulation remains bounded",
            ],
            "risk_modes": [
                "Data providers miss update cadence",
                "Operational liveness impact during network delays",
            ],
            "status": "proposed",
            "timeout_s": 180,
        },
        {
            "hypothesis_id": "H_perp_oracle_clamp_tightening_v1",
            "mechanism_change": "Tighten perp settlement clamp (`max_move_bps`) to reduce profitable oracle manipulation envelopes.",
            "representation_shift_used": "restrict",
            "expected_metric_delta": [2, -1, 1, 0, 1],
            "null_hypothesis": "Tighter clamp does not reduce best attack profitability.",
            "falsification_recipe": "perp_clamp_profit",
            "support_recipe": "perp_clamp_profit",
            "formal_obligations": [
                "Bounded clamp remains monotone in max_move_bps",
                "No sign inversion in PnL due to clamp arithmetic",
                "Deterministic clamp tie-break rules",
            ],
            "risk_modes": [
                "Excessive clamp creates pricing lag",
                "Capital efficiency degradation in volatile periods",
            ],
            "status": "proposed",
            "timeout_s": 180,
        },
        {
            "hypothesis_id": "H_batch_greedy_ab_default_v1",
            "mechanism_change": "Promote greedy AB ordering to default for eligible single-direction batches while preserving fallback guards.",
            "representation_shift_used": "heuristic",
            "expected_metric_delta": [0, 1, 2, -1, 2],
            "null_hypothesis": "Greedy AB ordering cannot satisfy current invariants and determinism constraints.",
            "falsification_recipe": "batch_greedy_invariants",
            "support_recipe": "batch_greedy_invariants",
            "formal_obligations": [
                "(A,B) objective monotonicity vs baseline ordering",
                "Conservation checks on settlement outputs",
                "Deterministic ordering under tie cases",
            ],
            "risk_modes": [
                "Pathological slippage in mixed-direction batches",
                "Performance overhead for large intent sets",
            ],
            "status": "proposed",
            "timeout_s": 120,
        },
        {
            "hypothesis_id": "H_cpmm_esso_formal_gate_v1",
            "mechanism_change": "Enforce ESSO verify-multi as a promotion gate for CPMM safety-critical kernel changes.",
            "representation_shift_used": "equiv",
            "expected_metric_delta": [2, 0, 0, -1, 2],
            "null_hypothesis": "Current CPMM kernel cannot be reliably verified under deterministic ESSO gates.",
            "falsification_recipe": "esso_cpmm_verify",
            "support_recipe": "esso_cpmm_verify",
            "formal_obligations": [
                "Inductiveness queries remain solver-agreed",
                "Determinism fingerprints stable across trials",
                "No UNKNOWN/TIMEOUT acceptance",
            ],
            "risk_modes": [
                "Solver version drift",
                "Timeout sensitivity on larger state bounds",
            ],
            "status": "proposed",
            "timeout_s": 180,
        },
        {
            "hypothesis_id": "H_batch_canonical_lean_gate_v1",
            "mechanism_change": "Use Lean canonicalization checks as a hard gate for deterministic batch tie-break claims.",
            "representation_shift_used": "equiv",
            "expected_metric_delta": [1, 0, 1, -1, 2],
            "null_hypothesis": "Canonicalization lemma cannot be machine-checked in current local toolchain.",
            "falsification_recipe": "lean_batch_canonical",
            "support_recipe": "lean_batch_canonical",
            "formal_obligations": [
                "Lexicographic tie-break equivalence theorem compiles",
                "No `sorry` or unverifiable assumptions introduced",
                "Build is reproducible on local toolchain",
            ],
            "risk_modes": [
                "Mathlib/toolchain drift",
                "Proof brittleness under refactors",
            ],
            "status": "proposed",
            "timeout_s": 180,
        },
        {
            "hypothesis_id": "H_roundtrip_profit_guard_v1",
            "mechanism_change": "Add roundtrip-profit regression guard for AMM curve changes (reject curves with positive 2-swap profit witness).",
            "representation_shift_used": "reduce",
            "expected_metric_delta": [1, 0, 1, -1, 1],
            "null_hypothesis": "Current curve implementations already exhibit positive 2-swap profit under bounded sweep.",
            "falsification_recipe": "roundtrip_no_positive_profit",
            "support_recipe": "roundtrip_no_positive_profit",
            "formal_obligations": [
                "No positive 2-swap roundtrip profit under bounded deterministic sweep",
                "Regression guard deterministic with fixed grid",
            ],
            "risk_modes": [
                "Bounded sweep misses higher-dimensional exploits",
                "Guard overfits current integer domains",
            ],
            "status": "proposed",
            "timeout_s": 120,
        },
        {
            "hypothesis_id": "H_roundtrip_positive_profit_exists_v1",
            "mechanism_change": "Assume current curves admit profitable 2-swap roundtrip and require emergency hardening.",
            "representation_shift_used": "relax",
            "expected_metric_delta": [1, -1, 0, -1, 0],
            "null_hypothesis": "There is bounded-domain evidence of positive roundtrip profit in current curves.",
            "falsification_recipe": "roundtrip_positive_profit_exists",
            "support_recipe": "roundtrip_positive_profit_exists",
            "formal_obligations": [
                "Construct positive-profit witness if it exists",
                "Ensure witness is reproducible under deterministic grid",
            ],
            "risk_modes": [
                "False positives from malformed arithmetic assumptions",
                "Bounded search may miss larger-domain witnesses",
            ],
            "status": "proposed",
            "timeout_s": 120,
        },
    ]
    specs.extend(
        [
            {
                "hypothesis_id": "H_batch_ab_gap_detector_guard_v1",
                "mechanism_change": "Add AB-gap detector plus bounded optimizer fallback when limit-price ordering leaves material executable volume.",
                "representation_shift_used": "reduce",
                "expected_metric_delta": [1, 1, 2, -1, 1],
                "null_hypothesis": "No bounded batch-clearing A-gap exists beyond trivial noise.",
                "falsification_recipe": "batch_clearing_gap_exists",
                "support_recipe": "batch_clearing_gap_exists",
                "formal_obligations": [
                    "A-gap witness reproducible under fixed seed",
                    "Fallback keeps deterministic tie-break and conservation",
                    "Optimizer only activates when gap threshold is met",
                ],
                "risk_modes": [
                    "Bounded witness domains under-represent production batches",
                    "Optimizer overhead in large intent sets",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_batch_limit_price_status_quo_optimal_v1",
                "mechanism_change": "Retain status-quo limit-price ordering as globally sufficient for bounded batch clearing.",
                "representation_shift_used": "equiv",
                "expected_metric_delta": [0, 0, 0, 1, 2],
                "null_hypothesis": "No bounded A-gap witness exists for current ordering.",
                "falsification_recipe": "batch_clearing_no_gap",
                "support_recipe": "batch_clearing_no_gap",
                "formal_obligations": [
                    "No positive A-gap witness in deterministic search domains",
                    "Ordering remains deterministic under ties",
                ],
                "risk_modes": [
                    "Execution quality regression hidden by status-quo assumption",
                    "Search incompleteness in larger spaces",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_route_exact_out_2hop_enable_v1",
                "mechanism_change": "Enable 2-hop exact-out routing when witness shows strictly lower required input than direct path.",
                "representation_shift_used": "reduce",
                "expected_metric_delta": [0, 1, 2, -1, 0],
                "null_hypothesis": "No reproducible 2-hop exact-out witness improves over direct route.",
                "falsification_recipe": "route_exact_out_2hop_value",
                "support_recipe": "route_exact_out_2hop_value",
                "formal_obligations": [
                    "Python and Z3 checker agreement on witness arithmetic",
                    "Deterministic tie-break for equal-input routes",
                    "Route validity constraints preserved",
                ],
                "risk_modes": [
                    "Witness may be sparse outside bounded domains",
                    "Path explosion for large route graphs",
                ],
                "status": "proposed",
                "timeout_s": 60,
            },
            {
                "hypothesis_id": "H_route_exact_out_direct_only_sufficient_v1",
                "mechanism_change": "Keep direct-only exact-out routing (status-quo claim: 2-hop does not add value).",
                "representation_shift_used": "equiv",
                "expected_metric_delta": [0, 0, 0, 1, 1],
                "null_hypothesis": "Direct-only exact-out is sufficient in bounded witness domains.",
                "falsification_recipe": "route_exact_out_no_2hop_value",
                "support_recipe": "route_exact_out_no_2hop_value",
                "formal_obligations": [
                    "No 2-hop strict-improvement witness in deterministic check",
                    "Direct route remains deterministic and valid",
                ],
                "risk_modes": [
                    "Execution quality loss from missed multi-hop opportunities",
                    "False confidence from narrow witness families",
                ],
                "status": "proposed",
                "timeout_s": 60,
            },
            {
                "hypothesis_id": "H_il_insurance_hardening_required_v1",
                "mechanism_change": "Require IL insurance hardening: strict position verification, premium/coverage coupling, and exposure reconciliation.",
                "representation_shift_used": "restrict",
                "expected_metric_delta": [3, -1, 1, 0, 1],
                "null_hypothesis": "Current IL insurance logic has no critical/high bounded vulnerabilities.",
                "falsification_recipe": "il_insurance_vuln_presence",
                "support_recipe": "il_insurance_vuln_presence",
                "formal_obligations": [
                    "Critical/high vulnerability witnesses are reproducible",
                    "Hardening eliminates unbacked claim paths",
                    "Exposure accounting converges after claim processing",
                ],
                "risk_modes": [
                    "Hardening can reduce capital flexibility",
                    "Migration risk for existing IL coverage positions",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_il_insurance_status_quo_safe_v1",
                "mechanism_change": "Keep current IL insurance mechanism unchanged (status-quo safety claim).",
                "representation_shift_used": "equiv",
                "expected_metric_delta": [0, 0, 0, 1, 1],
                "null_hypothesis": "Current IL insurance is already safe against critical/high abuse.",
                "falsification_recipe": "il_insurance_status_quo_safe",
                "support_recipe": "il_insurance_status_quo_safe",
                "formal_obligations": [
                    "No critical/high findings in bounded vulnerability suite",
                    "Claim and exposure bookkeeping remain consistent",
                ],
                "risk_modes": [
                    "Catastrophic safety gap if claim is false",
                    "Latency in detecting latent exploit vectors",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_settlement_normal_form_gate_v1",
                "mechanism_change": "Promote settlement normal-form canonicalization checks as deterministic gate before acceptance.",
                "representation_shift_used": "equiv",
                "expected_metric_delta": [1, 0, 1, -1, 2],
                "null_hypothesis": "Normal-form canonicalization checks do not hold under deterministic regression cases.",
                "falsification_recipe": "settlement_normal_form",
                "support_recipe": "settlement_normal_form",
                "formal_obligations": [
                    "Semantically equivalent settlements normalize identically",
                    "Optional/missing fields cannot break canonical order",
                    "Fill ordering tie-break remains deterministic",
                ],
                "risk_modes": [
                    "Canonicalization overhead on large batches",
                    "Potential blind spots in untested edge structures",
                ],
                "status": "proposed",
                "timeout_s": 60,
            },
            {
                "hypothesis_id": "H_settlement_ordering_nondeterminism_exists_v1",
                "mechanism_change": "Assume settlement output canonicalization is still nondeterministic in bounded edge cases.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, 0, -1, -1],
                "null_hypothesis": "Nondeterminism exists in bounded normal-form tests.",
                "falsification_recipe": "settlement_ordering_nondeterminism_exists",
                "support_recipe": "settlement_ordering_nondeterminism_exists",
                "formal_obligations": [
                    "Construct reproducible mismatch between equivalent settlements",
                    "Show canonicalization non-idempotence or ordering drift",
                ],
                "risk_modes": [
                    "False alarm from malformed synthetic fixtures",
                    "Under-approximation of production payload variety",
                ],
                "status": "proposed",
                "timeout_s": 60,
            },
            {
                "hypothesis_id": "H_lp_rounding_regression_gate_v1",
                "mechanism_change": "Maintain LP rounding regression suite as hard gate for liquidity-accounting changes.",
                "representation_shift_used": "restrict",
                "expected_metric_delta": [1, 0, 0, -1, 1],
                "null_hypothesis": "LP rounding tests are unstable or currently failing.",
                "falsification_recipe": "lp_rounding_tests",
                "support_recipe": "lp_rounding_tests",
                "formal_obligations": [
                    "Zero failing deterministic LP rounding tests",
                    "No split-claim arithmetic drift under tested cases",
                ],
                "risk_modes": [
                    "Coverage gaps in untested high-precision ranges",
                    "False confidence from narrow deterministic fixtures",
                ],
                "status": "proposed",
                "timeout_s": 60,
            },
            {
                "hypothesis_id": "H_perp_fee_share_full_capture_guard_v1",
                "mechanism_change": "Set protocol fee share to full capture in bounded perps manipulation envelope to neutralize LP-assisted attack profit.",
                "representation_shift_used": "restrict",
                "expected_metric_delta": [2, -1, 1, 0, 1],
                "null_hypothesis": "Fee-share setting does not materially change LP-assisted manipulation feasibility.",
                "falsification_recipe": "perp_lp_fee_share_guard",
                "support_recipe": "perp_lp_fee_share_guard",
                "formal_obligations": [
                    "Attack exists for partial fee shares but not at full capture in bounded sweep",
                    "Transition preserves deterministic settlement rules",
                ],
                "risk_modes": [
                    "LP incentives degrade under full capture",
                    "Attack may migrate to alternate mechanism channel",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_perp_fee_share_irrelevant_v1",
                "mechanism_change": "Assume protocol fee-share choice is irrelevant to LP-assisted oracle-manipulation envelope.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [0, 1, -1, 0, 0],
                "null_hypothesis": "Fee share has no bounded effect on attack success.",
                "falsification_recipe": "perp_lp_fee_share_irrelevant",
                "support_recipe": "perp_lp_fee_share_irrelevant",
                "formal_obligations": [
                    "Attack feasibility invariant across tested fee-share settings",
                ],
                "risk_modes": [
                    "Misleading aggregate metric hiding boundary discontinuities",
                    "Overfitting to single reserve regime",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_perp_high_reserve_hardening_v1",
                "mechanism_change": "Raise effective reserve floor to shrink bounded manipulation profitability envelope in perps settlement.",
                "representation_shift_used": "restrict",
                "expected_metric_delta": [2, -1, 1, 0, 0],
                "null_hypothesis": "Higher reserve regime does not reduce bounded best attack profit.",
                "falsification_recipe": "perp_reserve_hardening_effect",
                "support_recipe": "perp_reserve_hardening_effect",
                "formal_obligations": [
                    "Best attack profit decreases monotonically across tested reserve buckets",
                    "No arithmetic sign inversions in bounded sweeps",
                ],
                "risk_modes": [
                    "Capital lockup increases",
                    "Market depth assumptions may shift over time",
                ],
                "status": "proposed",
                "timeout_s": 120,
            },
            {
                "hypothesis_id": "H_curve_sum_boost_exact_out_candidate_v1",
                "mechanism_change": "Adopt sum-boost curve candidate in bounded regimes where exact-out requires lower input than CPMM without extra non-minimality.",
                "representation_shift_used": "heuristic",
                "expected_metric_delta": [0, 1, 1, -1, 0],
                "null_hypothesis": "Sum-boost provides no bounded exact-out input advantage vs CPMM.",
                "falsification_recipe": "curve_sum_boost_exact_out_advantage",
                "support_recipe": "curve_sum_boost_exact_out_advantage",
                "formal_obligations": [
                    "Exact-out lower-input win count for sum-boost exceeds CPMM in bounded sweep",
                    "No increase in non-minimal rate vs CPMM in the same sweep",
                ],
                "risk_modes": [
                    "Heuristic curve may harm other market regimes",
                    "Bounded win pattern may not extrapolate",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_cpmm_exact_out_semantics_and_gap_monitoring_v1",
                "mechanism_change": "Treat CPMM exact-out semantics + overdelivery-gap visibility as a hard regression gate: exact-out reserve updates must use requested amount_out, and receipts must expose amount_out_quote and overdelivery_gap for monitoring and optional policy guards.",
                "representation_shift_used": "restrict",
                "expected_metric_delta": [2, 0, 1, -1, 2],
                "null_hypothesis": "CPMM exact-out semantics or overdelivery-gap visibility regressed under the regression suite.",
                "falsification_recipe": "pytest_pass::tests/core/test_cpmm.py",
                "support_recipe": "pytest_pass::tests/core/test_cpmm.py",
                "formal_obligations": [
                    "`tests/core/test_cpmm.py` passes deterministically",
                    "Exact-out post-state debits reserve_out by requested amount_out (not amount_out_quote)",
                    "Kernel exposes amount_out_quote and overdelivery_gap for monitoring",
                ],
                "risk_modes": [
                    "Tests may miss extreme small-reserve regimes; add bounded miners for monitoring",
                    "Policy guards can reject valid small trades if too strict",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_cpmm_overdelivery_witness_exists_v2",
                "mechanism_change": "Overdelivery witness exists under bounded exact-out CPMM search; treat as expected rounding asymmetry and keep as a regression sentinel (it should remain reproducible unless semantics change).",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": "No bounded exact-out overdelivery witness exists under the current CPMM semantics.",
                "falsification_recipe": "cpmm_overdelivery_witness",
                "support_recipe": "cpmm_overdelivery_witness",
                "formal_obligations": [
                    "Overdelivery witness remains reproducible under fixed seed/budget",
                    "No timeout/error interpreted as support",
                ],
                "risk_modes": [
                    "Bounded witness does not characterize severity distribution",
                    "Semantic changes could invalidate expected witness class; update diagnostics accordingly",
                ],
                "status": "proposed",
                "timeout_s": 60,
            },
            {
                "hypothesis_id": "H_intent_normal_form_gate_v1",
                "mechanism_change": "Treat intent normal-form regression tests as a hard determinism and safety gate before promoting intent-processing changes.",
                "representation_shift_used": "equiv",
                "expected_metric_delta": [1, 0, 1, -1, 2],
                "null_hypothesis": "Intent normal-form tests are unstable or failing under current implementation.",
                "falsification_recipe": "intent_normal_form_tests",
                "support_recipe": "intent_normal_form_tests",
                "formal_obligations": [
                    "Intent canonicalization is deterministic",
                    "Equivalent intents normalize to the same representation",
                    "Parser/normalizer invariants hold under regression fixtures",
                ],
                "risk_modes": [
                    "Untested payload shapes outside regression fixtures",
                    "Overhead if normalization grows in complexity",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_intent_normal_form_status_quo_unstable_v1",
                "mechanism_change": "Assume current intent normal-form behavior remains unstable in bounded regression tests.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": "Intent-normalization regressions are present.",
                "falsification_recipe": "intent_normal_form_regression_exists",
                "support_recipe": "intent_normal_form_regression_exists",
                "formal_obligations": [
                    "Produce deterministic failing witness in intent normal-form tests",
                    "Show canonical representation mismatch under equivalent inputs",
                ],
                "risk_modes": [
                    "False signal from flaky test harness",
                    "Synthetic fixture bias",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_state_root_determinism_gate_v1",
                "mechanism_change": "Promote state-root determinism tests to hard acceptance gate for state transition changes.",
                "representation_shift_used": "equiv",
                "expected_metric_delta": [2, 0, 0, -1, 2],
                "null_hypothesis": "State root determinism tests are not stable under current code path.",
                "falsification_recipe": "state_root_determinism",
                "support_recipe": "state_root_determinism",
                "formal_obligations": [
                    "Identical state transitions yield identical roots",
                    "No hidden nondeterministic map/set ordering in root computation",
                    "Regression suite remains green across repeated runs",
                ],
                "risk_modes": [
                    "Determinism only validated for covered state slices",
                    "Potential performance overhead from deterministic sorting",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_state_root_nondeterminism_exists_v1",
                "mechanism_change": "Assume state-root nondeterminism still exists in bounded regression domains.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": "State root nondeterminism exists for tested transitions.",
                "falsification_recipe": "state_root_nondeterminism_exists",
                "support_recipe": "state_root_nondeterminism_exists",
                "formal_obligations": [
                    "Exhibit reproducible root mismatch under equivalent transitions",
                    "Trace mismatch to canonicalization/ordering source",
                ],
                "risk_modes": [
                    "False positives from unstable fixtures",
                    "Insufficient state-space coverage",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_cpmm_ref_parity_gate_v1",
                "mechanism_change": "Enforce CPMM reference parity tests as fail-closed promotion gate for cpmm code-path edits.",
                "representation_shift_used": "equiv",
                "expected_metric_delta": [2, 0, 1, -1, 2],
                "null_hypothesis": "CPMM implementation and generated reference diverge in current regression suite.",
                "falsification_recipe": "cpmm_ref_parity",
                "support_recipe": "cpmm_ref_parity",
                "formal_obligations": [
                    "Implementation output equals reference output on bounded fixtures",
                    "Rounding edge cases remain parity-safe",
                    "No hidden branch divergence under tested parameters",
                ],
                "risk_modes": [
                    "Parity blind spots outside fixture envelope",
                    "Reference drift not reflected in tests",
                ],
                "status": "proposed",
                "timeout_s": 120,
            },
            {
                "hypothesis_id": "H_cpmm_ref_parity_broken_v1",
                "mechanism_change": "Assume CPMM implementation/reference parity is currently broken in bounded tests.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": "No implementation/reference divergence exists in bounded CPMM parity tests.",
                "falsification_recipe": "cpmm_ref_parity_broken",
                "support_recipe": "cpmm_ref_parity_broken",
                "formal_obligations": [
                    "Produce deterministic failing CPMM parity fixture",
                    "Identify branch or arithmetic source of mismatch",
                ],
                "risk_modes": [
                    "False mismatch from stale generated references",
                    "Low external validity of narrow fixture sets",
                ],
                "status": "proposed",
                "timeout_s": 120,
            },
            {
                "hypothesis_id": "H_dex_v8_ref_parity_gate_v1",
                "mechanism_change": "Use DEX v8 reference parity tests as a strict acceptance gate for mechanism-level changes.",
                "representation_shift_used": "equiv",
                "expected_metric_delta": [2, 0, 1, -1, 2],
                "null_hypothesis": "DEX v8 implementation and reference diverge under current parity suite.",
                "falsification_recipe": "dex_v8_ref_parity",
                "support_recipe": "dex_v8_ref_parity",
                "formal_obligations": [
                    "End-to-end parity holds for covered v8 traces",
                    "Deterministic output equality under replay",
                    "No invariant regressions hidden by reference mismatch",
                ],
                "risk_modes": [
                    "Coverage gaps in parity fixture universe",
                    "Reference artifacts lagging implementation semantics",
                ],
                "status": "proposed",
                "timeout_s": 120,
            },
            {
                "hypothesis_id": "H_dex_v8_ref_parity_broken_v1",
                "mechanism_change": "Assume DEX v8 implementation/reference parity is currently broken on bounded fixtures.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": "No deterministic v8 parity break exists in bounded regression tests.",
                "falsification_recipe": "dex_v8_ref_parity_broken",
                "support_recipe": "dex_v8_ref_parity_broken",
                "formal_obligations": [
                    "Demonstrate reproducible parity mismatch on bounded fixture",
                    "Confirm mismatch is not harness artifact",
                ],
                "risk_modes": [
                    "False alarm from fixture drift",
                    "Unrepresentative failure mode",
                ],
                "status": "proposed",
                "timeout_s": 120,
            },
            {
                "hypothesis_id": "H_perp_v2_invariants_gate_v1",
                "mechanism_change": "Gate perps-v2 mechanism edits on invariant regression suite to prevent latent safety regressions.",
                "representation_shift_used": "restrict",
                "expected_metric_delta": [3, -1, 1, -1, 1],
                "null_hypothesis": "Perps-v2 invariant suite is currently failing or unstable.",
                "falsification_recipe": "perp_v2_invariants",
                "support_recipe": "perp_v2_invariants",
                "formal_obligations": [
                    "All bounded perps-v2 invariants pass deterministically",
                    "Invariant suite catches arithmetic/state safety regressions",
                    "No UNKNOWN accepted as support",
                ],
                "risk_modes": [
                    "Coverage misses new edge regimes",
                    "Safety/performance tradeoff from stricter guards",
                ],
                "status": "proposed",
                "timeout_s": 120,
            },
            {
                "hypothesis_id": "H_perp_v2_invariant_break_exists_v1",
                "mechanism_change": "Assume an invariant break still exists in perps-v2 bounded regression suite.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": "No deterministic invariant break exists in bounded perps-v2 tests.",
                "falsification_recipe": "perp_v2_invariant_break_exists",
                "support_recipe": "perp_v2_invariant_break_exists",
                "formal_obligations": [
                    "Produce deterministic failing invariant test case",
                    "Attach minimal counterexample trace",
                ],
                "risk_modes": [
                    "Harness fragility mistaken for protocol issue",
                    "Counterexample non-transferable to production settings",
                ],
                "status": "proposed",
                "timeout_s": 120,
            },
            {
                "hypothesis_id": "H_perp_v2_oracle_equiv_gate_v1",
                "mechanism_change": "Require perps-v2 oracle equivalence checks as deterministic guard against oracle logic drift.",
                "representation_shift_used": "equiv",
                "expected_metric_delta": [2, 0, 1, -1, 2],
                "null_hypothesis": "Oracle equivalence tests are failing under current code path.",
                "falsification_recipe": "perp_v2_oracle_equiv",
                "support_recipe": "perp_v2_oracle_equiv",
                "formal_obligations": [
                    "Oracle math paths are equivalent for bounded test envelope",
                    "No silent deviation in settlement-driving price logic",
                    "Deterministic replay parity holds",
                ],
                "risk_modes": [
                    "Equivalence blind spots for untested oracle regimes",
                    "Potential liveness penalty from extra checks",
                ],
                "status": "proposed",
                "timeout_s": 120,
            },
            {
                "hypothesis_id": "H_perp_v2_oracle_divergence_exists_v1",
                "mechanism_change": "Assume bounded perps-v2 oracle divergence still exists.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": "No bounded oracle divergence exists under current regression checks.",
                "falsification_recipe": "perp_v2_oracle_divergence_exists",
                "support_recipe": "perp_v2_oracle_divergence_exists",
                "formal_obligations": [
                    "Produce deterministic divergence witness in oracle equivalence tests",
                    "Show economically relevant downstream impact signal",
                ],
                "risk_modes": [
                    "Apparent divergence due to fixture mismatch",
                    "Low transfer to production oracle cadence",
                ],
                "status": "proposed",
                "timeout_s": 120,
            },
            {
                "hypothesis_id": "H_curve_selection_safety_gate_v1",
                "mechanism_change": "Gate curve-selection mechanism changes on curve-selection regression safety checks.",
                "representation_shift_used": "restrict",
                "expected_metric_delta": [2, 0, 1, -1, 1],
                "null_hypothesis": "Curve-selection safety regression tests are currently failing.",
                "falsification_recipe": "curve_selection_safety",
                "support_recipe": "curve_selection_safety",
                "formal_obligations": [
                    "Curve selection invariants pass deterministic test suite",
                    "No unsafe curve-choice transitions under bounded fixtures",
                    "Decision path remains deterministic",
                ],
                "risk_modes": [
                    "Safety suite misses adversarial market regimes",
                    "Selection rigidity may reduce capital efficiency",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_curve_selection_unsafe_exists_v1",
                "mechanism_change": "Assume unsafe curve-selection behavior still exists under bounded regression tests.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": "No bounded unsafe curve-selection witness exists in regression suite.",
                "falsification_recipe": "curve_selection_unsafe_exists",
                "support_recipe": "curve_selection_unsafe_exists",
                "formal_obligations": [
                    "Construct deterministic unsafe curve-selection witness",
                    "Bind witness to regression failure output",
                ],
                "risk_modes": [
                    "False positives from synthetic edge cases",
                    "Unclear production frequency of discovered witness",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_split_routing_regression_gate_v1",
                "mechanism_change": "Use split-routing regression tests as hard gate for router updates.",
                "representation_shift_used": "restrict",
                "expected_metric_delta": [1, 0, 1, -1, 1],
                "null_hypothesis": "Split-routing regression tests are unstable or failing.",
                "falsification_recipe": "split_routing_regression",
                "support_recipe": "split_routing_regression",
                "formal_obligations": [
                    "Routing invariants hold on deterministic fixture set",
                    "No regression in route feasibility and output monotonicity",
                ],
                "risk_modes": [
                    "Regression suite under-covers multi-pool pathologies",
                    "Potential compute overhead from stricter checks",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_split_routing_regression_exists_v1",
                "mechanism_change": "Assume split-routing regressions are still present in bounded tests.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": "No split-routing regression exists in bounded test suite.",
                "falsification_recipe": "split_routing_regression_exists",
                "support_recipe": "split_routing_regression_exists",
                "formal_obligations": [
                    "Produce deterministic failing split-routing regression test",
                    "Attach failing fixture/output diff",
                ],
                "risk_modes": [
                    "False alarm from test-harness drift",
                    "Low external validity of synthetic fixture failures",
                ],
                "status": "proposed",
                "timeout_s": 90,
            },
            {
                "hypothesis_id": "H_batch_clearing_regression_gate_v1",
                "mechanism_change": "Use batch-clearing regression tests as acceptance gate for matching/settlement updates.",
                "representation_shift_used": "restrict",
                "expected_metric_delta": [2, 0, 1, -1, 1],
                "null_hypothesis": "Batch-clearing regression suite is currently failing or unstable.",
                "falsification_recipe": "batch_clearing_regression",
                "support_recipe": "batch_clearing_regression",
                "formal_obligations": [
                    "Batch-clearing invariants pass deterministic tests",
                    "No settlement conservation regressions",
                    "Ordering behavior remains deterministic under test fixtures",
                ],
                "risk_modes": [
                    "Fixture coverage gaps in large intent sets",
                    "Potential performance overhead in strict mode",
                ],
                "status": "proposed",
                "timeout_s": 120,
            },
            {
                "hypothesis_id": "H_batch_clearing_invariant_break_exists_v1",
                "mechanism_change": "Assume batch-clearing invariant break still exists in bounded regression tests.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": "No deterministic batch-clearing invariant break exists in bounded tests.",
                "falsification_recipe": "batch_clearing_invariant_break_exists",
                "support_recipe": "batch_clearing_invariant_break_exists",
                "formal_obligations": [
                    "Produce deterministic failing batch-clearing regression witness",
                    "Show invariant violation in bounded trace",
                ],
                "risk_modes": [
                    "False failure due to test fixture mismatch",
                    "Witness may be too narrow for protocol-level conclusions",
                ],
                "status": "proposed",
                "timeout_s": 120,
            },
        ]
    )
    target = max(0, int(target_hypotheses))
    auto_enabled = bool(auto_pytest_hypotheses)
    auto_files = max(0, int(max_auto_pytest_files))
    if target > 0:
        auto_enabled = True
        need = max(0, target - len(specs))
        files_needed = (need + 2) // 3
        auto_files = max(auto_files, files_needed)
    if auto_enabled and auto_files > 0:
        specs.extend(
            _auto_pytest_hypothesis_specs(
                max_auto_pytest_files=auto_files,
                offset_files=max(0, int(auto_pytest_offset_files)),
                replay_repeats=max(2, int(auto_pytest_replay_repeats)),
            )
        )

    seen: set[str] = set()
    dedup: list[dict[str, Any]] = []
    for spec in specs:
        hid = str(spec.get("hypothesis_id", ""))
        if not hid or hid in seen:
            continue
        seen.add(hid)
        dedup.append(spec)
    specs = dedup

    if target > 0 and len(specs) > target:
        specs = specs[:target]

    for spec in specs:
        if spec["representation_shift_used"] not in VALID_TRANSFORMS:
            raise ValueError(f"invalid transform: {spec['representation_shift_used']}")
    return specs

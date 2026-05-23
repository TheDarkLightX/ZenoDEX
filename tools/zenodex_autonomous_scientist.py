#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]

DIMENSIONS = [
    "safety_invariant_strength",
    "capital_efficiency",
    "execution_quality",
    "performance_cost",
    "determinism_simplicity",
]

# Required representation-shift labels.
VALID_TRANSFORMS = {"equiv", "reduce", "relax", "restrict", "heuristic"}


def _now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _stable_hash(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:12]


def _safe_token(text: str, *, max_len: int = 120) -> str:
    token = re.sub(r"[^A-Za-z0-9_.-]+", "_", str(text)).strip("._")
    if not token:
        token = "x"
    return token[:max_len]


def _safe_tag(text: str, *, max_len: int = 48) -> str:
    # PopperPad tag validator is stricter; normalize to lowercase [a-z0-9_.-].
    token = re.sub(r"[^a-z0-9_.-]+", "-", str(text).lower()).strip("-.")
    if not token:
        token = "x"
    return token[:max_len]


def _run_cmd(cmd: list[str], *, cwd: Path = ROOT, timeout_s: int = 180) -> tuple[int | None, str, str, float, bool]:
    t0 = time.time()
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(cwd),
            text=True,
            capture_output=True,
            timeout=max(1, int(timeout_s)),
        )
    except subprocess.TimeoutExpired as exc:
        return None, str(exc.stdout or ""), str(exc.stderr or ""), float(time.time() - t0), True
    return int(proc.returncode), proc.stdout, proc.stderr, float(time.time() - t0), False


def _extract_json(text: str) -> dict[str, Any] | None:
    s = str(text or "").strip()
    if not s:
        return None
    try:
        obj = json.loads(s)
        return obj if isinstance(obj, dict) else None
    except Exception:
        pass
    for line in reversed(s.splitlines()):
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
            if isinstance(obj, dict):
                return obj
        except Exception:
            continue
    return None


def _run_json_cmd(cmd: list[str], *, cwd: Path = ROOT, timeout_s: int = 180) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    rc, out, err, dt, timed_out = _run_cmd(cmd, cwd=cwd, timeout_s=timeout_s)
    payload = _extract_json(out)
    meta = {
        "command": cmd,
        "returncode": rc,
        "timeout": bool(timed_out),
        "duration_s": dt,
        "stdout_tail": out[-1500:],
        "stderr_tail": err[-1500:],
    }
    return payload, meta


def _popper_cmd(args: list[str]) -> list[str]:
    cmd = (
        "cd "
        + shlex.quote(str(ROOT))
        + " && PYTHONPATH=external/PopperPad/src python3 -m popperpad "
        + " ".join(shlex.quote(str(x)) for x in args)
    )
    return ["bash", "-lc", cmd]


def _append_jsonl(path: Path, row: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(row, sort_keys=True) + "\n")


def _read_json(path: Path, *, default: Any) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


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


REQUIRED_HYPOTHESIS_FIELDS = {
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


def _load_hypotheses_json(path: Path) -> list[dict[str, Any]]:
    raw = _read_json(path, default={})
    specs: list[dict[str, Any]]
    if isinstance(raw, list):
        specs = [x for x in raw if isinstance(x, dict)]
    elif isinstance(raw, dict):
        rows = raw.get("hypotheses")
        if isinstance(rows, list):
            specs = [x for x in rows if isinstance(x, dict)]
        else:
            raise ValueError(f"invalid hypotheses JSON shape (missing list): {path}")
    else:
        raise ValueError(f"invalid hypotheses JSON: {path}")
    out: list[dict[str, Any]] = []
    seen: set[str] = set()
    for row in specs:
        missing = [k for k in REQUIRED_HYPOTHESIS_FIELDS if k not in row]
        if missing:
            raise ValueError(f"hypothesis missing required fields {missing}: {row.get('hypothesis_id')}")
        hid = str(row["hypothesis_id"])
        if hid in seen:
            continue
        seen.add(hid)
        if row["representation_shift_used"] not in VALID_TRANSFORMS:
            raise ValueError(f"invalid transform: {row['representation_shift_used']} ({hid})")
        out.append(dict(row))
    return out


def _ensure_state(state_path: Path, candidates: list[dict[str, Any]]) -> dict[str, Any]:
    if state_path.exists():
        state = _read_json(state_path, default={})
        state.setdefault("hypotheses", {})
        for cand in candidates:
            hid = cand["hypothesis_id"]
            if hid not in state["hypotheses"]:
                state["hypotheses"][hid] = {
                    "status": "proposed",
                    "confidence": 0.5,
                    "evaluations": 0,
                    "supports": 0,
                    "refutes": 0,
                    "inconclusive": 0,
                    "popper": {},
                    "history": [],
                }
        state.setdefault("frontier_history", [])
        state.setdefault("epoch_history", [])
        state.setdefault("baseline_ready", False)
        state.setdefault("ideas_initialized", False)
        return state
    hypotheses: dict[str, Any] = {}
    for cand in candidates:
        hypotheses[cand["hypothesis_id"]] = {
            "status": "proposed",
            "confidence": 0.5,
            "evaluations": 0,
            "supports": 0,
            "refutes": 0,
            "inconclusive": 0,
            "popper": {},
            "history": [],
        }
    return {
        "schema": "zenodex/autonomous-scientist-state/v1",
        "created_at": _now_iso(),
        "last_epoch": 0,
        "stagnation_epochs": 0,
        "ideas_initialized": False,
        "hypotheses": hypotheses,
        "frontier_history": [],
        "epoch_history": [],
        "baseline_ready": False,
    }


def _ensure_ideapad(ideapad_path: Path, state: dict[str, Any], candidates: list[dict[str, Any]]) -> None:
    existing_ids: set[str] = set()
    if ideapad_path.exists():
        for line in ideapad_path.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except Exception:
                continue
            if isinstance(row, dict):
                hid = row.get("hypothesis_id")
                if isinstance(hid, str):
                    existing_ids.add(hid)
    for cand in candidates:
        hid = str(cand["hypothesis_id"])
        if hid in existing_ids:
            continue
        row = {
            "schema": "zenodex/ideapad/v1",
            "created_at": _now_iso(),
            **cand,
        }
        _append_jsonl(ideapad_path, row)
    state["ideas_initialized"] = True


def _popper_query(pad: Path, schema: str, limit: int = 200) -> dict[str, Any]:
    payload, _meta = _run_json_cmd(
        _popper_cmd(["--pad", str(pad), "query", "--schema", schema, "--limit", str(limit)]),
        cwd=ROOT,
        timeout_s=120,
    )
    return payload or {}


def _popper_add_obj(pad: Path, obj: dict[str, Any]) -> str:
    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False, encoding="utf-8") as fh:
        tmp = Path(fh.name)
        fh.write(json.dumps(obj, sort_keys=True))
        fh.write("\n")
    try:
        payload, meta = _run_json_cmd(
            _popper_cmd(["--pad", str(pad), "add", "--json", str(tmp)]),
            cwd=ROOT,
            timeout_s=120,
        )
    finally:
        tmp.unlink(missing_ok=True)
    if payload is None or not payload.get("ok") or not payload.get("obj_ref"):
        raise RuntimeError(f"popperpad add failed: {meta}")
    return str(payload["obj_ref"])


def _popper_run(pad: Path, cmd: str, *, context_ref: str, hypothesis_ref: str) -> dict[str, Any]:
    payload, _meta = _run_json_cmd(
        _popper_cmd(["--pad", str(pad), cmd, "--context", context_ref, hypothesis_ref]),
        cwd=ROOT,
        timeout_s=180,
    )
    return payload or {"ok": False, "verdict": "INCONCLUSIVE", "edge_refs": [], "evidence_refs": []}


def _ensure_popper_hypothesis(
    *,
    pad: Path,
    context_ref: str,
    domain_ref: str,
    state_hyp: dict[str, Any],
    cand: dict[str, Any],
) -> dict[str, Any]:
    pop = dict(state_hyp.get("popper") or {})
    check_id = str(cand["support_recipe"])
    timeout_s = int(cand.get("timeout_s", 180))
    for mode in ("support", "refute"):
        key = f"{mode}_recipe_ref"
        if key in pop:
            continue
        recipe_id = f"zenodex_autonomous_{cand['hypothesis_id']}_{mode}_{check_id}_v1_{_stable_hash(cand['hypothesis_id'] + mode + check_id)}"
        cmd = (
            f"cd {shlex.quote(str(ROOT))} && "
            f"python3 tools/zenodex_autonomous_checks.py --check {shlex.quote(check_id)} "
            f"--mode {shlex.quote(mode)} --timeout-s {int(timeout_s)}"
        )
        recipe_obj = {
            "schema": "popperpad/recipe/v1",
            "recipe_id": recipe_id,
            "verdict_on_pass": mode,
            "timeout_ms": int(timeout_s) * 1000,
            "argv": ["bash", "-lc", cmd],
        }
        pop[key] = _popper_add_obj(pad, recipe_obj)

    if "hypothesis_ref" not in pop:
        statement_payload = {
            "hypothesis_id": cand["hypothesis_id"],
            "mechanism_change": cand["mechanism_change"],
            "representation_shift_used": cand["representation_shift_used"],
            "expected_metric_delta": cand["expected_metric_delta"],
            "null_hypothesis": cand["null_hypothesis"],
            "falsification_recipe": cand["falsification_recipe"],
            "support_recipe": cand["support_recipe"],
            "formal_obligations": cand["formal_obligations"],
            "risk_modes": cand["risk_modes"],
        }
        hyp_obj = {
            "schema": "popperpad/hypothesis/v1",
            "hypothesis_id": cand["hypothesis_id"],
            "kind": "mechanism",
            "title": str(cand["mechanism_change"]),
            "statement": {"lang": "json", "body": json.dumps(statement_payload, sort_keys=True)},
            "domain_ref": domain_ref,
            "context_ref": context_ref,
            "tags": [
                "zenodex",
                "autonomous-scientist",
                f"transform-{_safe_tag(str(cand['representation_shift_used']), max_len=24)}",
                f"check-{_safe_tag(check_id, max_len=48)}",
            ],
            "check_recipe_refs": [pop["support_recipe_ref"], pop["refute_recipe_ref"]],
        }
        pop["hypothesis_ref"] = _popper_add_obj(pad, hyp_obj)

    state_hyp["popper"] = pop
    return pop


def _run_check_once(check_id: str, mode: str, *, epoch_dir: Path, hypothesis_id: str, timeout_s: int) -> dict[str, Any]:
    safe_hypothesis_id = _safe_token(hypothesis_id, max_len=120)
    safe_check_id = _safe_token(check_id, max_len=120)
    out_path = epoch_dir / f"{safe_hypothesis_id}_{mode}_{safe_check_id}.json"
    cmd = [
        "python3",
        "tools/zenodex_autonomous_checks.py",
        "--check",
        check_id,
        "--mode",
        mode,
        "--timeout-s",
        str(int(timeout_s)),
        "--json-out",
        str(out_path),
    ]
    rc, out, err, dt, timed_out = _run_cmd(cmd, cwd=ROOT, timeout_s=int(timeout_s) + 30)
    payload = _read_json(out_path, default={}) if out_path.exists() else (_extract_json(out) or {})
    if not payload:
        payload = {
            "schema": "zenodex/autonomous-check/v1",
            "check": check_id,
            "mode": mode,
            "status": "inconclusive",
            "reason": "runner_failed",
            "signal": None,
            "counterexample": None,
            "metrics": {},
        }
    payload["runner"] = {
        "returncode": rc,
        "timeout": timed_out,
        "duration_s": dt,
        "stdout_tail": out[-1200:],
        "stderr_tail": err[-1200:],
    }
    return payload


def _vector(cand: dict[str, Any]) -> list[float]:
    return [float(x) for x in cand["expected_metric_delta"]]


def _adjusted_vector(cand: dict[str, Any], hst: dict[str, Any]) -> list[float]:
    conf = float(hst.get("confidence", 0.0))
    return [float(x) * conf for x in _vector(cand)]


def _dominates(a: list[float], b: list[float]) -> bool:
    return all(x >= y for x, y in zip(a, b)) and any(x > y for x, y in zip(a, b))


def _compute_frontier(candidates: list[dict[str, Any]], state: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for cand in candidates:
        hid = cand["hypothesis_id"]
        hst = state["hypotheses"][hid]
        if hst["status"] == "falsified":
            continue
        raw = _vector(cand)
        adj = _adjusted_vector(cand, hst)
        rows.append(
            {
                "hypothesis_id": hid,
                "status": hst["status"],
                "confidence": float(hst["confidence"]),
                "metric_vector": raw,
                "adjusted_metric_vector": adj,
                "representation_shift_used": cand["representation_shift_used"],
            }
        )
    frontier: list[dict[str, Any]] = []
    for row in rows:
        dominated = False
        for other in rows:
            if other["hypothesis_id"] == row["hypothesis_id"]:
                continue
            if _dominates(other["adjusted_metric_vector"], row["adjusted_metric_vector"]):
                dominated = True
                break
        if not dominated:
            frontier.append(row)
    frontier.sort(key=lambda r: (sum(r["adjusted_metric_vector"]), r["hypothesis_id"]), reverse=True)
    return frontier


def _info_gain_score(cand: dict[str, Any], hst: dict[str, Any], epoch: int) -> float:
    potential = sum(max(0.0, x) for x in _vector(cand))
    status = str(hst.get("status", "proposed"))
    if status == "falsified":
        return 0.0
    uncertainty = 1.0 if status == "proposed" else 0.8 if status == "inconclusive" else 0.2
    conf = float(hst.get("confidence", 0.5))
    evals = int(hst.get("evaluations", 0))
    repetition_penalty = 1.0 / (1.0 + 0.35 * float(max(0, evals)))
    base = uncertainty * max(0.05, 1.0 - conf) * (1.0 + potential / 10.0) * repetition_penalty
    jitter = int(_stable_hash(f"{epoch}:{cand['hypothesis_id']}"), 16) % 1000
    return float(base + (jitter / 1_000_000.0))


def _select_epoch_queue(
    *,
    candidates: list[dict[str, Any]],
    state: dict[str, Any],
    epoch: int,
    max_width: int,
    exploration_ratio: float,
    max_supported_repeats: int,
    max_falsified_repeats: int,
) -> list[str]:
    check_eval_count: dict[str, int] = {}
    for cand in candidates:
        hid = str(cand["hypothesis_id"])
        check_id = str(cand["support_recipe"])
        hst = state["hypotheses"][hid]
        check_eval_count[check_id] = int(check_eval_count.get(check_id, 0)) + int(hst.get("evaluations", 0))

    rows_all: list[tuple[str, float, float, str, float, int]] = []
    rows_preferred: list[tuple[str, float, float, str, float, int]] = []
    for cand in candidates:
        hid = cand["hypothesis_id"]
        hst = state["hypotheses"][hid]
        status = str(hst.get("status", "proposed"))
        evals = int(hst.get("evaluations", 0))
        potential = sum(max(0.0, x) for x in _vector(cand))
        check_id = str(cand["support_recipe"])
        novelty = 1.0 / (1.0 + float(check_eval_count.get(check_id, 0)))
        info_gain = _info_gain_score(cand, hst, epoch) * (1.0 + 0.6 * novelty)
        row = (hid, potential, info_gain, status, novelty, evals)
        rows_all.append(row)

        if status == "falsified" and evals >= max(0, int(max_falsified_repeats)):
            continue
        if status == "supported" and evals >= max(1, int(max_supported_repeats)):
            continue
        rows_preferred.append(row)

    if not rows_all:
        return []
    active_rows = rows_preferred if rows_preferred else rows_all
    unresolved = [r for r in active_rows if r[3] in {"proposed", "inconclusive"}]
    primary = unresolved if unresolved else active_rows

    rows_potential = sorted(primary, key=lambda x: (x[1], x[4], -x[5], x[2], x[0]), reverse=True)
    rows_info = sorted(primary, key=lambda x: (x[2], x[4], -x[5], x[1], x[0]), reverse=True)
    rows_fill = sorted(active_rows, key=lambda x: (x[4], -x[5], x[2], x[1], x[0]), reverse=True)

    width = max(1, min(int(max_width), len(rows_all)))
    explore_n = int(round(width * float(exploration_ratio)))
    exploit_n = width - explore_n
    if exploit_n <= 0:
        exploit_n = 1
        explore_n = width - 1

    selected: list[str] = []
    for hid, _, _, _, _, _ in rows_potential:
        if len(selected) >= exploit_n:
            break
        selected.append(hid)
    for hid, _, _, _, _, _ in rows_info:
        if len(selected) >= width:
            break
        if hid in selected:
            continue
        selected.append(hid)
    for hid, _, _, _, _, _ in rows_fill:
        if len(selected) >= width:
            break
        if hid in selected:
            continue
        selected.append(hid)
    return selected


def _collect_event_rows(candidates: list[dict[str, Any]], state: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for cand in candidates:
        hid = str(cand["hypothesis_id"])
        hst = state["hypotheses"][hid]
        for event in hst.get("history", []):
            refute_direct = event.get("refute_direct") or {}
            support_direct = event.get("support_direct") or {}
            metrics = support_direct.get("metrics") if support_direct else refute_direct.get("metrics")
            basis = support_direct if support_direct else refute_direct
            counterexample = basis.get("counterexample")
            try:
                metrics_fp = json.dumps(metrics, sort_keys=True)
            except Exception:
                metrics_fp = str(metrics)
            try:
                counterexample_fp = json.dumps(counterexample, sort_keys=True)
            except Exception:
                counterexample_fp = str(counterexample)
            rows.append(
                {
                    "hypothesis_id": hid,
                    "epoch": int(event.get("epoch", 0)),
                    "status": str(event.get("status", "inconclusive")),
                    "transform": str(cand["representation_shift_used"]),
                    "check": str(cand["support_recipe"]),
                    "duration_s": float(refute_direct.get("duration_s") or 0.0) + float(support_direct.get("duration_s") or 0.0),
                    "metrics_fp": metrics_fp,
                    "counterexample_fp": counterexample_fp if counterexample is not None else "",
                    "reason": str(basis.get("reason", "")),
                }
            )
    return rows


def _derive_deep_insights(
    *,
    candidates: list[dict[str, Any]],
    state: dict[str, Any],
    frontier_gain: int,
) -> list[dict[str, Any]]:
    events = _collect_event_rows(candidates, state)
    if not events:
        return []

    insights: list[dict[str, Any]] = []

    by_transform: dict[str, dict[str, int]] = {}
    for row in events:
        tr = row["transform"]
        st = row["status"]
        slot = by_transform.setdefault(tr, {"supported": 0, "falsified": 0, "inconclusive": 0, "total": 0})
        slot["total"] += 1
        slot[st] = int(slot.get(st, 0)) + 1
    transform_scores: dict[str, Any] = {}
    for tr, slot in by_transform.items():
        total = max(1, int(slot["total"]))
        transform_scores[tr] = {
            "total": int(slot["total"]),
            "supported": int(slot.get("supported", 0)),
            "falsified": int(slot.get("falsified", 0)),
            "inconclusive": int(slot.get("inconclusive", 0)),
            "support_rate": float(slot.get("supported", 0)) / float(total),
            "falsify_rate": float(slot.get("falsified", 0)) / float(total),
        }
    insights.append(
        {
            "insight": "Transform-level outcomes are uneven; prioritize transforms with high falsify-rate for harder stress-testing and high support-rate only when coupled to novel checks.",
            "details": {"transform_scores": transform_scores},
        }
    )

    by_check: dict[str, dict[str, Any]] = {}
    for row in events:
        ch = row["check"]
        slot = by_check.setdefault(
            ch,
            {
                "total": 0,
                "supported": 0,
                "falsified": 0,
                "inconclusive": 0,
                "dur_sum": 0.0,
                "metrics_fp": set(),
                "statuses": set(),
                "counterexamples": set(),
                "reasons": {},
            },
        )
        slot["total"] += 1
        slot[row["status"]] = int(slot.get(row["status"], 0)) + 1
        slot["dur_sum"] = float(slot["dur_sum"]) + float(row["duration_s"])
        slot["metrics_fp"].add(str(row["metrics_fp"]))
        slot["statuses"].add(str(row["status"]))
        cfp = str(row.get("counterexample_fp", ""))
        if cfp:
            slot["counterexamples"].add(cfp)
        reason = str(row.get("reason", ""))
        if reason:
            slot["reasons"][reason] = int(slot["reasons"].get(reason, 0)) + 1

    deterministic_checks: list[dict[str, Any]] = []
    expensive_checks: list[dict[str, Any]] = []
    counterexample_diversity: list[dict[str, Any]] = []
    for check_id, slot in by_check.items():
        total = int(slot["total"])
        if total >= 2 and len(slot["metrics_fp"]) == 1 and len(slot["statuses"]) == 1:
            deterministic_checks.append(
                {
                    "check": check_id,
                    "evaluations": total,
                    "status": list(slot["statuses"])[0],
                }
            )
        expensive_checks.append({"check": check_id, "total_duration_s": float(slot["dur_sum"]), "evaluations": total})
        counterexample_diversity.append(
            {
                "check": check_id,
                "falsified_evaluations": int(slot.get("falsified", 0)),
                "unique_counterexamples": int(len(slot["counterexamples"])),
                "inconclusive_evaluations": int(slot.get("inconclusive", 0)),
            }
        )
    expensive_checks.sort(key=lambda r: (r["total_duration_s"], r["check"]), reverse=True)
    counterexample_diversity.sort(
        key=lambda r: (r["falsified_evaluations"], -r["unique_counterexamples"], r["check"]),
        reverse=True,
    )
    deterministic_eval_total = sum(int(r["evaluations"]) for r in deterministic_checks)
    repeat_share = float(deterministic_eval_total) / float(max(1, len(events)))
    insights.append(
        {
            "insight": "Several checks are metric-stable across repeats; repeated confirmations add little information and should be deprioritized in favor of untested checks.",
            "details": {
                "deterministic_repeats": deterministic_checks[:8],
                "expensive_checks": expensive_checks[:5],
                "repeat_share_of_events": repeat_share,
            },
        }
    )
    insights.append(
        {
            "insight": "Counterexample diversity varies by check; low unique-counterexample count under repeated falsifications suggests a narrow adversarial witness class that needs broader search domains.",
            "details": {
                "counterexample_diversity": counterexample_diversity[:8],
            },
        }
    )

    total_unique_checks = len({str(c["support_recipe"]) for c in candidates})
    explored_checks = len(by_check)
    unresolved_by_reason: dict[str, int] = {}
    for row in events:
        if str(row["status"]) != "inconclusive":
            continue
        reason = str(row.get("reason", "") or "unknown")
        unresolved_by_reason[reason] = int(unresolved_by_reason.get(reason, 0)) + 1
    insights.append(
        {
            "insight": "Check-space coverage and unresolved concentration identify where deeper exploration is needed next.",
            "details": {
                "explored_checks": explored_checks,
                "total_candidate_checks": total_unique_checks,
                "check_coverage_ratio": float(explored_checks) / float(max(1, total_unique_checks)),
                "inconclusive_by_reason": dict(sorted(unresolved_by_reason.items(), key=lambda kv: kv[1], reverse=True)),
            },
        }
    )

    frontier = _compute_frontier(candidates, state)
    contribution_by_transform: dict[str, float] = {}
    for row in frontier:
        tr = str(row.get("representation_shift_used", ""))
        contrib = float(sum(max(0.0, float(v)) for v in row.get("adjusted_metric_vector", [])))
        contribution_by_transform[tr] = float(contribution_by_transform.get(tr, 0.0)) + contrib
    insights.append(
        {
            "insight": "Frontier contribution is concentrated in a subset of transforms; underperforming transforms should be redirected toward higher-novelty checks.",
            "details": {
                "frontier_positive_contribution_by_transform": dict(
                    sorted(contribution_by_transform.items(), key=lambda kv: kv[1], reverse=True)
                )
            },
        }
    )

    gains = [int(row.get("frontier_gain", 0)) for row in state.get("frontier_history", [])]
    gains.append(int(frontier_gain))
    tail = gains[-3:] if gains else [int(frontier_gain)]
    avg_tail = float(sum(tail)) / float(max(1, len(tail)))
    insights.append(
        {
            "insight": "Frontier marginal gain is decaying; next epochs should increase check novelty and counterfactual controls rather than re-confirm already-supported branches.",
            "details": {
                "frontier_gain_tail": tail,
                "frontier_gain_tail_avg": avg_tail,
            },
        }
    )
    return insights


def _unblock_plan(result: dict[str, Any]) -> str:
    reason = str(result.get("reason", ""))
    if reason == "timeout":
        return "Increase timeout budget for this check and reduce per-epoch width to keep progress."
    if reason == "mathlib_not_wired":
        return "Wire local mathlib path into `lean-mathlib/.lake/packages/mathlib` and rerun Lean gate."
    if reason in {"command_error_or_unparseable_json", "runner_failed", "unparseable_json"}:
        return "Stabilize command output contract (JSON) and rerun in isolated command recipe."
    return "Collect additional bounded evidence (larger domain/seed sweep) and rerun."


def _final_roadmap(candidates: list[dict[str, Any]], state: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for cand in candidates:
        hid = cand["hypothesis_id"]
        hst = state["hypotheses"][hid]
        status = str(hst["status"])
        if status == "supported":
            decision = "promote"
            rank_score = 300 + sum(max(0, x) for x in _vector(cand)) * float(hst["confidence"])
            rationale = "Supported by bounded checks and ledger evidence."
        elif status == "falsified":
            decision = "drop"
            rank_score = 0
            rationale = "Refuted under current bounded falsifier recipe."
        else:
            decision = "iterate"
            rank_score = 100 + sum(max(0, x) for x in _vector(cand)) * (1.0 - float(hst["confidence"]))
            rationale = "Inconclusive bounded evidence; keep in queue with unblock plan."
        rows.append(
            {
                "hypothesis_id": hid,
                "decision": decision,
                "status": status,
                "confidence": float(hst["confidence"]),
                "representation_shift_used": cand["representation_shift_used"],
                "expected_metric_delta": cand["expected_metric_delta"],
                "rationale": rationale,
                "rank_score": float(rank_score),
            }
        )
    rows.sort(key=lambda r: (r["rank_score"], r["hypothesis_id"]), reverse=True)
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description="Autonomous ZenoDEX scientist loop (epochs + checkpoints + evidence gates)")
    ap.add_argument("--run-root", type=Path, default=Path("runs/autonomous_scientist"))
    ap.add_argument("--pad", type=Path, default=Path("internal/popperpad/zenodex"))
    ap.add_argument("--hypotheses-json", type=Path, default=None)
    ap.add_argument("--max-epochs", type=int, default=4)
    ap.add_argument("--min-epochs", type=int, default=2)
    ap.add_argument("--max-width", type=int, default=3)
    ap.add_argument("--exploration-ratio", type=float, default=0.34)
    ap.add_argument("--auto-pytest-hypotheses", action="store_true")
    ap.add_argument("--max-auto-pytest-files", type=int, default=0)
    ap.add_argument("--auto-pytest-offset-files", type=int, default=0)
    ap.add_argument("--auto-pytest-replay-repeats", type=int, default=3)
    ap.add_argument("--target-hypotheses", type=int, default=0)
    ap.add_argument("--max-supported-repeats", type=int, default=2)
    ap.add_argument("--max-falsified-repeats", type=int, default=1)
    ap.add_argument("--marginal-frontier-threshold", type=int, default=0)
    ap.add_argument("--stagnation-epochs", type=int, default=2)
    args = ap.parse_args()

    run_root = (ROOT / args.run_root).resolve()
    pad = (ROOT / args.pad).resolve()
    run_root.mkdir(parents=True, exist_ok=True)
    epochs_dir = run_root / "epochs"
    epochs_dir.mkdir(parents=True, exist_ok=True)

    state_path = run_root / "state.json"
    ideapad_path = run_root / "ideapad.jsonl"
    insightpad_path = run_root / "insightpad.jsonl"
    baseline_path = run_root / "baseline.json"

    if args.hypotheses_json is not None:
        hyp_path = (ROOT / args.hypotheses_json).resolve() if not Path(args.hypotheses_json).is_absolute() else Path(args.hypotheses_json)
        candidates = _load_hypotheses_json(hyp_path)
    else:
        candidates = _candidate_specs(
            auto_pytest_hypotheses=bool(args.auto_pytest_hypotheses),
            max_auto_pytest_files=max(0, int(args.max_auto_pytest_files)),
            auto_pytest_offset_files=max(0, int(args.auto_pytest_offset_files)),
            auto_pytest_replay_repeats=max(2, int(args.auto_pytest_replay_repeats)),
            target_hypotheses=max(0, int(args.target_hypotheses)),
        )
    by_id = {c["hypothesis_id"]: c for c in candidates}

    state = _ensure_state(state_path, candidates)
    _ensure_ideapad(ideapad_path, state, candidates)

    # Locate PopperPad domain/context refs.
    domain_q = _popper_query(pad, "popperpad/domain/v1", limit=200).get("objects", [])
    context_q = _popper_query(pad, "popperpad/context/v1", limit=200).get("objects", [])
    domain_ref = None
    for row in domain_q:
        if str(row.get("domain_id")) == "zenodex":
            domain_ref = str(row.get("ref"))
            break
    context_ref = None
    for row in context_q:
        if str(row.get("context_key")) == "zenodex:local":
            context_ref = str(row.get("ref"))
            break
    if not domain_ref or not context_ref:
        raise RuntimeError("Missing PopperPad zenodex domain/context refs. Run bootstrap first.")

    # Baseline harness initialization (including migration for newly added checks).
    baseline = _read_json(
        baseline_path,
        default={
            "schema": "zenodex/autonomous-baseline/v1",
            "created_at": _now_iso(),
            "checks": {},
        },
    )
    baseline_rows = dict(baseline.get("checks") or {})
    baseline_changed = not baseline_path.exists()
    seen_checks = sorted({str(c["support_recipe"]) for c in candidates})
    for check_id in seen_checks:
        if check_id in baseline_rows:
            continue
        out = _run_check_once(
            check_id=check_id,
            mode="support",
            epoch_dir=run_root / "baseline",
            hypothesis_id=f"baseline_{check_id}",
            timeout_s=180,
        )
        baseline_rows[check_id] = out
        baseline_changed = True
    if baseline_changed:
        baseline = {
            "schema": "zenodex/autonomous-baseline/v1",
            "created_at": str(baseline.get("created_at", _now_iso())),
            "checks": baseline_rows,
        }
        _write_json(baseline_path, baseline)
    state["baseline_ready"] = True

    # Main epoch loop.
    max_epochs = max(1, int(args.max_epochs))
    min_epochs = max(1, int(args.min_epochs))
    max_width = max(1, int(args.max_width))
    exploration_ratio = min(0.95, max(0.05, float(args.exploration_ratio)))
    max_supported_repeats = max(1, int(args.max_supported_repeats))
    max_falsified_repeats = max(0, int(args.max_falsified_repeats))
    frontier_threshold = int(args.marginal_frontier_threshold)
    stagnation_target = max(1, int(args.stagnation_epochs))

    previous_frontier_ids: set[str] = set()
    if state.get("frontier_history"):
        previous_frontier_ids = set(state["frontier_history"][-1].get("frontier_ids", []))

    for epoch in range(int(state.get("last_epoch", 0)) + 1, max_epochs + 1):
        epoch_dir = epochs_dir / f"epoch_{epoch:04d}"
        epoch_dir.mkdir(parents=True, exist_ok=True)
        queue = _select_epoch_queue(
            candidates=candidates,
            state=state,
            epoch=epoch,
            max_width=max_width,
            exploration_ratio=exploration_ratio,
            max_supported_repeats=max_supported_repeats,
            max_falsified_repeats=max_falsified_repeats,
        )

        newly_falsified: list[dict[str, Any]] = []
        newly_supported: list[dict[str, Any]] = []
        inconclusive_rows: list[dict[str, Any]] = []
        evaluated: list[dict[str, Any]] = []

        for hid in queue:
            cand = by_id[hid]
            hst = state["hypotheses"][hid]
            prev_status = str(hst.get("status", "proposed"))

            popper = _ensure_popper_hypothesis(
                pad=pad,
                context_ref=context_ref,
                domain_ref=domain_ref,
                state_hyp=hst,
                cand=cand,
            )

            timeout_s = int(cand.get("timeout_s", 180))
            check_id = str(cand["support_recipe"])

            refute_direct = _run_check_once(
                check_id=check_id,
                mode="refute",
                epoch_dir=epoch_dir,
                hypothesis_id=hid,
                timeout_s=timeout_s,
            )
            refute_popper: dict[str, Any] | None = None
            support_direct: dict[str, Any] | None = None
            support_popper: dict[str, Any] | None = None

            final_status = "inconclusive"
            if refute_direct.get("status") == "pass":
                refute_popper = _popper_run(
                    pad,
                    "refute",
                    context_ref=context_ref,
                    hypothesis_ref=str(popper["hypothesis_ref"]),
                )
                final_status = "falsified"
            else:
                support_direct = _run_check_once(
                    check_id=check_id,
                    mode="support",
                    epoch_dir=epoch_dir,
                    hypothesis_id=hid,
                    timeout_s=timeout_s,
                )
                if support_direct.get("status") == "pass":
                    support_popper = _popper_run(
                        pad,
                        "prove",
                        context_ref=context_ref,
                        hypothesis_ref=str(popper["hypothesis_ref"]),
                    )
                    final_status = "supported"
                else:
                    final_status = "inconclusive"

            # Update hypothesis state.
            hst["evaluations"] = int(hst.get("evaluations", 0)) + 1
            hst["status"] = final_status
            if final_status == "supported":
                hst["supports"] = int(hst.get("supports", 0)) + 1
                hst["confidence"] = min(0.95, max(float(hst.get("confidence", 0.5)), 0.6 + 0.1 * (int(hst["supports"]) - 1)))
            elif final_status == "falsified":
                hst["refutes"] = int(hst.get("refutes", 0)) + 1
                hst["confidence"] = 0.05
            else:
                hst["inconclusive"] = int(hst.get("inconclusive", 0)) + 1
                hst["confidence"] = max(0.2, float(hst.get("confidence", 0.5)) - 0.05)

            event = {
                "epoch": epoch,
                "at": _now_iso(),
                "status": final_status,
                "refute_direct": refute_direct,
                "refute_popper": refute_popper,
                "support_direct": support_direct,
                "support_popper": support_popper,
            }
            hst.setdefault("history", []).append(event)
            evaluated.append({"hypothesis_id": hid, "event": event})

            if final_status == "falsified":
                newly_falsified.append(
                    {
                        "hypothesis_id": hid,
                        "counterexample": refute_direct.get("counterexample"),
                        "confidence": hst["confidence"],
                        "evidence_refs": (refute_popper or {}).get("evidence_refs", []),
                    }
                )
                _append_jsonl(
                    insightpad_path,
                    {
                        "schema": "zenodex/insightpad/v1",
                        "created_at": _now_iso(),
                        "epoch": epoch,
                        "type": "falsification",
                        "hypothesis_id": hid,
                        "insight": f"Null held under bounded recipe `{check_id}`; drop current mechanism variant.",
                        "counterexample": refute_direct.get("counterexample"),
                    },
                )
            elif final_status == "supported":
                newly_supported.append(
                    {
                        "hypothesis_id": hid,
                        "confidence": hst["confidence"],
                        "evidence_refs": (support_popper or {}).get("evidence_refs", []),
                        "metrics": (support_direct or {}).get("metrics", {}),
                    }
                )
                _append_jsonl(
                    insightpad_path,
                    {
                        "schema": "zenodex/insightpad/v1",
                        "created_at": _now_iso(),
                        "epoch": epoch,
                        "type": "support",
                        "hypothesis_id": hid,
                        "insight": f"Falsifier failed and support recipe passed for `{check_id}` under bounded budget.",
                        "metrics": (support_direct or {}).get("metrics", {}),
                    },
                )
            else:
                basis = support_direct or refute_direct
                inconclusive_rows.append(
                    {
                        "hypothesis_id": hid,
                        "reason": basis.get("reason"),
                        "unblock_plan": _unblock_plan(basis),
                        "confidence": hst["confidence"],
                    }
                )
                _append_jsonl(
                    insightpad_path,
                    {
                        "schema": "zenodex/insightpad/v1",
                        "created_at": _now_iso(),
                        "epoch": epoch,
                        "type": "inconclusive",
                        "hypothesis_id": hid,
                        "insight": f"Inconclusive bounded evidence for `{check_id}`; keep branch alive with unblock plan.",
                        "reason": basis.get("reason"),
                        "unblock_plan": _unblock_plan(basis),
                    },
                )

        frontier = _compute_frontier(candidates, state)
        frontier_ids = [row["hypothesis_id"] for row in frontier]
        frontier_gain = len(set(frontier_ids) - previous_frontier_ids)
        if frontier_gain <= frontier_threshold:
            state["stagnation_epochs"] = int(state.get("stagnation_epochs", 0)) + 1
        else:
            state["stagnation_epochs"] = 0
        previous_frontier_ids = set(frontier_ids)

        # Rank next experiments by expected information gain.
        next_ranked: list[dict[str, Any]] = []
        for cand in candidates:
            hid = cand["hypothesis_id"]
            hst = state["hypotheses"][hid]
            score = _info_gain_score(cand, hst, epoch + 1)
            evals = int(hst.get("evaluations", 0))
            status = str(hst.get("status", "proposed"))
            if status == "supported" and evals >= max_supported_repeats:
                score *= 0.25
            if status == "falsified" and evals >= max_falsified_repeats:
                score *= 0.10
            next_ranked.append(
                {
                    "hypothesis_id": hid,
                    "status": status,
                    "confidence": float(hst["confidence"]),
                    "expected_information_gain": score,
                    "expected_metric_delta": cand["expected_metric_delta"],
                }
            )
        next_ranked.sort(key=lambda r: (r["expected_information_gain"], r["hypothesis_id"]), reverse=True)
        deep_insights = _derive_deep_insights(candidates=candidates, state=state, frontier_gain=frontier_gain)
        for deep in deep_insights:
            _append_jsonl(
                insightpad_path,
                {
                    "schema": "zenodex/insightpad/v1",
                    "created_at": _now_iso(),
                    "epoch": epoch,
                    "type": "deep_insight",
                    "insight": str(deep.get("insight", "")),
                    "details": deep.get("details", {}),
                },
            )

        epoch_snapshot = {
            "schema": "zenodex/autonomous-epoch/v1",
            "epoch": epoch,
            "timestamp": _now_iso(),
            "budgets": {
                "max_depth": 1,
                "max_width": max_width,
                "max_supported_repeats": max_supported_repeats,
                "max_falsified_repeats": max_falsified_repeats,
                "per_check_timeout_s": {c["hypothesis_id"]: int(c.get("timeout_s", 180)) for c in candidates},
                "exploration_ratio": exploration_ratio,
            },
            "queue": queue,
            "outputs": {
                "pareto_frontier_snapshot": frontier,
                "newly_falsified": newly_falsified,
                "newly_supported": newly_supported,
                "inconclusive_items": inconclusive_rows,
                "deep_insights": deep_insights,
                "next_experiment_queue": next_ranked[:10],
            },
            "frontier_gain": frontier_gain,
            "stagnation_epochs": int(state.get("stagnation_epochs", 0)),
            "evaluated": evaluated,
        }

        _write_json(epoch_dir / "snapshot.json", epoch_snapshot)
        _append_jsonl(run_root / "epoch_summaries.jsonl", epoch_snapshot)

        # PopperPad checkpoint per epoch (graceful on failure).
        checkpoint_payload, _ = _run_json_cmd(
            _popper_cmd(["--pad", str(pad), "checkpoint"]),
            cwd=ROOT,
            timeout_s=120,
        )
        epoch_snapshot["popperpad_checkpoint"] = checkpoint_payload or {"ok": False}
        _write_json(epoch_dir / "snapshot.json", epoch_snapshot)

        state["last_epoch"] = epoch
        state.setdefault("frontier_history", []).append(
            {
                "epoch": epoch,
                "frontier_ids": frontier_ids,
                "frontier_gain": frontier_gain,
            }
        )
        state.setdefault("epoch_history", []).append(
            {
                "epoch": epoch,
                "queue": queue,
                "frontier_gain": frontier_gain,
                "newly_supported": [r["hypothesis_id"] for r in newly_supported],
                "newly_falsified": [r["hypothesis_id"] for r in newly_falsified],
                "inconclusive": [r["hypothesis_id"] for r in inconclusive_rows],
            }
        )
        _write_json(state_path, state)

        if epoch >= min_epochs and int(state.get("stagnation_epochs", 0)) >= stagnation_target:
            break

    # Final ranked roadmap.
    roadmap_rows = _final_roadmap(candidates, state)
    _write_json(run_root / "final_roadmap.json", {"schema": "zenodex/autonomous-roadmap/v1", "rows": roadmap_rows})

    md_lines = [
        "# ZenoDEX Autonomous Scientist Roadmap",
        "",
        f"- Generated at: {_now_iso()}",
        f"- Run root: `{run_root}`",
        "",
        "| Rank | Hypothesis | Decision | Status | Confidence | Transform | Expected Delta [S,C,E,P,D] |",
        "|---:|---|---|---|---:|---|---|",
    ]
    for i, row in enumerate(roadmap_rows, 1):
        md_lines.append(
            "| "
            + str(i)
            + " | "
            + row["hypothesis_id"]
            + " | "
            + row["decision"]
            + " | "
            + row["status"]
            + " | "
            + f"{row['confidence']:.2f}"
            + " | "
            + row["representation_shift_used"]
            + " | "
            + str(row["expected_metric_delta"])
            + " |"
        )
    md_lines.append("")
    md_lines.append("## Rationale")
    for row in roadmap_rows:
        md_lines.append(f"- `{row['hypothesis_id']}`: {row['decision']} ({row['rationale']})")
    (run_root / "final_roadmap.md").write_text("\n".join(md_lines) + "\n", encoding="utf-8")

    print(json.dumps({"ok": True, "run_root": str(run_root), "epochs_completed": int(state.get("last_epoch", 0))}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

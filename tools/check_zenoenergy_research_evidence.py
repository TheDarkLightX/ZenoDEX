#!/usr/bin/env python3
"""Replay committed ZenoEnergy research evidence and fail closed on drift."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


@dataclass(frozen=True)
class EvidenceCheck:
    check_id: str
    passed: bool
    detail: str

    def to_dict(self) -> dict[str, object]:
        return {
            "check_id": self.check_id,
            "passed": self.passed,
            "detail": self.detail,
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    parser.add_argument("--skip-popperpad-doctor", action="store_true")
    args = parser.parse_args()

    report = replay_zenoenergy_evidence(
        root=args.root,
        run_popperpad_doctor=not args.skip_popperpad_doctor,
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0 if report["ok"] else 1


def replay_zenoenergy_evidence(
    *,
    root: Path = ROOT,
    run_popperpad_doctor: bool = True,
) -> dict[str, Any]:
    checks: list[EvidenceCheck] = []
    payloads: dict[str, Any] = {}

    set_aware = _load_json(
        root / "data/upba_energy/upba_v2_energy_set_aware_compare_120x80_seed20260523_20260524.json"
    )
    payloads["set_aware"] = set_aware
    checks.extend(_check_set_aware(set_aware))

    neighborhood = _load_json(
        root / "data/upba_energy/upba_v2_energy_neighborhood_benchmark_seed20260525.json"
    )
    payloads["neighborhood"] = neighborhood
    checks.extend(_check_neighborhood(neighborhood))

    repair = _load_json(
        root / "data/upba_energy/upba_v2_energy_repair_selector_benchmark_seed20260526_20260527.json"
    )
    payloads["repair_selector"] = repair
    checks.extend(_check_repair_selector(repair))

    cross_seed = _load_json(
        root / "data/upba_energy/upba_v2_repair_selector_cross_seed_seed20260526_20260531.json"
    )
    payloads["repair_selector_cross_seed"] = cross_seed
    checks.extend(_check_repair_selector_cross_seed(cross_seed))

    formal = _load_json(
        root / "data/upba_energy/upba_v2_repair_selector_formal_boundary_receipt.json"
    )
    payloads["formal_boundary"] = formal
    checks.extend(_check_formal_boundary(formal))

    fallback_formal = _load_json(
        root / "data/upba_energy/upba_v2_fallback_checked_stop_formal_receipt.json"
    )
    lean_source = (
        root / "lean-mathlib/Proofs/UniformBatchOptimality.lean"
    ).read_text(encoding="utf-8")
    payloads["fallback_checked_stop_formal"] = fallback_formal
    checks.extend(_check_fallback_checked_stop_formal(fallback_formal, lean_source))

    fallback_audit = _load_json(
        root / "data/upba_energy/upba_v2_energy_fallback_permutation_audit_200_seed20260518.json"
    )
    payloads["fallback_permutation_audit"] = fallback_audit
    checks.extend(_check_fallback_permutation_audit(fallback_audit))

    topk_sweep = _load_json(
        root / "data/upba_energy/upba_v2_energy_topk_sweep_holdout_seed20260518.json"
    )
    payloads["topk_sweep"] = topk_sweep
    checks.extend(_check_topk_sweep(topk_sweep))

    popperpad_readme = (
        root / "internal/popperpad/zenoenergy/README.md"
    ).read_text(encoding="utf-8")
    checks.extend(_check_popperpad_status_text(popperpad_readme))
    if run_popperpad_doctor:
        checks.append(_run_popperpad_doctor(root))

    ok = all(check.passed for check in checks)
    return {
        "schema": "zenodex/energy/research_evidence_replay_receipt/v1",
        "ok": ok,
        "check_count": len(checks),
        "passed_count": sum(1 for check in checks if check.passed),
        "failed_count": sum(1 for check in checks if not check.passed),
        "checks": [check.to_dict() for check in checks],
        "summary": _summary(payloads),
    }


def _check_set_aware(report: dict[str, Any]) -> list[EvidenceCheck]:
    checks: list[EvidenceCheck] = []
    checks.append(
        _expect_equal(
            "set_aware.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_set_aware_comparison/v1",
        )
    )
    modes = report["modes"]
    checks.append(
        _expect_true(
            "set_aware.zero_invalid_accepts",
            all(int(mode["invalid_accept_count"]) == 0 for mode in modes.values()),
            "all modes have invalid_accept_count = 0",
        )
    )
    checks.append(
        _expect_true(
            "set_aware.aggregate_top10_recall",
            float(modes["aggregate_learned"]["top_10_recall"]) >= 1.0,
            "aggregate learned top_10_recall is 1.0",
        )
    )
    checks.append(
        _expect_true(
            "set_aware.negative_knowledge_recorded",
            bool(report["interpretation"]["set_aware_top1_improved"]) is False
            and float(modes["set_aware_learned"]["mean_verifier_calls"])
            >= float(modes["aggregate_learned"]["mean_verifier_calls"]),
            "set-aware linear ranker did not beat aggregate learned baseline",
        )
    )
    return checks


def _check_neighborhood(report: dict[str, Any]) -> list[EvidenceCheck]:
    limited = report["modes"]["limited"]
    neighborhood = report["modes"]["neighborhood"]
    return [
        _expect_equal(
            "neighborhood.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_neighborhood_benchmark/v1",
        ),
        _expect_true(
            "neighborhood.safety",
            int(neighborhood["invalid_accept_count"]) == 0
            and int(neighborhood["original_subset_violation_count"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True,
            "zero invalid accepts, zero subset violations, verifier authoritative",
        ),
        _expect_true(
            "neighborhood.regret_reduced",
            float(neighborhood["mean_volume_regret"]) < float(limited["mean_volume_regret"]),
            "neighborhood reduces mean volume regret versus limited",
        ),
        _expect_true(
            "neighborhood.call_cost_negative",
            float(neighborhood["mean_calls_until_full_winner_or_exhausted"])
            > float(limited["mean_calls_until_full_winner_or_exhausted"]),
            "neighborhood increases calls until full winner, negative knowledge preserved",
        ),
    ]


def _check_repair_selector(report: dict[str, Any]) -> list[EvidenceCheck]:
    modes = report["modes"]
    full = modes["full_neighborhood"]
    learned = modes["learned_selected"]
    hand = modes["hand_selected"]
    return [
        _expect_equal(
            "repair_selector.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_repair_selector_benchmark/v1",
        ),
        _expect_true(
            "repair_selector.safety",
            _all_modes_zero(modes)
            and int(report["safety"]["invalid_accept_count"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True,
            "zero invalid accepts and verifier authoritative",
        ),
        _expect_true(
            "repair_selector.compression",
            float(learned["candidate_count_mean"]) < float(full["candidate_count_mean"])
            and float(learned["mean_added_count"]) < float(full["mean_added_count"])
            and float(learned["mean_volume_regret"]) <= float(full["mean_volume_regret"]),
            "learned selector compresses full neighborhood without higher mean volume regret",
        ),
        _expect_true(
            "repair_selector.hand_baseline_negative",
            float(learned["mean_volume_regret"]) >= float(hand["mean_volume_regret"]),
            "learned selector does not strictly beat hand-selected subset on this split",
        ),
    ]


def _check_repair_selector_cross_seed(report: dict[str, Any]) -> list[EvidenceCheck]:
    aggregate = report["aggregate"]
    learned = aggregate["modes"]["learned_selected"]
    full = aggregate["modes"]["full_neighborhood"]
    return [
        _expect_equal(
            "repair_selector_cross_seed.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_repair_selector_cross_seed/v1",
        ),
        _expect_true(
            "repair_selector_cross_seed.safety",
            bool(aggregate["all_safety_passed"]) is True
            and int(report["safety"]["invalid_accept_count"]) == 0
            and int(report["safety"]["original_subset_violation_count"]) == 0,
            "all cross-seed runs have zero invalid accepts and zero subset violations",
        ),
        _expect_true(
            "repair_selector_cross_seed.compression_all_pairs",
            int(aggregate["compression_pass_count"]) == int(report["run_count"])
            and int(aggregate["compression_fail_count"]) == 0,
            "compression passed on every seed pair",
        ),
        _expect_true(
            "repair_selector_cross_seed.aggregate_regret",
            float(learned["mean_volume_regret"]["mean"])
            <= float(full["mean_volume_regret"]["mean"]),
            "learned selected aggregate mean regret is no worse than full neighborhood",
        ),
        _expect_true(
            "repair_selector_cross_seed.hand_negative",
            int(aggregate["strict_hand_win_count"]) < int(report["run_count"]),
            "learned selector does not strictly beat hand-selected subset on every seed pair",
        ),
    ]


def _check_formal_boundary(report: dict[str, Any]) -> list[EvidenceCheck]:
    names = set(str(name) for name in report["formal_names"])
    return [
        _expect_equal(
            "formal_boundary.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_repair_selector_formal_boundary_receipt/v1",
        ),
        _expect_true(
            "formal_boundary.commands",
            all(int(command["exit_code"]) == 0 for command in report["commands"]),
            "Lean target and focused formal regression are recorded as passing",
        ),
        _expect_true(
            "formal_boundary.names",
            {
                "def AdvisorySelectedRepairSet",
                "theorem advisory_selected_repair_set_implies_candidate_subset",
                "theorem advisory_selected_repair_set_upper_bound_certificate_implies_base_weak_optimal",
            }.issubset(names),
            "selector-specific Lean names are present in receipt",
        ),
        _expect_true(
            "formal_boundary.scope_limit",
            "base list" in str(report["limits"]),
            "receipt states base-list scope limit",
        ),
    ]


def _check_fallback_checked_stop_formal(
    report: dict[str, Any],
    lean_source: str,
) -> list[EvidenceCheck]:
    names = set(str(name) for name in report["formal_names"])
    required = {
        "def FullFallbackEquivalentOrder",
        "theorem full_fallback_equivalent_order_preserves_membership_iff",
        "theorem full_fallback_equivalent_order_preserves_weak_optimality_iff",
        "def CheckedStopCertificate",
        "theorem checked_stop_certificate_implies_concat_weak_optimal",
        "theorem checked_stop_certificate_with_full_permutation_implies_full_weak_optimal",
        "theorem checked_stop_certificate_with_exact_full_implies_global_weak_optimal",
        "theorem reordered_exact_upper_bound_certificate_implies_global_weak_optimal",
        "theorem upba_v2_advisory_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal",
        "theorem upba_v2_hard_barrier_hybrid_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal",
        "theorem upba_v2_dominance_pruned_partial_fill_bounded_grid_certificate_implies_global_weak_optimal",
    }
    missing_from_source = [
        name
        for name in sorted(required)
        if name not in lean_source
    ]
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b")
    return [
        _expect_equal(
            "fallback_checked_stop_formal.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_fallback_checked_stop_formal_receipt/v1",
        ),
        _expect_true(
            "fallback_checked_stop_formal.commands",
            all(int(command["exit_code"]) == 0 for command in report["commands"]),
            "Lean target and focused formal regression are recorded as passing",
        ),
        _expect_true(
            "fallback_checked_stop_formal.names",
            required.issubset(names) and not missing_from_source,
            "fallback and checked-stop theorem names are present in receipt and Lean source",
        ),
        _expect_true(
            "fallback_checked_stop_formal.no_placeholders",
            forbidden.search(lean_source) is None,
            "Lean source has no sorry/admit/axiom/unsafe placeholders",
        ),
        _expect_true(
            "fallback_checked_stop_formal.scope_limit",
            "Online early stop" in " ".join(str(limit) for limit in report["limits"]),
            "receipt states online early-stop suffix-bound limit",
        ),
    ]


def _check_fallback_permutation_audit(report: dict[str, Any]) -> list[EvidenceCheck]:
    modes = report["modes"]
    learned = modes["learned"]
    hybrid = modes["hybrid"]
    return [
        _expect_equal(
            "fallback_permutation_audit.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_benchmark_report/v1",
        ),
        _expect_true(
            "fallback_permutation_audit.zero_invalid_accepts",
            int(report["invalid_accept_count"]) == 0 and _all_modes_zero(modes),
            "all fallback audit modes have zero invalid accepts",
        ),
        _expect_true(
            "fallback_permutation_audit.permutation_premise",
            all(int(mode["permutation_violation_count"]) == 0 for mode in modes.values()),
            "all audit modes preserve the full-fallback permutation premise",
        ),
        _expect_true(
            "fallback_permutation_audit.learned_recovery",
            int(learned["fallback_recovered_count"]) == int(learned["batches"])
            and float(learned["top_10_recall"]) == 1.0
            and float(hybrid["top_10_recall"]) == 1.0,
            "learned and hybrid orderings recover every exact winner by top-k or fallback",
        ),
        _expect_true(
            "fallback_permutation_audit.checked_stop_offline",
            float(learned["checked_stop_top_k_rate"]) == 1.0
            and float(learned["checked_stop_at_winner_rate"]) == 1.0
            and float(modes["random"]["checked_stop_top_k_rate"]) < 1.0,
            "checked-stop audit succeeds for learned top-k and remains nontrivial versus random",
        ),
    ]


def _check_topk_sweep(report: dict[str, Any]) -> list[EvidenceCheck]:
    modes = report["modes"]
    learned = modes["learned"]
    hybrid = modes["hybrid"]
    return [
        _expect_equal(
            "topk_sweep.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_topk_sweep/v1",
        ),
        _expect_true(
            "topk_sweep.permutation_premise",
            all(int(mode["permutation_violation_count"]) == 0 for mode in modes.values()),
            "all top-k sweep modes preserve hash-permutation ordering",
        ),
        _expect_true(
            "topk_sweep.learned_checked_stop_k2",
            float(learned["top_k"]["2"]["checked_stop_top_k_rate"]) == 1.0
            and float(learned["top_k"]["2"]["false_exclusion_rate"]) == 0.0
            and float(hybrid["top_k"]["2"]["checked_stop_top_k_rate"]) == 1.0,
            "learned and hybrid checked-stop audits reach 100% by k=2 on holdout",
        ),
        _expect_true(
            "topk_sweep.checked_stop_at_winner",
            all(float(mode["checked_stop_at_winner_rate"]) == 1.0 for mode in modes.values()),
            "checked-stop certificate holds at the exact winner for every mode",
        ),
        _expect_true(
            "topk_sweep.random_top10_negative",
            float(modes["random"]["top_k"]["10"]["false_exclusion_rate"]) > 0.0,
            "random top-10 misses many winners, so the sweep is not vacuous",
        ),
    ]


def _check_popperpad_status_text(readme: str) -> list[EvidenceCheck]:
    expected = {
        "H_ZENOENERGY_SET_AWARE_COMPARE_SAFETY_20260517": "supported",
        "H_ZENOENERGY_SET_AWARE_LINEAR_STRICTLY_IMPROVES_AGGREGATE_20260517": "falsified",
        "H_ZENOENERGY_NEIGHBORHOOD_SAFETY_SUBSET_20260517_V2": "supported",
        "H_ZENOENERGY_NEIGHBORHOOD_REDUCES_REGRET_20260517_V2": "supported",
        "H_ZENOENERGY_NEIGHBORHOOD_REDUCES_VERIFIER_CALLS_20260517_V2": "falsified",
        "H_ZENOENERGY_REPAIR_SELECTOR_SAFETY_20260517": "supported",
        "H_ZENOENERGY_REPAIR_SELECTOR_COMPRESSES_FULL_NEIGHBORHOOD_20260517": "supported",
        "H_ZENOENERGY_REPAIR_SELECTOR_STRICTLY_BEATS_HAND_SELECTED_20260517": "falsified",
        "H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_SAFETY_20260517": "supported",
        "H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_COMPRESSES_FULL_NEIGHBORHOOD_20260517": "supported",
        "H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_STRICTLY_BEATS_HAND_SELECTED_20260517": "falsified",
        "H_ZENOENERGY_REPAIR_SELECTOR_FORMAL_BOUNDARY_RECEIPT_20260517": "supported",
        "H_ZENOENERGY_FALLBACK_CHECKED_STOP_FORMAL_RECEIPT_20260517": "supported",
    }
    checks = []
    for hypothesis_id, state in expected.items():
        checks.append(
            _expect_true(
                f"popperpad.status.{hypothesis_id}",
                f"{hypothesis_id}: {state}" in readme,
                f"{hypothesis_id} is recorded as {state}",
            )
        )
    return checks


def _run_popperpad_doctor(root: Path) -> EvidenceCheck:
    proc = subprocess.run(
        [
            sys.executable,
            "-m",
            "popperpad",
            "--pad",
            "internal/popperpad/zenoenergy",
            "doctor",
        ],
        cwd=root,
        env={**_clean_env(), "PYTHONPATH": "external/PopperPad/src"},
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=30,
        check=False,
    )
    if proc.returncode != 0:
        return EvidenceCheck(
            check_id="popperpad.doctor",
            passed=False,
            detail=(proc.stdout + proc.stderr).strip()[:500],
        )
    try:
        payload = json.loads(proc.stdout)
        passed = bool(payload["ok"]) and bool(payload["result"]["ok"])
    except (json.JSONDecodeError, KeyError, TypeError):
        passed = False
    return EvidenceCheck(
        check_id="popperpad.doctor",
        passed=passed,
        detail="PopperPad doctor ok" if passed else proc.stdout.strip()[:500],
    )


def _summary(payloads: dict[str, Any]) -> dict[str, Any]:
    repair_cross = payloads["repair_selector_cross_seed"]
    fallback_audit = payloads["fallback_permutation_audit"]
    topk_sweep = payloads["topk_sweep"]
    return {
        "set_aware_negative_knowledge": payloads["set_aware"]["interpretation"][
            "negative_knowledge"
        ],
        "neighborhood_regret_delta": payloads["neighborhood"]["deltas"][
            "mean_volume_regret_delta"
        ],
        "repair_selector_cross_seed": {
            "run_count": repair_cross["run_count"],
            "compression_pass_count": repair_cross["aggregate"]["compression_pass_count"],
            "strict_hand_win_count": repair_cross["aggregate"]["strict_hand_win_count"],
            "invalid_accept_count": repair_cross["safety"]["invalid_accept_count"],
            "original_subset_violation_count": repair_cross["safety"][
                "original_subset_violation_count"
            ],
        },
        "formal_boundary_claim": payloads["formal_boundary"]["claim"],
        "fallback_checked_stop_claim": payloads["fallback_checked_stop_formal"]["claim"],
        "fallback_permutation_audit": {
            "batches": fallback_audit["modes"]["learned"]["batches"],
            "learned_top_10_recall": fallback_audit["modes"]["learned"]["top_10_recall"],
            "learned_checked_stop_top_k_rate": fallback_audit["modes"]["learned"][
                "checked_stop_top_k_rate"
            ],
            "learned_permutation_violation_count": fallback_audit["modes"]["learned"][
                "permutation_violation_count"
            ],
            "invalid_accept_count": fallback_audit["invalid_accept_count"],
        },
        "topk_sweep": {
            "batches": topk_sweep["modes"]["learned"]["batches"],
            "learned_k2_checked_stop_rate": topk_sweep["modes"]["learned"]["top_k"]["2"][
                "checked_stop_top_k_rate"
            ],
            "learned_k2_false_exclusion_rate": topk_sweep["modes"]["learned"]["top_k"]["2"][
                "false_exclusion_rate"
            ],
            "random_k10_false_exclusion_rate": topk_sweep["modes"]["random"]["top_k"]["10"][
                "false_exclusion_rate"
            ],
        },
    }


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Research Evidence Replay",
        "",
        "```text",
        f"ok: {str(report['ok']).lower()}",
        f"check_count: {report['check_count']}",
        f"passed_count: {report['passed_count']}",
        f"failed_count: {report['failed_count']}",
        "```",
        "",
        "| check | result | detail |",
        "| --- | --- | --- |",
    ]
    for check in report["checks"]:
        lines.append(
            "| "
            + " | ".join(
                (
                    str(check["check_id"]),
                    "pass" if check["passed"] else "fail",
                    str(check["detail"]).replace("|", "/"),
                )
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "## Summary",
            "",
            "```json",
            json.dumps(report["summary"], indent=2, sort_keys=True),
            "```",
        ]
    )
    return "\n".join(lines) + "\n"


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(path)
    return json.loads(path.read_text(encoding="utf-8"))


def _all_modes_zero(modes: dict[str, Any]) -> bool:
    return all(
        int(mode["invalid_accept_count"]) == 0
        and int(mode.get("original_subset_violation_count", 0)) == 0
        for mode in modes.values()
    )


def _expect_equal(check_id: str, actual: object, expected: object) -> EvidenceCheck:
    return EvidenceCheck(
        check_id=check_id,
        passed=actual == expected,
        detail=f"expected {expected!r}, observed {actual!r}",
    )


def _expect_true(check_id: str, condition: bool, detail: str) -> EvidenceCheck:
    return EvidenceCheck(check_id=check_id, passed=bool(condition), detail=detail)


def _clean_env() -> dict[str, str]:
    import os

    return {key: value for key, value in os.environ.items() if key != "PYTHONPATH"}


if __name__ == "__main__":
    raise SystemExit(main())

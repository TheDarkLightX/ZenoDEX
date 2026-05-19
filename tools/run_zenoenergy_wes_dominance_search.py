#!/usr/bin/env python3
"""Run WES over ZenoEnergy UPBA v2 dominance-cover candidates.

The WES layer ranks candidate pruning claims. The checker reconstructs the
synthetic UPBA batch, runs deterministic UPBA verification, and labels only the
result of the dominance-cover certificate check.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from random import Random
from time import perf_counter
from typing import Any, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

WES_SRC = ROOT / "external/WitnessEnergySearch/src"
if WES_SRC.exists() and str(WES_SRC) not in sys.path:
    sys.path.insert(0, str(WES_SRC))

from src.core.uniform_batch_clearing import UniformBatchCertificateV1
from src.energy.upba_v2_dominance_cover import (
    build_upba_v2_dominance_cover_certificate,
    verify_upba_v2_dominance_cover_certificate,
)
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import hand_energy_from_record
from src.energy.upba_v2_ranker import (
    VerifiedCandidateResult,
    deterministic_best_verified_candidate,
    verify_candidates_in_order,
)
from tools.generate_upba_energy_dataset import SyntheticBatch, generate_synthetic_batch


SYSTEM_ID = "zenoenergy_upba_v2_dominance_cover"
CHECKER_ID = "zenoenergy_upba_v2_dominance_cover_checker"
TARGET_PASS = "dominance_cover_certificate_passes"
TARGET_REJECT_WEAK = "dominance_cover_rejects_weak_pruned_set"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=40)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--budget", type=int, default=60)
    parser.add_argument("--top-k", type=int, default=20)
    parser.add_argument("--seed", type=int, default=20260539)
    parser.add_argument("--out-dir", type=Path, default=Path("runs/wes/zenoenergy_dominance_cover"))
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    parser.add_argument("--candidates-jsonl", type=Path)
    args = parser.parse_args()

    report = run_zenoenergy_wes_dominance_search(
        batches=args.batches,
        candidates_per_batch=args.candidates_per_batch,
        budget=args.budget,
        top_k=args.top_k,
        seed=args.seed,
        out_dir=args.out_dir,
        candidates_jsonl=args.candidates_jsonl,
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


def run_zenoenergy_wes_dominance_search(
    *,
    batches: int,
    candidates_per_batch: int,
    budget: int,
    top_k: int,
    seed: int,
    out_dir: Path,
    candidates_jsonl: Path | None = None,
) -> dict[str, Any]:
    Candidate, CheckResult, ResultLabel, LinearEnergyRanker, compare_candidate_search_policies = _wes_api()
    candidates = build_wes_dominance_candidates(
        batches=batches,
        candidates_per_batch=candidates_per_batch,
        seed=seed,
    )
    if candidates_jsonl is not None:
        candidates_jsonl.parent.mkdir(parents=True, exist_ok=True)
        candidates_jsonl.write_text(
            "".join(json.dumps(candidate.to_obj(), sort_keys=True) + "\n" for candidate in candidates),
            encoding="utf-8",
        )

    # Small transparent prior: candidate metadata says whether the pruning claim
    # is a known constructive witness or a known weak-pruning negative control.
    ranker = LinearEnergyRanker(
        weights={
            "constraint.dominance_cover_constructive_witness": -3.0,
            "constraint.dominance_cover_negative_control": -2.0,
            "constraint.pruned_candidate_count": 0.05,
            "checker_budget_cost": 0.02,
        }
    )
    started = perf_counter()
    wes_report = compare_candidate_search_policies(
        candidates=candidates,
        out_dir=out_dir,
        checker=check_wes_dominance_candidate,
        budget=max(1, budget),
        seed=f"zenoenergy-wes-{seed}",
        ranker=ranker,
        run_id="WES-ZENOENERGY-DOMINANCE-COVER-001",
        top_k=max(1, top_k),
        online_learning_rate=0.02,
        online_window=64,
    )
    elapsed_ms = (perf_counter() - started) * 1000.0
    summary = _summarize_wes_report(wes_report)
    ok = (
        summary["input_candidates"] == len(candidates)
        and summary["model_online_checked"] > 0
        and summary["model_online_useful_at_k"] > 0
        and summary["declared_priority_useful_at_k"] > 0
        and summary["checker_invalid_accept_count"] == 0
    )
    return {
        "schema": "zenodex/energy/zenoenergy_wes_dominance_search/v1",
        "ok": ok,
        "wes_commit": _wes_commit(),
        "wes_report_schema": wes_report.get("schema"),
        "batches": batches,
        "candidates_per_batch": candidates_per_batch,
        "input_candidates": len(candidates),
        "budget": budget,
        "top_k": top_k,
        "seed": seed,
        "wall_clock_ms": elapsed_ms,
        "summary": summary,
        "wes_report": wes_report,
        "safety": {
            "verifier_authoritative": True,
            "wes_ranks_only": True,
            "scorer_authorizes_settlement": False,
            "model_output_in_state_root": False,
            "invalid_accept_count": 0,
        },
        "limits": [
            "The WES bridge uses bounded synthetic UPBA batches reconstructed from deterministic seeds.",
            "WES ranks dominance-cover candidate claims; UPBA verification and dominance-cover checking provide labels.",
            "The bridge is search-efficiency evidence only. It is not a UPBA v2 bounded-grid production verifier.",
        ],
        "negative_knowledge": [
            "Weak pruned sets remain useful negative controls because the checker rejects uncovered better verified candidates.",
            "A passing WES search report does not remove the full-list completeness obligation for bounded-grid claims.",
        ],
    }


def build_wes_dominance_candidates(
    *,
    batches: int,
    candidates_per_batch: int,
    seed: int,
) -> list[Any]:
    Candidate, _CheckResult, _ResultLabel, _LinearEnergyRanker, _compare = _wes_api()
    candidates: list[Any] = []
    rng = Random(seed)
    for batch_index in range(batches):
        # Advance through the same random stream that the checker will replay
        # per explicit batch seed. The candidate payload stores standalone seed
        # material so WES can check rows in any order.
        batch_seed = rng.randint(1, 2**31 - 1)
        modes = (
            ("winner_only", "dominance_cover_winner_only", 0.0, True, False),
            ("hand_top1", "dominance_cover_hand_top1", 1.0, False, False),
            ("weak_pruned", "dominance_cover_weak_negative", 2.0, False, True),
        )
        for mode, lane, declared_energy, constructive, negative in modes:
            predicates = [TARGET_PASS]
            if negative:
                predicates = [TARGET_REJECT_WEAK]
            candidates.append(
                Candidate(
                    system_id=SYSTEM_ID,
                    candidate_id=f"zenoenergy-dominance-{seed}-{batch_index}-{mode}",
                    source_lane=lane,
                    state_features={
                        "batch_index": batch_index,
                        "candidates_per_batch": candidates_per_batch,
                    },
                    action_features={
                        "prune_mode": mode,
                        "pruned_candidate_count": 1,
                    },
                    constraint_features={
                        "declared_energy": declared_energy,
                        "search_priority": declared_energy,
                        "dominance_cover_constructive_witness": constructive,
                        "dominance_cover_negative_control": negative,
                        "dominance_cover_claim": True,
                    },
                    checker_budget_cost=1.0,
                    expected_checker=CHECKER_ID,
                    target_predicates=tuple(predicates),
                    deterministic_seed=f"{seed}:{batch_seed}:{batch_index}:{mode}",
                    payload={
                        "schema": "zenodex/energy/wes_dominance_candidate_payload/v1",
                        "seed": seed,
                        "batch_seed": batch_seed,
                        "batch_index": batch_index,
                        "candidates_per_batch": candidates_per_batch,
                        "mode": mode,
                    },
                )
            )
    return candidates


def check_wes_dominance_candidate(candidate: Any) -> Any:
    _Candidate, CheckResult, ResultLabel, _LinearEnergyRanker, _compare = _wes_api()
    started = perf_counter()
    try:
        payload = candidate.payload
        if not isinstance(payload, dict):
            return CheckResult(
                result=ResultLabel.MALFORMED,
                checker=CHECKER_ID,
                checker_ms=(perf_counter() - started) * 1000.0,
                notes="candidate payload must be an object",
            )
        mode = str(payload["mode"])
        batch = generate_synthetic_batch(
            rng=Random(int(payload["batch_seed"])),
            batch_index=int(payload["batch_index"]),
            target_candidate_count=int(payload["candidates_per_batch"]),
        )
        full_candidates = tuple(item.candidate for item in batch.candidates)
        full_results = verify_candidates_in_order(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=full_candidates,
        )
        winner = deterministic_best_verified_candidate(full_results)
        if winner is None:
            return _check_result(
                CheckResult,
                ResultLabel,
                started=started,
                result=ResultLabel.CHECKED_SAFE,
                notes="synthetic full list had no verifier-accepted candidate",
                telemetry={"mode": mode, "full_valid_count": 0},
            )
        pruned_candidates, winner_hash = _pruned_candidates_for_mode(
            mode=mode,
            batch=batch,
            full_results=full_results,
            winner=winner,
        )
        if not pruned_candidates:
            return _check_result(
                CheckResult,
                ResultLabel,
                started=started,
                result=ResultLabel.CHECKED_SAFE,
                notes="mode produced no pruned candidate",
                telemetry={"mode": mode, "full_valid_count": sum(1 for item in full_results if item.ok)},
            )
        pruned_results = verify_candidates_in_order(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=pruned_candidates,
        )
        receipt = build_upba_v2_dominance_cover_certificate(
            full_results=full_results,
            pruned_results=pruned_results,
            winner_hash=winner_hash,
            full_list_complete_for_claim=True,
            scope=f"wes-synthetic-full-list:{mode}",
        )
        structural_ok = verify_upba_v2_dominance_cover_certificate(receipt)
        telemetry = {
            "mode": mode,
            "dominance_cover_ok": receipt["dominance_cover_ok"],
            "certificate_ok": receipt["ok"],
            "structural_verify_ok": structural_ok,
            "full_valid_count": receipt["full_valid_count"],
            "pruned_valid_count": receipt["pruned_valid_count"],
            "uncovered_full_count": receipt["uncovered_full_count"],
            "certificate_hash": receipt["certificate_hash"],
        }
        if bool(receipt["ok"]):
            return _check_result(
                CheckResult,
                ResultLabel,
                started=started,
                result=ResultLabel.NEAR_MISS,
                violated_predicate=TARGET_PASS,
                replay_receipt=str(receipt["certificate_hash"]),
                witness_value=0.9,
                telemetry=telemetry,
                notes="dominance-cover certificate passed for supplied verified full list",
            )
        if mode == "weak_pruned" and int(receipt["uncovered_full_count"]) > 0:
            return _check_result(
                CheckResult,
                ResultLabel,
                started=started,
                result=ResultLabel.INVARIANT_VIOLATION,
                violated_predicate=TARGET_REJECT_WEAK,
                replay_receipt=str(receipt["certificate_hash"]),
                witness_value=0.75,
                telemetry=telemetry,
                notes="weak pruned claim rejected because a better verified candidate was uncovered",
            )
        return _check_result(
            CheckResult,
            ResultLabel,
            started=started,
            result=ResultLabel.CHECKED_SAFE,
            replay_receipt=str(receipt["certificate_hash"]),
            telemetry=telemetry,
            notes="dominance-cover claim did not pass",
        )
    except Exception as exc:
        return CheckResult(
            result=ResultLabel.MALFORMED,
            checker=CHECKER_ID,
            checker_ms=(perf_counter() - started) * 1000.0,
            telemetry={"error": type(exc).__name__},
            notes=str(exc),
        )


def _pruned_candidates_for_mode(
    *,
    mode: str,
    batch: SyntheticBatch,
    full_results: Sequence[VerifiedCandidateResult],
    winner: VerifiedCandidateResult,
) -> tuple[tuple[UniformBatchCertificateV1, ...], str | None]:
    if mode == "winner_only":
        return (winner.candidate,), winner.certificate_hash
    if mode == "hand_top1":
        return _hand_ordered_candidates(batch=batch, candidates=tuple(item.candidate for item in batch.candidates))[:1], None
    if mode == "weak_pruned":
        accepted = sorted(
            (result for result in full_results if result.ok),
            key=lambda result: (result.volume, result.surplus, result.certificate_hash),
        )
        if len(accepted) < 2:
            return (), None
        return (accepted[0].candidate,), accepted[0].certificate_hash
    raise ValueError(f"unknown dominance-cover prune mode: {mode}")


def _hand_ordered_candidates(
    *,
    batch: SyntheticBatch,
    candidates: Sequence[UniformBatchCertificateV1],
) -> tuple[UniformBatchCertificateV1, ...]:
    from src.energy.upba_v2_ranker import advisory_candidate_hash

    return tuple(
        sorted(
            candidates,
            key=lambda candidate: (
                hand_energy_from_record(
                    extract_upba_v2_feature_record(
                        pool=batch.pool,
                        intents=batch.intents,
                        balances=batch.balances,
                        candidate=candidate,
                        include_verifier_label=False,
                    )
                ),
                advisory_candidate_hash(candidate),
            ),
        )
    )


def _check_result(
    CheckResult: type,
    ResultLabel: Any,
    *,
    started: float,
    result: Any,
    violated_predicate: str | None = None,
    replay_receipt: str | None = None,
    witness_value: float | None = None,
    telemetry: dict[str, object] | None = None,
    notes: str = "",
) -> Any:
    return CheckResult(
        result=result,
        checker=CHECKER_ID,
        checker_ms=(perf_counter() - started) * 1000.0,
        violated_predicate=violated_predicate,
        replay_receipt=replay_receipt,
        witness_value=witness_value,
        telemetry=telemetry or {},
        notes=notes,
    )


def _summarize_wes_report(report: dict[str, object]) -> dict[str, object]:
    runs = report["runs"]
    if not isinstance(runs, dict):
        raise TypeError("WES report runs must be a mapping")
    summary: dict[str, object] = {
        "input_candidates": int(report["input_candidates"]),
        "top_k": int(report["top_k"]),
        "checker_invalid_accept_count": 0,
    }
    for name, run in runs.items():
        if not isinstance(run, dict):
            continue
        order = run["actual_search_order"]
        if not isinstance(order, dict):
            continue
        summary[f"{name}_checked"] = int(run["checked"])
        summary[f"{name}_useful_at_k"] = int(order["useful_at_k"])
        summary[f"{name}_calls_to_first_useful"] = order["calls_to_first_useful"]
        summary[f"{name}_near_misses_at_k"] = int(order["near_misses_at_k"])
        summary[f"{name}_non_useful_at_k"] = int(order["non_useful_at_k"])
    return summary


def _wes_api() -> tuple[Any, Any, Any, Any, Any]:
    if not WES_SRC.exists():
        raise RuntimeError(
            "external/WitnessEnergySearch is required; clone git@github.com:TheDarkLightX/WitnessEnergySearch.git into external/"
        )
    try:
        from wes.ranker import LinearEnergyRanker
        from wes.schema import Candidate, CheckResult, ResultLabel
        from wes.search import compare_candidate_search_policies
    except ModuleNotFoundError as exc:
        raise RuntimeError("WES is not importable from external/WitnessEnergySearch/src") from exc
    return Candidate, CheckResult, ResultLabel, LinearEnergyRanker, compare_candidate_search_policies


def _wes_commit() -> str | None:
    head = ROOT / "external/WitnessEnergySearch/.git/HEAD"
    if not head.exists():
        return None
    text = head.read_text(encoding="utf-8").strip()
    if text.startswith("ref: "):
        ref_path = ROOT / "external/WitnessEnergySearch/.git" / text.removeprefix("ref: ")
        return ref_path.read_text(encoding="utf-8").strip() if ref_path.exists() else None
    return text


def _markdown_report(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# ZenoEnergy WES Dominance Search",
        "",
        "WES ranks candidate dominance-cover pruning claims. The UPBA verifier and deterministic dominance-cover checker provide the labels.",
        "",
        "## Summary",
        "",
        f"WES commit: `{report['wes_commit']}`",
        "",
        "| policy | checked | useful@k | calls to first useful | near misses@k | non-useful@k |",
        "| --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for policy in (
        "model_online",
        "model_frozen",
        "declared_priority",
        "cheap_first",
        "input_order",
        "random_seeded",
    ):
        lines.append(
            "| {policy} | {checked} | {useful} | {calls} | {near} | {non_useful} |".format(
                policy=policy,
                checked=summary.get(f"{policy}_checked", 0),
                useful=summary.get(f"{policy}_useful_at_k", 0),
                calls=summary.get(f"{policy}_calls_to_first_useful"),
                near=summary.get(f"{policy}_near_misses_at_k", 0),
                non_useful=summary.get(f"{policy}_non_useful_at_k", 0),
            )
        )
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- WES changes checker order only.",
            "- A passing WES result does not authorize settlement.",
            "- The dominance-cover checker still depends on deterministic UPBA verification.",
            "- The benchmark uses bounded synthetic full lists, so production promotion still requires real replay and full-list completeness evidence.",
            "",
            "## Negative Knowledge",
            "",
        ]
    )
    for item in report["negative_knowledge"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


if __name__ == "__main__":
    raise SystemExit(main())

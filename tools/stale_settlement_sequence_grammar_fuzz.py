from __future__ import annotations

"""State-feedback explorer for stale provided-settlement replay and settlement drift."""

import argparse
import copy
import json
import sys
from pathlib import Path
from typing import Any, Sequence

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from tools import dex_engine_settlement_sequence_grammar_fuzz as legacy
from tools.stateful_feedback import (
    ExplorationTargetReport,
    FeedbackMode,
    Mutation,
    explore_bounded_frontier,
    load_dangerous_surface_manifest,
    report_to_json,
)
from tools.stateful_semantics import sequence_action_summary, stale_settlement_semantic_state


TARGET = legacy.TARGET_BY_NAME["dex_engine_settlement_sequence"]
SEED_DERIVATION = "SettlementSeq->WarmupThenStatefulProvidedAb"
MUTATED_DERIVATIONS: tuple[tuple[str, str], ...] = (
    ("stale_provided_settlement", "SettlementSeq->WarmupThenStaleProvidedAb"),
    ("missing_required_settlement", "SettlementSeq->WarmupThenMissingSettlementRequired"),
    ("settlement_without_intents", "SettlementSeq->WarmupThenSettlementWithoutIntents"),
    ("too_many_settlement_fills", "SettlementSeq->WarmupThenTooManySettlementFills"),
)


def _case_payload(derivation: str) -> object:
    return copy.deepcopy(legacy._find_case(TARGET.name, derivation).payload)


def _seed_payload() -> object:
    return _case_payload(SEED_DERIVATION)


def _payload_expandable(payload: object) -> bool:
    return isinstance(payload, dict)


def _trace(payload: object) -> tuple[str, str, int]:
    return legacy._trace_outcome(
        runner=TARGET.runner,
        payload=payload,
        trace_files=TARGET.trace_files,
    )


def _mutation_for(derivation: str):
    return lambda payload: _case_payload(derivation)


MUTATIONS: tuple[Mutation, ...] = tuple(
    Mutation(name=name, apply=_mutation_for(derivation)) for name, derivation in MUTATED_DERIVATIONS
)


def explore_target(
    name: str = "stale_settlement_sequence",
    *,
    max_depth: int = 1,
    max_frontier: int = 64,
    target_manifest: str | None = None,
    target_id: str | None = None,
    feedback_mode: FeedbackMode = "stateful",
):
    if name != "stale_settlement_sequence":
        raise KeyError(f"unknown target: {name}")
    dangerous_surfaces = load_dangerous_surface_manifest(target_manifest)
    return explore_bounded_frontier(
        harness_id="settlement_sequence:stale_settlement_sequence",
        seed=_seed_payload(),
        mutations=MUTATIONS,
        trace_fn=_trace,
        expandable=_payload_expandable,
        max_depth=max_depth,
        max_frontier=max_frontier,
        feedback_mode=feedback_mode,
        dangerous_surfaces=dangerous_surfaces,
        target_id=target_id,
        semantic_state_fn=stale_settlement_semantic_state,
        action_summary_fn=lambda prev_payload, next_payload, mutation_name: sequence_action_summary(
            stale_settlement_semantic_state,
            prev_payload,
            next_payload,
            mutation_name,
        ),
    )


def explore_all_targets(
    *,
    max_depth: int = 1,
    max_frontier: int = 64,
    target_manifest: str | None = None,
    target_id: str | None = None,
    feedback_mode: FeedbackMode = "stateful",
):
    return (
        explore_target(
            max_depth=max_depth,
            max_frontier=max_frontier,
            target_manifest=target_manifest,
            target_id=target_id,
            feedback_mode=feedback_mode,
        ),
    )


def _reports_json(reports: Sequence[ExplorationTargetReport]) -> dict[str, Any]:
    return {
        "schema": "zenodex/stale-settlement-sequence-grammar-fuzz/v1",
        "reports": [report_to_json(report) for report in reports],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", default="stale_settlement_sequence", choices=("stale_settlement_sequence",))
    parser.add_argument("--format", default="json", choices=("json", "text"))
    parser.add_argument("--max-depth", type=int, default=1)
    parser.add_argument("--max-frontier", type=int, default=64)
    parser.add_argument("--target-manifest")
    parser.add_argument("--target-id")
    parser.add_argument("--feedback-mode", choices=("legacy", "stateful"), default="stateful")
    args = parser.parse_args(list(argv) if argv is not None else None)

    reports = explore_all_targets(
        max_depth=args.max_depth,
        max_frontier=args.max_frontier,
        target_manifest=args.target_manifest,
        target_id=args.target_id,
        feedback_mode=args.feedback_mode,
    )
    if args.format == "json":
        print(json.dumps(_reports_json(reports), indent=2, sort_keys=True))
        return 0
    for report in reports:
        print(
            f"[{report.target}] cases={report.total_cases} outcomes={report.unique_outcome_count} "
            f"paths={report.unique_path_count} states={report.unique_state_count} transitions={report.unique_transition_count}"
        )
        if report.reached_target_ids:
            print(f"  targets: {', '.join(report.reached_target_ids)}")
        for case in report.cases:
            print(f"  - depth={case.depth} {case.mutation}: {case.outcome_label} path={case.path_id} len={case.path_length}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

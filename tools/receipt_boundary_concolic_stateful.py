from __future__ import annotations

"""State-feedback wrapper for receipt boundary concolic exploration."""

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Sequence

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from tools import receipt_boundary_concolic as legacy
from tools.stateful_feedback import (
    ExplorationTargetReport,
    FeedbackMode,
    Mutation,
    explore_bounded_frontier,
    load_dangerous_surface_manifest,
    report_to_json,
)
from tools.stateful_semantics import receipt_boundary_semantic_state, sequence_action_summary


def _legacy_mutations(target: legacy.Target) -> tuple[Mutation, ...]:
    return tuple(Mutation(name=mutation.name, apply=mutation.apply) for mutation in target.mutations)


def explore_target(
    name: str,
    *,
    max_depth: int = 2,
    max_frontier: int = 256,
    target_manifest: str | None = None,
    target_id: str | None = None,
    feedback_mode: FeedbackMode = "stateful",
):
    target = legacy.TARGET_INDEX[name]
    dangerous_surfaces = load_dangerous_surface_manifest(target_manifest)
    semantic_state_fn = receipt_boundary_semantic_state(target.name)
    return explore_bounded_frontier(
        harness_id=f"receipt_boundary_concolic:{name}",
        seed=target.valid_seed,
        mutations=_legacy_mutations(target),
        trace_fn=lambda payload: legacy._trace_outcome(target, payload),
        expandable=lambda payload: legacy._payload_expandable(target, payload),
        max_depth=max_depth,
        max_frontier=max_frontier,
        feedback_mode=feedback_mode,
        dangerous_surfaces=dangerous_surfaces,
        target_id=target_id,
        semantic_state_fn=semantic_state_fn,
        action_summary_fn=lambda prev_payload, next_payload, mutation_name: sequence_action_summary(
            semantic_state_fn,
            prev_payload,
            next_payload,
            mutation_name,
        ),
    )


def explore_all_targets(
    *,
    max_depth: int = 2,
    max_frontier: int = 256,
    target_manifest: str | None = None,
    target_id: str | None = None,
    feedback_mode: FeedbackMode = "stateful",
):
    return tuple(
        explore_target(
            target.name,
            max_depth=max_depth,
            max_frontier=max_frontier,
            target_manifest=target_manifest,
            target_id=target_id,
            feedback_mode=feedback_mode,
        )
        for target in legacy.TARGETS
    )


def _reports_json(reports: Sequence[ExplorationTargetReport]) -> dict[str, Any]:
    return {
        "schema": "zenodex/receipt-boundary-concolic-stateful/v1",
        "reports": [report_to_json(report) for report in reports],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", default="all", choices=("all",) + tuple(sorted(legacy.TARGET_INDEX)))
    parser.add_argument("--format", default="json", choices=("json", "text"))
    parser.add_argument("--max-depth", type=int, default=2)
    parser.add_argument("--max-frontier", type=int, default=256)
    parser.add_argument("--target-manifest")
    parser.add_argument("--target-id")
    parser.add_argument("--feedback-mode", choices=("legacy", "stateful"), default="stateful")
    args = parser.parse_args(list(argv) if argv is not None else None)

    reports = (
        explore_all_targets(
            max_depth=args.max_depth,
            max_frontier=args.max_frontier,
            target_manifest=args.target_manifest,
            target_id=args.target_id,
            feedback_mode=args.feedback_mode,
        )
        if args.target == "all"
        else (
            explore_target(
                args.target,
                max_depth=args.max_depth,
                max_frontier=args.max_frontier,
                target_manifest=args.target_manifest,
                target_id=args.target_id,
                feedback_mode=args.feedback_mode,
            ),
        )
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

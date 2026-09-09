"""Replay five finite design counterexamples; this is not the ZenoLacuna engine."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


def quotient_question() -> dict[str, object]:
    relations = ({(0, 0)}, {(0, 0)}, {(0, 1)})
    answers = (0, 1, 1)
    violations = [
        [left, right]
        for left in range(3)
        for right in range(left + 1, 3)
        if relations[left] == relations[right] and answers[left] != answers[right]
    ]
    return {
        "id": "quotient_congruence",
        "counterexample": {"question_answers": answers, "bad_pairs": violations},
        "required_guard": "reject_question_not_constant_on_semantic_classes",
        "example_checked": violations == [[0, 1]],
    }


def incomplete_question_policy() -> dict[str, object]:
    answers = (0, 1, 1)
    partitions = [{h for h in range(3) if answers[h] == a} for a in (0, 1)]
    unresolved = [sorted(part) for part in partitions if len(part) > 1]
    return {
        "id": "unseparable_continuation",
        "counterexample": {
            "available_questions": 1,
            "useful_first_split": len(partitions) == 2,
            "unseparable_children": unresolved,
        },
        "required_guard": "propagate_tagged_infinity_to_root_policy",
        "example_checked": unresolved == [[1, 2]],
    }


def narrowed_assumptions() -> dict[str, object]:
    protected_applicability = {0, 1}
    revised_assumptions = {0}
    uncovered = sorted(protected_applicability - revised_assumptions)
    return {
        "id": "protected_applicability",
        "counterexample": {
            "positive_witness_survives": 0 in revised_assumptions,
            "lost_contexts": uncovered,
        },
        "required_guard": "preserve_each_protected_applicability_class",
        "example_checked": uncovered == [1] and bool(revised_assumptions),
    }


def nondeterministic_histories() -> dict[str, object]:
    complete_trace_union = {(0, 0), (1, 1)}
    pointwise_union = {(first, second) for first in (0, 1) for second in (0, 1)}
    extra = sorted(pointwise_union - complete_trace_union)
    return {
        "id": "history_correlation",
        "counterexample": {"newly_admitted_traces": extra},
        "required_guard": "preserve_complete_trace_language_or_fixed_run_choice",
        "example_checked": extra == [(0, 1), (1, 0)],
    }


def fixture_completeness() -> dict[str, object]:
    def reference(value: int) -> int:
        return value

    def mutant(value: int) -> int:
        return 129 if value == 128 else value

    fixtures_agree = all(reference(x) == mutant(x) for x in range(128))
    full_mismatches = [x for x in range(256) if reference(x) != mutant(x)]
    return {
        "id": "fixture_scope",
        "counterexample": {
            "all_selected_fixtures_agree": fixtures_agree,
            "full_domain_mismatches": full_mismatches,
        },
        "required_guard": "enumerate_declared_concrete_domain_or_check_simulation",
        "example_checked": fixtures_agree and full_mismatches == [128],
    }


def main() -> None:
    examples = [
        quotient_question(),
        incomplete_question_policy(),
        narrowed_assumptions(),
        nondeterministic_histories(),
        fixture_completeness(),
    ]
    if not all(row["example_checked"] is True for row in examples):
        raise SystemExit("design_counterexample_mismatch")
    report = {
        "schema": "zenolacuna/design-counterexamples-v1",
        "status": "EXAMPLES_CHECKED",
        "authority": "NONE",
        "engine_implemented": False,
        "theorems_machine_checked": False,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "examples": examples,
    }
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()

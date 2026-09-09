"""Finite-model acceptance, fixed counterexamples, and independent tree oracle.

RIPR: construct each invalid premise/repair directly, call its public gate, and
observe exact rejection plus immutable input identity. Oracle grades: fixed
reviewed vectors 2; exhaustive complete-tree comparison 3. Shell histories,
runtime coverage, and source correspondence are separate acceptance surfaces.
"""

from dataclasses import replace
from itertools import product

import pytest

import src.zenolacuna.check as closure_module
from src.zenolacuna.check import close_model
from src.zenolacuna.engine import analyze, assess_repair
from src.zenolacuna.model import (
    Candidate,
    Evidence,
    Hypothesis,
    LacunaError,
    Outcome,
    OutcomeKind,
    Question,
    Requirement,
    Scope,
    ScopeKind,
    Witness,
    Workflow,
)
from src.zenolacuna.questions import choose_question, filter_answer
from src.zenolacuna.relations import check_witness, preservation_error, semantic_classes
from tests.zenolacuna_oracle import OracleQuestion, optimal_tree


def finite_scope(count: int = 3, questions: tuple[Question, ...] = ()) -> Scope:
    outcomes = tuple(Outcome(f"o{i}", f"full observation {i}", OutcomeKind.ACCEPT)
                     for i in range(count + 1))
    domain = ((0,), tuple(range(1, count + 1)))
    return Scope(
        name="independent finite fixture", contexts=("protected", "disputed"),
        outcomes=outcomes, assumptions=(0, 1), contract=domain,
        protected=(Requirement("success", (0,), domain, ((0,), ())),),
        hypotheses=tuple(Hypothesis(f"h{i}", ((0,), (i + 1,))) for i in range(count)),
        questions=questions,
    )


def question(name: str, answers: tuple[int, ...], cost: int = 1) -> Question:
    return Question(name, "Which complete behavior is intended?", cost,
                    tuple(str(answer) for answer in answers))


def candidate(scope: Scope, hypothesis: int = 0) -> Candidate:
    return Candidate("candidate", scope.hypotheses[hypothesis].allowed, scope.assumptions)


def test_s01_given_distinguishing_witness_when_checked_then_all_premises_hold() -> None:
    scope = finite_scope(2, (question("q", (0, 1)),))
    report = analyze(scope)
    assert report.code == "MISSING_REQUIREMENT"
    assert report.workflow is Workflow.NEEDS_DECISION
    witness = report.witness
    assert witness is not None
    assert witness.scope_root == scope.root
    assert witness.context == 1
    assert (witness.left_hypothesis, witness.right_hypothesis) == (0, 1)
    assert (witness.left_outcome, witness.right_outcome) == (1, 2)
    check_witness(scope, witness)


@pytest.mark.parametrize("field,value", [
    ("scope_root", "0" * 64), ("context", 0), ("context", -1),
    ("left_hypothesis", 9), ("right_hypothesis", True),
    ("left_outcome", 0), ("right_outcome", 1),
])
def test_s02_false_witness_premise_rejects_without_mutating_scope(field: str, value: object) -> None:
    scope = finite_scope(2)
    before = scope.root
    witness = Witness(scope.root, 1, 0, 1, 1, 2)
    # The deliberate wrong type must reach the runtime boundary.
    invalid = replace(witness, **{field: value})  # type: ignore[arg-type]
    with pytest.raises(LacunaError, match="^WITNESS_PREMISE_FAILED$"):
        check_witness(scope, invalid)
    assert scope.root == before


@pytest.mark.parametrize("right", [0, 1])
def test_nondeterministic_outcomes_do_not_witness_distinct_semantic_classes(right: int) -> None:
    scope = finite_scope(2)
    same = ((0,), (1, 2))
    scope = replace(scope, hypotheses=(Hypothesis("h0", same), Hypothesis("h1", same)))
    with pytest.raises(LacunaError, match="^WITNESS_PREMISE_FAILED$"):
        check_witness(scope, Witness(scope.root, 1, 0, right, 1, 2))


def test_witness_must_show_a_difference_in_allowed_sets_not_two_common_outcomes() -> None:
    scope = finite_scope(3)
    scope = replace(scope, hypotheses=(
        Hypothesis("smaller", ((0,), (1, 2))),
        Hypothesis("larger", ((0,), (1, 2, 3))),
    ))
    with pytest.raises(LacunaError, match="^WITNESS_PREMISE_FAILED$"):
        check_witness(scope, Witness(scope.root, 1, 0, 1, 1, 2))
    check_witness(scope, Witness(scope.root, 1, 0, 1, 1, 3))


def test_analyze_selects_a_set_difference_when_nondeterministic_rows_overlap() -> None:
    scope = finite_scope(3)
    scope = replace(scope, hypotheses=(
        Hypothesis("smaller", ((0,), (1, 2))),
        Hypothesis("larger", ((0,), (1, 2, 3))),
    ), questions=(question("q", (0, 1)),))
    report = analyze(scope)
    assert report.witness is not None
    assert report.witness.right_outcome == 3
    assert report.witness.left_outcome in (1, 2)


def test_equivalent_observation_representative_cannot_change_repair_verdict() -> None:
    scope = finite_scope(2)
    equivalent = replace(scope.outcomes[2], observation=scope.outcomes[1].observation)
    scope = replace(scope, outcomes=scope.outcomes[:2] + (equivalent,))
    assert semantic_classes(scope, (0, 1)) == ((0, 1),)
    for chosen in (0, 1):
        report = assess_repair(scope, (0, 1), candidate(scope, chosen))
        assert report.workflow is Workflow.READY_FOR_REPLAY
    for chosen in (0, 1):
        assert close_model(scope, (0, 1), candidate(scope, chosen)).workflow is Workflow.COMPLETE_FOR_SCOPE


def test_s03_complete_observation_quotient_retains_reject_and_terminal_effect() -> None:
    scope = finite_scope(3)
    outcomes = (
        scope.outcomes[0], Outcome("normal", "value=7;effect=none", OutcomeKind.ACCEPT),
        Outcome("reject", "value=7;effect=none", OutcomeKind.REJECT),
        Outcome("terminal", "value=7;effect=closed", OutcomeKind.ACCEPT),
    )
    same_source_behavior = Hypothesis("other-source", ((0,), (1,)))
    scope = replace(scope, outcomes=outcomes, hypotheses=scope.hypotheses + (same_source_behavior,))
    assert semantic_classes(scope, (0, 1, 2, 3)) == ((0, 3), (1,), (2,))


def test_s04_intentional_nondeterminism_preserves_the_complete_allowed_set() -> None:
    scope = finite_scope(3)
    scope = replace(scope, hypotheses=(Hypothesis("approved family", ((0,), (1, 2))),))
    report = close_model(scope, (0,), candidate(scope))
    assert report.workflow is Workflow.COMPLETE_FOR_SCOPE
    for outcome in (1, 2):
        assert preservation_error(scope, Candidate("member", ((0,), (outcome,)), (0, 1))) is None
    invalid = Candidate("outside family", ((0,), (3,)), (0, 1))
    assert assess_repair(scope, (0,), invalid).code == "CODE_BUG:DECIDED_REQUIREMENT_VIOLATION"


def test_s05_answer_retains_exact_subset_and_cannot_restore_eliminated_interpretations() -> None:
    scope = finite_scope(4, (question("q", (0, 1, 0, 1)),))
    assert filter_answer(scope, (0, 1, 2, 3), "q", "1") == (1, 3)
    assert filter_answer(scope, (0, 1, 2), "q", "1") == (1,)
    assert filter_answer(scope, (1, 3), "q", "1") == (1, 3)
    with pytest.raises(LacunaError, match="^EMPTY_H_CONFLICT$"):
        filter_answer(scope, (1, 3), "q", "0")


def test_s06_empty_interpretations_never_close() -> None:
    scope = finite_scope()
    report = analyze(scope, ())
    assert report.workflow is Workflow.INCONCLUSIVE
    assert report.code == "EMPTY_H_CONFLICT"
    with pytest.raises(LacunaError, match="^EMPTY_H_CONFLICT$"):
        close_model(scope, (), candidate(scope))


def test_s07_outside_answer_requires_model_revision_and_is_noop() -> None:
    scope = finite_scope(2, (question("q", (0, 1)),))
    before = scope.root
    with pytest.raises(LacunaError, match="^NEEDS_MODEL_REVISION$"):
        filter_answer(scope, (0, 1), "q", "third interpretation")
    assert scope.root == before


def test_s08_all_protected_positive_behaviors_survive_not_just_one() -> None:
    scope = finite_scope(2)
    required = Requirement("every required behavior", (0, 1), scope.contract, ((0,), (1, 2)))
    scope = replace(scope, protected=(required,))
    assert preservation_error(scope, Candidate("all", scope.contract, (0, 1))) is None
    assert preservation_error(scope, candidate(scope)) == "REQUIRED_BEHAVIOR_LOST"


def test_s08_protected_clause_violation_is_rejected_even_when_base_contract_allows_it() -> None:
    scope = finite_scope(2)
    protected = Requirement("approved behavior", (0, 1), ((0,), (1,)), ((0,), ()))
    scope = replace(scope, protected=(protected,))
    assert preservation_error(scope, candidate(scope, 1)) == "PROTECTED_REQUIREMENT_LOST"


def test_s09_reject_only_scope_cannot_close_without_required_positive_witness() -> None:
    scope = finite_scope(1)
    scope = replace(scope, protected=(), outcomes=tuple(
        replace(outcome, kind=OutcomeKind.REJECT) for outcome in scope.outcomes))
    with pytest.raises(LacunaError, match="^MISSING_POSITIVE_WITNESS$"):
        close_model(scope, (0,), candidate(scope))


def test_s10_weak_roundtrip_disagreement_is_missing_requirement_before_decision() -> None:
    scope = finite_scope(2, (question("compatibility", (0, 1)),))
    for i in (0, 1):
        assert preservation_error(scope, candidate(scope, i)) is None
        report = assess_repair(scope, (0, 1), candidate(scope, i))
        assert report.code == "MISSING_REQUIREMENT"
        assert report.workflow is Workflow.NEEDS_DECISION
    assert assess_repair(scope, (0,), candidate(scope, 1)).code == "CODE_BUG:DECIDED_REQUIREMENT_VIOLATION"


def test_s11_current_contract_violation_is_code_bug_without_revising_requirement() -> None:
    scope = finite_scope(2)
    before = scope.root
    invalid = Candidate("incorrect code", ((1,), (1,)), (0, 1))
    report = assess_repair(scope, (0,), invalid)
    assert report.workflow is Workflow.REPAIR_REQUIRED
    assert report.code == "CODE_BUG:PROTECTED_REQUIREMENT_LOST"
    assert scope.root == before


def test_s19_questions_without_any_separator_never_complete() -> None:
    scope = finite_scope(3, (question("constant", (0, 0, 0)),))
    report = analyze(scope)
    assert report.code == "UNSEPARABLE_IN_LANGUAGE"
    assert report.workflow is Workflow.INCONCLUSIVE
    assert report.survivors == (0, 1, 2)


def test_s20_partial_question_search_cannot_claim_exact_optimality() -> None:
    scope = finite_scope(3, (question("qA", (0, 1, 1)), question("qB", (0, 0, 1))))
    limited = replace(scope, max_work=1)
    policy = choose_question(limited, (0, 1, 2))
    assert policy.status == "DP_BUDGET_EXCEEDED"
    assert policy.question is None
    assert policy.worst_cost is None


def test_s21_complete_finite_replay_carries_only_model_claim() -> None:
    scope = finite_scope(1)
    report = close_model(scope, (0,), candidate(scope))
    assert report.workflow is Workflow.COMPLETE_FOR_SCOPE
    assert report.evidence is Evidence.EXHAUSTIVE_FINITE
    assert report.claim == "FINITE_MODEL_ONLY"
    assert report.authority == "NONE"
    assert report.history_bound is None


def test_closure_must_replay_every_context_not_just_a_positive_fixture() -> None:
    scope = finite_scope(1)
    invalid = Candidate("agrees only on positive fixture", ((0,), (0,)), (0, 1))
    before = scope.root
    with pytest.raises(LacunaError, match="^CONTRACT_VIOLATION$"):
        close_model(scope, (0,), invalid)
    assert scope.root == before


def test_closure_cannot_silently_drop_required_outcome_from_approved_family() -> None:
    scope = finite_scope(2)
    required = Requirement("two successes", (0, 1), scope.contract, scope.contract)
    scope = replace(scope, hypotheses=(Hypothesis("family", scope.contract),), protected=(required,))
    invalid = Candidate("one surviving witness", ((0,), (1,)), (0, 1))
    with pytest.raises(LacunaError, match="^REQUIRED_BEHAVIOR_LOST$"):
        close_model(scope, (0,), invalid)


def test_closure_cannot_choose_one_unresolved_interpretation_for_the_caller() -> None:
    scope = finite_scope(2, (question("q", (0, 1)),))
    with pytest.raises(LacunaError, match="^UNRESOLVED_DECISIONS$"):
        close_model(scope, (0, 1), candidate(scope))


def test_independent_closure_replays_class_resolution_despite_mutated_analysis(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    scope = finite_scope(3)
    scope = replace(scope, hypotheses=(
        Hypothesis("smaller", ((0,), (1, 2))),
        Hypothesis("larger", ((0,), (1, 2, 3))),
    ), questions=(question("q", (0, 1)),))
    incorrect = replace(analyze(scope), classes=((0, 1),), workflow=Workflow.READY_FOR_REPLAY)
    monkeypatch.setattr(closure_module, "analyze", lambda *_: incorrect)
    common_behavior = Candidate("fits both unresolved hypotheses", ((0,), (1,)), (0, 1))
    with pytest.raises(LacunaError, match="^UNRESOLVED_DECISIONS$"):
        close_model(scope, (0, 1), common_behavior)


def test_closure_without_replay_budget_is_inconclusive() -> None:
    scope = replace(finite_scope(1), max_work=1)
    with pytest.raises(LacunaError, match="^REPLAY_BUDGET_EXCEEDED$"):
        close_model(scope, (0,), candidate(scope))


def test_s21_bounded_history_never_promotes_unbounded_evidence() -> None:
    scope = replace(finite_scope(1), kind=ScopeKind.BOUNDED_HISTORY, history_bound=2)
    report = close_model(scope, (0,), candidate(scope))
    assert report.evidence is Evidence.BOUNDED_SEARCH
    assert report.history_bound == 2
    assert report.claim == "FINITE_MODEL_ONLY"
    assert replace(scope, history_bound=3).root != report.scope_root


def test_graph_closure_without_complete_graph_adapter_is_unknown() -> None:
    scope = replace(finite_scope(1), kind=ScopeKind.FINITE_STATE_GRAPH)
    report = close_model(scope, (0,), candidate(scope))
    assert report.evidence is Evidence.UNKNOWN
    assert report.workflow is Workflow.INCONCLUSIVE


def test_s26_noncongruent_question_cannot_split_equivalent_source_representatives() -> None:
    scope = finite_scope(3)
    scope = replace(scope, hypotheses=(scope.hypotheses[0],
        replace(scope.hypotheses[0], name="same behavior"), scope.hypotheses[2]),
        questions=(question("invalid", (0, 1, 1)),))
    with pytest.raises(LacunaError, match="^NON_CONGRUENT_QUESTION$"):
        choose_question(scope, (0, 1, 2))


def test_s26_questions_are_total_on_all_interpretations() -> None:
    with pytest.raises(LacunaError, match="^QUESTION_NOT_TOTAL$"):
        finite_scope(3, (question("partial", (0, 1)),))


def test_s27_unseparable_child_propagates_infinity_to_root() -> None:
    scope = finite_scope(3, (question("q", (0, 1, 1)),))
    for survivors in ((1, 2), (0, 1, 2)):
        policy = choose_question(scope, survivors)
        assert policy.status == "UNSEPARABLE_IN_LANGUAGE"
        assert policy.question is None
        assert policy.worst_cost is None


def test_s28_narrowed_assumptions_cannot_erase_protected_input() -> None:
    scope = finite_scope(1)
    required = Requirement("both input classes", (0, 1), scope.contract, scope.contract)
    scope = replace(scope, protected=(required,))
    invalid = replace(candidate(scope), assumptions=(0,))
    assert preservation_error(scope, invalid) == "PROTECTED_REQUIREMENT_LOST"


def test_projection_cannot_collapse_different_protected_verdicts() -> None:
    scope = finite_scope(2)
    same_observation = replace(scope.outcomes[2], observation=scope.outcomes[1].observation)
    required = Requirement("keep one", (1,), scope.contract, ((), (1,)))
    scope = replace(scope, outcomes=scope.outcomes[:2] + (same_observation,), protected=(required,))
    with pytest.raises(LacunaError, match="^OBSERVATION_LOSES_REQUIREMENT$"):
        semantic_classes(scope, (0, 1))


def test_s29_complete_trace_union_excludes_cross_product_history() -> None:
    scope = finite_scope(3)
    outcomes = (scope.outcomes[0],) + tuple(
        Outcome(f"trace-{trace}", trace, OutcomeKind.ACCEPT) for trace in ("00", "11", "01"))
    scope = replace(scope, outcomes=outcomes,
                    hypotheses=(Hypothesis("approved union", ((0,), (1, 2))),))
    assert {scope.outcomes[o].observation for o in scope.hypotheses[0].allowed[1]} == {"00", "11"}
    invalid = Candidate("cross product", ((0,), (1, 2, 3)), (0, 1))
    assert assess_repair(scope, (0,), invalid).code == "CODE_BUG:DECIDED_REQUIREMENT_VIOLATION"


def test_s31_question_order_does_not_change_exact_minimax_tie_break() -> None:
    questions = (question("qB", (0, 0, 1)), question("qA", (0, 1, 1)))
    for ordered in (questions, tuple(reversed(questions))):
        policy = choose_question(finite_scope(3, ordered), (0, 1, 2))
        assert (policy.status, policy.question, policy.worst_cost) == ("EXACT_MINIMAX", "qA", 2)


@pytest.mark.parametrize("count", [2, 3, 4, 5])
def test_minimax_matches_independent_complete_tree_enumeration(count: int) -> None:
    vectors = tuple(product((0, 1), repeat=count))
    # All pairs through four classes; five-class pairs have identical paths,
    # so use three bit questions plus each binary split to exercise deeper trees.
    families = ((a, b) for a in vectors for b in vectors) if count <= 4 else (
        (tuple(i & 1 for i in range(count)), tuple((i >> 1) & 1 for i in range(count)),
         tuple((i >> 2) & 1 for i in range(count)), vector) for vector in vectors)
    for family in families:
        questions = tuple(question(f"q{i}", vector, i + 1) for i, vector in enumerate(family))
        expected = optimal_tree(count, tuple(OracleQuestion(q.name, q.cost, q.answers) for q in questions))
        actual = choose_question(finite_scope(count, questions), tuple(range(count)))
        assert (actual.worst_cost, actual.question) == expected
        assert actual.status == ("UNSEPARABLE_IN_LANGUAGE" if expected[0] is None else "EXACT_MINIMAX")

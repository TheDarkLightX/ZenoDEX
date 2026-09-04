from __future__ import annotations

from dataclasses import replace

import pytest

from experiments.choice_fiber_robustness_v1.named_choice_fiber import (
    ChoiceFiberPolynomial,
)
from experiments.choice_fiber_treewidth_certificate_v1.treewidth_certificate import (
    DEFAULT_PROFILE,
    CoveragePlanV1,
    EliminationOrderV1,
    TreewidthCoverageRequestV1,
    TreewidthReject,
    VerifiedTreewidthCoverageV1,
    brute_force_scoped_minimum,
    deterministic_context,
    prefix_coverage_plan,
    reverify_treewidth_coverage,
    verify_treewidth_coverage,
)
from experiments.zrpf_choice_subcube_coverage_v1.subcube_certificate import (
    CoverageCertificate,
    Leaf,
    Split,
    Subcube,
)


def _polynomial(
    choices: tuple[str, ...],
    coefficients: dict[tuple[str, ...], int],
    namespace: str = "treewidth-test",
) -> ChoiceFiberPolynomial:
    return ChoiceFiberPolynomial.from_coefficients(choices, coefficients, namespace)


def _request(
    polynomial: ChoiceFiberPolynomial,
    *,
    order: tuple[str, ...] | None = None,
    depth: int = 0,
    label: str = "test",
) -> TreewidthCoverageRequestV1:
    choices = polynomial.manifest.choice_ids
    return TreewidthCoverageRequestV1(
        deterministic_context(label),
        polynomial,
        EliminationOrderV1(order or choices),
        prefix_coverage_plan(len(choices), depth),
    )


def test_separator_message_kills_independent_bag_minimum_falsifier() -> None:
    polynomial = _polynomial(
        ("y", "z"),
        {("y",): 1, ("z",): 1, ("y", "z"): 1},
    )
    outcome = verify_treewidth_coverage(_request(polynomial))
    oracle = brute_force_scoped_minimum(polynomial, Subcube(0, 0))

    assert outcome.result.minimum == oracle[0] == -1
    assert outcome.result.assignment == oracle[1] == (("y", -1), ("z", -1))
    assert -3 < outcome.result.minimum  # independently minimizing owner bags is unsound


def test_pairwise_chain_matches_independent_oracle() -> None:
    polynomial = _polynomial(
        ("a", "b", "c", "d"),
        {
            (): 4,
            ("a",): 2,
            ("b",): -1,
            ("a", "b"): 3,
            ("b", "c"): -4,
            ("c", "d"): 5,
        },
    )
    request = _request(polynomial, depth=2)
    outcome = verify_treewidth_coverage(request)
    oracle = brute_force_scoped_minimum(polynomial, Subcube(0, 0))

    assert outcome.result.minimum == oracle[0]
    assert outcome.result.assignment == oracle[1]
    assert outcome.result.leaf_count == 4
    assert reverify_treewidth_coverage(request, outcome)


def test_higher_order_factors_match_independent_oracle() -> None:
    polynomial = _polynomial(
        ("a", "b", "c", "d"),
        {
            (): 2,
            ("a", "b", "c"): -3,
            ("a", "c", "d"): 4,
            ("b", "d"): -1,
        },
    )
    request = _request(polynomial, order=("d", "b", "a", "c"), depth=1)
    outcome = verify_treewidth_coverage(request)
    oracle = brute_force_scoped_minimum(polynomial, Subcube(0, 0))

    assert (outcome.result.minimum, outcome.result.assignment) == oracle[:2]
    assert max(item.scoped_minimum.induced_width for item in outcome.leaf_evidence) == 2


def test_scope_substitution_preserves_fixed_factor_polarity() -> None:
    polynomial = _polynomial(
        ("x", "y"),
        {(): 1, ("y",): -1, ("x", "y"): 1},
    )
    outcome = verify_treewidth_coverage(_request(polynomial, depth=1))
    negative_x = next(
        item
        for item in outcome.leaf_evidence
        if item.scope == Subcube(fixed_mask=1, positive_mask=0)
    )
    oracle = brute_force_scoped_minimum(polynomial, negative_x.scope)

    assert negative_x.scoped_minimum.minimum == oracle[0] == -1
    assert negative_x.scoped_minimum.assignment == (("x", -1), ("y", 1))


def test_all_fixed_scope_has_constant_message_forest() -> None:
    polynomial = _polynomial(("x",), {(): 3, ("x",): 2})
    outcome = verify_treewidth_coverage(_request(polynomial, depth=1))

    assert tuple(item.scoped_minimum.message_cells for item in outcome.leaf_evidence) == (0, 0)
    assert outcome.result.minimum == 1
    assert outcome.result.assignment == (("x", -1),)


def test_irregular_recursive_partition_is_exactly_consumed() -> None:
    polynomial = _polynomial(
        ("a", "b", "c"),
        {("a",): 2, ("b",): 3, ("a", "c"): -4},
    )
    plan = CoveragePlanV1(
        (
            Subcube(0b001, 0b000),
            Subcube(0b011, 0b001),
            Subcube(0b011, 0b011),
        )
    )
    request = TreewidthCoverageRequestV1(
        deterministic_context("comb"),
        polynomial,
        EliminationOrderV1(("a", "b", "c")),
        plan,
    )
    outcome = verify_treewidth_coverage(request)
    oracle = brute_force_scoped_minimum(polynomial, Subcube(0, 0))

    assert outcome.result.minimum == oracle[0]
    assert outcome.result.assignment == oracle[1]
    assert outcome.result.leaf_count == 3


def test_elimination_order_changes_evidence_but_not_exact_result() -> None:
    polynomial = _polynomial(
        ("x", "y", "z"),
        {("x", "y"): 2, ("y", "z"): -3, ("x",): 1},
    )
    forward = verify_treewidth_coverage(
        _request(polynomial, order=("x", "y", "z"), label="same-context")
    )
    reverse = verify_treewidth_coverage(
        _request(polynomial, order=("z", "y", "x"), label="same-context")
    )

    assert forward.result == reverse.result
    assert forward.receipt.verification_subject_root == reverse.receipt.verification_subject_root
    assert forward.receipt.evidence_root != reverse.receipt.evidence_root


def test_semantic_equality_cannot_substitute_exact_lineage() -> None:
    first = _polynomial(("x",), {("x",): 3}, "first-lineage")
    second = _polynomial(("x",), {("x",): 3}, "second-lineage")
    first_outcome = verify_treewidth_coverage(_request(first, label="lineage"))
    second_outcome = verify_treewidth_coverage(_request(second, label="lineage"))

    assert first.semantic_root == second.semantic_root
    assert first.root != second.root
    assert (
        first_outcome.receipt.verification_subject_root
        != second_outcome.receipt.verification_subject_root
    )


def test_direct_receipt_construction_requires_verifier_mint() -> None:
    with pytest.raises(TreewidthReject, match="VERIFIER_OWNERSHIP_REQUIRED"):
        VerifiedTreewidthCoverageV1(bytes(32), bytes(32), bytes(32))


def test_foreign_profile_and_incomplete_order_fail_closed() -> None:
    polynomial = _polynomial(("x", "y"), {("x", "y"): 1})
    request = _request(polynomial)
    foreign = replace(DEFAULT_PROFILE, max_induced_width=11)
    with pytest.raises(TreewidthReject, match="FOREIGN_VERIFIER_PROFILE"):
        verify_treewidth_coverage(replace(request, profile=foreign))

    with pytest.raises(TreewidthReject, match="ELIMINATION_ORDER_DOMAIN_MISMATCH"):
        verify_treewidth_coverage(replace(request, elimination_order=EliminationOrderV1(("x",))))
    with pytest.raises(TreewidthReject, match="DUPLICATE_ELIMINATION_CHOICE"):
        EliminationOrderV1(("x", "x"))


def test_scope_omission_overlap_and_reordering_fail_closed() -> None:
    polynomial = _polynomial(("x",), {("x",): 1})
    base = _request(polynomial)
    omitted = CoveragePlanV1((Subcube(1, 0),))
    with pytest.raises(TreewidthReject, match="INVALID_EXACT_SCOPE_COVERAGE"):
        verify_treewidth_coverage(replace(base, coverage_plan=omitted))

    overlapping = CoveragePlanV1((Subcube(0, 0), Subcube(1, 0), Subcube(1, 1)))
    with pytest.raises(TreewidthReject, match="INVALID_EXACT_SCOPE_COVERAGE"):
        verify_treewidth_coverage(replace(base, coverage_plan=overlapping))

    with pytest.raises(TreewidthReject, match="NONCANONICAL_SCOPE_ORDER"):
        CoveragePlanV1((Subcube(1, 1), Subcube(1, 0)))
    with pytest.raises(TreewidthReject, match="DUPLICATE_SUBCUBE_SCOPE"):
        CoveragePlanV1((Subcube(1, 0), Subcube(1, 0)))


def test_induced_width_cap_rejects_before_message_enumeration() -> None:
    choices = tuple(f"c{index:02d}" for index in range(14))
    polynomial = _polynomial(choices, {choices: 1})
    with pytest.raises(TreewidthReject, match="INDUCED_WIDTH_CAPACITY_EXCEEDED"):
        verify_treewidth_coverage(_request(polynomial))


def test_aggregate_message_cap_rejects_before_table_enumeration() -> None:
    choices = tuple(f"c{index:03d}" for index in range(247))
    coefficients = {tuple(choices[start : start + 13]): 1 for start in range(0, len(choices), 13)}
    polynomial = _polynomial(choices, coefficients, "message-cap")
    with pytest.raises(TreewidthReject, match="MESSAGE_CELL_CAPACITY_EXCEEDED"):
        verify_treewidth_coverage(_request(polynomial))


def test_tampered_oversized_plan_rejects_before_scope_copy() -> None:
    polynomial = _polynomial(("x",), {("x",): 1})
    plan = prefix_coverage_plan(1, 0)
    object.__setattr__(plan, "scopes", tuple(Subcube(0, 0) for _ in range(257)))
    request = _request(polynomial)
    object.__setattr__(request, "coverage_plan", plan)

    with pytest.raises(TreewidthReject, match="COVERAGE_SCOPE_CAPACITY_EXCEEDED"):
        verify_treewidth_coverage(request)


def test_projection_incidence_cap_precedes_scope_projection() -> None:
    choices = tuple(f"c{index:02d}" for index in range(10))
    coefficients: dict[tuple[str, ...], int] = {}
    remaining_occurrences = 4096
    masks = sorted(
        range(1, 1 << len(choices)),
        key=lambda mask: (-mask.bit_count(), mask),
    )
    for mask in masks:
        monomial = tuple(choice for ordinal, choice in enumerate(choices) if mask & (1 << ordinal))
        if len(monomial) <= remaining_occurrences:
            coefficients[monomial] = 1
            remaining_occurrences -= len(monomial)
        if remaining_occurrences == 0:
            break
    assert sum(len(monomial) for monomial in coefficients) == 4096
    polynomial = _polynomial(choices, coefficients, "projection-cap")
    request = _request(polynomial, depth=8)

    with pytest.raises(TreewidthReject, match="PROJECTION_WORK_CAPACITY_EXCEEDED"):
        verify_treewidth_coverage(request)


def test_large_zero_polynomial_uses_precomputed_subtree_orders() -> None:
    choices = tuple(f"c{index:03d}" for index in range(202))
    polynomial = _polynomial(choices, {}, "subtree-order-preflight")
    request = _request(polynomial, depth=8)
    outcome = verify_treewidth_coverage(request)

    assert outcome.result.minimum == 0
    assert outcome.result.assignment == tuple((choice, -1) for choice in choices)
    assert outcome.aggregate_message_cells == 49_664
    assert outcome.aggregate_work_units < 20_000_000


def test_tampered_result_receipt_leaf_and_tree_fail_reverification() -> None:
    polynomial = _polynomial(("x", "y"), {("x",): 1, ("x", "y"): 2})
    request = _request(polynomial, depth=1)

    outcome = verify_treewidth_coverage(request)
    object.__setattr__(outcome.result, "minimum", 999)
    assert not reverify_treewidth_coverage(request, outcome)

    outcome = verify_treewidth_coverage(request)
    object.__setattr__(outcome.receipt, "evidence_root", bytes.fromhex("ff" * 32))
    assert not reverify_treewidth_coverage(request, outcome)

    outcome = verify_treewidth_coverage(request)
    object.__setattr__(outcome.leaf_evidence[0], "scope", Subcube(1, 1))
    assert not reverify_treewidth_coverage(request, outcome)

    outcome = verify_treewidth_coverage(request)
    tree = outcome.coverage_certificate.tree
    assert isinstance(tree, Split)
    swapped = CoverageCertificate(
        outcome.coverage_certificate.manifest_root,
        outcome.coverage_certificate.subject_root,
        Split(tree.choice_ordinal, tree.positive, tree.negative),
    )
    object.__setattr__(outcome, "coverage_certificate", swapped)
    assert not reverify_treewidth_coverage(request, outcome)


def test_untrusted_coverage_tree_is_bounded_before_recursive_operations() -> None:
    polynomial = _polynomial(("x",), {("x",): 1})
    request = _request(polynomial)

    outcome = verify_treewidth_coverage(request)
    cycle = Split(0, Leaf(bytes(32)), Leaf(bytes.fromhex("01" * 32)))
    object.__setattr__(cycle, "negative", cycle)
    forged = object.__new__(CoverageCertificate)
    object.__setattr__(forged, "manifest_root", bytes(32))
    object.__setattr__(forged, "subject_root", bytes(32))
    object.__setattr__(forged, "tree", cycle)
    object.__setattr__(outcome, "coverage_certificate", forged)
    assert not reverify_treewidth_coverage(request, outcome)

    outcome = verify_treewidth_coverage(request)
    deep: Leaf | Split = Leaf(bytes(32))
    for depth in range(300):
        deep = Split(depth % 256, deep, Leaf(depth.to_bytes(32, "big")))
    forged = object.__new__(CoverageCertificate)
    object.__setattr__(forged, "manifest_root", bytes(32))
    object.__setattr__(forged, "subject_root", bytes(32))
    object.__setattr__(forged, "tree", deep)
    object.__setattr__(outcome, "coverage_certificate", forged)
    assert not reverify_treewidth_coverage(request, outcome)

    outcome = verify_treewidth_coverage(request)
    shared = Leaf(bytes(32))
    aliased = CoverageCertificate(bytes(32), bytes(32), Split(0, shared, shared))
    object.__setattr__(outcome, "coverage_certificate", aliased)
    assert not reverify_treewidth_coverage(request, outcome)


def test_tampered_polynomial_is_reconstructed_at_point_of_use() -> None:
    polynomial = _polynomial(("x",), {("x",): 1})
    request = _request(polynomial)
    object.__setattr__(polynomial.terms[0], "coefficient", 99)
    with pytest.raises(TreewidthReject, match="INVALID_POLYNOMIAL"):
        verify_treewidth_coverage(request)


def test_zero_polynomial_uses_canonical_lexicographic_minimizer() -> None:
    polynomial = _polynomial(("x", "y"), {})
    outcome = verify_treewidth_coverage(_request(polynomial))

    assert outcome.result.minimum == 0
    assert outcome.result.assignment == (("x", -1), ("y", -1))


def test_subclassed_request_and_scope_are_rejected() -> None:
    polynomial = _polynomial(("x",), {("x",): 1})

    class ForgedRequest(TreewidthCoverageRequestV1):
        pass

    class ForgedScope(Subcube):
        pass

    forged_request = ForgedRequest(
        deterministic_context("forged"),
        polynomial,
        EliminationOrderV1(("x",)),
        prefix_coverage_plan(1, 0),
    )
    with pytest.raises(TreewidthReject, match="INVALID_VERIFICATION_REQUEST"):
        verify_treewidth_coverage(forged_request)
    with pytest.raises(TreewidthReject, match="INVALID_COVERAGE_PLAN"):
        CoveragePlanV1((ForgedScope(0, 0),))

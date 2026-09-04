from __future__ import annotations

import hashlib
from fractions import Fraction

import pytest
from choice_fiber_polynomial_v1 import (
    ChoiceAtomV1,
    ChoiceFiberPolynomialV1,
    ChoiceFiberReject,
    ChoiceManifestV1,
    TermV1,
)


def _source_root(name: str) -> str:
    return hashlib.sha256(f"research-source:{name}".encode()).hexdigest()


def _manifest(*choice_ids: str) -> ChoiceManifestV1:
    return ChoiceManifestV1(
        tuple(ChoiceAtomV1(choice_id, _source_root(choice_id)) for choice_id in sorted(choice_ids))
    )


def test_shared_and_independent_choices_have_different_exact_semantics() -> None:
    manifest = _manifest("policy", "risk")
    shared = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=10,
        coefficients={"risk": 3},
    ).add(
        ChoiceFiberPolynomialV1.affine(
            manifest,
            center=20,
            coefficients={"risk": 5},
        )
    )
    independent = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=10,
        coefficients={"risk": 3},
    ).add(
        ChoiceFiberPolynomialV1.affine(
            manifest,
            center=20,
            coefficients={"policy": 5},
        )
    )

    assert shared.support() == (22, 38)
    assert independent.support() == (22, 28, 32, 38)
    assert shared.function_root != independent.function_root


def test_affine_bound_is_sharp_without_branch_expansion() -> None:
    manifest = _manifest("market", "policy", "risk")
    value = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=128,
        coefficients={"market": 13, "policy": 11, "risk": 7},
    )

    assert value.exact_affine_bounds() == (97, 159)
    assert min(value.branch_values()) == 97
    assert max(value.branch_values()) == 159


def test_multiplication_introduces_exact_interaction_fiber() -> None:
    manifest = _manifest("policy", "risk")
    left = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=10,
        coefficients={"risk": 2},
    )
    right = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=20,
        coefficients={"policy": 3},
    )

    product = left.multiply(right)

    assert product.coefficient_map() == {
        (): 200,
        ("policy",): 30,
        ("policy", "risk"): 6,
        ("risk",): 40,
    }
    assert product.support() == (136, 184, 204, 276)
    assert not product.is_affine()
    with pytest.raises(ChoiceFiberReject, match="NON_AFFINE_POLYNOMIAL"):
        product.exact_affine_bounds()


def test_shared_sign_multiplication_reduces_epsilon_squared_to_one() -> None:
    manifest = _manifest("risk")
    left = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=10,
        coefficients={"risk": 2},
    )
    right = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=20,
        coefficients={"risk": 3},
    )

    product = left.multiply(right)

    assert product.coefficient_map() == {(): 206, ("risk",): 70}
    assert product.support() == (136, 276)


def test_assignment_distribution_and_distinct_support_are_not_interchangeable() -> None:
    manifest = _manifest("left", "right")
    value = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=0,
        coefficients={"left": 1, "right": 1},
    )

    assert value.branch_values() == (-2, 0, 0, 2)
    assert value.support() == (-2, 0, 2)
    assert value.uniform_assignment_moments() == (Fraction(0), Fraction(2))
    distinct_variance = sum(Fraction(item * item) for item in value.support()) / 3
    assert distinct_variance == Fraction(8, 3)
    assert value.distribution_root != value.support_root


def test_foreign_manifest_cannot_be_hidden_by_equal_printed_choice_id() -> None:
    left_manifest = ChoiceManifestV1((ChoiceAtomV1("risk", _source_root("left-risk")),))
    right_manifest = ChoiceManifestV1((ChoiceAtomV1("risk", _source_root("right-risk")),))
    left = ChoiceFiberPolynomialV1.affine(
        left_manifest,
        center=0,
        coefficients={"risk": 1},
    )
    right = ChoiceFiberPolynomialV1.affine(
        right_manifest,
        center=0,
        coefficients={"risk": 1},
    )

    with pytest.raises(ChoiceFiberReject, match="FOREIGN_CHOICE_MANIFEST"):
        left.add(right)


def test_zero_impact_choice_remains_in_closed_coverage_manifest() -> None:
    manifest = _manifest("policy", "risk")
    with_zero = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=5,
        coefficients={"policy": 0, "risk": 2},
    )
    smaller_manifest = _manifest("risk")
    without_choice = ChoiceFiberPolynomialV1.affine(
        smaller_manifest,
        center=5,
        coefficients={"risk": 2},
    )

    assert with_zero.support() == without_choice.support() == (3, 7)
    assert with_zero.manifest.root != without_choice.manifest.root
    assert with_zero.function_root != without_choice.function_root


def test_constructor_rejects_noncanonical_or_ambiguous_values() -> None:
    risk = ChoiceAtomV1("risk", _source_root("risk"))
    policy = ChoiceAtomV1("policy", _source_root("policy"))
    with pytest.raises(ChoiceFiberReject, match="NON_CANONICAL_CHOICE_ORDER"):
        ChoiceManifestV1((risk, policy))
    with pytest.raises(ChoiceFiberReject, match="DUPLICATE_CHOICE_ID"):
        ChoiceManifestV1((risk, risk))
    with pytest.raises(ChoiceFiberReject, match="NON_REDUCED_MONOMIAL"):
        TermV1(("risk", "risk"), 1)
    with pytest.raises(ChoiceFiberReject, match="ZERO_TERM_MUST_BE_OMITTED"):
        TermV1((), 0)
    with pytest.raises(ChoiceFiberReject, match="NON_INTEGER_COEFFICIENT"):
        TermV1((), True)


def test_assignment_is_total_over_exact_manifest() -> None:
    manifest = _manifest("policy", "risk")
    value = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=5,
        coefficients={"risk": 2},
    )

    with pytest.raises(ChoiceFiberReject, match="ASSIGNMENT_DOMAIN_MISMATCH"):
        value.evaluate({"risk": 1})
    with pytest.raises(ChoiceFiberReject, match="INVALID_SIGN_VALUE"):
        value.evaluate({"policy": 0, "risk": 1})
    with pytest.raises(ChoiceFiberReject, match="INVALID_SIGN_VALUE"):
        value.evaluate({"policy": -1, "risk": True})

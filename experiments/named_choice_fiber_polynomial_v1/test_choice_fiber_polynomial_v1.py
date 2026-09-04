from __future__ import annotations

import hashlib
import json
from collections.abc import Iterator, Mapping
from fractions import Fraction
from pathlib import Path

import pytest
from check_packet import _assert_manifest_identity, _assert_tau_receipt
from choice_fiber_polynomial_v1 import (
    MAX_COEFFICIENT_BITS,
    MAX_EXACT_ENUMERATION_CHOICES,
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


def test_distribution_is_independent_of_truth_table_coordinate_names() -> None:
    manifest = _manifest("left", "right")
    left = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=0,
        coefficients={"left": 1},
    )
    right = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=0,
        coefficients={"right": 1},
    )

    assert (
        left.distribution()
        == right.distribution()
        == (
            (-1, Fraction(1, 2)),
            (1, Fraction(1, 2)),
        )
    )
    assert left.distribution_root == right.distribution_root
    assert left.truth_table_root != right.truth_table_root
    assert left.function_root != right.function_root


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

    assert left_manifest.semantic_root == right_manifest.semantic_root
    assert left_manifest.lineage_root != right_manifest.lineage_root
    assert left.function_root == right.function_root
    assert left.root != right.root
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
    class StringAlias(str):
        pass

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
    with pytest.raises(ChoiceFiberReject, match="INVALID_CHOICE_ID"):
        ChoiceAtomV1(StringAlias("risk"), _source_root("risk"))
    with pytest.raises(ChoiceFiberReject, match="INVALID_MONOMIAL_CHOICE_ID"):
        TermV1((StringAlias("risk"),), 1)
    with pytest.raises(ChoiceFiberReject, match="INVALID_MONOMIAL_CHOICE_ID"):
        TermV1(("risk", 1), 1)  # type: ignore[arg-type]
    with pytest.raises(ChoiceFiberReject, match="INVALID_MONOMIAL_CHOICE_ID"):
        TermV1(([],), 1)  # type: ignore[arg-type]
    with pytest.raises(ChoiceFiberReject, match="INVALID_MONOMIAL"):
        ChoiceFiberPolynomialV1.from_coefficients(
            _manifest("i", "k", "r", "s"),
            {"risk": 1},  # type: ignore[dict-item]
        )
    with pytest.raises(ChoiceFiberReject, match="INVALID_MONOMIAL_CHOICE_ID"):
        ChoiceFiberPolynomialV1.from_coefficients(
            _manifest("risk"),
            {(1,): 1},  # type: ignore[dict-item]
        )


def test_assignment_is_total_over_exact_manifest() -> None:
    class SplitViewMapping(Mapping[str, int]):
        def __getitem__(self, key: str) -> int:
            if key != "risk":
                raise KeyError(key)
            return 7

        def __iter__(self) -> Iterator[str]:
            return iter(("risk",))

        def __len__(self) -> int:
            return 1

        def values(self) -> tuple[int, ...]:  # type: ignore[override]
            # Deliberately violates Mapping's view contract to model an
            # adversarial split-view implementation.
            return (1,)

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
    with pytest.raises(ChoiceFiberReject, match="INVALID_SIGN_VALUE"):
        ChoiceFiberPolynomialV1.affine(
            _manifest("risk"),
            center=0,
            coefficients={"risk": 1},
        ).evaluate(SplitViewMapping())
    with pytest.raises(ChoiceFiberReject, match="INVALID_ASSIGNMENT_MAPPING"):
        value.evaluate(None)  # type: ignore[arg-type]


def test_resource_profile_fails_closed_before_unbounded_work() -> None:
    maximum = (1 << MAX_COEFFICIENT_BITS) - 1
    bounded = ChoiceFiberPolynomialV1.from_coefficients(_manifest("risk"), {(): maximum})
    assert len(bounded.function_root) == 64
    with pytest.raises(ChoiceFiberReject, match="COEFFICIENT_CAPACITY_EXCEEDED"):
        ChoiceFiberPolynomialV1.from_coefficients(
            _manifest("risk"),
            {(): 1 << MAX_COEFFICIENT_BITS},
        )

    at_limit = _manifest(*(f"c{index:02d}" for index in range(MAX_EXACT_ENUMERATION_CHOICES)))
    value_at_limit = ChoiceFiberPolynomialV1.from_coefficients(at_limit, {(): 1})
    assert len(value_at_limit.assignments()) == 1 << MAX_EXACT_ENUMERATION_CHOICES

    over_limit = _manifest(*(f"c{index:02d}" for index in range(MAX_EXACT_ENUMERATION_CHOICES + 1)))
    value_over_limit = ChoiceFiberPolynomialV1.from_coefficients(over_limit, {(): 1})
    with pytest.raises(ChoiceFiberReject, match="ASSIGNMENT_SPACE_TOO_LARGE"):
        value_over_limit.assignments()


def test_packet_gate_rejects_self_consistent_forged_tau_verdicts() -> None:
    experiment = Path(__file__).resolve().parent
    tau = json.loads((experiment / "generated" / "tau_receipt.json").read_text())
    profile = json.loads((experiment / "tau_profile.json").read_text())
    tau["actual"] = ["T"] * 15
    tau["expected"] = ["T"] * 15
    with pytest.raises(SystemExit, match="TAU_VERDICT_MISMATCH"):
        _assert_tau_receipt(tau, profile)

    tau = json.loads((experiment / "generated" / "tau_receipt.json").read_text())
    tau["production_authority"] = True
    with pytest.raises(SystemExit, match="TAU:FIELD_SET_MISMATCH"):
        _assert_tau_receipt(tau, profile)


def test_packet_gate_rejects_claim_promotion_and_subject_substitution() -> None:
    experiment = Path(__file__).resolve().parent
    profile = json.loads((experiment / "tau_profile.json").read_text())
    tau = json.loads((experiment / "generated" / "tau_receipt.json").read_text())
    profile["claim_status"] = "PRODUCTION_READY"
    with pytest.raises(SystemExit, match="TAU_PROFILE_IDENTITY_MISMATCH"):
        _assert_tau_receipt(tau, profile)

    manifest = json.loads((experiment / "generated" / "source_manifest.json").read_text())
    manifest["claim_status"] = "PRODUCTION_READY"
    with pytest.raises(SystemExit, match="MANIFEST_IDENTITY_MISMATCH"):
        _assert_manifest_identity(manifest)

    manifest = json.loads((experiment / "generated" / "source_manifest.json").read_text())
    manifest["base_commit"] = "0" * 40
    with pytest.raises(SystemExit, match="MANIFEST_IDENTITY_MISMATCH"):
        _assert_manifest_identity(manifest)

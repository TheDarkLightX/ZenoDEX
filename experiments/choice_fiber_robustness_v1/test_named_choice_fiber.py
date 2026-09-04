from __future__ import annotations

import unittest
from collections.abc import Iterator, Mapping
from dataclasses import replace

from named_choice_fiber import (
    MAX_COEFFICIENT_BITS,
    CanonicalTerm,
    ChoiceFiberError,
    ChoiceFiberManifest,
    ChoiceFiberPolynomial,
    ChoiceOccurrence,
    RawTerm,
    brute_force_minimum,
    create_affine_certificate,
    create_component_certificate,
    create_forest_certificate,
    verify_affine_certificate,
    verify_component_certificate,
    verify_forest_certificate,
)


class NamedChoiceFiberTests(unittest.TestCase):
    def test_affine_certificate_matches_exhaustive_baseline(self) -> None:
        polynomial = ChoiceFiberPolynomial.from_coefficients(
            ("alice", "bob", "mallory"),
            {
                (): 9,
                ("alice",): 4,
                ("bob",): -7,
                ("mallory",): 2,
            },
        )
        baseline = brute_force_minimum(polynomial)
        certificate = create_affine_certificate(polynomial)
        self.assertEqual(certificate.minimum, baseline.minimum)
        self.assertEqual(certificate.assignment, baseline.assignment)
        self.assertTrue(verify_affine_certificate(polynomial, certificate))

    def test_independent_choices_must_not_be_conflated(self) -> None:
        independent = ChoiceFiberPolynomial.from_coefficients(
            ("x", "y"),
            {(): 1, ("x",): 1, ("y",): -1},
            "independent",
        )
        shared_manifest = ChoiceFiberManifest.admit(
            ("x",),
            (
                ChoiceOccurrence("constant", "x"),
                ChoiceOccurrence("positive", "x"),
                ChoiceOccurrence("negative", "x"),
            ),
        )
        shared = ChoiceFiberPolynomial.compile(
            shared_manifest,
            (
                RawTerm(1, (), "constant-source"),
                RawTerm(1, ("positive",), "positive-source"),
                RawTerm(-1, ("negative",), "negative-source"),
            ),
        )
        self.assertEqual(brute_force_minimum(independent).minimum, -1)
        self.assertEqual(brute_force_minimum(shared).minimum, 1)

    def test_repeated_shared_choice_reduces_to_constant(self) -> None:
        manifest = ChoiceFiberManifest.admit(
            ("x",),
            (
                ChoiceOccurrence("x:first", "x"),
                ChoiceOccurrence("x:second", "x"),
            ),
        )
        polynomial = ChoiceFiberPolynomial.compile(
            manifest,
            (RawTerm(7, ("x:first", "x:second"), "square"),),
        )
        self.assertEqual(polynomial.coefficient_map, {(): 7})
        self.assertEqual(brute_force_minimum(polynomial).minimum, 7)

    def test_negated_alias_changes_coefficient_polarity(self) -> None:
        manifest = ChoiceFiberManifest.admit(
            ("x",),
            (ChoiceOccurrence("not-x", "x", -1),),
        )
        polynomial = ChoiceFiberPolynomial.compile(
            manifest,
            (RawTerm(3, ("not-x",), "negated"),),
        )
        self.assertEqual(polynomial.coefficient_map, {("x",): -3})

    def test_semantically_equal_polynomials_retain_distinct_lineage(self) -> None:
        first = ChoiceFiberPolynomial.from_coefficients(("x",), {("x",): 3}, "first")
        second = ChoiceFiberPolynomial.from_coefficients(("x",), {("x",): 3}, "second")
        self.assertEqual(first.semantic_root, second.semantic_root)
        self.assertNotEqual(first.manifest.root, second.manifest.root)
        self.assertNotEqual(first.lineage_root, second.lineage_root)
        self.assertNotEqual(first.root, second.root)

    def test_nonlinear_interaction_makes_affine_certificate_reject(self) -> None:
        polynomial = ChoiceFiberPolynomial.from_coefficients(
            ("x", "y"),
            {(): 2, ("x",): 1, ("y",): 1, ("x", "y"): -3},
        )
        self.assertEqual(brute_force_minimum(polynomial).minimum, -3)
        with self.assertRaisesRegex(ChoiceFiberError, "NONAFFINE_POLYNOMIAL"):
            create_affine_certificate(polynomial)

    def test_pairwise_forest_dp_matches_exhaustive_baseline(self) -> None:
        polynomial = ChoiceFiberPolynomial.from_coefficients(
            ("a", "b", "c", "d"),
            {
                (): 5,
                ("a",): 2,
                ("b",): -3,
                ("c",): 4,
                ("d",): 1,
                ("a", "b"): 7,
                ("b", "c"): -2,
                ("c", "d"): 6,
            },
        )
        baseline = brute_force_minimum(polynomial)
        certificate = create_forest_certificate(polynomial)
        self.assertEqual(certificate.minimum, baseline.minimum)
        self.assertEqual(certificate.assignment, baseline.assignment)
        self.assertTrue(verify_forest_certificate(polynomial, certificate))

    def test_cycle_is_rejected_instead_of_silently_dropping_an_edge(self) -> None:
        polynomial = ChoiceFiberPolynomial.from_coefficients(
            ("x", "y", "z"),
            {
                (): 2,
                ("x", "y"): 1,
                ("y", "z"): 1,
                ("x", "z"): -3,
            },
        )
        self.assertEqual(brute_force_minimum(polynomial).minimum, -3)
        with self.assertRaisesRegex(ChoiceFiberError, "INTERACTION_GRAPH_NOT_FOREST"):
            create_forest_certificate(polynomial)

    def test_higher_order_components_compress_independent_blocks(self) -> None:
        coefficients: dict[tuple[str, ...], int] = {(): 13}
        choices: list[str] = []
        for block in range(4):
            local = tuple(f"b{block}:{index}" for index in range(3))
            choices.extend(local)
            coefficients[local] = block + 1
            coefficients[(local[0],)] = 2 - block
        polynomial = ChoiceFiberPolynomial.from_coefficients(choices, coefficients)
        baseline = brute_force_minimum(polynomial)
        certificate = create_component_certificate(polynomial)
        self.assertEqual(certificate.minimum, baseline.minimum)
        self.assertEqual(sum(item.assignments_checked for item in certificate.components), 32)
        self.assertEqual(baseline.assignments_checked, 4096)
        self.assertTrue(verify_component_certificate(polynomial, certificate))

    def test_forged_affine_minimum_rejects(self) -> None:
        polynomial = ChoiceFiberPolynomial.from_coefficients(("x",), {(): 3, ("x",): 2})
        certificate = create_affine_certificate(polynomial)
        forged = replace(certificate, minimum=certificate.minimum + 1)
        self.assertFalse(verify_affine_certificate(polynomial, forged))

    def test_stale_polynomial_certificate_rejects(self) -> None:
        original = ChoiceFiberPolynomial.from_coefficients(("x",), {(): 3, ("x",): 2}, "original")
        changed = ChoiceFiberPolynomial.from_coefficients(("x",), {(): 3, ("x",): 3}, "changed")
        self.assertFalse(verify_affine_certificate(changed, create_affine_certificate(original)))

    def test_incomplete_assignment_rejects(self) -> None:
        polynomial = ChoiceFiberPolynomial.from_coefficients(("x", "y"), {("x",): 1})
        with self.assertRaisesRegex(ChoiceFiberError, "INCOMPLETE_OR_SURPLUS_ASSIGNMENT"):
            polynomial.evaluate({"x": 1})
        with self.assertRaisesRegex(ChoiceFiberError, "INVALID_ASSIGNMENT_SIGN"):
            polynomial.evaluate({"x": True, "y": -1})
        with self.assertRaisesRegex(ChoiceFiberError, "INVALID_ASSIGNMENT_MAPPING"):
            polynomial.evaluate(None)  # type: ignore[arg-type]

    def test_assignment_mapping_is_snapshotted_once(self) -> None:
        class SplitViewMapping(Mapping[str, int]):
            def __getitem__(self, key: str) -> int:
                if key != "x":
                    raise KeyError(key)
                return 99

            def __iter__(self) -> Iterator[str]:
                return iter(("x",))

            def __len__(self) -> int:
                return 1

            def values(self) -> tuple[int, ...]:  # type: ignore[override]
                # Deliberately violates Mapping's view contract to model an
                # adversarial split-view implementation.
                return (1,)

        polynomial = ChoiceFiberPolynomial.from_coefficients(("x",), {("x",): 1})
        with self.assertRaisesRegex(ChoiceFiberError, "INVALID_ASSIGNMENT_SIGN"):
            polynomial.evaluate(SplitViewMapping())

    def test_coefficient_and_identifier_resources_are_bounded(self) -> None:
        maximum = (1 << MAX_COEFFICIENT_BITS) - 1
        bounded = ChoiceFiberPolynomial.from_coefficients(("x",), {("x",): maximum})
        self.assertEqual(len(bounded.root), 64)
        with self.assertRaisesRegex(ChoiceFiberError, "COEFFICIENT_CAPACITY_EXCEEDED"):
            ChoiceFiberPolynomial.from_coefficients(
                ("x",),
                {("x",): 1 << MAX_COEFFICIENT_BITS},
            )
        with self.assertRaisesRegex(ChoiceFiberError, "INVALID_CHOICE_IDENTITIES"):
            ChoiceFiberPolynomial.from_coefficients(("x" * 129,), {})

    def test_component_certificate_rejects_forged_partition(self) -> None:
        polynomial = ChoiceFiberPolynomial.from_coefficients(("x", "y"), {("x", "y"): 1})
        certificate = create_component_certificate(polynomial)
        forged = replace(certificate, components=())
        self.assertFalse(verify_component_certificate(polynomial, forged))

    def test_caller_cannot_forge_derived_terms(self) -> None:
        valid = ChoiceFiberPolynomial.from_coefficients(("x",), {(): 3, ("x",): 2}, "valid")
        with self.assertRaisesRegex(ChoiceFiberError, "DERIVED_TERM_MISMATCH"):
            ChoiceFiberPolynomial(
                valid.manifest,
                (CanonicalTerm((), 999),),
                valid.raw_terms,
            )

    def test_forest_certificate_rejects_forged_dp_row(self) -> None:
        polynomial = ChoiceFiberPolynomial.from_coefficients(("x", "y"), {("x",): 2, ("x", "y"): 1})
        certificate = create_forest_certificate(polynomial)
        forged_row = replace(
            certificate.rows[0],
            value_if_minus=certificate.rows[0].value_if_minus + 1,
        )
        forged = replace(certificate, rows=(forged_row,) + certificate.rows[1:])
        self.assertFalse(verify_forest_certificate(polynomial, forged))

    def test_numeric_aliases_do_not_create_distinct_roots_for_equal_values(self) -> None:
        with self.assertRaisesRegex(ChoiceFiberError, "NONINTEGER_COEFFICIENT"):
            CanonicalTerm(("x",), 1.0)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ChoiceFiberError, "NONINTEGER_COEFFICIENT"):
            CanonicalTerm(("x",), True)
        polynomial = ChoiceFiberPolynomial.from_coefficients(("x",), {("x",): 1})
        certificate = create_affine_certificate(polynomial)
        with self.assertRaisesRegex(ChoiceFiberError, "INVALID_AFFINE_CERTIFICATE"):
            replace(
                certificate,
                minimum=float(certificate.minimum),  # type: ignore[arg-type]
            )

    def test_constructor_deep_owns_only_exact_tuple_values(self) -> None:
        mutable_occurrences = ["x:one"]
        with self.assertRaisesRegex(ChoiceFiberError, "INVALID_TERM_OCCURRENCES"):
            RawTerm(1, mutable_occurrences, "source")  # type: ignore[arg-type]
        valid = ChoiceFiberPolynomial.from_coefficients(("x",), {("x",): 1})
        with self.assertRaisesRegex(ChoiceFiberError, "INVALID_RAW_TERMS"):
            ChoiceFiberPolynomial(
                valid.manifest,
                valid.terms,
                list(valid.raw_terms),  # type: ignore[arg-type]
            )

    def test_choice_identity_and_capacity_have_typed_rejections(self) -> None:
        with self.assertRaisesRegex(ChoiceFiberError, "EMPTY_CHOICE_IDENTITY"):
            ChoiceOccurrence("occurrence", "")
        with self.assertRaisesRegex(ChoiceFiberError, "CHOICE_CAPACITY_EXCEEDED"):
            ChoiceFiberManifest.admit(
                (f"choice-{index:03d}" for index in range(257)),
                (),
            )
        with self.assertRaisesRegex(ChoiceFiberError, "EMPTY_CHOICE_IDENTITY"):
            ChoiceOccurrence("\ud800", "x")
        with self.assertRaisesRegex(ChoiceFiberError, "INVALID_CHOICE_IDENTITIES"):
            ChoiceFiberManifest.admit(("\ud800",), ())

    def test_composite_exhaustive_work_is_bounded_before_enumeration(self) -> None:
        choices = tuple(f"c{index:02d}" for index in range(20))
        coefficients: dict[tuple[str, ...], int] = {}
        # Twenty-one distinct dense monomials fit every individual dimension
        # cap while exceeding the packet's total term-incidence work budget.
        for omitted in range(20):
            coefficients[
                tuple(choice for index, choice in enumerate(choices) if index != omitted)
            ] = 1
        coefficients[choices] = 1
        polynomial = ChoiceFiberPolynomial.from_coefficients(choices, coefficients)
        with self.assertRaisesRegex(
            ChoiceFiberError,
            "EXHAUSTIVE_WORK_CAPACITY_EXCEEDED",
        ):
            brute_force_minimum(polynomial)
        with self.assertRaisesRegex(
            ChoiceFiberError,
            "EXHAUSTIVE_WORK_CAPACITY_EXCEEDED",
        ):
            create_component_certificate(polynomial)

    def test_caller_controlled_equality_cannot_forge_derived_values(self) -> None:
        class AlwaysEqual:
            def __eq__(self, other: object) -> bool:
                return True

        class ForgedCanonicalTerm(CanonicalTerm):
            def __eq__(self, other: object) -> bool:
                return True

        polynomial = ChoiceFiberPolynomial.from_coefficients(
            ("x",),
            {("x",): 1},
        )
        forged = AlwaysEqual()
        self.assertFalse(
            verify_affine_certificate(
                polynomial,
                forged,  # type: ignore[arg-type]
            )
        )
        self.assertFalse(
            verify_forest_certificate(
                polynomial,
                forged,  # type: ignore[arg-type]
            )
        )
        self.assertFalse(
            verify_component_certificate(
                polynomial,
                forged,  # type: ignore[arg-type]
            )
        )
        with self.assertRaisesRegex(ChoiceFiberError, "INVALID_CANONICAL_TERMS"):
            ChoiceFiberPolynomial(
                polynomial.manifest,
                (ForgedCanonicalTerm(("x",), 999),),
                polynomial.raw_terms,
            )

        certificate = create_affine_certificate(polynomial)
        object.__setattr__(certificate, "minimum", AlwaysEqual())
        self.assertFalse(verify_affine_certificate(polynomial, certificate))

        changed_term = polynomial.terms[0]
        object.__setattr__(changed_term, "coefficient", 999)
        self.assertFalse(
            verify_affine_certificate(
                polynomial,
                create_affine_certificate(
                    ChoiceFiberPolynomial.from_coefficients(("x",), {("x",): 1})
                ),
            )
        )


if __name__ == "__main__":
    unittest.main()

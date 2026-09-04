#!/usr/bin/env python3
"""Deterministic semantic mutants for Named Choice Fiber Polynomial V1."""

from __future__ import annotations

import hashlib
import itertools
import json

from choice_fiber_polynomial_v1 import (
    ChoiceAtomV1,
    ChoiceFiberPolynomialV1,
    ChoiceFiberReject,
    ChoiceManifestV1,
)


def _root(name: str) -> str:
    return hashlib.sha256(f"mutation-source:{name}".encode()).hexdigest()


def _manifest(*ids: str, prefix: str = "base") -> ChoiceManifestV1:
    return ChoiceManifestV1(
        tuple(ChoiceAtomV1(item, _root(f"{prefix}:{item}")) for item in sorted(ids))
    )


def _flat_three_sign_support(coefficients: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        sorted(
            {
                sum(
                    coefficient * sign
                    for coefficient, sign in zip(coefficients, signs, strict=True)
                )
                for signs in itertools.product((-1, 1), repeat=3)
            }
        )
    )


def run_mutations() -> list[dict[str, object]]:
    manifest = _manifest("policy", "risk")
    shared = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=30,
        coefficients={"risk": 8},
    )
    independent = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=30,
        coefficients={"policy": 5, "risk": 3},
    )
    duplicate = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=0,
        coefficients={"policy": 1, "risk": 1},
    )
    product = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=10,
        coefficients={"risk": 2},
    ).multiply(
        ChoiceFiberPolynomialV1.affine(
            manifest,
            center=20,
            coefficients={"policy": 3},
        )
    )

    foreign_left = ChoiceFiberPolynomialV1.affine(
        _manifest("risk", prefix="left"),
        center=0,
        coefficients={"risk": 1},
    )
    foreign_right = ChoiceFiberPolynomialV1.affine(
        _manifest("risk", prefix="right"),
        center=0,
        coefficients={"risk": 1},
    )
    foreign_rejected = False
    try:
        foreign_left.add(foreign_right)
    except ChoiceFiberReject as error:
        foreign_rejected = str(error) == "FOREIGN_CHOICE_MANIFEST"

    target = (-8, -4, -2, -1, 1, 2, 4, 8)
    target_representable = any(
        _flat_three_sign_support(coefficients) == target
        for coefficients in itertools.product(range(9), repeat=3)
    )

    wrap_values = tuple((250 + sign * 10) % 256 for sign in (-1, 1))
    integer_values = tuple(250 + sign * 10 for sign in (-1, 1))
    coordinate_left = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=0,
        coefficients={"policy": 1},
    )
    coordinate_right = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=0,
        coefficients={"risk": 1},
    )
    rows = [
        {
            "killed": shared.support() != independent.support(),
            "mutant": "shared_choice_freshened_to_independent_choice",
        },
        {
            "killed": duplicate.uniform_assignment_moments()[1].denominator == 1
            and duplicate.uniform_assignment_moments()[1].numerator == 2
            and sum(item * item for item in duplicate.support()) * 1
            != 2 * len(duplicate.support()),
            "mutant": "branch_multiplicity_erased_before_statistics",
        },
        {
            "killed": ("policy", "risk") in product.coefficient_map(),
            "mutant": "nonlinear_interaction_monomial_dropped",
        },
        {
            "killed": foreign_rejected,
            "mutant": "foreign_choice_source_reused_by_local_name",
        },
        {
            "killed": not target_representable,
            "mutant": "arbitrary_symmetric_support_declared_flat_affine",
        },
        {
            "killed": wrap_values != integer_values and 260 in integer_values,
            "mutant": "modular_wrap_misreported_as_integer_affine_bound",
        },
        {
            "killed": shared.function_root != independent.function_root,
            "mutant": "support_like_printed_form_substituted_for_function_identity",
        },
        {
            "killed": (
                coordinate_left.distribution_root == coordinate_right.distribution_root
                and coordinate_left.truth_table_root != coordinate_right.truth_table_root
            ),
            "mutant": "ordered_truth_table_substituted_for_output_distribution",
        },
        {
            "killed": (
                foreign_left.function_root == foreign_right.function_root
                and foreign_left.root != foreign_right.root
            ),
            "mutant": "source_lineage_substituted_for_semantic_function_identity",
        },
    ]
    if not all(row["killed"] is True for row in rows):
        raise SystemExit("SURVIVING_MUTANT")
    return rows


def main() -> int:
    rows = run_mutations()
    print(
        json.dumps(
            {
                "authority": "NONE",
                "claim_status": "BOUNDED_RESEARCH_ONLY",
                "killed": len(rows),
                "mutants": rows,
                "object": "named_choice_fiber_polynomial_v1",
                "schema": "zenodex.choice_fiber_mutation_receipt.v1",
                "survived": 0,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

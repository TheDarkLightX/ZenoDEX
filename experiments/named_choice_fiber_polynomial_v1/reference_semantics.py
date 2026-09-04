#!/usr/bin/env python3
"""Independent direct enumerator for Named Choice Fiber Polynomial V1.

This oracle intentionally does not import the implementation under test. It
uses plain coefficient maps and exhaustive assignments for the small retained
examples.
"""

from __future__ import annotations

import itertools
import json
from fractions import Fraction

CoefficientMap = dict[tuple[str, ...], int]


def _reduce_monomial(names: tuple[str, ...]) -> tuple[str, ...]:
    parity: set[str] = set()
    for name in names:
        if name in parity:
            parity.remove(name)
        else:
            parity.add(name)
    return tuple(sorted(parity))


def _add(left: CoefficientMap, right: CoefficientMap) -> CoefficientMap:
    result = dict(left)
    for monomial, coefficient in right.items():
        result[monomial] = result.get(monomial, 0) + coefficient
    return {monomial: coefficient for monomial, coefficient in result.items() if coefficient}


def _multiply(left: CoefficientMap, right: CoefficientMap) -> CoefficientMap:
    result: CoefficientMap = {}
    for left_names, left_coefficient in left.items():
        for right_names, right_coefficient in right.items():
            monomial = _reduce_monomial((*left_names, *right_names))
            result[monomial] = result.get(monomial, 0) + left_coefficient * right_coefficient
    return {monomial: coefficient for monomial, coefficient in result.items() if coefficient}


def _branch_values(
    choice_ids: tuple[str, ...],
    coefficients: CoefficientMap,
) -> tuple[int, ...]:
    values: list[int] = []
    for signs in itertools.product((-1, 1), repeat=len(choice_ids)):
        assignment = dict(zip(choice_ids, signs, strict=True))
        total = 0
        for monomial, coefficient in coefficients.items():
            term = coefficient
            for choice_id in monomial:
                term *= assignment[choice_id]
            total += term
        values.append(total)
    return tuple(values)


def _support(
    choice_ids: tuple[str, ...],
    coefficients: CoefficientMap,
) -> list[int]:
    return sorted(set(_branch_values(choice_ids, coefficients)))


def build_report() -> dict[str, object]:
    choice_ids = ("policy", "risk")
    shared = _add({(): 10, ("risk",): 3}, {(): 20, ("risk",): 5})
    independent = _add({(): 10, ("risk",): 3}, {(): 20, ("policy",): 5})
    product = _multiply({(): 10, ("risk",): 2}, {(): 20, ("policy",): 3})
    duplicate: CoefficientMap = {("policy",): 1, ("risk",): 1}
    duplicate_values = _branch_values(choice_ids, duplicate)
    count = len(duplicate_values)
    mean = Fraction(sum(duplicate_values), count)
    variance = (
        sum(
            ((Fraction(value) - mean) ** 2 for value in duplicate_values),
            start=Fraction(0),
        )
        / count
    )

    return {
        "authority": "NONE",
        "claim_status": "BOUNDED_RESEARCH_ONLY",
        "invariants": {
            "affine_bounds": "center +/- sum(abs(coefficients))",
            "choice_identity": ("equal choice_id within one manifest means shared sign"),
            "multiplication": ("monomial choice sets combine by symmetric difference"),
            "projection_rule": (
                "truth table, output distribution, and support cannot replace the named function"
            ),
        },
        "nonclaims": [
            "not a production number type",
            "not a Tau Net throughput result",
            "not a settlement or governance authority",
            "not proof that nonlinear circuits remain compact",
            "not a novelty or patent-clearance opinion",
        ],
        "object": "named_choice_fiber_polynomial_v1",
        "oracle": "independent_direct_enumerator_without_runtime_import",
        "results": {
            "duplicate_branch_multiset": list(duplicate_values),
            "duplicate_support": _support(choice_ids, duplicate),
            "independent_product_coefficients": [
                {
                    "coefficient": coefficient,
                    "monomial": list(monomial),
                }
                for monomial, coefficient in sorted(product.items())
            ],
            "independent_product_support": _support(choice_ids, product),
            "independent_sign_support": _support(choice_ids, independent),
            "shared_sign_support": _support(choice_ids, shared),
            "uniform_assignment_mean": [mean.numerator, mean.denominator],
            "uniform_assignment_variance": [
                variance.numerator,
                variance.denominator,
            ],
        },
        "schema": "zenodex.choice_fiber_experiment_report.v1",
        "strongest_claim": (
            "Exact correlation semantics require retained correlation identity; "
            "named choice IDs provide one canonical encoding. Affine extrema "
            "are linear-time; closure under arbitrary multiplication requires "
            "allowing higher-order interaction terms."
        ),
    }


def main() -> int:
    print(json.dumps(build_report(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

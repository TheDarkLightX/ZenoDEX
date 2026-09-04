#!/usr/bin/env python3
"""Deterministic independent report for Named Choice Fiber Polynomial V1."""

from __future__ import annotations

import hashlib
import json

from choice_fiber_polynomial_v1 import (
    ChoiceAtomV1,
    ChoiceFiberPolynomialV1,
    ChoiceManifestV1,
)


def _source_root(name: str) -> str:
    return hashlib.sha256(f"research-source:{name}".encode()).hexdigest()


def _manifest(*choice_ids: str) -> ChoiceManifestV1:
    return ChoiceManifestV1(
        tuple(ChoiceAtomV1(choice_id, _source_root(choice_id)) for choice_id in sorted(choice_ids))
    )


def build_report() -> dict[str, object]:
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
    duplicate = ChoiceFiberPolynomialV1.affine(
        manifest,
        center=0,
        coefficients={"policy": 1, "risk": 1},
    )
    mean, variance = duplicate.uniform_assignment_moments()

    return {
        "authority": "NONE",
        "claim_status": "BOUNDED_RESEARCH_ONLY",
        "invariants": {
            "affine_bounds": "center +/- sum(abs(coefficients))",
            "choice_identity": "equal choice_id within one manifest means shared sign",
            "multiplication": "monomial choice sets combine by symmetric difference",
            "projection_rule": "support and distribution cannot replace the named function",
        },
        "nonclaims": [
            "not a production number type",
            "not a Tau Net throughput result",
            "not a settlement or governance authority",
            "not proof that nonlinear circuits remain compact",
            "not a novelty or patent-clearance opinion",
        ],
        "object": "named_choice_fiber_polynomial_v1",
        "results": {
            "duplicate_branch_multiset": list(duplicate.branch_values()),
            "duplicate_support": list(duplicate.support()),
            "independent_product_coefficients": [term.canonical_record() for term in product.terms],
            "independent_product_support": list(product.support()),
            "independent_sign_support": list(independent.support()),
            "shared_sign_support": list(shared.support()),
            "uniform_assignment_mean": [mean.numerator, mean.denominator],
            "uniform_assignment_variance": [variance.numerator, variance.denominator],
        },
        "schema": "zenodex.choice_fiber_experiment_report.v1",
        "strongest_claim": (
            "Named choice identity is necessary for exact correlation semantics; "
            "affine extrema are linear-time; exact multiplication requires interaction terms."
        ),
    }


def main() -> int:
    print(json.dumps(build_report(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

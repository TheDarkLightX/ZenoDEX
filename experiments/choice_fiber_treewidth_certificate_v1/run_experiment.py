#!/usr/bin/env python3
"""Deterministic campaigns for the scoped treewidth coverage certificate."""

from __future__ import annotations

import hashlib
import json
from dataclasses import replace
from itertools import product
from pathlib import Path

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

ROOT = Path(__file__).resolve().parent


def _polynomial(
    choices: tuple[str, ...],
    coefficients: dict[tuple[str, ...], int],
    namespace: str,
) -> ChoiceFiberPolynomial:
    return ChoiceFiberPolynomial.from_coefficients(choices, coefficients, namespace)


def _request(
    polynomial: ChoiceFiberPolynomial,
    label: str,
    *,
    order: tuple[str, ...] | None = None,
    depth: int = 0,
) -> TreewidthCoverageRequestV1:
    choices = polynomial.manifest.choice_ids
    return TreewidthCoverageRequestV1(
        deterministic_context(label),
        polynomial,
        EliminationOrderV1(order or choices),
        prefix_coverage_plan(len(choices), depth),
    )


def exhaustive_campaign() -> dict[str, int]:
    """Compare the DP against direct evaluation over two bounded families."""

    choices = ("a", "b", "c")
    keys = ((), ("a",), ("b",), ("c",), ("a", "b"), ("b", "c"))
    orders = (choices, tuple(reversed(choices)))
    full_cases = 0
    full_assignments = 0
    maximum_width = 0
    for case_index, vector in enumerate(product((-1, 0, 1), repeat=len(keys))):
        coefficients = {
            key: coefficient for key, coefficient in zip(keys, vector, strict=True) if coefficient
        }
        polynomial = _polynomial(choices, coefficients, f"bounded-full:{case_index}")
        oracle = brute_force_scoped_minimum(polynomial, Subcube(0, 0))
        for order in orders:
            outcome = verify_treewidth_coverage(_request(polynomial, "bounded-full", order=order))
            if (outcome.result.minimum, outcome.result.assignment) != oracle[:2]:
                raise AssertionError("FULL_CUBE_DP_ORACLE_DISAGREEMENT")
            if not reverify_treewidth_coverage(
                _request(polynomial, "bounded-full", order=order), outcome
            ):
                raise AssertionError("FULL_CUBE_REVERIFICATION_DISAGREEMENT")
            maximum_width = max(
                maximum_width,
                max(item.scoped_minimum.induced_width for item in outcome.leaf_evidence),
            )
            full_cases += 1
            full_assignments += oracle[2]

    scoped_choices = ("x", "y")
    scoped_keys = ((), ("x",), ("y",), ("x", "y"))
    scoped_cases = 0
    scoped_global_assignments = 0
    scoped_leaf_assignments = 0
    for case_index, vector in enumerate(product(range(-2, 3), repeat=len(scoped_keys))):
        coefficients = {
            key: coefficient
            for key, coefficient in zip(scoped_keys, vector, strict=True)
            if coefficient
        }
        polynomial = _polynomial(scoped_choices, coefficients, f"bounded-scope:{case_index}")
        request = _request(polynomial, "bounded-scope", depth=1)
        outcome = verify_treewidth_coverage(request)
        oracle = brute_force_scoped_minimum(polynomial, Subcube(0, 0))
        scoped_global_assignments += oracle[2]
        if (outcome.result.minimum, outcome.result.assignment) != oracle[:2]:
            raise AssertionError("SCOPED_COVERAGE_DP_ORACLE_DISAGREEMENT")
        for item in outcome.leaf_evidence:
            leaf_oracle = brute_force_scoped_minimum(polynomial, item.scope)
            if (
                item.scoped_minimum.minimum,
                item.scoped_minimum.assignment,
            ) != leaf_oracle[:2]:
                raise AssertionError("SCOPED_LEAF_DP_ORACLE_DISAGREEMENT")
            scoped_leaf_assignments += leaf_oracle[2]
        scoped_cases += 1

    higher_order_keys = (
        (),
        ("a",),
        ("b",),
        ("c",),
        ("a", "b"),
        ("b", "c"),
        ("a", "b", "c"),
    )
    higher_order_cases = 0
    higher_order_assignments = 0
    for case_index, vector in enumerate(product((-1, 0, 1), repeat=len(higher_order_keys))):
        coefficients = {
            key: coefficient
            for key, coefficient in zip(higher_order_keys, vector, strict=True)
            if coefficient
        }
        polynomial = _polynomial(
            choices,
            coefficients,
            f"bounded-higher-order:{case_index}",
        )
        oracle = brute_force_scoped_minimum(polynomial, Subcube(0, 0))
        for order in orders:
            outcome = verify_treewidth_coverage(
                _request(polynomial, "bounded-higher-order", order=order)
            )
            if (outcome.result.minimum, outcome.result.assignment) != oracle[:2]:
                raise AssertionError("HIGHER_ORDER_DP_ORACLE_DISAGREEMENT")
            maximum_width = max(
                maximum_width,
                max(item.scoped_minimum.induced_width for item in outcome.leaf_evidence),
            )
            higher_order_cases += 1
            higher_order_assignments += oracle[2]

    return {
        "full_cube_assignments_checked": full_assignments,
        "full_cube_ordered_cases": full_cases,
        "higher_order_assignments_checked": higher_order_assignments,
        "higher_order_cases": higher_order_cases,
        "maximum_induced_width_seen": maximum_width,
        "scoped_global_assignments_checked": scoped_global_assignments,
        "scoped_leaf_assignments_checked": scoped_leaf_assignments,
        "scoped_partition_cases": scoped_cases,
        "total_cases": full_cases + scoped_cases + higher_order_cases,
        "total_oracle_assignments_checked": (
            full_assignments
            + higher_order_assignments
            + scoped_global_assignments
            + scoped_leaf_assignments
        ),
    }


def attack_campaign() -> list[dict[str, object]]:
    """Kill named authority, binding, coverage, and capacity mutations."""

    attacks: list[dict[str, object]] = []

    def record(attack_id: str, killed: bool) -> None:
        if not killed:
            raise AssertionError(f"SURVIVING_MUTANT:{attack_id}")
        attacks.append({"id": attack_id, "killed": True})

    polynomial = _polynomial(("x", "y"), {("x",): 1, ("x", "y"): 2}, "attacks")
    request = _request(polynomial, "attacks", depth=1)

    direct_rejected = False
    try:
        VerifiedTreewidthCoverageV1(bytes(32), bytes(32), bytes(32))
    except TreewidthReject as error:
        direct_rejected = error.code == "VERIFIER_OWNERSHIP_REQUIRED"
    record("A01_DIRECT_RECEIPT_CONSTRUCTION", direct_rejected)

    changed = verify_treewidth_coverage(request)
    object.__setattr__(changed.result, "minimum", changed.result.minimum + 1)
    record("A02_RESULT_REPOINTING", not reverify_treewidth_coverage(request, changed))

    changed = verify_treewidth_coverage(request)
    object.__setattr__(changed.receipt, "evidence_root", bytes.fromhex("ff" * 32))
    record("A03_EVIDENCE_ROOT_REPOINTING", not reverify_treewidth_coverage(request, changed))

    changed = verify_treewidth_coverage(request)
    object.__setattr__(changed.leaf_evidence[0], "scope", Subcube(1, 1))
    record("A04_SCOPE_LEAF_REPOINTING", not reverify_treewidth_coverage(request, changed))

    profile_rejected = False
    try:
        verify_treewidth_coverage(
            replace(
                request,
                profile=replace(DEFAULT_PROFILE, max_induced_width=11),
            )
        )
    except TreewidthReject as error:
        profile_rejected = error.code == "FOREIGN_VERIFIER_PROFILE"
    record("A05_FOREIGN_PROFILE", profile_rejected)

    order_rejected = False
    try:
        verify_treewidth_coverage(replace(request, elimination_order=EliminationOrderV1(("x",))))
    except TreewidthReject as error:
        order_rejected = error.code == "ELIMINATION_ORDER_DOMAIN_MISMATCH"
    record("A06_INCOMPLETE_ELIMINATION_ORDER", order_rejected)

    omission_rejected = False
    try:
        verify_treewidth_coverage(replace(request, coverage_plan=CoveragePlanV1((Subcube(1, 0),))))
    except TreewidthReject as error:
        omission_rejected = error.code == "INVALID_EXACT_SCOPE_COVERAGE"
    record("A07_SCOPE_OMISSION", omission_rejected)

    overlap_rejected = False
    try:
        verify_treewidth_coverage(
            replace(
                request,
                coverage_plan=CoveragePlanV1((Subcube(0, 0), Subcube(1, 0), Subcube(1, 1))),
            )
        )
    except TreewidthReject as error:
        overlap_rejected = error.code == "INVALID_EXACT_SCOPE_COVERAGE"
    record("A08_SCOPE_OVERLAP", overlap_rejected)

    reorder_rejected = False
    try:
        CoveragePlanV1((Subcube(1, 1), Subcube(1, 0)))
    except TreewidthReject as error:
        reorder_rejected = error.code == "NONCANONICAL_SCOPE_ORDER"
    record("A09_NONCANONICAL_SCOPE_ORDER", reorder_rejected)

    first = _polynomial(("x",), {("x",): 3}, "lineage-first")
    second = _polynomial(("x",), {("x",): 3}, "lineage-second")
    first_receipt = verify_treewidth_coverage(_request(first, "same-context")).receipt
    second_receipt = verify_treewidth_coverage(_request(second, "same-context")).receipt
    record(
        "A10_SEMANTIC_ROOT_LINEAGE_SUBSTITUTION",
        first.semantic_root == second.semantic_root
        and first_receipt.verification_subject_root != second_receipt.verification_subject_root,
    )

    clique_choices = tuple(f"c{index:02d}" for index in range(14))
    width_rejected = False
    try:
        verify_treewidth_coverage(
            _request(
                _polynomial(clique_choices, {clique_choices: 1}, "width-cap"),
                "width-cap",
            )
        )
    except TreewidthReject as error:
        width_rejected = error.code == "INDUCED_WIDTH_CAPACITY_EXCEEDED"
    record("A11_INDUCED_WIDTH_CAP", width_rejected)

    changed = verify_treewidth_coverage(request)
    object.__setattr__(changed.result, "leaf_count", 1)
    record("A12_RESULT_LEAF_COUNT_REPOINTING", not reverify_treewidth_coverage(request, changed))

    changed = verify_treewidth_coverage(request)
    cycle = Split(0, Leaf(bytes(32)), Leaf(bytes.fromhex("01" * 32)))
    object.__setattr__(cycle, "negative", cycle)
    cyclic_certificate = object.__new__(CoverageCertificate)
    object.__setattr__(cyclic_certificate, "manifest_root", bytes(32))
    object.__setattr__(cyclic_certificate, "subject_root", bytes(32))
    object.__setattr__(cyclic_certificate, "tree", cycle)
    object.__setattr__(changed, "coverage_certificate", cyclic_certificate)
    record("A13_CYCLIC_UNTRUSTED_COVERAGE_TREE", not reverify_treewidth_coverage(request, changed))

    changed = verify_treewidth_coverage(request)
    deep: Leaf | Split = Leaf(bytes(32))
    for depth in range(300):
        deep = Split(depth % 256, deep, Leaf(depth.to_bytes(32, "big")))
    deep_certificate = object.__new__(CoverageCertificate)
    object.__setattr__(deep_certificate, "manifest_root", bytes(32))
    object.__setattr__(deep_certificate, "subject_root", bytes(32))
    object.__setattr__(deep_certificate, "tree", deep)
    object.__setattr__(changed, "coverage_certificate", deep_certificate)
    record("A14_DEEP_UNTRUSTED_COVERAGE_TREE", not reverify_treewidth_coverage(request, changed))

    changed = verify_treewidth_coverage(request)
    shared = Leaf(bytes(32))
    aliased_certificate = CoverageCertificate(bytes(32), bytes(32), Split(0, shared, shared))
    object.__setattr__(changed, "coverage_certificate", aliased_certificate)
    record("A15_ALIASED_UNTRUSTED_COVERAGE_TREE", not reverify_treewidth_coverage(request, changed))

    return attacks


def demonstrations() -> dict[str, object]:
    separator = _polynomial(
        ("y", "z"),
        {("y",): 1, ("z",): 1, ("y", "z"): 1},
        "separator-counterexample",
    )
    separator_outcome = verify_treewidth_coverage(_request(separator, "separator"))

    polarity = _polynomial(
        ("x", "y"),
        {(): 1, ("y",): -1, ("x", "y"): 1},
        "scope-polarity",
    )
    polarity_outcome = verify_treewidth_coverage(_request(polarity, "polarity", depth=1))
    negative_x = next(
        item for item in polarity_outcome.leaf_evidence if item.scope == Subcube(1, 0)
    )

    chain_choices = tuple(f"v{index:02d}" for index in range(12))
    chain_coefficients: dict[tuple[str, ...], int] = {(): 7}
    for index, choice in enumerate(chain_choices):
        chain_coefficients[(choice,)] = (index % 5) - 2 or 1
        if index:
            chain_coefficients[(chain_choices[index - 1], choice)] = ((index * 7) % 9) - 4 or 1
    chain = _polynomial(chain_choices, chain_coefficients, "chain")
    chain_outcome = verify_treewidth_coverage(_request(chain, "chain", depth=4))
    chain_oracle = brute_force_scoped_minimum(chain, Subcube(0, 0))
    if (chain_outcome.result.minimum, chain_outcome.result.assignment) != chain_oracle[:2]:
        raise AssertionError("CHAIN_DEMONSTRATION_DISAGREEMENT")

    return {
        "chain_partition": {
            "aggregate_message_cells": chain_outcome.aggregate_message_cells,
            "aggregate_work_units": chain_outcome.aggregate_work_units,
            "brute_assignments": chain_oracle[2],
            "choices": len(chain_choices),
            "induced_width": max(
                item.scoped_minimum.induced_width for item in chain_outcome.leaf_evidence
            ),
            "leaf_count": chain_outcome.result.leaf_count,
            "minimum": chain_outcome.result.minimum,
        },
        "scope_polarity": {
            "minimum_under_x_negative": negative_x.scoped_minimum.minimum,
            "minimizer": [
                [choice_id, sign] for choice_id, sign in negative_x.scoped_minimum.assignment
            ],
        },
        "separator_counterexample": {
            "exact_minimum": separator_outcome.result.minimum,
            "independent_bag_minima_sum": -3,
            "killed": separator_outcome.result.minimum == -1,
        },
    }


def build_report() -> dict[str, object]:
    attacks = attack_campaign()
    report: dict[str, object] = {
        "attack_summary": {
            "killed": len(attacks),
            "named_attacks": len(attacks),
            "survived": 0,
        },
        "attacks": attacks,
        "authority": "NONE",
        "checked_claims": [
            "exact owned polynomial snapshot",
            "declared source-pinned verifier profile",
            "derived ZRPF ordinal manifest",
            "scope substitution",
            "derived elimination decomposition",
            "complete separator messages",
            "exact recursive subcube coverage",
            "exact bounded global minimum",
        ],
        "claim_status": "BOUNDED_RESEARCH_ONLY",
        "classification": "USEFUL_COMPOSITE_NOT_CURRENTLY_NOVEL",
        "demonstrations": demonstrations(),
        "exhaustive_campaign": exhaustive_campaign(),
        "nonclaims": [
            "novelty",
            "optimal treewidth",
            "cryptographic receipt soundness",
            "unbounded scalability",
            "governance completeness",
            "M6 completion",
            "settlement authority",
            "production readiness",
        ],
        "object": "choice_fiber_treewidth_coverage_certificate_v1",
        "receipt_backend": "PYTHON_REFERENCE_REPLAY",
        "schema": "zenodex.choice-fiber-treewidth-campaign.v1",
    }
    report["content_sha256_without_this_field"] = hashlib.sha256(
        json.dumps(report, separators=(",", ":"), sort_keys=True).encode("ascii")
    ).hexdigest()
    return report


def main() -> int:
    report = build_report()
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    (ROOT / "report.json").write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

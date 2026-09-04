from __future__ import annotations

import json
from hashlib import sha256
from itertools import product
from pathlib import Path

from named_choice_fiber import (
    ChoiceFiberError,
    ChoiceFiberManifest,
    ChoiceFiberPolynomial,
    ChoiceOccurrence,
    RawTerm,
    brute_force_minimum,
    certificate_size_bytes,
    create_affine_certificate,
    create_component_certificate,
    create_forest_certificate,
    verify_affine_certificate,
    verify_component_certificate,
    verify_forest_certificate,
)


def _affine_case(size: int) -> dict[str, object]:
    choices = tuple(f"actor:{index:02d}" for index in range(size))
    coefficients: dict[tuple[str, ...], int] = {(): 3 * size}
    for index, choice in enumerate(choices):
        coefficient = ((index * 17 + 5) % 19) - 9
        if coefficient:
            coefficients[(choice,)] = coefficient
    polynomial = ChoiceFiberPolynomial.from_coefficients(choices, coefficients, f"affine:{size}")
    certificate = create_affine_certificate(polynomial)
    baseline = brute_force_minimum(polynomial)
    if baseline.minimum != certificate.minimum or not verify_affine_certificate(
        polynomial, certificate
    ):
        raise AssertionError("affine certificate mismatch")
    return {
        "choices": size,
        "terms": len(polynomial.terms),
        "brute_assignments": baseline.assignments_checked,
        "certificate_rows": size,
        "certificate_bytes": certificate_size_bytes(certificate),
        "minimum": certificate.minimum,
    }


def _forest_case(size: int, compare_bruteforce: bool) -> dict[str, object]:
    choices = tuple(f"member:{index:02d}" for index in range(size))
    coefficients: dict[tuple[str, ...], int] = {(): size}
    for index, choice in enumerate(choices):
        coefficient = (index % 5) - 2
        if coefficient:
            coefficients[(choice,)] = coefficient
        if index:
            coefficients[(choices[index - 1], choice)] = ((index * 7) % 11) - 5 or 1
    polynomial = ChoiceFiberPolynomial.from_coefficients(choices, coefficients, f"forest:{size}")
    certificate = create_forest_certificate(polynomial)
    if not verify_forest_certificate(polynomial, certificate):
        raise AssertionError("forest certificate did not verify")
    baseline_checks: int | None = None
    if compare_bruteforce:
        baseline = brute_force_minimum(polynomial)
        baseline_checks = baseline.assignments_checked
        if baseline.minimum != certificate.minimum:
            raise AssertionError("forest certificate mismatch")
    return {
        "choices": size,
        "edges": size - 1,
        "brute_assignments": baseline_checks,
        "certificate_rows": len(certificate.rows),
        "certificate_bytes": certificate_size_bytes(certificate),
        "minimum": certificate.minimum,
    }


def _component_case(blocks: int, block_size: int, compare_bruteforce: bool) -> dict[str, object]:
    choices: list[str] = []
    coefficients: dict[tuple[str, ...], int] = {(): 2 * blocks}
    for block in range(blocks):
        local = tuple(f"coalition:{block:02d}:{index}" for index in range(block_size))
        choices.extend(local)
        coefficients[local] = block % 7 + 1
        for index, choice in enumerate(local):
            coefficient = ((block + 2 * index) % 5) - 2
            if coefficient:
                coefficients[(choice,)] = coefficient
    polynomial = ChoiceFiberPolynomial.from_coefficients(
        choices, coefficients, f"components:{blocks}:{block_size}"
    )
    certificate = create_component_certificate(polynomial)
    if not verify_component_certificate(polynomial, certificate):
        raise AssertionError("component certificate did not verify")
    baseline_checks: int | None = None
    if compare_bruteforce:
        baseline = brute_force_minimum(polynomial)
        baseline_checks = baseline.assignments_checked
        if baseline.minimum != certificate.minimum:
            raise AssertionError("component certificate mismatch")
    return {
        "choices": len(choices),
        "blocks": blocks,
        "block_size": block_size,
        "global_branches": 2 ** len(choices),
        "brute_assignments": baseline_checks,
        "component_assignments": sum(item.assignments_checked for item in certificate.components),
        "certificate_bytes": certificate_size_bytes(certificate),
        "minimum": certificate.minimum,
    }


def _falsifiers() -> list[dict[str, object]]:
    records: list[dict[str, object]] = []

    independent = ChoiceFiberPolynomial.from_coefficients(
        ("x", "y"), {(): 1, ("x",): 1, ("y",): -1}, "independent"
    )
    shared_manifest = ChoiceFiberManifest.admit(
        ("x",),
        (
            ChoiceOccurrence("x:positive", "x"),
            ChoiceOccurrence("x:negative", "x"),
        ),
    )
    shared = ChoiceFiberPolynomial.compile(
        shared_manifest,
        (
            RawTerm(1, (), "constant"),
            RawTerm(1, ("x:positive",), "positive"),
            RawTerm(-1, ("x:negative",), "negative"),
        ),
    )
    records.append(
        {
            "id": "F01_CORRELATION_ERASURE",
            "independent_minimum": brute_force_minimum(independent).minimum,
            "shared_minimum": brute_force_minimum(shared).minimum,
            "killed": brute_force_minimum(independent).minimum
            != brute_force_minimum(shared).minimum,
        }
    )

    nonlinear = ChoiceFiberPolynomial.from_coefficients(
        ("x", "y"),
        {(): 2, ("x",): 1, ("y",): 1, ("x", "y"): -3},
        "nonlinear",
    )
    affine_projection = ChoiceFiberPolynomial.from_coefficients(
        ("x", "y"), {(): 2, ("x",): 1, ("y",): 1}, "affine-projection"
    )
    records.append(
        {
            "id": "F02_INTERACTION_DROPPED",
            "exact_minimum": brute_force_minimum(nonlinear).minimum,
            "projected_minimum": brute_force_minimum(affine_projection).minimum,
            "killed": brute_force_minimum(nonlinear).minimum
            < 0
            <= brute_force_minimum(affine_projection).minimum,
        }
    )

    cycle = ChoiceFiberPolynomial.from_coefficients(
        ("x", "y", "z"),
        {(): 2, ("x", "y"): 1, ("y", "z"): 1, ("x", "z"): -3},
        "cycle",
    )
    dropped = ChoiceFiberPolynomial.from_coefficients(
        ("x", "y", "z"),
        {(): 2, ("x", "y"): 1, ("y", "z"): 1},
        "dropped-cycle-edge",
    )
    rejected = False
    try:
        create_forest_certificate(cycle)
    except ChoiceFiberError as error:
        rejected = str(error) == "INTERACTION_GRAPH_NOT_FOREST"
    records.append(
        {
            "id": "F03_CYCLE_EDGE_DROPPED",
            "exact_minimum": brute_force_minimum(cycle).minimum,
            "dropped_edge_minimum": brute_force_minimum(dropped).minimum,
            "forest_gate_rejected_cycle": rejected,
            "killed": rejected
            and brute_force_minimum(cycle).minimum < 0 <= brute_force_minimum(dropped).minimum,
        }
    )

    polynomial = ChoiceFiberPolynomial.from_coefficients(("x",), {(): 3, ("x",): 2}, "bound")
    changed = ChoiceFiberPolynomial.from_coefficients(("x",), {(): 3, ("x",): 3}, "changed")
    records.append(
        {
            "id": "F04_STALE_OR_REPOINTED_CERTIFICATE",
            "killed": not verify_affine_certificate(changed, create_affine_certificate(polynomial)),
        }
    )
    return records


def _bounded_campaign() -> dict[str, int]:
    affine_cases = 0
    affine_assignments = 0
    choices = ("a", "b", "c")
    for coefficients_vector in product(range(-2, 3), repeat=4):
        coefficients: dict[tuple[str, ...], int] = {(): coefficients_vector[0]}
        for choice_id, coefficient in zip(choices, coefficients_vector[1:], strict=True):
            if coefficient:
                coefficients[(choice_id,)] = coefficient
        polynomial = ChoiceFiberPolynomial.from_coefficients(
            choices, coefficients, f"campaign:affine:{affine_cases}"
        )
        baseline = brute_force_minimum(polynomial)
        affine_certificate = create_affine_certificate(polynomial)
        if baseline.minimum != affine_certificate.minimum or not verify_affine_certificate(
            polynomial, affine_certificate
        ):
            raise AssertionError("bounded affine campaign found disagreement")
        affine_cases += 1
        affine_assignments += baseline.assignments_checked

    forest_cases = 0
    forest_assignments = 0
    coefficient_keys = (
        (),
        ("a",),
        ("b",),
        ("c",),
        ("a", "b"),
        ("b", "c"),
    )
    for coefficients_vector in product((-1, 0, 1), repeat=len(coefficient_keys)):
        coefficients = {
            key: coefficient
            for key, coefficient in zip(coefficient_keys, coefficients_vector, strict=True)
            if coefficient
        }
        polynomial = ChoiceFiberPolynomial.from_coefficients(
            choices, coefficients, f"campaign:forest:{forest_cases}"
        )
        baseline = brute_force_minimum(polynomial)
        forest_certificate = create_forest_certificate(polynomial)
        if baseline.minimum != forest_certificate.minimum or not verify_forest_certificate(
            polynomial, forest_certificate
        ):
            raise AssertionError("bounded forest campaign found disagreement")
        forest_cases += 1
        forest_assignments += baseline.assignments_checked

    topology_choices = ("a", "b", "c", "d")
    possible_edges = tuple(
        (topology_choices[left], topology_choices[right])
        for left in range(len(topology_choices))
        for right in range(left + 1, len(topology_choices))
    )
    topology_cases = 0
    topology_forests = 0
    topology_cycles = 0
    topology_assignments = 0

    def independently_is_forest(edges: tuple[tuple[str, str], ...]) -> bool:
        parent = {choice_id: choice_id for choice_id in topology_choices}

        def find(choice_id: str) -> str:
            while parent[choice_id] != choice_id:
                choice_id = parent[choice_id]
            return choice_id

        for left, right in edges:
            left_root = find(left)
            right_root = find(right)
            if left_root == right_root:
                return False
            parent[right_root] = left_root
        return True

    for mask in range(1 << len(possible_edges)):
        selected_edges = tuple(
            edge for index, edge in enumerate(possible_edges) if mask & (1 << index)
        )
        coefficients = {
            (): 3,
            **{
                (choice_id,): index - 2
                for index, choice_id in enumerate(topology_choices)
                if index != 2
            },
            **{edge: ((index * 5 + 3) % 7) - 3 or 1 for index, edge in enumerate(selected_edges)},
        }
        polynomial = ChoiceFiberPolynomial.from_coefficients(
            topology_choices, coefficients, f"campaign:topology:{mask}"
        )
        expected_forest = independently_is_forest(selected_edges)
        try:
            forest_certificate = create_forest_certificate(polynomial)
        except ChoiceFiberError as error:
            if expected_forest or str(error) != "INTERACTION_GRAPH_NOT_FOREST":
                raise AssertionError("forest topology classifier disagreement") from error
            topology_cycles += 1
        else:
            if not expected_forest:
                raise AssertionError("cyclic interaction graph admitted as forest")
            baseline = brute_force_minimum(polynomial)
            if baseline.minimum != forest_certificate.minimum or not verify_forest_certificate(
                polynomial, forest_certificate
            ):
                raise AssertionError("forest topology minimum disagreement")
            topology_forests += 1
            topology_assignments += baseline.assignments_checked
        topology_cases += 1

    return {
        "affine_cases": affine_cases,
        "affine_assignments": affine_assignments,
        "forest_cases": forest_cases,
        "forest_assignments": forest_assignments,
        "topology_cases": topology_cases,
        "topology_forests": topology_forests,
        "topology_cycles_rejected": topology_cycles,
        "topology_assignments": topology_assignments,
        "total_cases": affine_cases + forest_cases + topology_cases,
        "total_assignments": (affine_assignments + forest_assignments + topology_assignments),
    }


def build_report() -> dict[str, object]:
    affine = [_affine_case(size) for size in (4, 8, 12, 16)]
    forest = [
        _forest_case(4, True),
        _forest_case(8, True),
        _forest_case(12, True),
        _forest_case(16, True),
        _forest_case(32, False),
        _forest_case(64, False),
    ]
    components = [
        _component_case(2, 3, True),
        _component_case(4, 3, True),
        _component_case(8, 3, False),
        _component_case(16, 3, False),
    ]
    falsifiers = _falsifiers()
    if not all(bool(item["killed"]) for item in falsifiers):
        raise AssertionError("a permanent falsifier survived")
    report: dict[str, object] = {
        "schema": "zenodex.named-choice-fiber-experiment.v1",
        "claim_ceiling": "BOUNDED_RESEARCH_ONLY",
        "candidate": "Named Choice-Fiber Polynomial",
        "classification": "USEFUL_COMPOSITE_NOT_CURRENTLY_NOVEL",
        "affine_cases": affine,
        "pairwise_forest_cases": forest,
        "nonlinear_component_cases": components,
        "bounded_campaign": _bounded_campaign(),
        "falsifiers": falsifiers,
        "hardness_boundary": {
            "general_pairwise_minimization": "NP-hard via weighted Max-Cut",
            "affine": "exact O(n + m)",
            "pairwise_forest": "exact O(n + m)",
            "bounded_components": "exact O(sum(2^component_size * local_terms))",
            "bounded_treewidth_extension": "known exact dynamic-programming direction; not implemented",
        },
        "nonclaims": [
            "No novelty, patentability, or freedom-to-operate conclusion",
            "No unbounded polynomial-size certificate for general interactions",
            "No Tau runtime, ZRPF, M6, governance, or settlement authority",
            "No open-population counting or Sybil-resistance theorem",
            "No cryptographic binding beyond deterministic SHA-256 identities",
        ],
    }
    stable = json.dumps(report, sort_keys=True, separators=(",", ":")).encode("utf-8")
    report["content_sha256_without_this_field"] = sha256(stable).hexdigest()
    return report


def main() -> None:
    report = build_report()
    output = Path(__file__).with_name("report.json")
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

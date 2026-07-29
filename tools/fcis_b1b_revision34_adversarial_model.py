#!/usr/bin/env python3
"""Exhaustive bounded falsification model for the B1B Revision 3.4 boundary.

This is evidence only.  It constructs no ZenoDEX authority and imports no
runtime, state, settlement, receipt, bundle, proof, datastore, or shell module.
"""

from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from enum import Enum


class UpdateModelCode(Enum):
    ACCEPT = "accept"
    STRUCTURAL_REJECT = "structural_reject"
    ALGORITHM_REJECT = "algorithm_version_mismatch"
    LANGUAGE_REJECT = "accepted_language_version_mismatch"
    POLICY_ROOT_REJECT = "policy_root_mismatch"
    EMBEDDED_ROOT_REJECT = "configuration_root_mismatch"
    COMMAND_ROOT_REJECT = "command_root_mismatch"
    DEPLOYMENT_REJECT = "deployment_mismatch"
    DOMAIN_REJECT = "domain_mismatch"
    VERSION_REJECT = "version_increment_mismatch"
    ACTIVATION_REJECT = "activation_sequence_mismatch"


@dataclass(frozen=True, slots=True)
class UpdateFacts:
    structurally_exact: bool
    algorithm_matches: bool
    language_matches: bool
    policy_root_matches: bool
    embedded_configuration_root_matches: bool
    command_root_matches: bool
    deployment_matches: bool
    domain_matches: bool
    version_increments: bool
    activation_is_successor_sequence: bool


def derive_revision34_update(facts: UpdateFacts) -> UpdateModelCode:
    """Model the exact fail-closed Revision 3.4 guard order."""

    ordered = (
        (facts.structurally_exact, UpdateModelCode.STRUCTURAL_REJECT),
        (facts.algorithm_matches, UpdateModelCode.ALGORITHM_REJECT),
        (facts.language_matches, UpdateModelCode.LANGUAGE_REJECT),
        (facts.policy_root_matches, UpdateModelCode.POLICY_ROOT_REJECT),
        (
            facts.embedded_configuration_root_matches,
            UpdateModelCode.EMBEDDED_ROOT_REJECT,
        ),
        (facts.command_root_matches, UpdateModelCode.COMMAND_ROOT_REJECT),
        (facts.deployment_matches, UpdateModelCode.DEPLOYMENT_REJECT),
        (facts.domain_matches, UpdateModelCode.DOMAIN_REJECT),
        (facts.version_increments, UpdateModelCode.VERSION_REJECT),
        (
            facts.activation_is_successor_sequence,
            UpdateModelCode.ACTIVATION_REJECT,
        ),
    )
    for predicate, rejection in ordered:
        if not predicate:
            return rejection
    return UpdateModelCode.ACCEPT


def derive_unsafe_admit_then_root_update(facts: UpdateFacts) -> UpdateModelCode:
    """The refuted Revision 3.3 shape, retained only as a negative control."""

    if not facts.structurally_exact:
        return UpdateModelCode.STRUCTURAL_REJECT
    if not facts.command_root_matches:
        return UpdateModelCode.COMMAND_ROOT_REJECT
    if not facts.deployment_matches:
        return UpdateModelCode.DEPLOYMENT_REJECT
    if not facts.domain_matches:
        return UpdateModelCode.DOMAIN_REJECT
    if not facts.version_increments:
        return UpdateModelCode.VERSION_REJECT
    if not facts.activation_is_successor_sequence:
        return UpdateModelCode.ACTIVATION_REJECT
    return UpdateModelCode.ACCEPT


def _all_facts() -> tuple[UpdateFacts, ...]:
    return tuple(UpdateFacts(*bits) for bits in itertools.product((False, True), repeat=10))


def _topological_order(edges: tuple[tuple[str, str], ...]) -> tuple[str, ...] | None:
    nodes = sorted({node for edge in edges for node in edge})
    incoming = {node: 0 for node in nodes}
    outgoing: dict[str, list[str]] = {node: [] for node in nodes}
    for source, target in edges:
        outgoing[source].append(target)
        incoming[target] += 1
    ready = sorted(node for node, count in incoming.items() if count == 0)
    order: list[str] = []
    while ready:
        node = ready.pop(0)
        order.append(node)
        for target in sorted(outgoing[node]):
            incoming[target] -= 1
            if incoming[target] == 0:
                ready.append(target)
                ready.sort()
    return tuple(order) if len(order) == len(nodes) else None


def revision34_dependency_edges() -> tuple[tuple[str, str], ...]:
    return (
        ("exact_pre_state", "transition_cause"),
        ("authenticated_command", "transition_cause"),
        ("authenticated_context", "transition_cause"),
        ("untrusted_content", "admitted_configuration"),
        ("admitted_configuration", "validated_configuration"),
        ("validated_configuration", "evaluation_candidate"),
        ("transition_cause", "evaluation_candidate"),
        ("deterministic_outputs", "evaluation_candidate"),
        ("evaluation_candidate", "candidate_root"),
        ("candidate_root", "receipt"),
        ("evaluation_candidate", "decision"),
        ("receipt", "decision"),
        ("decision", "commit_bundle"),
    )


def receipt_cycle_mutant_edges() -> tuple[tuple[str, str], ...]:
    return revision34_dependency_edges() + (("receipt", "evaluation_candidate"),)


def build_report() -> dict[str, object]:
    facts = _all_facts()
    safe_results = tuple(derive_revision34_update(case) for case in facts)
    unsafe_results = tuple(derive_unsafe_admit_then_root_update(case) for case in facts)
    safe_accepts = sum(result is UpdateModelCode.ACCEPT for result in safe_results)
    unsafe_invalid_accepts = sum(
        result is UpdateModelCode.ACCEPT
        and not (
            case.algorithm_matches
            and case.language_matches
            and case.policy_root_matches
            and case.embedded_configuration_root_matches
        )
        for case, result in zip(facts, unsafe_results, strict=True)
    )
    safe_order = _topological_order(revision34_dependency_edges())
    mutant_order = _topological_order(receipt_cycle_mutant_edges())
    return {
        "schema": "zenodex/fcis/b1b-revision34-adversarial-model/v1",
        "cases": len(facts),
        "safe_accepts": safe_accepts,
        "unsafe_semantically_invalid_accepts": unsafe_invalid_accepts,
        "dependency_order": safe_order,
        "receipt_cycle_mutant_rejected": mutant_order is None,
        "all_guards_required_for_accept": all(
            (result is UpdateModelCode.ACCEPT)
            == all(
                (
                    case.structurally_exact,
                    case.algorithm_matches,
                    case.language_matches,
                    case.policy_root_matches,
                    case.embedded_configuration_root_matches,
                    case.command_root_matches,
                    case.deployment_matches,
                    case.domain_matches,
                    case.version_increments,
                    case.activation_is_successor_sequence,
                )
            )
            for case, result in zip(facts, safe_results, strict=True)
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = build_report()
    ok = (
        report["cases"] == 1_024
        and report["safe_accepts"] == 1
        and int(report["unsafe_semantically_invalid_accepts"]) > 0
        and report["receipt_cycle_mutant_rejected"] is True
        and report["all_guards_required_for_accept"] is True
    )
    if args.json:
        print(json.dumps({**report, "ok": ok}, sort_keys=True))
    else:
        print(f"cases={report['cases']}")
        print(f"safe_accepts={report['safe_accepts']}")
        print(
            "unsafe_semantically_invalid_accepts="
            f"{report['unsafe_semantically_invalid_accepts']}"
        )
        print(f"receipt_cycle_mutant_rejected={report['receipt_cycle_mutant_rejected']}")
        print(f"all_guards_required_for_accept={report['all_guards_required_for_accept']}")
        print(f"ok={ok}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

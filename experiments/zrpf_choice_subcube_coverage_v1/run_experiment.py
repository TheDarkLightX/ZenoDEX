#!/usr/bin/env python3
"""Run the bounded ZRPF choice-fiber coverage experiment."""

from __future__ import annotations

import json
import time
from dataclasses import replace

from subcube_certificate import (
    CertificateReject,
    ChoiceManifest,
    CoverageCertificate,
    Leaf,
    Split,
    Subcube,
    brute_force_partition,
    build_canonical_certificate,
    comb_partition,
    deterministic_digest,
    explicit_scope_manifest_bytes,
    make_receipt,
    prefix_partition,
    verify_certificate,
    verify_volume_separation_partition,
)


def recursively_generated_partitions(nchoices: int) -> tuple[tuple[Subcube, ...], ...]:
    """Enumerate all distinct recursively split partitions through n=3."""

    memo: dict[Subcube, frozenset[tuple[Subcube, ...]]] = {}
    limit = (1 << nchoices) - 1

    def rec(region: Subcube) -> frozenset[tuple[Subcube, ...]]:
        cached = memo.get(region)
        if cached is not None:
            return cached
        partitions: set[tuple[Subcube, ...]] = {(region,)}
        free = limit & ~region.fixed_mask
        while free:
            bit = free & -free
            ordinal = bit.bit_length() - 1
            negative = rec(region.with_choice(ordinal, False))
            positive = rec(region.with_choice(ordinal, True))
            for left in negative:
                for right in positive:
                    partitions.add(tuple(sorted(left + right)))
            free ^= bit
        frozen = frozenset(partitions)
        memo[region] = frozen
        return frozen

    return tuple(sorted(rec(Subcube(0, 0)), key=lambda value: (len(value), value)))


def exhaustive_campaign() -> dict[str, object]:
    cases = 0
    total_assignments = 0
    total_probes = 0
    total_nodes = 0
    by_n: list[dict[str, int]] = []
    for nchoices in (1, 2, 3):
        manifest = ChoiceManifest(tuple(f"choice-{i}" for i in range(nchoices)))
        subject = deterministic_digest(f"exhaustive-subject:{nchoices}")
        partitions = recursively_generated_partitions(nchoices)
        for case_index, scopes in enumerate(partitions):
            receipts = tuple(
                make_receipt(
                    manifest,
                    subject,
                    scope,
                    f"exhaustive:{nchoices}:{case_index}:{scope.fixed_mask}:{scope.positive_mask}",
                )
                for scope in scopes
            )
            certificate = build_canonical_certificate(manifest, subject, receipts)
            stats = verify_certificate(manifest, subject, certificate, receipts)
            general = verify_volume_separation_partition(manifest, subject, receipts)
            brute = brute_force_partition(manifest, subject, receipts)
            if not brute.accepted:
                raise AssertionError((nchoices, case_index, brute))
            cases += 1
            total_assignments += brute.assignments_checked
            total_probes += brute.membership_probes
            total_nodes += stats.nodes
            if general.total_covered_assignments != 1 << nchoices:
                raise AssertionError(general)
        by_n.append({"named_choices": nchoices, "distinct_partitions": len(partitions)})
    return {
        "cases": cases,
        "total_assignments_checked": total_assignments,
        "total_membership_probes": total_probes,
        "total_certificate_nodes_checked": total_nodes,
        "by_choice_count": by_n,
    }


def _expect_reject(label: str, expected: str, operation: object) -> dict[str, str]:
    try:
        assert callable(operation)
        operation()
    except CertificateReject as exc:
        if exc.code != expected:
            raise AssertionError(f"{label}: expected {expected}, got {exc.code}") from exc
        return {"attack": label, "killed_by": exc.code}
    raise AssertionError(f"{label}: attack survived")


def attack_campaign() -> list[dict[str, str]]:
    manifest = ChoiceManifest(("oracle-shock", "fee-policy", "sequencer-mode"))
    subject = deterministic_digest("attack-subject")
    receipts = prefix_partition(manifest, subject, 2)
    certificate = build_canonical_certificate(manifest, subject, receipts)
    root = certificate.tree
    if not isinstance(root, Split):
        raise TypeError("expected split root")

    attacks: list[dict[str, str]] = []
    attacks.append(
        _expect_reject(
            "omit_one_subcube",
            "MISSING_SPLIT_BRANCH",
            lambda: build_canonical_certificate(manifest, subject, receipts[:-1]),
        )
    )

    attacks.append(
        _expect_reject(
            "general_checker_omission",
            "SUBCUBE_VOLUME_OMISSION",
            lambda: verify_volume_separation_partition(manifest, subject, receipts[:-1]),
        )
    )

    parent = make_receipt(manifest, subject, Subcube(0, 0), "overlap-parent")
    attacks.append(
        _expect_reject(
            "overlap_parent_and_children",
            "REGION_LEAF_OVERLAPS_OTHER_SCOPE",
            lambda: build_canonical_certificate(manifest, subject, (parent, *receipts)),
        )
    )

    attacks.append(
        _expect_reject(
            "general_checker_overlap",
            "PAIRWISE_SUBCUBE_OVERLAP",
            lambda: verify_volume_separation_partition(manifest, subject, (parent, *receipts)),
        )
    )

    swapped = CoverageCertificate(
        certificate.manifest_root,
        certificate.subject_root,
        Split(root.choice_ordinal, root.positive, root.negative),
    )
    attacks.append(
        _expect_reject(
            "swap_negative_positive_children",
            "LEAF_SCOPE_PATH_MISMATCH",
            lambda: verify_certificate(manifest, subject, swapped, receipts),
        )
    )

    renamed = ChoiceManifest(("fee-policy", "oracle-shock", "sequencer-mode"))
    attacks.append(
        _expect_reject(
            "relabel_choice_ordinals",
            "MANIFEST_ROOT_MISMATCH",
            lambda: verify_certificate(renamed, subject, certificate, receipts),
        )
    )

    foreign_subject = deterministic_digest("foreign-subject")
    attacks.append(
        _expect_reject(
            "cross_subject_receipt",
            "FOREIGN_RECEIPT_SUBJECT",
            lambda: verify_certificate(
                manifest,
                subject,
                certificate,
                (replace(receipts[0], subject_root=foreign_subject), *receipts[1:]),
            ),
        )
    )

    attacks.append(
        _expect_reject(
            "mutate_leaf_proof_commitment",
            "UNKNOWN_LEAF_RECEIPT",
            lambda: verify_certificate(
                manifest,
                subject,
                certificate,
                (
                    replace(
                        receipts[0],
                        proof_commitment=deterministic_digest("forged-proof"),
                    ),
                    *receipts[1:],
                ),
            ),
        )
    )

    surplus = make_receipt(manifest, subject, receipts[0].scope, "surplus-copy")
    attacks.append(
        _expect_reject(
            "surplus_unconsumed_receipt",
            "SURPLUS_UNCONSUMED_RECEIPT",
            lambda: verify_certificate(manifest, subject, certificate, (*receipts, surplus)),
        )
    )

    receipt_by_scope = {receipt.scope: receipt for receipt in receipts}
    # Same exact four singleton scopes as the canonical x0-then-x1 tree, but
    # split by x1 first.  Coverage is correct; representation is noncanonical.
    noncanonical = CoverageCertificate(
        manifest.root,
        subject,
        Split(
            1,
            Split(
                0,
                Leaf(receipt_by_scope[Subcube(0b11, 0b00)].root(manifest)),
                Leaf(receipt_by_scope[Subcube(0b11, 0b01)].root(manifest)),
            ),
            Split(
                0,
                Leaf(receipt_by_scope[Subcube(0b11, 0b10)].root(manifest)),
                Leaf(receipt_by_scope[Subcube(0b11, 0b11)].root(manifest)),
            ),
        ),
    )
    verify_volume_separation_partition(manifest, subject, receipts)
    attacks.append(
        _expect_reject(
            "alternate_valid_split_order",
            "NONCANONICAL_SPLIT_CHOICE",
            lambda: verify_certificate(manifest, subject, noncanonical, receipts),
        )
    )

    reused = CoverageCertificate(
        manifest.root,
        subject,
        Split(
            0,
            Split(0, Leaf(receipts[0].root(manifest)), Leaf(receipts[1].root(manifest))),
            root.positive,
        ),
    )
    attacks.append(
        _expect_reject(
            "reuse_choice_on_path",
            "CHOICE_REUSED_ON_PATH",
            lambda: verify_certificate(manifest, subject, reused, receipts),
        )
    )
    return attacks


def benchmark_rows() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for nchoices, fixed_prefix in ((8, 8), (12, 8), (16, 8), (64, 8)):
        manifest = ChoiceManifest(tuple(f"c{i:03d}" for i in range(nchoices)))
        subject = deterministic_digest(f"benchmark:{nchoices}:{fixed_prefix}")
        receipts = prefix_partition(manifest, subject, fixed_prefix)
        certificate = build_canonical_certificate(manifest, subject, receipts)

        started = time.perf_counter()
        stats = verify_certificate(manifest, subject, certificate, receipts)
        tree_seconds = time.perf_counter() - started
        general_started = time.perf_counter()
        general = verify_volume_separation_partition(manifest, subject, receipts)
        general_seconds = time.perf_counter() - general_started

        brute_seconds: float | None = None
        brute_assignments: int | None = None
        brute_probes: int | None = None
        if nchoices <= 16:
            started = time.perf_counter()
            brute = brute_force_partition(manifest, subject, receipts)
            brute_seconds = time.perf_counter() - started
            if not brute.accepted:
                raise AssertionError(brute)
            brute_assignments = brute.assignments_checked
            brute_probes = brute.membership_probes

        tree_bytes = len(certificate.encoded())
        explicit_bytes = len(explicit_scope_manifest_bytes(manifest, subject, receipts))
        rows.append(
            {
                "named_choices": nchoices,
                "fixed_choices_per_leaf": fixed_prefix,
                "free_choices_per_leaf": nchoices - fixed_prefix,
                "leaves": stats.leaves,
                "tree_nodes": stats.nodes,
                "general_pair_checks": general.unordered_pairs_checked,
                "tree_certificate_bytes": tree_bytes,
                "explicit_scope_manifest_bytes": explicit_bytes,
                "explicit_over_tree_byte_ratio": round(explicit_bytes / tree_bytes, 4),
                "tree_verifier_seconds": round(tree_seconds, 6),
                "general_verifier_seconds": round(general_seconds, 6),
                "brute_force_seconds": (
                    round(brute_seconds, 6) if brute_seconds is not None else None
                ),
                "brute_assignments": brute_assignments,
                "brute_membership_probes": brute_probes,
            }
        )

    manifest = ChoiceManifest(tuple(f"c{i:03d}" for i in range(64)))
    subject = deterministic_digest("benchmark:comb:64")
    receipts = comb_partition(manifest, subject, 64)
    certificate = build_canonical_certificate(manifest, subject, receipts)
    stats = verify_certificate(manifest, subject, certificate, receipts)
    general = verify_volume_separation_partition(manifest, subject, receipts)
    tree_bytes = len(certificate.encoded())
    explicit_bytes = len(explicit_scope_manifest_bytes(manifest, subject, receipts))
    rows.append(
        {
            "named_choices": 64,
            "partition_shape": "comb",
            "leaves": stats.leaves,
            "tree_nodes": stats.nodes,
            "general_pair_checks": general.unordered_pairs_checked,
            "tree_certificate_bytes": tree_bytes,
            "explicit_scope_manifest_bytes": explicit_bytes,
            "explicit_over_tree_byte_ratio": round(explicit_bytes / tree_bytes, 4),
            "tree_verifier_seconds": None,
            "general_verifier_seconds": None,
            "brute_force_seconds": None,
            "brute_assignments": None,
            "brute_membership_probes": None,
        }
    )
    return rows


def main() -> int:
    exhaustive = exhaustive_campaign()
    attacks = attack_campaign()
    benchmarks = benchmark_rows()

    # Smallest bounded witness found by exhaustive exact-cover search: this is
    # an exact partition, but no choice is fixed in every cell at the root, so
    # it is outside recursive split-tree form.
    witness_manifest = ChoiceManifest(("x0", "x1", "x2"))
    witness_subject = deterministic_digest("nonrecursive-witness")
    witness_scopes = (
        Subcube(0b011, 0b000),
        Subcube(0b101, 0b001),
        Subcube(0b110, 0b110),
        Subcube(0b111, 0b010),
        Subcube(0b111, 0b101),
    )
    witness_receipts = tuple(
        make_receipt(
            witness_manifest,
            witness_subject,
            scope,
            f"nonrecursive:{index}",
        )
        for index, scope in enumerate(witness_scopes)
    )
    witness_brute = brute_force_partition(witness_manifest, witness_subject, witness_receipts)
    witness_general = verify_volume_separation_partition(
        witness_manifest, witness_subject, witness_receipts
    )
    tree_reject = _expect_reject(
        "nonrecursive_exact_partition",
        "NON_RECURSIVE_SUBCUBE_PARTITION",
        lambda: build_canonical_certificate(witness_manifest, witness_subject, witness_receipts),
    )
    result = {
        "authority": "NONE",
        "claim_status": "BOUNDED_RESEARCH_ONLY",
        "candidate": "Canonical Named Choice Subcube Partition Tree V1",
        "semantic_object": "exact disjoint cover of {-1,+1}^n by recursively split axis-aligned subcubes",
        "survivor": {
            "decision": "RETAIN_AS_ZRPF_COVERAGE_PRIMITIVE",
            "reason": (
                "full binary splitting makes omission and overlap unrepresentable; "
                "named manifest roots and scope-bound receipts close relabeling"
            ),
            "guest_verifier_cost": "linear in certificate nodes plus receipt/scope hashing",
            "host_projection": (
                "a recursive proof may expose one fixed-size seal after proving the "
                "linear tree check inside the guest"
            ),
        },
        "exhaustive_campaign": exhaustive,
        "attacks": attacks,
        "attack_summary": {
            "named_attacks": len(attacks),
            "killed": len(attacks),
            "survived": 0,
        },
        "benchmarks": benchmarks,
        "generality_boundary": {
            "named_choices": 3,
            "cells": 5,
            "scopes": [
                {
                    "fixed_mask": scope.fixed_mask,
                    "positive_mask": scope.positive_mask,
                }
                for scope in witness_scopes
            ],
            "brute_oracle": witness_brute.code,
            "general_volume_separation_checker": {
                "accepted": True,
                "unordered_pairs_checked": witness_general.unordered_pairs_checked,
            },
            "recursive_tree_checker": tree_reject,
        },
        "nonclaims": [
            "not a novel decision-tree or subcube-partition theorem",
            "not a certificate for every possible exact subcube partition",
            "not a cryptographic proof that any leaf computation is correct",
            "not constant total proving work; recursive sealing only makes host verification succinct",
            "not a replacement for ZRPF receipt soundness, image identity, or proof-context binding",
            "not a Tau Net throughput result",
            "not production settlement authority",
        ],
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

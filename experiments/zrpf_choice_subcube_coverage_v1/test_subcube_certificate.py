#!/usr/bin/env python3
"""Focused tests for the bounded subcube coverage reference."""

from __future__ import annotations

import unittest

from subcube_certificate import (
    MAX_BRUTE_MEMBERSHIP_PROBES,
    MAX_CHOICE_COUNT,
    MAX_RECEIPTS,
    CertificateReject,
    ChoiceManifest,
    CoverageCertificate,
    Leaf,
    ShardReceipt,
    Split,
    Subcube,
    brute_force_partition,
    build_canonical_certificate,
    deterministic_digest,
    make_receipt,
    prefix_partition,
    verify_certificate,
    verify_volume_separation_partition,
)


class SubcubeCertificateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = ChoiceManifest(("a", "b", "c", "d"))
        self.subject = deterministic_digest("test-subject")

    def test_full_scope_is_one_leaf_exact_cover(self) -> None:
        receipts = (make_receipt(self.manifest, self.subject, Subcube(0, 0), "root"),)
        certificate = build_canonical_certificate(self.manifest, self.subject, receipts)
        stats = verify_certificate(self.manifest, self.subject, certificate, receipts)
        self.assertEqual(stats.nodes, 1)
        self.assertTrue(brute_force_partition(self.manifest, self.subject, receipts).accepted)

    def test_prefix_partition_matches_brute_oracle(self) -> None:
        receipts = prefix_partition(self.manifest, self.subject, 3)
        certificate = build_canonical_certificate(self.manifest, self.subject, receipts)
        stats = verify_certificate(self.manifest, self.subject, certificate, receipts)
        brute = brute_force_partition(self.manifest, self.subject, receipts)
        self.assertTrue(brute.accepted)
        self.assertEqual(stats.leaves, 8)
        self.assertEqual(stats.nodes, 15)

    def test_omission_has_canonical_assignment_witness(self) -> None:
        receipts = prefix_partition(self.manifest, self.subject, 2)[:-1]
        result = brute_force_partition(self.manifest, self.subject, receipts)
        self.assertFalse(result.accepted)
        self.assertEqual(result.code, "COVERAGE_OMISSION")
        self.assertEqual(result.first_assignment_mask, 0b11)

    def test_overlap_has_canonical_assignment_witness(self) -> None:
        children = prefix_partition(self.manifest, self.subject, 1)
        root = make_receipt(self.manifest, self.subject, Subcube(0, 0), "root")
        result = brute_force_partition(self.manifest, self.subject, (root, *children))
        self.assertFalse(result.accepted)
        self.assertEqual(result.code, "COVERAGE_OVERLAP")
        self.assertEqual(result.first_assignment_mask, 0)

    def test_positive_bits_must_be_fixed(self) -> None:
        with self.assertRaisesRegex(CertificateReject, "POSITIVE_BIT_NOT_FIXED"):
            Subcube(0b001, 0b011).validate(4)

    def test_constructor_inputs_are_exact_immutable_values(self) -> None:
        names = ["a"]
        with self.assertRaisesRegex(CertificateReject, "CHOICE_MANIFEST_NOT_TUPLE"):
            ChoiceManifest(names)  # type: ignore[arg-type]
        with self.assertRaisesRegex(CertificateReject, "INVALID_CHOICE_NAME"):
            ChoiceManifest((1,))  # type: ignore[arg-type]
        with self.assertRaisesRegex(
            CertificateReject,
            "SCOPE_MASK_NOT_EXACT_INTEGER",
        ):
            Subcube(True, False)
        with self.assertRaisesRegex(CertificateReject, "INVALID_CHOICE_ORDINAL"):
            Subcube(0, 0).with_choice(-1, False)
        with self.assertRaisesRegex(CertificateReject, "INVALID_CHOICE_ORDINAL"):
            Subcube(0, 0).with_choice(MAX_CHOICE_COUNT, False)
        with self.assertRaisesRegex(CertificateReject, "BAD_SUBJECT_ROOT_LENGTH"):
            make_receipt(
                self.manifest,
                bytearray(self.subject),  # type: ignore[arg-type]
                Subcube(0, 0),
                "mutable-subject",
            )
        with self.assertRaisesRegex(CertificateReject, "BAD_RECEIPT_DIGEST_LENGTH"):
            ShardReceipt(
                self.subject,
                Subcube(0, 0),
                bytearray(bytes(32)),  # type: ignore[arg-type]
            )
        with self.assertRaisesRegex(
            CertificateReject,
            "BAD_LEAF_RECEIPT_ROOT_LENGTH",
        ):
            Leaf(bytearray(bytes(32)))  # type: ignore[arg-type]
        with self.assertRaisesRegex(CertificateReject, "BAD_MANIFEST_ROOT_LENGTH"):
            CoverageCertificate(
                bytearray(self.manifest.root),  # type: ignore[arg-type]
                self.subject,
                Leaf(bytes(32)),
            )

    def test_subclassed_authority_values_are_rejected(self) -> None:
        receipts = prefix_partition(self.manifest, self.subject, 1)
        certificate = build_canonical_certificate(self.manifest, self.subject, receipts)

        class ForgedManifest(ChoiceManifest):
            @property
            def root(self) -> bytes:
                return self_manifest_root

        self_manifest_root = self.manifest.root
        forged_manifest = ForgedManifest(("mallory-a", "mallory-b", "mallory-c", "mallory-d"))
        with self.assertRaisesRegex(CertificateReject, "INVALID_CHOICE_MANIFEST"):
            verify_certificate(
                forged_manifest,
                self.subject,
                certificate,
                receipts,
            )

        class ForgedReceipt(ShardReceipt):
            pass

        forged_receipt = ForgedReceipt(
            receipts[0].subject_root,
            receipts[0].scope,
            receipts[0].proof_commitment,
        )
        with self.assertRaisesRegex(CertificateReject, "INVALID_SHARD_RECEIPT"):
            verify_volume_separation_partition(
                self.manifest,
                self.subject,
                (forged_receipt,),
            )

        class ForgedCertificate(CoverageCertificate):
            pass

        forged_certificate = ForgedCertificate(
            certificate.manifest_root,
            certificate.subject_root,
            certificate.tree,
        )
        with self.assertRaisesRegex(CertificateReject, "INVALID_COVERAGE_CERTIFICATE"):
            verify_certificate(
                self.manifest,
                self.subject,
                forged_certificate,
                receipts,
            )

    def test_resource_profile_fails_closed(self) -> None:
        self.assertEqual(MAX_BRUTE_MEMBERSHIP_PROBES, 20_000_000)
        with self.assertRaisesRegex(CertificateReject, "TOO_MANY_CHOICES"):
            ChoiceManifest(tuple(f"choice-{index}" for index in range(MAX_CHOICE_COUNT + 1)))
        receipt = make_receipt(
            self.manifest,
            self.subject,
            Subcube(0, 0),
            "capacity",
        )
        with self.assertRaisesRegex(CertificateReject, "RECEIPT_CAPACITY_EXCEEDED"):
            verify_volume_separation_partition(
                self.manifest,
                self.subject,
                (receipt for _ in range(MAX_RECEIPTS + 1)),
            )

        tree: Leaf | Split = Leaf(bytes(32))
        for ordinal in range(MAX_CHOICE_COUNT):
            tree = Split(ordinal, tree, Leaf(bytes(32)))
        tree = Split(0, tree, Leaf(bytes(32)))
        with self.assertRaisesRegex(CertificateReject, "INVALID_SPLIT_ORDINAL"):
            Split(MAX_CHOICE_COUNT, Leaf(bytes(32)), Leaf(bytes(32)))
        with self.assertRaisesRegex(
            CertificateReject,
            "TREE_DEPTH_CAPACITY_EXCEEDED",
        ):
            CoverageCertificate(self.manifest.root, self.subject, tree)

        brute_manifest = ChoiceManifest(tuple(f"b{index}" for index in range(20)))
        brute_receipt = make_receipt(
            brute_manifest,
            self.subject,
            Subcube(0, 0),
            "brute-capacity",
        )
        with self.assertRaisesRegex(
            CertificateReject,
            "BRUTE_MEMBERSHIP_CAPACITY_EXCEEDED",
        ):
            brute_force_partition(
                brute_manifest,
                self.subject,
                (brute_receipt,) * 20,
            )

    def test_subject_is_an_external_pinned_input(self) -> None:
        receipts = prefix_partition(self.manifest, self.subject, 1)
        certificate = build_canonical_certificate(self.manifest, self.subject, receipts)
        with self.assertRaisesRegex(CertificateReject, "CERTIFICATE_SUBJECT_MISMATCH"):
            verify_certificate(
                self.manifest,
                deterministic_digest("other-subject"),
                certificate,
                receipts,
            )

    def test_nonrecursive_exact_partition_uses_general_checker(self) -> None:
        scopes = (
            Subcube(0b011, 0b000),
            Subcube(0b101, 0b001),
            Subcube(0b110, 0b110),
            Subcube(0b111, 0b010),
            Subcube(0b111, 0b101),
        )
        manifest = ChoiceManifest(("x0", "x1", "x2"))
        receipts = tuple(
            make_receipt(manifest, self.subject, scope, f"cell:{index}")
            for index, scope in enumerate(scopes)
        )
        self.assertTrue(brute_force_partition(manifest, self.subject, receipts).accepted)
        stats = verify_volume_separation_partition(manifest, self.subject, receipts)
        self.assertEqual(stats.unordered_pairs_checked, 10)
        with self.assertRaisesRegex(CertificateReject, "NON_RECURSIVE_SUBCUBE_PARTITION"):
            build_canonical_certificate(manifest, self.subject, receipts)


if __name__ == "__main__":
    unittest.main()

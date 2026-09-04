#!/usr/bin/env python3
"""Exact bounded coverage certificates for named Boolean choice fibers.

This module is a research reference model.  It deliberately separates:

* semantic scope: an axis-aligned subcube of ``{-1,+1}^n``;
* exact lineage: a receipt commitment for the proof assigned to that scope;
* coverage structure: a canonical full binary partition tree.

The tree is useful when a proof scheduler is free to create recursively split
shards.  It is not a complete representation of every possible exact subcube
partition.
"""

from __future__ import annotations

import hashlib
import struct
from collections.abc import Iterable
from dataclasses import dataclass
from typing import TypeAlias

Digest = bytes
ZERO32 = bytes(32)
MAX_CHOICE_COUNT = 256
MAX_CHOICE_NAME_BYTES = 128
MAX_RECEIPTS = 4096
MAX_TREE_NODES = 2 * MAX_RECEIPTS - 1
MAX_BRUTE_CHOICES = 20
MAX_BRUTE_MEMBERSHIP_PROBES = 20_000_000


class CertificateReject(ValueError):
    """Typed research rejection with a stable code."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


def _u32(value: int) -> bytes:
    if value < 0 or value > 0xFFFF_FFFF:
        raise CertificateReject("U32_OUT_OF_RANGE")
    return struct.pack(">I", value)


def _frame(value: bytes) -> bytes:
    return _u32(len(value)) + value


def _hash(domain: bytes, *parts: bytes) -> Digest:
    material = _frame(domain) + b"".join(_frame(part) for part in parts)
    return hashlib.sha256(material).digest()


def _require_digest(value: object, code: str) -> bytes:
    if type(value) is not bytes or len(value) != 32:
        raise CertificateReject(code)
    return value


def _mask_bytes(mask: int, nchoices: int) -> bytes:
    width = (nchoices + 7) // 8
    return mask.to_bytes(width, "big")


@dataclass(frozen=True, slots=True)
class ChoiceManifest:
    """Closed authoritative mapping from choice ordinals to stable names."""

    names: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.names) is not tuple:
            raise CertificateReject("CHOICE_MANIFEST_NOT_TUPLE")
        if not self.names:
            raise CertificateReject("EMPTY_CHOICE_MANIFEST")
        if len(self.names) > MAX_CHOICE_COUNT:
            raise CertificateReject("TOO_MANY_CHOICES")
        if any(type(name) is not str for name in self.names):
            raise CertificateReject("INVALID_CHOICE_NAME")
        encoded = [name.encode("utf-8") for name in self.names]
        if any(not item for item in encoded):
            raise CertificateReject("EMPTY_CHOICE_NAME")
        if any(len(item) > MAX_CHOICE_NAME_BYTES for item in encoded):
            raise CertificateReject("CHOICE_NAME_TOO_LONG")
        if len(set(encoded)) != len(encoded):
            raise CertificateReject("DUPLICATE_CHOICE_NAME")

    @property
    def root(self) -> Digest:
        return _hash(
            b"choice_manifest_v1",
            _u32(len(self.names)),
            *(name.encode("utf-8") for name in self.names),
        )


@dataclass(frozen=True, slots=True, order=True)
class Subcube:
    """Partial assignment represented by a fixed mask and positive mask.

    A fixed bit with a zero positive bit denotes -1.  A fixed bit with a one
    positive bit denotes +1.  Unfixed bits are free.
    """

    fixed_mask: int
    positive_mask: int

    def __post_init__(self) -> None:
        if type(self.fixed_mask) is not int or type(self.positive_mask) is not int:
            raise CertificateReject("SCOPE_MASK_NOT_EXACT_INTEGER")

    def validate(self, nchoices: int) -> None:
        if type(nchoices) is not int or nchoices <= 0:
            raise CertificateReject("INVALID_CHOICE_COUNT")
        if nchoices > MAX_CHOICE_COUNT:
            raise CertificateReject("TOO_MANY_CHOICES")
        limit = (1 << nchoices) - 1
        if self.fixed_mask < 0 or self.positive_mask < 0:
            raise CertificateReject("NEGATIVE_SCOPE_MASK")
        if self.fixed_mask & ~limit or self.positive_mask & ~limit:
            raise CertificateReject("SCOPE_MASK_OUT_OF_RANGE")
        if self.positive_mask & ~self.fixed_mask:
            raise CertificateReject("POSITIVE_BIT_NOT_FIXED")

    def extends(self, parent: Subcube) -> bool:
        if type(parent) is not Subcube:
            raise CertificateReject("INVALID_PARENT_SCOPE")
        return (
            self.fixed_mask & parent.fixed_mask == parent.fixed_mask
            and (self.positive_mask ^ parent.positive_mask) & parent.fixed_mask == 0
        )

    def with_choice(self, ordinal: int, positive: bool) -> Subcube:
        if type(ordinal) is not int or ordinal < 0 or ordinal >= MAX_CHOICE_COUNT:
            raise CertificateReject("INVALID_CHOICE_ORDINAL")
        if type(positive) is not bool:
            raise CertificateReject("INVALID_CHOICE_SIGN")
        bit = 1 << ordinal
        if self.fixed_mask & bit:
            raise CertificateReject("CHOICE_REUSED_ON_PATH")
        fixed = self.fixed_mask | bit
        values = self.positive_mask | bit if positive else self.positive_mask
        return Subcube(fixed, values)

    def matches_assignment(self, assignment_mask: int) -> bool:
        if type(assignment_mask) is not int or assignment_mask < 0:
            raise CertificateReject("INVALID_ASSIGNMENT_MASK")
        return (assignment_mask ^ self.positive_mask) & self.fixed_mask == 0

    def semantic_bytes(self, nchoices: int) -> bytes:
        self.validate(nchoices)
        return (
            _u32(nchoices)
            + _frame(_mask_bytes(self.fixed_mask, nchoices))
            + _frame(_mask_bytes(self.positive_mask, nchoices))
        )

    def semantic_root(self, manifest_root: Digest, nchoices: int) -> Digest:
        _require_digest(manifest_root, "BAD_MANIFEST_ROOT_LENGTH")
        return _hash(
            b"choice_subcube_scope_v1",
            manifest_root,
            self.semantic_bytes(nchoices),
        )


@dataclass(frozen=True, slots=True)
class ShardReceipt:
    """Research receipt metadata for one exact subcube.

    ``proof_commitment`` is opaque here.  Cryptographic receipt soundness and
    the assertion that it proves every assignment in ``scope`` are external
    premises, not established by this coverage checker.
    """

    subject_root: Digest
    scope: Subcube
    proof_commitment: Digest

    def __post_init__(self) -> None:
        _require_digest(self.subject_root, "BAD_RECEIPT_DIGEST_LENGTH")
        _require_digest(self.proof_commitment, "BAD_RECEIPT_DIGEST_LENGTH")
        if type(self.scope) is not Subcube:
            raise CertificateReject("INVALID_RECEIPT_SCOPE")

    def validate(self, manifest: ChoiceManifest, expected_subject_root: Digest) -> None:
        if type(self) is not ShardReceipt:
            raise CertificateReject("INVALID_SHARD_RECEIPT")
        if type(manifest) is not ChoiceManifest:
            raise CertificateReject("INVALID_CHOICE_MANIFEST")
        _require_digest(expected_subject_root, "BAD_SUBJECT_ROOT_LENGTH")
        if self.subject_root != expected_subject_root:
            raise CertificateReject("FOREIGN_RECEIPT_SUBJECT")
        self.scope.validate(len(manifest.names))

    def root(self, manifest: ChoiceManifest) -> Digest:
        self.validate(manifest, self.subject_root)
        return self.root_from_manifest(manifest.root, len(manifest.names))

    def root_from_manifest(
        self,
        manifest_root: Digest,
        nchoices: int,
    ) -> Digest:
        _require_digest(manifest_root, "BAD_MANIFEST_ROOT_LENGTH")
        self.scope.validate(nchoices)
        return _hash(
            b"choice_fiber_shard_receipt_v1",
            self.subject_root,
            self.scope.semantic_root(manifest_root, nchoices),
            self.proof_commitment,
        )


@dataclass(frozen=True, slots=True)
class Leaf:
    receipt_root: Digest

    def __post_init__(self) -> None:
        _require_digest(self.receipt_root, "BAD_LEAF_RECEIPT_ROOT_LENGTH")


@dataclass(frozen=True, slots=True)
class Split:
    choice_ordinal: int
    negative: Tree
    positive: Tree

    def __post_init__(self) -> None:
        if (
            type(self.choice_ordinal) is not int
            or self.choice_ordinal < 0
            or self.choice_ordinal >= MAX_CHOICE_COUNT
        ):
            raise CertificateReject("INVALID_SPLIT_ORDINAL")
        if type(self.negative) not in (Leaf, Split) or type(self.positive) not in (
            Leaf,
            Split,
        ):
            raise CertificateReject("UNKNOWN_TREE_NODE")


Tree: TypeAlias = Leaf | Split


@dataclass(frozen=True, slots=True)
class CoverageCertificate:
    manifest_root: Digest
    subject_root: Digest
    tree: Tree

    def __post_init__(self) -> None:
        _require_digest(self.manifest_root, "BAD_MANIFEST_ROOT_LENGTH")
        _require_digest(self.subject_root, "BAD_SUBJECT_ROOT_LENGTH")
        _validate_tree_resource_profile(self.tree)

    def encoded(self) -> bytes:
        return (
            _frame(b"choice_fiber_partition_tree_v1")
            + _frame(self.manifest_root)
            + _frame(self.subject_root)
            + _encode_tree(self.tree)
        )

    @property
    def root(self) -> Digest:
        return hashlib.sha256(self.encoded()).digest()


@dataclass(frozen=True, slots=True)
class VerificationStats:
    nodes: int
    splits: int
    leaves: int
    scope_checks: int
    canonical_split_checks: int
    receipt_hashes: int


@dataclass(frozen=True, slots=True)
class BruteResult:
    accepted: bool
    code: str
    first_assignment_mask: int | None
    matching_receipt_roots: tuple[str, ...]
    assignments_checked: int
    membership_probes: int


@dataclass(frozen=True, slots=True)
class VolumeSeparationStats:
    leaves: int
    unordered_pairs_checked: int
    total_covered_assignments: int


def _encode_tree(tree: Tree) -> bytes:
    if type(tree) is Leaf:
        if len(tree.receipt_root) != 32:
            raise CertificateReject("BAD_LEAF_RECEIPT_ROOT_LENGTH")
        return b"\x00" + tree.receipt_root
    if type(tree) is Split:
        return (
            b"\x01"
            + _u32(tree.choice_ordinal)
            + _encode_tree(tree.negative)
            + _encode_tree(tree.positive)
        )
    raise CertificateReject("UNKNOWN_TREE_NODE")


def _validate_tree_resource_profile(tree: Tree) -> None:
    if type(tree) not in (Leaf, Split):
        raise CertificateReject("UNKNOWN_TREE_NODE")
    pending: list[tuple[Tree, int]] = [(tree, 0)]
    nodes = 0
    leaves = 0
    while pending:
        node, depth = pending.pop()
        nodes += 1
        if nodes > MAX_TREE_NODES:
            raise CertificateReject("TREE_NODE_CAPACITY_EXCEEDED")
        if depth > MAX_CHOICE_COUNT:
            raise CertificateReject("TREE_DEPTH_CAPACITY_EXCEEDED")
        if type(node) is Leaf:
            leaves += 1
            if leaves > MAX_RECEIPTS:
                raise CertificateReject("RECEIPT_CAPACITY_EXCEEDED")
            continue
        if type(node) is not Split:
            raise CertificateReject("UNKNOWN_TREE_NODE")
        pending.append((node.positive, depth + 1))
        pending.append((node.negative, depth + 1))


def _bounded_receipts(receipts: Iterable[ShardReceipt]) -> tuple[ShardReceipt, ...]:
    retained: list[ShardReceipt] = []
    for receipt in receipts:
        if len(retained) == MAX_RECEIPTS:
            raise CertificateReject("RECEIPT_CAPACITY_EXCEEDED")
        if type(receipt) is not ShardReceipt:
            raise CertificateReject("INVALID_SHARD_RECEIPT")
        retained.append(receipt)
    return tuple(retained)


def build_canonical_certificate(
    manifest: ChoiceManifest,
    subject_root: Digest,
    receipts: Iterable[ShardReceipt],
) -> CoverageCertificate:
    """Build the unique canonical split tree for a recursively split cover."""

    if type(manifest) is not ChoiceManifest:
        raise CertificateReject("INVALID_CHOICE_MANIFEST")
    _require_digest(subject_root, "BAD_SUBJECT_ROOT_LENGTH")
    receipt_tuple = _bounded_receipts(receipts)
    if not receipt_tuple:
        raise CertificateReject("EMPTY_RECEIPT_SET")
    for receipt in receipt_tuple:
        receipt.validate(manifest, subject_root)
    manifest_root = manifest.root
    nchoices = len(manifest.names)
    roots = tuple(receipt.root_from_manifest(manifest_root, nchoices) for receipt in receipt_tuple)
    if len(set(roots)) != len(roots):
        raise CertificateReject("DUPLICATE_RECEIPT_ROOT")
    scopes = tuple(receipt.scope for receipt in receipt_tuple)
    if len(set(scopes)) != len(scopes):
        raise CertificateReject("DUPLICATE_SUBCUBE_SCOPE")

    def rec(region: Subcube, indexes: tuple[int, ...]) -> Tree:
        exact = tuple(index for index in indexes if scopes[index] == region)
        if exact:
            if len(exact) != 1 or len(indexes) != 1:
                raise CertificateReject("REGION_LEAF_OVERLAPS_OTHER_SCOPE")
            return Leaf(roots[exact[0]])
        if any(not scopes[index].extends(region) for index in indexes):
            raise CertificateReject("SCOPE_ESCAPES_REGION")

        free_limit = ((1 << len(manifest.names)) - 1) & ~region.fixed_mask
        universal_fixed = free_limit
        for index in indexes:
            universal_fixed &= scopes[index].fixed_mask
        if universal_fixed == 0:
            raise CertificateReject("NON_RECURSIVE_SUBCUBE_PARTITION")
        split_bit = universal_fixed & -universal_fixed
        ordinal = split_bit.bit_length() - 1
        negative = tuple(index for index in indexes if not scopes[index].positive_mask & split_bit)
        positive = tuple(index for index in indexes if scopes[index].positive_mask & split_bit)
        if not negative or not positive:
            raise CertificateReject("MISSING_SPLIT_BRANCH")
        return Split(
            ordinal,
            rec(region.with_choice(ordinal, False), negative),
            rec(region.with_choice(ordinal, True), positive),
        )

    tree = rec(Subcube(0, 0), tuple(range(len(receipt_tuple))))
    return CoverageCertificate(manifest.root, subject_root, tree)


def verify_certificate(
    manifest: ChoiceManifest,
    expected_subject_root: Digest,
    certificate: CoverageCertificate,
    receipts: Iterable[ShardReceipt],
) -> VerificationStats:
    """Verify exact recursive coverage, receipt binding, and canonical shape."""

    if type(manifest) is not ChoiceManifest:
        raise CertificateReject("INVALID_CHOICE_MANIFEST")
    _require_digest(expected_subject_root, "BAD_SUBJECT_ROOT_LENGTH")
    if type(certificate) is not CoverageCertificate:
        raise CertificateReject("INVALID_COVERAGE_CERTIFICATE")
    _validate_tree_resource_profile(certificate.tree)
    if certificate.manifest_root != manifest.root:
        raise CertificateReject("MANIFEST_ROOT_MISMATCH")
    if certificate.subject_root != expected_subject_root:
        raise CertificateReject("CERTIFICATE_SUBJECT_MISMATCH")
    receipt_tuple = _bounded_receipts(receipts)
    by_root: dict[Digest, ShardReceipt] = {}
    manifest_root = manifest.root
    nchoices = len(manifest.names)
    for receipt in receipt_tuple:
        receipt.validate(manifest, expected_subject_root)
        root = receipt.root_from_manifest(manifest_root, nchoices)
        if root in by_root:
            raise CertificateReject("DUPLICATE_RECEIPT_ROOT")
        by_root[root] = receipt

    seen_roots: set[Digest] = set()

    def rec(tree: Tree, region: Subcube) -> tuple[int, int, int, int, int, int, int]:
        # Return counts plus the intersection of fixed masks across descendant
        # semantic leaf scopes, needed to enforce the canonical split choice.
        if type(tree) is Leaf:
            receipt = by_root.get(tree.receipt_root)
            if receipt is None:
                raise CertificateReject("UNKNOWN_LEAF_RECEIPT")
            if tree.receipt_root in seen_roots:
                raise CertificateReject("REUSED_LEAF_RECEIPT")
            seen_roots.add(tree.receipt_root)
            if receipt.scope != region:
                raise CertificateReject("LEAF_SCOPE_PATH_MISMATCH")
            return (1, 0, 1, 1, 0, 1, receipt.scope.fixed_mask)
        if type(tree) is not Split:
            raise CertificateReject("UNKNOWN_TREE_NODE")
        if tree.choice_ordinal < 0 or tree.choice_ordinal >= len(manifest.names):
            raise CertificateReject("SPLIT_ORDINAL_OUT_OF_RANGE")
        bit = 1 << tree.choice_ordinal
        if region.fixed_mask & bit:
            raise CertificateReject("CHOICE_REUSED_ON_PATH")
        neg = rec(tree.negative, region.with_choice(tree.choice_ordinal, False))
        pos = rec(tree.positive, region.with_choice(tree.choice_ordinal, True))
        universal_descendant = neg[6] & pos[6] & ~region.fixed_mask
        if universal_descendant == 0:
            raise CertificateReject("NO_CANONICAL_SPLIT_AVAILABLE")
        canonical_bit = universal_descendant & -universal_descendant
        if bit != canonical_bit:
            raise CertificateReject("NONCANONICAL_SPLIT_CHOICE")
        return (
            1 + neg[0] + pos[0],
            1 + neg[1] + pos[1],
            neg[2] + pos[2],
            neg[3] + pos[3],
            1 + neg[4] + pos[4],
            neg[5] + pos[5],
            neg[6] & pos[6],
        )

    nodes, splits, leaves, scope_checks, canonical_checks, hashes, _ = rec(
        certificate.tree, Subcube(0, 0)
    )
    if seen_roots != set(by_root):
        raise CertificateReject("SURPLUS_UNCONSUMED_RECEIPT")
    return VerificationStats(nodes, splits, leaves, scope_checks, canonical_checks, hashes)


def brute_force_partition(
    manifest: ChoiceManifest,
    expected_subject_root: Digest,
    receipts: Iterable[ShardReceipt],
) -> BruteResult:
    """Independent exhaustive exact-cover oracle over every full assignment."""

    if type(manifest) is not ChoiceManifest:
        raise CertificateReject("INVALID_CHOICE_MANIFEST")
    _require_digest(expected_subject_root, "BAD_SUBJECT_ROOT_LENGTH")
    receipt_tuple = _bounded_receipts(receipts)
    if len(manifest.names) > MAX_BRUTE_CHOICES:
        raise CertificateReject("BRUTE_CHOICE_CAPACITY_EXCEEDED")
    assignment_count = 1 << len(manifest.names)
    if assignment_count * len(receipt_tuple) > MAX_BRUTE_MEMBERSHIP_PROBES:
        raise CertificateReject("BRUTE_MEMBERSHIP_CAPACITY_EXCEEDED")
    manifest_root = manifest.root
    nchoices = len(manifest.names)
    roots: list[Digest] = []
    for receipt in receipt_tuple:
        receipt.validate(manifest, expected_subject_root)
        roots.append(receipt.root_from_manifest(manifest_root, nchoices))
    if len(set(roots)) != len(roots):
        return BruteResult(False, "DUPLICATE_RECEIPT_ROOT", None, (), 0, 0)
    probes = 0
    checked = 0
    for assignment in range(assignment_count):
        matching: list[str] = []
        for root, receipt in zip(roots, receipt_tuple, strict=True):
            probes += 1
            if receipt.scope.matches_assignment(assignment):
                matching.append(root.hex())
        checked += 1
        if not matching:
            return BruteResult(False, "COVERAGE_OMISSION", assignment, (), checked, probes)
        if len(matching) > 1:
            return BruteResult(
                False,
                "COVERAGE_OVERLAP",
                assignment,
                tuple(matching),
                checked,
                probes,
            )
    return BruteResult(True, "EXACT_PARTITION", None, (), checked, probes)


def verify_volume_separation_partition(
    manifest: ChoiceManifest,
    expected_subject_root: Digest,
    receipts: Iterable[ShardReceipt],
) -> VolumeSeparationStats:
    """Verify an arbitrary exact subcube partition without enumeration.

    For valid subcubes C_i of a finite Boolean cube U:

    * pairwise separation proves C_i are disjoint;
    * ``sum_i |C_i| = |U|`` then proves their union is all of U.

    This checker accepts more partitions than the recursive tree checker, but
    requires one comparison per unordered receipt pair.
    """

    if type(manifest) is not ChoiceManifest:
        raise CertificateReject("INVALID_CHOICE_MANIFEST")
    _require_digest(expected_subject_root, "BAD_SUBJECT_ROOT_LENGTH")
    receipt_tuple = _bounded_receipts(receipts)
    if not receipt_tuple:
        raise CertificateReject("EMPTY_RECEIPT_SET")
    roots: list[Digest] = []
    scopes: list[Subcube] = []
    nchoices = len(manifest.names)
    manifest_root = manifest.root
    for receipt in receipt_tuple:
        receipt.validate(manifest, expected_subject_root)
        roots.append(receipt.root_from_manifest(manifest_root, nchoices))
        scopes.append(receipt.scope)
    if len(set(roots)) != len(roots):
        raise CertificateReject("DUPLICATE_RECEIPT_ROOT")
    if len(set(scopes)) != len(scopes):
        raise CertificateReject("DUPLICATE_SUBCUBE_SCOPE")

    pairs = 0
    for left_index, left in enumerate(scopes):
        for right in scopes[left_index + 1 :]:
            pairs += 1
            common_fixed = left.fixed_mask & right.fixed_mask
            opposite = (left.positive_mask ^ right.positive_mask) & common_fixed
            if opposite == 0:
                raise CertificateReject("PAIRWISE_SUBCUBE_OVERLAP")

    covered = sum(1 << (nchoices - scope.fixed_mask.bit_count()) for scope in scopes)
    universe = 1 << nchoices
    if covered != universe:
        if covered < universe:
            raise CertificateReject("SUBCUBE_VOLUME_OMISSION")
        raise CertificateReject("SUBCUBE_VOLUME_EXCESS")
    return VolumeSeparationStats(len(scopes), pairs, covered)


def explicit_scope_manifest_bytes(
    manifest: ChoiceManifest,
    subject_root: Digest,
    receipts: Iterable[ShardReceipt],
) -> bytes:
    """Canonical explicit-list baseline used only for size comparison."""

    if type(manifest) is not ChoiceManifest:
        raise CertificateReject("INVALID_CHOICE_MANIFEST")
    _require_digest(subject_root, "BAD_SUBJECT_ROOT_LENGTH")
    manifest_root = manifest.root
    nchoices = len(manifest.names)
    ordered = sorted(
        _bounded_receipts(receipts),
        key=lambda receipt: (
            receipt.scope.fixed_mask,
            receipt.scope.positive_mask,
            receipt.root_from_manifest(manifest_root, nchoices),
        ),
    )
    return (
        _frame(b"explicit_choice_subcube_manifest_v1")
        + _frame(manifest_root)
        + _frame(subject_root)
        + _u32(len(ordered))
        + b"".join(
            _frame(receipt.scope.semantic_bytes(nchoices))
            + receipt.root_from_manifest(manifest_root, nchoices)
            for receipt in ordered
        )
    )


def deterministic_digest(label: str) -> Digest:
    if type(label) is not str:
        raise CertificateReject("INVALID_DIGEST_LABEL")
    return hashlib.sha256(label.encode("utf-8")).digest()


def make_receipt(
    manifest: ChoiceManifest,
    subject_root: Digest,
    scope: Subcube,
    label: str,
) -> ShardReceipt:
    if type(manifest) is not ChoiceManifest:
        raise CertificateReject("INVALID_CHOICE_MANIFEST")
    _require_digest(subject_root, "BAD_SUBJECT_ROOT_LENGTH")
    if type(scope) is not Subcube:
        raise CertificateReject("INVALID_RECEIPT_SCOPE")
    if type(label) is not str or not label:
        raise CertificateReject("INVALID_RECEIPT_LABEL")
    scope.validate(len(manifest.names))
    return ShardReceipt(subject_root, scope, deterministic_digest(label))


def prefix_partition(
    manifest: ChoiceManifest,
    subject_root: Digest,
    fixed_prefix_length: int,
) -> tuple[ShardReceipt, ...]:
    """Partition by every assignment to the first ``k`` choice ordinals."""

    if type(manifest) is not ChoiceManifest:
        raise CertificateReject("INVALID_CHOICE_MANIFEST")
    _require_digest(subject_root, "BAD_SUBJECT_ROOT_LENGTH")
    nchoices = len(manifest.names)
    if (
        type(fixed_prefix_length) is not int
        or fixed_prefix_length < 0
        or fixed_prefix_length > nchoices
    ):
        raise CertificateReject("BAD_PREFIX_LENGTH")
    if 1 << fixed_prefix_length > MAX_RECEIPTS:
        raise CertificateReject("RECEIPT_CAPACITY_EXCEEDED")
    fixed = (1 << fixed_prefix_length) - 1
    return tuple(
        make_receipt(
            manifest,
            subject_root,
            Subcube(fixed, assignment),
            f"prefix:{nchoices}:{fixed_prefix_length}:{assignment}",
        )
        for assignment in range(1 << fixed_prefix_length)
    )


def comb_partition(
    manifest: ChoiceManifest,
    subject_root: Digest,
    depth: int,
) -> tuple[ShardReceipt, ...]:
    """Irregular recursive partition with ``depth + 1`` leaves."""

    if type(manifest) is not ChoiceManifest:
        raise CertificateReject("INVALID_CHOICE_MANIFEST")
    _require_digest(subject_root, "BAD_SUBJECT_ROOT_LENGTH")
    if type(depth) is not int or depth < 0 or depth > len(manifest.names):
        raise CertificateReject("BAD_COMB_DEPTH")
    scopes: list[Subcube] = []
    region = Subcube(0, 0)
    for ordinal in range(depth):
        scopes.append(region.with_choice(ordinal, False))
        region = region.with_choice(ordinal, True)
    scopes.append(region)
    return tuple(
        make_receipt(manifest, subject_root, scope, f"comb:{depth}:{index}")
        for index, scope in enumerate(scopes)
    )

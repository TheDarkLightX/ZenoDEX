"""
Standalone Jellyfish-style sparse Merkle candidate for the multi-lane keystone.

This module is intentionally not wired into ``state_root.py`` or ledger
acceptance. It is live code for the planned keystone data structure: a
deterministic, domain-separated compact sparse tree with membership and
non-membership proofs. A production root claim still needs integration tests
that bind this module to the actual ledger/state-root path.

The proof dataclasses below are in-process transcripts, not a public wire ABI.
Any network/client use still needs canonical proof serialization with unknown
field rejection and versioning.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Iterable, Mapping

from .canonical import domain_sep_bytes, encode_bytes, encode_uvarint

JMT_VERSION = 1
JMT_KEY_BYTES = 32
JMT_KEY_BITS = JMT_KEY_BYTES * 8
JMT_HASH_BYTES = 32

_EMPTY_PREFIX = domain_sep_bytes("jmt_empty", version=JMT_VERSION)
_LEAF_PREFIX = domain_sep_bytes("jmt_leaf", version=JMT_VERSION)
_INTERNAL_PREFIX = domain_sep_bytes("jmt_internal", version=JMT_VERSION)


def _sha256(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()


def empty_hash(depth: int) -> bytes:
    if not isinstance(depth, int) or isinstance(depth, bool) or depth < 0 or depth > JMT_KEY_BITS:
        raise ValueError("JMT empty depth must be in [0, 256]")
    return _sha256(_EMPTY_PREFIX + encode_uvarint(depth))


EMPTY_ROOT_BYTES = empty_hash(0)
EMPTY_ROOT_HEX = "0x" + EMPTY_ROOT_BYTES.hex()


def _validate_key(key: bytes) -> bytes:
    if not isinstance(key, bytes):
        raise TypeError("JMT key must be bytes")
    key_bytes = bytes(key)
    if len(key_bytes) != JMT_KEY_BYTES:
        raise ValueError(f"JMT key must be exactly {JMT_KEY_BYTES} bytes")
    return key_bytes


def _validate_value(value: bytes) -> bytes:
    if not isinstance(value, bytes):
        raise TypeError("JMT value must be bytes")
    return bytes(value)


def _validate_hash(value: bytes, *, name: str) -> bytes:
    if not isinstance(value, bytes):
        raise TypeError(f"{name} must be bytes")
    value_bytes = bytes(value)
    if len(value_bytes) != JMT_HASH_BYTES:
        raise ValueError(f"{name} must be exactly {JMT_HASH_BYTES} bytes")
    return value_bytes


def _root_bytes(root: str | bytes) -> bytes:
    if isinstance(root, str):
        if not root.startswith("0x") or len(root) != 2 + JMT_HASH_BYTES * 2:
            raise ValueError("JMT root must be a 0x-prefixed 32-byte hex string")
        try:
            return bytes.fromhex(root[2:])
        except ValueError as exc:
            raise ValueError("JMT root must be valid hex") from exc
    return _validate_hash(root, name="JMT root")


def leaf_hash(key: bytes, value: bytes) -> bytes:
    key_bytes = _validate_key(key)
    value_bytes = _validate_value(value)
    return _sha256(_LEAF_PREFIX + key_bytes + encode_bytes(value_bytes))


def internal_hash(left: bytes, right: bytes) -> bytes:
    left_bytes = _validate_hash(left, name="left child hash")
    right_bytes = _validate_hash(right, name="right child hash")
    return _sha256(_INTERNAL_PREFIX + left_bytes + right_bytes)


@dataclass(frozen=True)
class JmtSibling:
    """Sibling hash on a proof path, stored from root to witness.

    ``sibling_on_left`` tells the verifier how to fold from the witness back up:
    true means ``parent = H(sibling || current)``, false means
    ``parent = H(current || sibling)``.
    """

    sibling_hash: bytes
    sibling_on_left: bool

    def __post_init__(self) -> None:
        object.__setattr__(self, "sibling_hash", _validate_hash(self.sibling_hash, name="sibling hash"))
        if not isinstance(self.sibling_on_left, bool):
            raise TypeError("sibling_on_left must be bool")


def _validate_siblings(siblings: Iterable[JmtSibling]) -> tuple[JmtSibling, ...]:
    out = tuple(siblings)
    if len(out) > JMT_KEY_BITS:
        raise ValueError("JMT proof path exceeds key depth")
    for sibling in out:
        if not isinstance(sibling, JmtSibling):
            raise TypeError("JMT proof siblings must be JmtSibling values")
    return out


@dataclass(frozen=True)
class JmtMembershipProof:
    key: bytes
    value: bytes
    siblings: tuple[JmtSibling, ...]

    def __post_init__(self) -> None:
        object.__setattr__(self, "key", _validate_key(self.key))
        object.__setattr__(self, "value", _validate_value(self.value))
        object.__setattr__(self, "siblings", _validate_siblings(self.siblings))


@dataclass(frozen=True)
class JmtAbsenceProof:
    query_key: bytes
    witness_key: bytes | None
    witness_value: bytes | None
    siblings: tuple[JmtSibling, ...]

    def __post_init__(self) -> None:
        object.__setattr__(self, "query_key", _validate_key(self.query_key))
        if self.witness_key is None:
            if self.witness_value is not None:
                raise ValueError("witness_value must be None for an empty absence witness")
        else:
            object.__setattr__(self, "witness_key", _validate_key(self.witness_key))
            if self.witness_value is None:
                raise ValueError("witness_value is required when witness_key is present")
            object.__setattr__(self, "witness_value", _validate_value(self.witness_value))
        object.__setattr__(self, "siblings", _validate_siblings(self.siblings))


@dataclass(frozen=True)
class _EmptyNode:
    root: bytes


@dataclass(frozen=True)
class _LeafNode:
    key: bytes
    value: bytes
    root: bytes


@dataclass(frozen=True)
class _InternalNode:
    left: _Node
    right: _Node
    root: bytes


_Node = _EmptyNode | _LeafNode | _InternalNode


def _normalize_entries(
    entries: Mapping[bytes, bytes] | Iterable[tuple[bytes, bytes]],
) -> tuple[tuple[bytes, bytes], ...]:
    raw_items = entries.items() if isinstance(entries, Mapping) else entries
    normalized: list[tuple[bytes, bytes]] = []
    seen: set[bytes] = set()
    for key, value in raw_items:
        key_bytes = _validate_key(key)
        if key_bytes in seen:
            raise ValueError("duplicate JMT key after canonicalization")
        seen.add(key_bytes)
        normalized.append((key_bytes, _validate_value(value)))
    normalized.sort(key=lambda item: item[0])
    return tuple(normalized)


def _bit(key: bytes, depth: int) -> int:
    if depth < 0 or depth >= JMT_KEY_BITS:
        raise ValueError("JMT bit depth out of range")
    byte_index, bit_index = divmod(depth, 8)
    return (key[byte_index] >> (7 - bit_index)) & 1


def _build(entries: tuple[tuple[bytes, bytes], ...], depth: int) -> _Node:
    if not entries:
        return _EmptyNode(root=empty_hash(depth))
    if len(entries) == 1:
        key, value = entries[0]
        return _LeafNode(key=key, value=value, root=leaf_hash(key, value))
    if depth >= JMT_KEY_BITS:
        # With fixed 32-byte keys this should only be reachable if duplicate
        # canonical keys bypassed normalization.
        raise ValueError("JMT key path exhausted before leaves separated")

    left_entries = tuple(item for item in entries if _bit(item[0], depth) == 0)
    right_entries = tuple(item for item in entries if _bit(item[0], depth) == 1)
    left = _build(left_entries, depth + 1)
    right = _build(right_entries, depth + 1)
    return _InternalNode(left=left, right=right, root=internal_hash(left.root, right.root))


def _fold_root(witness_root: bytes, siblings: tuple[JmtSibling, ...]) -> bytes:
    root = witness_root
    for sibling in reversed(siblings):
        if sibling.sibling_on_left:
            root = internal_hash(sibling.sibling_hash, root)
        else:
            root = internal_hash(root, sibling.sibling_hash)
    return root


def _siblings_follow_key(siblings: tuple[JmtSibling, ...], key: bytes) -> bool:
    if len(siblings) > JMT_KEY_BITS:
        return False
    for depth, sibling in enumerate(siblings):
        if sibling.sibling_on_left != bool(_bit(key, depth)):
            return False
    return True


def _same_prefix(left: bytes, right: bytes, depth: int) -> bool:
    if depth < 0 or depth > JMT_KEY_BITS:
        return False
    return all(_bit(left, i) == _bit(right, i) for i in range(depth))


def compute_jmt_root(
    entries: Mapping[bytes, bytes] | Iterable[tuple[bytes, bytes]],
) -> str:
    """Return the 0x-prefixed root of the standalone compact sparse tree."""

    return "0x" + _build(_normalize_entries(entries), 0).root.hex()


def prove_jmt_membership(
    entries: Mapping[bytes, bytes] | Iterable[tuple[bytes, bytes]],
    key: bytes,
) -> JmtMembershipProof:
    key_bytes = _validate_key(key)
    root = _build(_normalize_entries(entries), 0)

    def go(node: _Node, depth: int, siblings: tuple[JmtSibling, ...]) -> JmtMembershipProof:
        if isinstance(node, _EmptyNode):
            raise KeyError("key is absent")
        if isinstance(node, _LeafNode):
            if node.key != key_bytes:
                raise KeyError("key is absent")
            return JmtMembershipProof(key=node.key, value=node.value, siblings=siblings)

        branch = _bit(key_bytes, depth)
        if branch == 0:
            return go(
                node.left,
                depth + 1,
                (*siblings, JmtSibling(sibling_hash=node.right.root, sibling_on_left=False)),
            )
        return go(
            node.right,
            depth + 1,
            (*siblings, JmtSibling(sibling_hash=node.left.root, sibling_on_left=True)),
        )

    return go(root, 0, ())


def verify_jmt_membership(
    root: str | bytes,
    key: bytes,
    value: bytes,
    proof: JmtMembershipProof,
) -> bool:
    try:
        root_bytes = _root_bytes(root)
        key_bytes = _validate_key(key)
        value_bytes = _validate_value(value)
    except (TypeError, ValueError):
        return False
    if not isinstance(proof, JmtMembershipProof):
        return False
    if proof.key != key_bytes or proof.value != value_bytes:
        return False
    if not _siblings_follow_key(proof.siblings, key_bytes):
        return False
    return _fold_root(leaf_hash(proof.key, proof.value), proof.siblings) == root_bytes


def prove_jmt_absence(
    entries: Mapping[bytes, bytes] | Iterable[tuple[bytes, bytes]],
    query_key: bytes,
) -> JmtAbsenceProof:
    query_key_bytes = _validate_key(query_key)
    root = _build(_normalize_entries(entries), 0)

    def go(node: _Node, depth: int, siblings: tuple[JmtSibling, ...]) -> JmtAbsenceProof:
        if isinstance(node, _EmptyNode):
            return JmtAbsenceProof(
                query_key=query_key_bytes,
                witness_key=None,
                witness_value=None,
                siblings=siblings,
            )
        if isinstance(node, _LeafNode):
            if node.key == query_key_bytes:
                raise KeyError("key is present")
            return JmtAbsenceProof(
                query_key=query_key_bytes,
                witness_key=node.key,
                witness_value=node.value,
                siblings=siblings,
            )

        branch = _bit(query_key_bytes, depth)
        if branch == 0:
            return go(
                node.left,
                depth + 1,
                (*siblings, JmtSibling(sibling_hash=node.right.root, sibling_on_left=False)),
            )
        return go(
            node.right,
            depth + 1,
            (*siblings, JmtSibling(sibling_hash=node.left.root, sibling_on_left=True)),
        )

    return go(root, 0, ())


def verify_jmt_absence(
    root: str | bytes,
    query_key: bytes,
    proof: JmtAbsenceProof,
) -> bool:
    try:
        root_bytes = _root_bytes(root)
        query_key_bytes = _validate_key(query_key)
    except (TypeError, ValueError):
        return False
    if not isinstance(proof, JmtAbsenceProof):
        return False
    if proof.query_key != query_key_bytes:
        return False
    if not _siblings_follow_key(proof.siblings, query_key_bytes):
        return False

    if proof.witness_key is None:
        witness_root = empty_hash(len(proof.siblings))
    else:
        if proof.witness_key == query_key_bytes or proof.witness_value is None:
            return False
        if not _same_prefix(proof.witness_key, query_key_bytes, len(proof.siblings)):
            return False
        witness_root = leaf_hash(proof.witness_key, proof.witness_value)
    return _fold_root(witness_root, proof.siblings) == root_bytes

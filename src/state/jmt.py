"""
Standalone Jellyfish-style sparse Merkle candidate for the multi-lane keystone.

This module is intentionally not wired into ``state_root.py`` or ledger
acceptance. It is live code for the planned keystone data structure: a
deterministic, domain-separated compact sparse tree with membership and
non-membership proofs. A production root claim still needs integration tests
that bind this module to the actual ledger/state-root path.

The proof dataclasses below are in-process transcripts. The
``encode_jmt_*_proof`` / ``decode_jmt_*_proof`` functions define the versioned
canonical JSON proof payload for this candidate module; any network/client use
still needs integration-level replay tests against its transport boundary.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Iterable, Mapping

from .canonical import canonical_json_bytes, domain_sep_bytes, encode_bytes, encode_uvarint

JMT_VERSION = 1
JMT_KEY_BYTES = 32
JMT_KEY_BITS = JMT_KEY_BYTES * 8
JMT_HASH_BYTES = 32

_EMPTY_PREFIX = domain_sep_bytes("jmt_empty", version=JMT_VERSION)
_LEAF_PREFIX = domain_sep_bytes("jmt_leaf", version=JMT_VERSION)
_INTERNAL_PREFIX = domain_sep_bytes("jmt_internal", version=JMT_VERSION)


def _sha256(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()


def _snapshot_bytes(value: object, *, name: str) -> bytes:
    if not isinstance(value, bytes):
        raise TypeError(f"{name} must be bytes")
    # ``bytes(value)`` dispatches a bytes-subclass ``__bytes__`` hook. Read the
    # actual immutable buffer so hostile protocol methods cannot substitute the
    # key, value, hash, or proof payload being authenticated.
    return value if type(value) is bytes else memoryview(value).tobytes()


def empty_hash(depth: int) -> bytes:
    if not isinstance(depth, int) or isinstance(depth, bool) or depth < 0 or depth > JMT_KEY_BITS:
        raise ValueError("JMT empty depth must be in [0, 256]")
    return _sha256(_EMPTY_PREFIX + encode_uvarint(depth))


EMPTY_ROOT_BYTES = empty_hash(0)
EMPTY_ROOT_HEX = "0x" + EMPTY_ROOT_BYTES.hex()


def _validate_key(key: bytes) -> bytes:
    key_bytes = _snapshot_bytes(key, name="JMT key")
    if len(key_bytes) != JMT_KEY_BYTES:
        raise ValueError(f"JMT key must be exactly {JMT_KEY_BYTES} bytes")
    return key_bytes


def _validate_value(value: bytes) -> bytes:
    return _snapshot_bytes(value, name="JMT value")


def _validate_hash(value: bytes, *, name: str) -> bytes:
    value_bytes = _snapshot_bytes(value, name=name)
    if len(value_bytes) != JMT_HASH_BYTES:
        raise ValueError(f"{name} must be exactly {JMT_HASH_BYTES} bytes")
    return value_bytes


def _root_bytes(root: str | bytes) -> bytes:
    if type(root) is str:
        if not root.startswith("0x") or len(root) != 2 + JMT_HASH_BYTES * 2:
            raise ValueError("JMT root must be a 0x-prefixed 32-byte hex string")
        try:
            return bytes.fromhex(root[2:])
        except ValueError as exc:
            raise ValueError("JMT root must be valid hex") from exc
    if isinstance(root, str):
        raise TypeError("JMT root text must be exact str")
    return _validate_hash(root, name="JMT root")


def _to_hex(value: bytes) -> str:
    return "0x" + bytes(value).hex()


def _from_hex(value: object, *, nbytes: int | None, name: str) -> bytes:
    if type(value) is not str:
        raise TypeError(f"{name} must be a canonical hex string")
    if not value.startswith("0x"):
        raise ValueError(f"{name} must be a canonical hex string")
    body = value[2:]
    if body != body.lower():
        raise ValueError(f"{name} must be canonical lowercase hex")
    if len(body) % 2 != 0:
        raise ValueError(f"{name} must have an even number of hex digits")
    if nbytes is not None and len(body) != nbytes * 2:
        raise ValueError(f"{name} must be canonical {nbytes}-byte hex")
    try:
        out = bytes.fromhex(body)
    except ValueError as exc:
        raise ValueError(f"{name} must be valid hex") from exc
    if value != _to_hex(out):
        raise ValueError(f"{name} must be canonical lowercase hex")
    return out


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


def _validate_siblings(siblings: object) -> tuple[JmtSibling, ...]:
    if type(siblings) is not tuple:
        raise TypeError("JMT proof siblings must be an exact tuple")
    if len(siblings) > JMT_KEY_BITS:
        raise ValueError("JMT proof path exceeds key depth")
    out: list[JmtSibling] = []
    for sibling in siblings:
        if type(sibling) is not JmtSibling:
            raise TypeError("JMT proof siblings must be JmtSibling values")
        try:
            sibling_hash = sibling.sibling_hash
            sibling_on_left = sibling.sibling_on_left
        except AttributeError as exc:
            raise TypeError("JMT proof sibling fields are missing") from exc
        out.append(
            JmtSibling(
                sibling_hash=sibling_hash,
                sibling_on_left=sibling_on_left,
            )
        )
    return tuple(out)


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


def _snapshot_membership_proof(proof: object) -> JmtMembershipProof:
    if type(proof) is not JmtMembershipProof:
        raise TypeError("proof must be a JmtMembershipProof")
    try:
        key = proof.key
        value = proof.value
        siblings = proof.siblings
    except AttributeError as exc:
        raise TypeError("JMT membership proof fields are missing") from exc
    return JmtMembershipProof(key=key, value=value, siblings=siblings)


def _snapshot_absence_proof(proof: object) -> JmtAbsenceProof:
    if type(proof) is not JmtAbsenceProof:
        raise TypeError("proof must be a JmtAbsenceProof")
    try:
        query_key = proof.query_key
        witness_key = proof.witness_key
        witness_value = proof.witness_value
        siblings = proof.siblings
    except AttributeError as exc:
        raise TypeError("JMT absence proof fields are missing") from exc
    return JmtAbsenceProof(
        query_key=query_key,
        witness_key=witness_key,
        witness_value=witness_value,
        siblings=siblings,
    )


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


def _require_object(value: object, *, name: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise TypeError(f"{name} must be an object")
    if any(not isinstance(key, str) for key in value):
        raise TypeError(f"{name} keys must be strings")
    return value


def _require_fields(value: Mapping[str, Any], expected: set[str], *, name: str) -> None:
    found = set(value)
    if found != expected:
        raise ValueError(f"unexpected {name} fields")


def _require_version(value: object) -> None:
    if not isinstance(value, int) or isinstance(value, bool) or value != JMT_VERSION:
        raise ValueError("JMT proof version mismatch")


def _sibling_to_wire(sibling: JmtSibling) -> dict[str, object]:
    return {
        "sibling_hash": _to_hex(sibling.sibling_hash),
        "sibling_on_left": sibling.sibling_on_left,
    }


def _sibling_from_wire(value: object) -> JmtSibling:
    obj = _require_object(value, name="JMT sibling")
    _require_fields(obj, {"sibling_hash", "sibling_on_left"}, name="JMT sibling")
    if not isinstance(obj["sibling_on_left"], bool):
        raise TypeError("JMT sibling_on_left must be bool")
    return JmtSibling(
        sibling_hash=_from_hex(obj["sibling_hash"], nbytes=JMT_HASH_BYTES, name="JMT sibling_hash"),
        sibling_on_left=obj["sibling_on_left"],
    )


def _siblings_to_wire(siblings: tuple[JmtSibling, ...]) -> list[dict[str, object]]:
    return [_sibling_to_wire(sibling) for sibling in siblings]


def _siblings_from_wire(value: object) -> tuple[JmtSibling, ...]:
    if type(value) is not list:
        raise TypeError("JMT siblings must be a list")
    if len(value) > JMT_KEY_BITS:
        raise ValueError("JMT proof path exceeds key depth")
    return _validate_siblings(tuple(_sibling_from_wire(item) for item in value))


def _reject_duplicate_json_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, value in pairs:
        if key in out:
            raise ValueError("JMT proof payload has duplicate fields")
        out[key] = value
    return out


def _load_proof_payload(payload: bytes) -> tuple[bytes, dict[str, Any]]:
    payload_bytes = _snapshot_bytes(payload, name="JMT proof payload")
    try:
        decoded = json.loads(payload_bytes.decode("utf-8"), object_pairs_hook=_reject_duplicate_json_object)
    except UnicodeDecodeError as exc:
        raise ValueError("JMT proof payload must be UTF-8") from exc
    except json.JSONDecodeError as exc:
        raise ValueError("JMT proof payload must be JSON") from exc
    return payload_bytes, _require_object(decoded, name="JMT proof payload")


def encode_jmt_membership_proof(proof: JmtMembershipProof) -> bytes:
    proof = _snapshot_membership_proof(proof)
    return canonical_json_bytes(
        {
            "kind": "membership",
            "version": JMT_VERSION,
            "key": _to_hex(proof.key),
            "value": _to_hex(proof.value),
            "siblings": _siblings_to_wire(proof.siblings),
        }
    )


def decode_jmt_membership_proof(payload: bytes) -> JmtMembershipProof:
    payload_bytes, obj = _load_proof_payload(payload)
    _require_fields(obj, {"kind", "version", "key", "value", "siblings"}, name="JMT membership proof")
    if obj["kind"] != "membership":
        raise ValueError("JMT membership proof kind mismatch")
    _require_version(obj["version"])
    proof = JmtMembershipProof(
        key=_from_hex(obj["key"], nbytes=JMT_KEY_BYTES, name="JMT key"),
        value=_from_hex(obj["value"], nbytes=None, name="JMT value"),
        siblings=_siblings_from_wire(obj["siblings"]),
    )
    if payload_bytes != encode_jmt_membership_proof(proof):
        raise ValueError("JMT membership proof payload must be canonical JSON")
    return proof


def encode_jmt_absence_proof(proof: JmtAbsenceProof) -> bytes:
    proof = _snapshot_absence_proof(proof)
    return canonical_json_bytes(
        {
            "kind": "absence",
            "version": JMT_VERSION,
            "query_key": _to_hex(proof.query_key),
            "witness_key": None if proof.witness_key is None else _to_hex(proof.witness_key),
            "witness_value": None if proof.witness_value is None else _to_hex(proof.witness_value),
            "siblings": _siblings_to_wire(proof.siblings),
        }
    )


def decode_jmt_absence_proof(payload: bytes) -> JmtAbsenceProof:
    payload_bytes, obj = _load_proof_payload(payload)
    _require_fields(
        obj,
        {"kind", "version", "query_key", "witness_key", "witness_value", "siblings"},
        name="JMT absence proof",
    )
    if obj["kind"] != "absence":
        raise ValueError("JMT absence proof kind mismatch")
    _require_version(obj["version"])
    witness_key = obj["witness_key"]
    witness_value = obj["witness_value"]
    proof = JmtAbsenceProof(
        query_key=_from_hex(obj["query_key"], nbytes=JMT_KEY_BYTES, name="JMT query_key"),
        witness_key=None
        if witness_key is None
        else _from_hex(witness_key, nbytes=JMT_KEY_BYTES, name="JMT witness_key"),
        witness_value=None if witness_value is None else _from_hex(witness_value, nbytes=None, name="JMT witness_value"),
        siblings=_siblings_from_wire(obj["siblings"]),
    )
    if payload_bytes != encode_jmt_absence_proof(proof):
        raise ValueError("JMT absence proof payload must be canonical JSON")
    return proof


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
        owned_proof = _snapshot_membership_proof(proof)
    except (AttributeError, TypeError, ValueError):
        return False
    if owned_proof.key != key_bytes or owned_proof.value != value_bytes:
        return False
    if not _siblings_follow_key(owned_proof.siblings, key_bytes):
        return False
    return (
        _fold_root(
            leaf_hash(owned_proof.key, owned_proof.value),
            owned_proof.siblings,
        )
        == root_bytes
    )


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
        owned_proof = _snapshot_absence_proof(proof)
    except (AttributeError, TypeError, ValueError):
        return False
    if owned_proof.query_key != query_key_bytes:
        return False
    if not _siblings_follow_key(owned_proof.siblings, query_key_bytes):
        return False

    if owned_proof.witness_key is None:
        witness_root = empty_hash(len(owned_proof.siblings))
    else:
        if (
            owned_proof.witness_key == query_key_bytes
            or owned_proof.witness_value is None
        ):
            return False
        if not _same_prefix(
            owned_proof.witness_key,
            query_key_bytes,
            len(owned_proof.siblings),
        ):
            return False
        witness_root = leaf_hash(
            owned_proof.witness_key,
            owned_proof.witness_value,
        )
    return _fold_root(witness_root, owned_proof.siblings) == root_bytes


def derive_jmt_insert_root(
    root: str | bytes,
    key: bytes,
    value: bytes,
    proof: JmtAbsenceProof,
) -> str:
    """Derive the exact successor root for insertion of one absent key.

    The absence proof authenticates the predecessor root. The same path then
    determines the unique Patricia subtree containing the new leaf. No archive
    or mutable tree object is trusted by this transition.
    """

    root_bytes = _root_bytes(root)
    key_bytes = _validate_key(key)
    value_bytes = _validate_value(value)
    owned_proof = _snapshot_absence_proof(proof)
    if not verify_jmt_absence(root_bytes, key_bytes, owned_proof):
        raise ValueError("JMT insertion requires an exact predecessor absence proof")

    path_depth = len(owned_proof.siblings)
    inserted_leaf = leaf_hash(key_bytes, value_bytes)
    if owned_proof.witness_key is None:
        successor_subtree = inserted_leaf
    else:
        witness_key = owned_proof.witness_key
        witness_value = owned_proof.witness_value
        if witness_value is None:  # Defensive; the owned type excludes this.
            raise ValueError("JMT insertion witness value is missing")
        divergence_depth = path_depth
        while (
            divergence_depth < JMT_KEY_BITS
            and _bit(key_bytes, divergence_depth)
            == _bit(witness_key, divergence_depth)
        ):
            divergence_depth += 1
        if divergence_depth == JMT_KEY_BITS:
            raise ValueError("JMT insertion key is already present")

        witness_leaf = leaf_hash(witness_key, witness_value)
        if _bit(key_bytes, divergence_depth) == 0:
            successor_subtree = internal_hash(inserted_leaf, witness_leaf)
        else:
            successor_subtree = internal_hash(witness_leaf, inserted_leaf)

        for depth in range(divergence_depth - 1, path_depth - 1, -1):
            empty_sibling = empty_hash(depth + 1)
            if _bit(key_bytes, depth) == 0:
                successor_subtree = internal_hash(successor_subtree, empty_sibling)
            else:
                successor_subtree = internal_hash(empty_sibling, successor_subtree)

    return _to_hex(_fold_root(successor_subtree, owned_proof.siblings))

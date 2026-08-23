from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from src.state.canonical import domain_sep_bytes, encode_bytes, encode_uvarint
from src.state.jmt import (
    EMPTY_ROOT_BYTES,
    EMPTY_ROOT_HEX,
    JMT_KEY_BITS,
    JMT_KEY_BYTES,
    JmtAbsenceProof,
    JmtMembershipProof,
    JmtSibling,
    compute_jmt_root,
    decode_jmt_absence_proof,
    decode_jmt_membership_proof,
    empty_hash,
    encode_jmt_absence_proof,
    encode_jmt_membership_proof,
    internal_hash,
    leaf_hash,
    prove_jmt_absence,
    prove_jmt_membership,
    verify_jmt_absence,
    verify_jmt_membership,
)

_REF_EMPTY_PREFIX = domain_sep_bytes("jmt_empty", version=1)
_REF_LEAF_PREFIX = domain_sep_bytes("jmt_leaf", version=1)
_REF_INTERNAL_PREFIX = domain_sep_bytes("jmt_internal", version=1)


def _key(n: int) -> bytes:
    return n.to_bytes(JMT_KEY_BYTES, "big")


def _ref_sha256(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()


def _ref_empty(depth: int) -> bytes:
    return _ref_sha256(_REF_EMPTY_PREFIX + encode_uvarint(depth))


def _ref_leaf(key: bytes, value: bytes) -> bytes:
    return _ref_sha256(_REF_LEAF_PREFIX + key + encode_bytes(value))


def _ref_internal(left: bytes, right: bytes) -> bytes:
    return _ref_sha256(_REF_INTERNAL_PREFIX + left + right)


def _ref_bit(key: bytes, depth: int) -> int:
    byte_index, bit_index = divmod(depth, 8)
    return (key[byte_index] >> (7 - bit_index)) & 1


def _ref_normalize(entries: list[tuple[bytes, bytes]]) -> tuple[tuple[bytes, bytes], ...]:
    if len({key for key, _ in entries}) != len(entries):
        raise ValueError("duplicate reference key")
    return tuple(sorted(entries, key=lambda item: item[0]))


def _ref_root(entries: tuple[tuple[bytes, bytes], ...], depth: int = 0) -> bytes:
    if not entries:
        return _ref_empty(depth)
    if len(entries) == 1:
        key, value = entries[0]
        return _ref_leaf(key, value)
    left = tuple(item for item in entries if _ref_bit(item[0], depth) == 0)
    right = tuple(item for item in entries if _ref_bit(item[0], depth) == 1)
    return _ref_internal(_ref_root(left, depth + 1), _ref_root(right, depth + 1))


def _ref_membership_siblings(
    entries: tuple[tuple[bytes, bytes], ...],
    key: bytes,
    depth: int = 0,
) -> tuple[JmtSibling, ...]:
    if not entries:
        raise KeyError("absent")
    if len(entries) == 1:
        if entries[0][0] != key:
            raise KeyError("absent")
        return ()
    left = tuple(item for item in entries if _ref_bit(item[0], depth) == 0)
    right = tuple(item for item in entries if _ref_bit(item[0], depth) == 1)
    if _ref_bit(key, depth) == 0:
        return (
            JmtSibling(sibling_hash=_ref_root(right, depth + 1), sibling_on_left=False),
            *_ref_membership_siblings(left, key, depth + 1),
        )
    return (
        JmtSibling(sibling_hash=_ref_root(left, depth + 1), sibling_on_left=True),
        *_ref_membership_siblings(right, key, depth + 1),
    )


def _ref_absence_proof(
    entries: tuple[tuple[bytes, bytes], ...],
    query: bytes,
    depth: int = 0,
) -> JmtAbsenceProof:
    if not entries:
        return JmtAbsenceProof(query_key=query, witness_key=None, witness_value=None, siblings=())
    if len(entries) == 1:
        key, value = entries[0]
        if key == query:
            raise KeyError("present")
        return JmtAbsenceProof(query_key=query, witness_key=key, witness_value=value, siblings=())
    left = tuple(item for item in entries if _ref_bit(item[0], depth) == 0)
    right = tuple(item for item in entries if _ref_bit(item[0], depth) == 1)
    if _ref_bit(query, depth) == 0:
        child = _ref_absence_proof(left, query, depth + 1)
        return JmtAbsenceProof(
            query_key=child.query_key,
            witness_key=child.witness_key,
            witness_value=child.witness_value,
            siblings=(
                JmtSibling(sibling_hash=_ref_root(right, depth + 1), sibling_on_left=False),
                *child.siblings,
            ),
        )
    child = _ref_absence_proof(right, query, depth + 1)
    return JmtAbsenceProof(
        query_key=child.query_key,
        witness_key=child.witness_key,
        witness_value=child.witness_value,
        siblings=(
            JmtSibling(sibling_hash=_ref_root(left, depth + 1), sibling_on_left=True),
            *child.siblings,
        ),
    )


class _HostileBytes(bytes):
    def __new__(cls, value: bytes) -> "_HostileBytes":
        return bytes.__new__(cls, value)

    def __getitem__(self, key):  # type: ignore[no-untyped-def]
        if isinstance(key, int):
            return 0xFF
        return super().__getitem__(key)

    def __eq__(self, other):  # type: ignore[no-untyped-def]
        return True

    def __ne__(self, other):  # type: ignore[no-untyped-def]
        return False


class _HostilePayload(bytes):
    def __new__(cls, raw: bytes, spoofed_text: str) -> "_HostilePayload":
        obj = bytes.__new__(cls, raw)
        obj._spoofed_text = spoofed_text
        return obj

    def decode(self, *args, **kwargs):  # type: ignore[no-untyped-def]
        return self._spoofed_text


class _BytesProtocolSpoof(bytes):
    def __new__(
        cls,
        raw: bytes,
        replacement: bytes,
    ) -> "_BytesProtocolSpoof":
        obj = bytes.__new__(cls, raw)
        obj._replacement = replacement
        return obj

    def __bytes__(self) -> bytes:
        return self._replacement


class _IncoherentEqualityBytes(bytes):
    def __eq__(self, other):  # type: ignore[no-untyped-def]
        return False

    def __ne__(self, other):  # type: ignore[no-untyped-def]
        return False

    __hash__ = bytes.__hash__


def _forge_frozen_dataclass(cls, **fields):  # type: ignore[no-untyped-def]
    value = object.__new__(cls)
    for name, field_value in fields.items():
        object.__setattr__(value, name, field_value)
    return value


def _wire(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def test_jmt_root_is_order_independent_and_binds_values() -> None:
    entries = [(_key(2), b"two"), (_key(1), b"one"), (_key(3), b"three")]

    root_a = compute_jmt_root(entries)
    root_b = compute_jmt_root(reversed(entries))
    root_changed = compute_jmt_root([(_key(2), b"two"), (_key(1), b"ONE"), (_key(3), b"three")])
    root_key_changed = compute_jmt_root([(_key(4), b"two"), (_key(1), b"one"), (_key(3), b"three")])

    assert root_a == root_b
    assert root_a != root_changed
    assert root_a != root_key_changed


def test_jmt_root_and_proofs_match_independent_reference_model() -> None:
    corpora = [
        [(_key(0), b"zero")],
        [(_key(0), b"zero"), (_key(1 << 255), b"high")],
        [(_key(1), b"one"), (_key(2), b"two"), (_key(255), b"max")],
        [(b"\x00" * JMT_KEY_BYTES, b"left"), (b"\x00" * (JMT_KEY_BYTES - 1) + b"\x01", b"right")],
        [(_key(7), b""), (_key(11), b"\x00"), (_key(19), b"longer-value")],
    ]

    for entries in corpora:
        normalized = _ref_normalize(entries)
        expected_root = "0x" + _ref_root(normalized).hex()
        assert compute_jmt_root(reversed(entries)) == expected_root

        for key, value in entries:
            live_proof = prove_jmt_membership(entries, key)
            expected_siblings = _ref_membership_siblings(normalized, key)
            assert live_proof == JmtMembershipProof(key=key, value=value, siblings=expected_siblings)
            assert verify_jmt_membership(expected_root, key, value, live_proof)

        absent_key = _key(123456789)
        if absent_key in {key for key, _ in entries}:
            absent_key = _key(123456790)
        live_absence = prove_jmt_absence(entries, absent_key)
        expected_absence = _ref_absence_proof(normalized, absent_key)
        assert live_absence == expected_absence
        assert verify_jmt_absence(expected_root, absent_key, live_absence)


def test_jmt_rejects_duplicate_canonical_keys() -> None:
    with pytest.raises(ValueError, match="duplicate JMT key"):
        compute_jmt_root([(_key(7), b"a"), (bytes(_key(7)), b"b")])


def test_jmt_rejects_bad_key_and_value_shapes() -> None:
    with pytest.raises(ValueError, match="JMT key must be exactly 32 bytes"):
        compute_jmt_root([(b"short", b"value")])
    with pytest.raises(ValueError, match="JMT key must be exactly 32 bytes"):
        compute_jmt_root([(b"x" * 33, b"value")])
    with pytest.raises(TypeError, match="JMT key must be bytes"):
        compute_jmt_root([(bytearray(_key(1)), b"value")])  # type: ignore[list-item]
    with pytest.raises(TypeError, match="JMT key must be bytes"):
        compute_jmt_root([("0x" + "01" * 32, b"value")])  # type: ignore[list-item]
    with pytest.raises(TypeError, match="JMT value must be bytes"):
        compute_jmt_root([(_key(1), "value")])  # type: ignore[list-item]
    with pytest.raises(TypeError, match="JMT value must be bytes"):
        compute_jmt_root([(_key(1), bytearray(b"value"))])  # type: ignore[list-item]


def test_jmt_empty_leaf_and_internal_domains_are_separated() -> None:
    assert compute_jmt_root([]) == EMPTY_ROOT_HEX
    empty_value_leaf = leaf_hash(_key(0), b"")
    empty_internal = internal_hash(EMPTY_ROOT_BYTES, EMPTY_ROOT_BYTES)
    assert empty_value_leaf != EMPTY_ROOT_BYTES
    assert empty_internal != EMPTY_ROOT_BYTES
    assert empty_internal != empty_value_leaf
    assert empty_hash(0) != empty_hash(1)
    assert compute_jmt_root([(_key(0), b"")]) != EMPTY_ROOT_HEX


def test_jmt_membership_proof_verifies_and_tampering_fails() -> None:
    entries = [(_key(1), b"one"), (_key(2), b"two"), (_key(255), b"max")]
    root = compute_jmt_root(entries)
    proof = prove_jmt_membership(entries, _key(2))

    assert verify_jmt_membership(root, _key(2), b"two", proof)
    assert not verify_jmt_membership(root, _key(2), b"TWO", proof)
    assert not verify_jmt_membership(root, _key(1), b"two", proof)

    assert proof.siblings
    sibling = proof.siblings[0]
    flipped = JmtSibling(
        sibling_hash=sibling.sibling_hash,
        sibling_on_left=not sibling.sibling_on_left,
    )
    tampered_proof = type(proof)(key=proof.key, value=proof.value, siblings=(flipped, *proof.siblings[1:]))
    assert not verify_jmt_membership(root, _key(2), b"two", tampered_proof)
    assert not verify_jmt_membership(root, _key(2), b"two", type(proof)(key=proof.key, value=proof.value, siblings=()))
    extra = type(proof)(
        key=proof.key,
        value=proof.value,
        siblings=(*proof.siblings, JmtSibling(sibling_hash=EMPTY_ROOT_BYTES, sibling_on_left=False)),
    )
    assert not verify_jmt_membership(root, _key(2), b"two", extra)
    assert not verify_jmt_membership("0x" + "ff" * 32, _key(2), b"two", proof)


def test_jmt_rejects_malformed_proof_siblings() -> None:
    with pytest.raises(ValueError, match="JMT empty depth"):
        empty_hash(-1)
    with pytest.raises(TypeError, match="left child hash must be bytes"):
        internal_hash(bytearray(EMPTY_ROOT_BYTES), EMPTY_ROOT_BYTES)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="right child hash must be exactly 32 bytes"):
        internal_hash(EMPTY_ROOT_BYTES, b"short")
    with pytest.raises(ValueError, match="sibling hash must be exactly 32 bytes"):
        JmtSibling(sibling_hash=b"short", sibling_on_left=False)
    with pytest.raises(TypeError, match="sibling_on_left must be bool"):
        JmtSibling(sibling_hash=EMPTY_ROOT_BYTES, sibling_on_left=0)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="JMT proof siblings must be JmtSibling values"):
        JmtMembershipProof(key=_key(1), value=b"one", siblings=(b"not-a-sibling",))  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="JMT proof path exceeds key depth"):
        JmtAbsenceProof(
            query_key=_key(1),
            witness_key=None,
            witness_value=None,
            siblings=tuple(JmtSibling(sibling_hash=EMPTY_ROOT_BYTES, sibling_on_left=False) for _ in range(257)),
        )
    with pytest.raises(ValueError, match="witness_value must be None"):
        JmtAbsenceProof(query_key=_key(1), witness_key=None, witness_value=b"unexpected", siblings=())
    with pytest.raises(ValueError, match="witness_value is required"):
        JmtAbsenceProof(query_key=_key(1), witness_key=_key(2), witness_value=None, siblings=())


def test_jmt_reject_paths_for_absent_membership_and_bad_verify_inputs() -> None:
    entries = {_key(1): b"one"}
    proof = prove_jmt_membership(entries, _key(1))

    assert compute_jmt_root(entries) == compute_jmt_root(list(entries.items()))
    with pytest.raises(KeyError, match="key is absent"):
        prove_jmt_membership([], _key(1))
    with pytest.raises(KeyError, match="key is absent"):
        prove_jmt_membership(entries, _key(2))

    assert not verify_jmt_membership("not-a-root", _key(1), b"one", proof)
    assert not verify_jmt_membership("0x" + "zz" * 32, _key(1), b"one", proof)
    assert not verify_jmt_membership(b"short", _key(1), b"one", proof)
    assert not verify_jmt_membership(7, _key(1), b"one", proof)  # type: ignore[arg-type]
    assert not verify_jmt_membership(EMPTY_ROOT_HEX, b"short", b"one", proof)
    assert not verify_jmt_membership(EMPTY_ROOT_HEX, _key(1), bytearray(b"one"), proof)  # type: ignore[arg-type]
    assert not verify_jmt_membership(EMPTY_ROOT_HEX, _key(1), b"one", object())  # type: ignore[arg-type]

    absence = prove_jmt_absence(entries, _key(2))
    assert not verify_jmt_absence("not-a-root", _key(2), absence)
    assert not verify_jmt_absence("0x" + "zz" * 32, _key(2), absence)
    assert not verify_jmt_absence(EMPTY_ROOT_HEX, b"short", absence)
    assert not verify_jmt_absence(EMPTY_ROOT_HEX, _key(2), object())  # type: ignore[arg-type]
    wrong_query = JmtAbsenceProof(
        query_key=_key(3),
        witness_key=absence.witness_key,
        witness_value=absence.witness_value,
        siblings=absence.siblings,
    )
    assert not verify_jmt_absence(compute_jmt_root(entries), _key(2), wrong_query)
    same_key_witness = JmtAbsenceProof(query_key=_key(2), witness_key=_key(2), witness_value=b"two", siblings=())
    assert not verify_jmt_absence(compute_jmt_root(entries), _key(2), same_key_witness)


def test_jmt_canonicalizes_bytes_subclasses_before_verification() -> None:
    entries = [(_key(0), b"present"), (_key(1 << 255), b"unrelated")]
    root = compute_jmt_root(entries)
    present_proof = prove_jmt_membership(entries, _key(0))
    unrelated_proof = prove_jmt_membership(entries, _key(1 << 255))

    hostile_key = _HostileBytes(_key(0))
    hostile_value = _HostileBytes(b"present")
    hostile_proof = JmtMembershipProof(
        key=hostile_key,
        value=hostile_value,
        siblings=present_proof.siblings,
    )

    assert type(hostile_proof.key) is bytes
    assert type(hostile_proof.value) is bytes
    assert verify_jmt_membership(root, _key(0), b"present", hostile_proof)

    forged_absence = JmtAbsenceProof(
        query_key=hostile_key,
        witness_key=_HostileBytes(unrelated_proof.key),
        witness_value=_HostileBytes(unrelated_proof.value),
        siblings=unrelated_proof.siblings,
    )

    assert type(forged_absence.query_key) is bytes
    assert type(forged_absence.witness_key) is bytes
    assert type(forged_absence.witness_value) is bytes
    assert not verify_jmt_absence(root, _key(0), forged_absence)


def test_jmt_membership_proof_serialization_is_canonical_and_verifies() -> None:
    entries = [(_key(1), b"one"), (_key(2), b"two"), (_key(255), b"max")]
    root = compute_jmt_root(entries)
    proof = prove_jmt_membership(entries, _key(2))

    encoded = encode_jmt_membership_proof(proof)
    decoded = decode_jmt_membership_proof(encoded)

    assert encoded == encode_jmt_membership_proof(decoded)
    assert decoded == proof
    assert verify_jmt_membership(root, _key(2), b"two", decoded)
    assert b" " not in encoded
    assert json.loads(encoded)["kind"] == "membership"


def test_jmt_absence_proof_serialization_is_canonical_and_verifies() -> None:
    entries = [(_key(42), b"answer")]
    root = compute_jmt_root(entries)
    proof = prove_jmt_absence(entries, _key(43))

    encoded = encode_jmt_absence_proof(proof)
    decoded = decode_jmt_absence_proof(encoded)

    assert encoded == encode_jmt_absence_proof(decoded)
    assert decoded == proof
    assert verify_jmt_absence(root, _key(43), decoded)
    assert json.loads(encoded)["kind"] == "absence"


def test_jmt_proof_serialization_rejects_unknown_fields_and_ambiguous_hex() -> None:
    proof = prove_jmt_membership([(_key(1), b"one"), (_key(2), b"two")], _key(1))
    payload = json.loads(encode_jmt_membership_proof(proof))

    with_unknown = dict(payload)
    with_unknown["extra"] = "ignored?"
    with pytest.raises(ValueError, match="unexpected JMT membership proof fields"):
        decode_jmt_membership_proof(_wire(with_unknown))

    uppercase_key = dict(payload)
    uppercase_key["key"] = "0x" + "AA" * JMT_KEY_BYTES
    with pytest.raises(ValueError, match="canonical lowercase hex"):
        decode_jmt_membership_proof(_wire(uppercase_key))

    wrong_kind = dict(payload)
    wrong_kind["kind"] = "absence"
    with pytest.raises(ValueError, match="JMT membership proof kind mismatch"):
        decode_jmt_membership_proof(_wire(wrong_kind))

    bad_version = dict(payload)
    bad_version["version"] = True
    with pytest.raises(ValueError, match="JMT proof version mismatch"):
        decode_jmt_membership_proof(_wire(bad_version))

    bad_sibling = dict(payload)
    bad_sibling["siblings"] = [{"sibling_hash": "0x" + "00" * 32, "sibling_on_left": False, "extra": 1}]
    with pytest.raises(ValueError, match="unexpected JMT sibling fields"):
        decode_jmt_membership_proof(_wire(bad_sibling))

    with pytest.raises(TypeError, match="JMT proof payload must be bytes"):
        decode_jmt_membership_proof(bytearray(encode_jmt_membership_proof(proof)))  # type: ignore[arg-type]


def test_jmt_proof_serialization_rejects_spoofed_payload_subclasses_and_noncanonical_json() -> None:
    proof = prove_jmt_membership([(_key(1), b"one"), (_key(2), b"two")], _key(1))
    encoded = encode_jmt_membership_proof(proof)
    payload = json.loads(encoded)

    spoofed = _HostilePayload(b"not-json", encoded.decode("utf-8"))
    with pytest.raises(ValueError, match="JMT proof payload must be JSON"):
        decode_jmt_membership_proof(spoofed)

    pretty = json.dumps(payload, sort_keys=True, indent=2).encode("utf-8")
    with pytest.raises(ValueError, match="JMT membership proof payload must be canonical JSON"):
        decode_jmt_membership_proof(pretty)

    reordered = json.dumps(payload, sort_keys=False, separators=(",", ":")).encode("utf-8")
    if reordered != encoded:
        with pytest.raises(ValueError, match="JMT membership proof payload must be canonical JSON"):
            decode_jmt_membership_proof(reordered)

    escaped = encoded.replace(b"membership", b"member\\u0073hip")
    assert escaped != encoded
    with pytest.raises(ValueError, match="JMT membership proof payload must be canonical JSON"):
        decode_jmt_membership_proof(escaped)

    with pytest.raises(ValueError, match="duplicate fields"):
        decode_jmt_membership_proof(
            b'{"key":"0x' + b"00" * 32 + b'","kind":"membership","siblings":[{"sibling_hash":"0x'
            + b"00" * 32
            + b'","sibling_hash":"0x'
            + b"11" * 32
            + b'","sibling_on_left":false}],"value":"0x","version":1}'
        )


def test_jmt_payload_and_key_bytes_subclasses_use_raw_buffers() -> None:
    # Arrange
    key_one = _key(1)
    key_two = _key(2)
    proof = JmtMembershipProof(key=key_one, value=b"one", siblings=())
    spoofed_payload = _BytesProtocolSpoof(
        b"not-json",
        encode_jmt_membership_proof(proof),
    )
    spoofed_key = _BytesProtocolSpoof(key_two, key_one)

    # Act / Assert
    with pytest.raises(ValueError, match="JMT proof payload must be JSON"):
        decode_jmt_membership_proof(spoofed_payload)
    assert compute_jmt_root([(spoofed_key, b"two")]) == compute_jmt_root(
        [(key_two, b"two")]
    )


def test_jmt_verifiers_reject_constructor_forged_incoherent_bytes() -> None:
    # Arrange
    key_one = _key(1)
    root = compute_jmt_root([(key_one, b"one")])
    forged_membership = _forge_frozen_dataclass(
        JmtMembershipProof,
        key=_IncoherentEqualityBytes(key_one),
        value=b"one",
        siblings=(),
    )
    forged_absence = _forge_frozen_dataclass(
        JmtAbsenceProof,
        query_key=key_one,
        witness_key=_IncoherentEqualityBytes(key_one),
        witness_value=b"one",
        siblings=(),
    )

    # Act
    membership_accepted = verify_jmt_membership(
        root,
        _key(2),
        b"one",
        forged_membership,
    )
    absence_accepted = verify_jmt_absence(root, key_one, forged_absence)

    # Assert
    assert not membership_accepted
    assert not absence_accepted


def test_jmt_verifiers_reject_malformed_forged_fields_without_raising() -> None:
    # Arrange
    key = _key(1)
    root = compute_jmt_root([(key, b"one")])
    malformed_membership = _forge_frozen_dataclass(
        JmtMembershipProof,
        key=key,
        value=b"one",
        siblings=(object(),),
    )
    malformed_absence = _forge_frozen_dataclass(
        JmtAbsenceProof,
        query_key=key,
        witness_key=None,
        witness_value=b"forged",
        siblings=(),
    )

    # Act / Assert
    assert not verify_jmt_membership(root, key, b"one", malformed_membership)
    assert not verify_jmt_absence(root, key, malformed_absence)


def test_jmt_encoders_revalidate_constructor_forged_proofs() -> None:
    # Arrange
    malformed_membership = _forge_frozen_dataclass(
        JmtMembershipProof,
        key=32,
        value=3,
        siblings=(),
    )
    malformed_absence = _forge_frozen_dataclass(
        JmtAbsenceProof,
        query_key=_key(1),
        witness_key=None,
        witness_value=b"forged",
        siblings=(),
    )

    # Act / Assert
    with pytest.raises(TypeError, match="JMT key must be bytes"):
        encode_jmt_membership_proof(malformed_membership)
    with pytest.raises(ValueError, match="witness_value must be None"):
        encode_jmt_absence_proof(malformed_absence)


def test_jmt_proof_serialization_rejects_malformed_payloads() -> None:
    proof = prove_jmt_membership([(_key(1), b"one"), (_key(2), b"two")], _key(1))
    payload = json.loads(encode_jmt_membership_proof(proof))

    with pytest.raises(ValueError, match="duplicate fields"):
        decode_jmt_membership_proof(b'{"kind":"membership","kind":"membership"}')
    with pytest.raises(ValueError, match="must be UTF-8"):
        decode_jmt_membership_proof(b"\xff")
    with pytest.raises(ValueError, match="must be JSON"):
        decode_jmt_membership_proof(b"{")
    with pytest.raises(TypeError, match="must be an object"):
        decode_jmt_membership_proof(b"[]")

    not_string_key = dict(payload)
    not_string_key["key"] = 7
    with pytest.raises(TypeError, match="JMT key must be a canonical hex string"):
        decode_jmt_membership_proof(_wire(not_string_key))

    no_prefix = dict(payload)
    no_prefix["key"] = "00" * JMT_KEY_BYTES
    with pytest.raises(ValueError, match="canonical hex string"):
        decode_jmt_membership_proof(_wire(no_prefix))

    odd_value = dict(payload)
    odd_value["value"] = "0x0"
    with pytest.raises(ValueError, match="even number"):
        decode_jmt_membership_proof(_wire(odd_value))

    short_key = dict(payload)
    short_key["key"] = "0x00"
    with pytest.raises(ValueError, match="canonical 32-byte hex"):
        decode_jmt_membership_proof(_wire(short_key))

    invalid_hex = dict(payload)
    invalid_hex["value"] = "0xgg"
    with pytest.raises(ValueError, match="valid hex"):
        decode_jmt_membership_proof(_wire(invalid_hex))

    whitespace_hex = dict(payload)
    whitespace_hex["value"] = "0x00 0a "
    with pytest.raises(ValueError, match="canonical lowercase hex"):
        decode_jmt_membership_proof(_wire(whitespace_hex))

    siblings_not_list = dict(payload)
    siblings_not_list["siblings"] = {}
    with pytest.raises(TypeError, match="JMT siblings must be a list"):
        decode_jmt_membership_proof(_wire(siblings_not_list))

    sibling_not_object = dict(payload)
    sibling_not_object["siblings"] = [7]
    with pytest.raises(TypeError, match="JMT sibling must be an object"):
        decode_jmt_membership_proof(_wire(sibling_not_object))

    sibling_bad_side = dict(payload)
    sibling_bad_side["siblings"] = [{"sibling_hash": "0x" + "00" * 32, "sibling_on_left": 0}]
    with pytest.raises(TypeError, match="JMT sibling_on_left must be bool"):
        decode_jmt_membership_proof(_wire(sibling_bad_side))

    with pytest.raises(TypeError, match="proof must be a JmtMembershipProof"):
        encode_jmt_membership_proof(object())  # type: ignore[arg-type]


def test_jmt_absence_proof_serialization_rejects_bad_payloads() -> None:
    proof = prove_jmt_absence([(_key(42), b"answer")], _key(43))
    payload = json.loads(encode_jmt_absence_proof(proof))

    with_unknown = dict(payload)
    with_unknown["extra"] = "ignored?"
    with pytest.raises(ValueError, match="unexpected JMT absence proof fields"):
        decode_jmt_absence_proof(_wire(with_unknown))

    wrong_kind = dict(payload)
    wrong_kind["kind"] = "membership"
    with pytest.raises(ValueError, match="JMT absence proof kind mismatch"):
        decode_jmt_absence_proof(_wire(wrong_kind))

    bad_version = dict(payload)
    bad_version["version"] = 999
    with pytest.raises(ValueError, match="JMT proof version mismatch"):
        decode_jmt_absence_proof(_wire(bad_version))

    bad_witness = dict(payload)
    bad_witness["witness_key"] = None
    bad_witness["witness_value"] = "0x00"
    with pytest.raises(ValueError, match="witness_value must be None"):
        decode_jmt_absence_proof(_wire(bad_witness))

    with pytest.raises(TypeError, match="proof must be a JmtAbsenceProof"):
        encode_jmt_absence_proof(object())  # type: ignore[arg-type]

    pretty = json.dumps(payload, sort_keys=True, indent=2).encode("utf-8")
    with pytest.raises(ValueError, match="JMT absence proof payload must be canonical JSON"):
        decode_jmt_absence_proof(pretty)


def test_jmt_handles_keys_that_diverge_only_at_final_bit() -> None:
    left = b"\x00" * JMT_KEY_BYTES
    right = b"\x00" * (JMT_KEY_BYTES - 1) + b"\x01"
    entries = [(left, b"left"), (right, b"right")]
    root = compute_jmt_root(entries)

    proof = prove_jmt_membership(entries, right)

    assert len(proof.siblings) == JMT_KEY_BITS
    assert verify_jmt_membership(root, right, b"right", proof)


def test_jmt_absence_proof_for_empty_branch_verifies_and_rejects_wrong_query() -> None:
    entries = [(_key(0), b"zero"), (_key(1), b"one")]
    root = compute_jmt_root(entries)
    absent_key = _key(1 << 255)
    proof = prove_jmt_absence(entries, absent_key)

    assert proof.witness_key is None
    assert verify_jmt_absence(root, absent_key, proof)
    assert not verify_jmt_absence(root, _key(0), proof)
    assert proof.siblings
    missing = JmtAbsenceProof(
        query_key=proof.query_key,
        witness_key=None,
        witness_value=None,
        siblings=proof.siblings[:-1],
    )
    assert not verify_jmt_absence(root, absent_key, missing)
    flipped = JmtAbsenceProof(
        query_key=proof.query_key,
        witness_key=None,
        witness_value=None,
        siblings=(
            JmtSibling(
                sibling_hash=proof.siblings[0].sibling_hash,
                sibling_on_left=not proof.siblings[0].sibling_on_left,
            ),
            *proof.siblings[1:],
        ),
    )
    assert not verify_jmt_absence(root, absent_key, flipped)


def test_jmt_absence_proof_for_divergent_leaf_verifies_and_present_key_rejects() -> None:
    entries = [(_key(42), b"answer")]
    root = compute_jmt_root(entries)
    proof = prove_jmt_absence(entries, _key(43))

    assert proof.witness_key == _key(42)
    assert proof.witness_value == b"answer"
    assert verify_jmt_absence(root, _key(43), proof)
    assert not verify_jmt_absence(root, _key(42), proof)
    with pytest.raises(KeyError, match="key is present"):
        prove_jmt_absence(entries, _key(42))


def test_jmt_absence_proof_rejects_tampered_witness_leaf() -> None:
    entries = [(_key(42), b"answer")]
    root = compute_jmt_root(entries)
    proof = prove_jmt_absence(entries, _key(43))

    tampered = JmtAbsenceProof(
        query_key=proof.query_key,
        witness_key=proof.witness_key,
        witness_value=b"wrong",
        siblings=proof.siblings,
    )
    assert not verify_jmt_absence(root, _key(43), tampered)


def test_jmt_absence_rejects_authenticated_unrelated_leaf_when_query_is_present() -> None:
    present = _key(0)
    unrelated = (1 << 255).to_bytes(JMT_KEY_BYTES, "big")
    entries = [(present, b"present"), (unrelated, b"unrelated")]
    root = compute_jmt_root(entries)
    unrelated_membership = prove_jmt_membership(entries, unrelated)

    forged_absence = JmtAbsenceProof(
        query_key=present,
        witness_key=unrelated_membership.key,
        witness_value=unrelated_membership.value,
        siblings=unrelated_membership.siblings,
    )

    assert not verify_jmt_absence(root, present, forged_absence)

    wrong_prefix = JmtAbsenceProof(
        query_key=unrelated,
        witness_key=present,
        witness_value=b"present",
        siblings=unrelated_membership.siblings,
    )
    assert not verify_jmt_absence(root, unrelated, wrong_prefix)


def test_jmt_absence_proof_descends_left_internal_branch() -> None:
    entries = [(_key(0), b"zero"), ((1 << 255).to_bytes(JMT_KEY_BYTES, "big"), b"high")]
    query = _key(2)
    root = compute_jmt_root(entries)
    proof = prove_jmt_absence(entries, query)

    assert proof.witness_key == _key(0)
    assert verify_jmt_absence(root, query, proof)


def test_jmt_is_standalone_and_not_imported_by_current_root_paths() -> None:
    repo_root = Path(__file__).resolve().parents[2]
    for rel in ("src/state/state_root.py", "src/state/support_root.py"):
        source = (repo_root / rel).read_text(encoding="utf-8")
        assert "src.state.jmt" not in source
        assert ".jmt" not in source

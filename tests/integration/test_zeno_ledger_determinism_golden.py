"""Cross-version determinism golden vectors.

Every consensus-critical hash in ZenoLedger must produce the **exact same
bytes** under every Python version, every CPU architecture, every JSON
library implementation detail. This file pins those values.

If any of these assertions fails:
  - A bug landed that changes the canonical encoding.
  - Python's dict iteration order or string-internal representation diverged.
  - A dependency (``hashlib``, ``json``) changed its output for the same
    input — extremely unlikely but possible across CPython releases.
  - The system is running on big-endian hardware that we never tested.

Any of those breaks every prior on-disk commitment, so a failure here is a
**deployment blocker**, not a test bug. Bump ``_v1`` only deliberately.

Coverage:
  - SHA-256 against published NIST test vectors.
  - ``canonical_json_bytes`` for empty/simple/nested/Unicode payloads.
  - ``domain_sep_bytes`` literal byte format.
  - ``encode_uvarint`` against published LEB128 test vectors.
  - ``hash_v0`` for representative domains and value types.
  - ``merkle_root_v0`` for tree sizes 0, 1, 2.
  - Python platform invariants (byte order, int size, hash algorithm
    availability).
"""

from __future__ import annotations

import hashlib
import platform
import sys

import pytest

from src.state.canonical import (
    CANONICAL_ENCODING_VERSION,
    MAX_UVARINT_BITS,
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    encode_bytes,
    encode_uvarint,
    sha256_hex,
)
from src.integration.zeno_ledger_v0 import (
    LEDGER_ROOT_VERSION,
    hash_v0,
    merkle_root_v0,
)


# -----------------------------------------------------------------------------
# A. Platform invariants — assumed by the rest of the suite.
# -----------------------------------------------------------------------------


class TestPlatformInvariants:
    def test_byte_order_is_little_endian(self) -> None:
        # CPython integer serialization is byte-order-agnostic in our API,
        # but downstream consumers (and any future Rust port) need to know.
        assert sys.byteorder == "little"

    def test_int_is_arbitrary_precision(self) -> None:
        # Test a 256-bit integer round-trips through canonical encoding.
        n = (1 << 256) - 1
        assert canonical_json_bytes(n) == str(n).encode()

    def test_sha256_available_in_hashlib_default(self) -> None:
        # SHA-256 is mandatory.
        assert "sha256" in hashlib.algorithms_guaranteed

    def test_default_text_encoding_is_utf8(self) -> None:
        # Default encoding affects how we serialize strings in canonical JSON.
        assert sys.getdefaultencoding() == "utf-8"

    def test_python_version_supports_required_features(self) -> None:
        # We require 3.11+ for ``self`` type annotations and ``Final``.
        assert sys.version_info >= (3, 11), (
            f"ZenoLedger requires Python 3.11+, got {sys.version_info}"
        )


# -----------------------------------------------------------------------------
# B. SHA-256 — NIST test vectors.
# -----------------------------------------------------------------------------


class TestSha256GoldenVectors:
    """https://www.di-mgt.com.au/sha_testvectors.html"""

    def test_empty_string(self) -> None:
        assert sha256_hex(b"") == (
            "0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        )

    def test_abc(self) -> None:
        assert sha256_hex(b"abc") == (
            "0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        )

    def test_448_bit_message(self) -> None:
        msg = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
        assert sha256_hex(msg) == (
            "0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        )

    def test_million_a(self) -> None:
        assert sha256_hex(b"a" * 1_000_000) == (
            "0xcdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
        )


# -----------------------------------------------------------------------------
# C. canonical_json_bytes — golden byte sequences.
# -----------------------------------------------------------------------------


class TestCanonicalJsonGoldenVectors:
    def test_empty_dict(self) -> None:
        assert canonical_json_bytes({}) == b"{}"

    def test_empty_list(self) -> None:
        assert canonical_json_bytes([]) == b"[]"

    def test_empty_string(self) -> None:
        assert canonical_json_bytes("") == b'""'

    def test_null(self) -> None:
        assert canonical_json_bytes(None) == b"null"

    def test_true(self) -> None:
        assert canonical_json_bytes(True) == b"true"

    def test_false(self) -> None:
        assert canonical_json_bytes(False) == b"false"

    def test_zero(self) -> None:
        assert canonical_json_bytes(0) == b"0"

    def test_negative_int(self) -> None:
        assert canonical_json_bytes(-42) == b"-42"

    def test_large_int(self) -> None:
        n = 2**128
        assert canonical_json_bytes(n) == str(n).encode()

    def test_single_key_dict(self) -> None:
        assert canonical_json_bytes({"a": 1}) == b'{"a":1}'

    def test_dict_keys_are_sorted(self) -> None:
        # Insertion order intentionally not alphabetical.
        assert canonical_json_bytes({"z": 1, "a": 2}) == b'{"a":2,"z":1}'

    def test_nested_dict_keys_sorted_at_every_level(self) -> None:
        v = {"outer_z": {"inner_b": 1, "inner_a": 2}, "outer_a": 3}
        assert canonical_json_bytes(v) == (
            b'{"outer_a":3,"outer_z":{"inner_a":2,"inner_b":1}}'
        )

    def test_list_preserves_order(self) -> None:
        assert canonical_json_bytes([3, 1, 2]) == b"[3,1,2]"

    def test_unicode_non_ascii_preserved(self) -> None:
        # ensure_ascii=False → UTF-8 bytes for the string content.
        assert canonical_json_bytes("zürich") == "\"zürich\"".encode("utf-8")

    def test_unicode_escapes_for_control_chars(self) -> None:
        # json.dumps escapes \x00 as \u0000.
        assert canonical_json_bytes("\x00") == b'"\\u0000"'


# -----------------------------------------------------------------------------
# D. domain_sep_bytes — literal byte format.
# -----------------------------------------------------------------------------


class TestDomainSepGoldenVectors:
    def test_simple_label_v1(self) -> None:
        assert domain_sep_bytes("x", version=1) == b"zenodex:x:v1\x00"

    def test_multichar_label_v1(self) -> None:
        assert domain_sep_bytes("zeno_ledger_v0", version=1) == b"zenodex:zeno_ledger_v0:v1\x00"

    def test_version_2(self) -> None:
        assert domain_sep_bytes("x", version=2) == b"zenodex:x:v2\x00"

    def test_version_99(self) -> None:
        assert domain_sep_bytes("x", version=99) == b"zenodex:x:v99\x00"

    def test_label_with_colon_internal(self) -> None:
        # The regex allows colons in labels (_DOMAIN_RE = [A-Za-z0-9_.:/-]).
        assert domain_sep_bytes("a:b", version=1) == b"zenodex:a:b:v1\x00"

    def test_label_with_dash(self) -> None:
        assert domain_sep_bytes("a-b", version=1) == b"zenodex:a-b:v1\x00"

    def test_label_with_slash(self) -> None:
        assert domain_sep_bytes("a/b", version=1) == b"zenodex:a/b:v1\x00"

    def test_label_with_dot(self) -> None:
        assert domain_sep_bytes("a.b", version=1) == b"zenodex:a.b:v1\x00"


# -----------------------------------------------------------------------------
# E. encode_uvarint — LEB128 golden vectors.
# -----------------------------------------------------------------------------


class TestUvarintGoldenVectors:
    """Reference: Protocol Buffers varint / LEB128 unsigned."""

    def test_zero(self) -> None:
        assert encode_uvarint(0) == b"\x00"

    def test_one(self) -> None:
        assert encode_uvarint(1) == b"\x01"

    def test_max_single_byte(self) -> None:
        # 127 fits in a single byte.
        assert encode_uvarint(127) == b"\x7f"

    def test_min_two_byte(self) -> None:
        # 128 = 0x80 requires two bytes: 0x80 (continuation) | 0x01.
        assert encode_uvarint(128) == b"\x80\x01"

    def test_max_two_byte(self) -> None:
        # 16383 = (2^14 - 1) = 0xff 0x7f.
        assert encode_uvarint(16_383) == b"\xff\x7f"

    def test_min_three_byte(self) -> None:
        assert encode_uvarint(16_384) == b"\x80\x80\x01"

    def test_max_uint32(self) -> None:
        # 2^32 - 1 → 5 bytes.
        assert encode_uvarint(2**32 - 1) == b"\xff\xff\xff\xff\x0f"

    def test_2_pow_64(self) -> None:
        # 2^64 → 10 bytes.
        assert encode_uvarint(2**64) == b"\x80\x80\x80\x80\x80\x80\x80\x80\x80\x02"


# -----------------------------------------------------------------------------
# F. encode_bytes — golden vectors.
# -----------------------------------------------------------------------------


class TestEncodeBytesGoldenVectors:
    def test_empty(self) -> None:
        assert encode_bytes(b"") == b"\x00"

    def test_single_byte(self) -> None:
        assert encode_bytes(b"A") == b"\x01A"

    def test_five_bytes(self) -> None:
        assert encode_bytes(b"hello") == b"\x05hello"

    def test_128_bytes_has_two_byte_length_prefix(self) -> None:
        payload = b"\x00" * 128
        encoded = encode_bytes(payload)
        # uvarint(128) = b'\x80\x01' (two bytes), then 128 payload bytes.
        assert encoded[:2] == b"\x80\x01"
        assert encoded[2:] == payload


# -----------------------------------------------------------------------------
# G. hash_v0 — golden vectors over fixed inputs.
# -----------------------------------------------------------------------------


class TestHashV0GoldenVectors:
    """Every committed hash in production must reproduce these bytes
    exactly across runs, Python versions, and platforms."""

    def test_empty_dict_domain_d(self) -> None:
        assert hash_v0("d", {}) == (
            "0xc98f946e0876c60f06c9f5a2ac0d47b5d85b881b1c028f876110fffe49181b16"
        )

    def test_empty_bytes_domain_d(self) -> None:
        assert hash_v0("d", b"") == (
            "0x5bbf4f21232d5ae3f564a0c15b080886e94277133cf47ca3e9c4747cc8817421"
        )

    def test_three_bytes_domain_d(self) -> None:
        assert hash_v0("d", b"abc") == (
            "0x445529fbfbe8abcac9fabe5102ff9c790a01722cb0d175dd01e128c157b56b7f"
        )

    def test_single_key_dict_domain_d(self) -> None:
        assert hash_v0("d", {"a": 1}) == (
            "0x8e14c3464013d28d3ce2c9f5452fc3a86f7f7fe4df3188e8ad911b5dad1be104"
        )

    def test_different_domain_yields_different_hash(self) -> None:
        a = hash_v0("d1", {"a": 1})
        b = hash_v0("d2", {"a": 1})
        assert a != b

    def test_same_dict_different_insertion_order_same_hash(self) -> None:
        # sort_keys ensures order independence.
        a = hash_v0("d", {"a": 1, "b": 2, "c": 3})
        b = hash_v0("d", {"c": 3, "b": 2, "a": 1})
        assert a == b


# -----------------------------------------------------------------------------
# H. merkle_root_v0 — golden vectors.
# -----------------------------------------------------------------------------


class TestMerkleRootGoldenVectors:
    def test_empty_tree(self) -> None:
        assert merkle_root_v0("d", []) == (
            "0x4e5d2c3b446d54875575d71538f8ca04efcd6279947e35ae160df966e4c184a1"
        )

    def test_single_leaf_all_zeros(self) -> None:
        assert merkle_root_v0("d", ["0x" + "00" * 32]) == (
            "0xa22f10e4014887f5e648dc2fbec52444d64ae0172247cd1a50bfd68d87404dd5"
        )

    def test_two_leaves_zero_and_ff(self) -> None:
        assert merkle_root_v0("d", ["0x" + "00" * 32, "0x" + "ff" * 32]) == (
            "0xe778aa88652042b9fe6b38b7295ac950962b9aad563311acbd35a614daa64862"
        )

    def test_two_leaves_reversed_yields_different_root(self) -> None:
        a = merkle_root_v0("d", ["0x" + "00" * 32, "0x" + "ff" * 32])
        b = merkle_root_v0("d", ["0x" + "ff" * 32, "0x" + "00" * 32])
        assert a != b


# -----------------------------------------------------------------------------
# I. canonical_hex_fixed_allow_0x — round-trip stability.
# -----------------------------------------------------------------------------


class TestCanonicalHexGoldenVectors:
    def test_lowercase_64_char_hash(self) -> None:
        h = "ab" * 32
        assert canonical_hex_fixed_allow_0x(h, nbytes=32, name="x") == "0x" + h

    def test_uppercase_normalized_to_lowercase(self) -> None:
        h = "AB" * 32
        assert canonical_hex_fixed_allow_0x(h, nbytes=32, name="x") == "0x" + ("ab" * 32)

    def test_0x_prefix_preserved(self) -> None:
        h = "0x" + "ab" * 32
        assert canonical_hex_fixed_allow_0x(h, nbytes=32, name="x") == h

    def test_0X_uppercase_prefix_normalized(self) -> None:
        h = "0X" + "AB" * 32
        assert canonical_hex_fixed_allow_0x(h, nbytes=32, name="x") == "0x" + ("ab" * 32)


# -----------------------------------------------------------------------------
# J. Pinned versions — drift detection.
# -----------------------------------------------------------------------------


class TestPinnedVersions:
    """Bumping any of these constants invalidates EVERY prior committed hash.
    Pin them here so accidental edits are caught before deployment."""

    def test_canonical_encoding_version_is_one(self) -> None:
        assert CANONICAL_ENCODING_VERSION == 1

    def test_ledger_root_version_is_one(self) -> None:
        assert LEDGER_ROOT_VERSION == 1

    def test_max_uvarint_bits_is_256(self) -> None:
        assert MAX_UVARINT_BITS == 256

    def test_hash_v0_output_format_is_64_char_lowercase_hex_with_0x_prefix(self) -> None:
        h = hash_v0("d", {"x": 1})
        assert h.startswith("0x")
        assert len(h) == 2 + 64
        body = h[2:]
        assert all(c in "0123456789abcdef" for c in body)


# -----------------------------------------------------------------------------
# K. Reproducibility report (informational).
# -----------------------------------------------------------------------------


def test_emit_environment_fingerprint(capsys: pytest.CaptureFixture[str]) -> None:
    """Print a fingerprint of the test environment alongside a known hash.

    Operators reading CI logs can grep for this line to compare across runs.
    The actual hash is the bit we care about; if it changes across runs of
    the *same* environment, something is wrong. If it changes across
    *different* environments, the platform pinning has drifted.
    """
    fingerprint = {
        "python_version": ".".join(map(str, sys.version_info[:3])),
        "python_implementation": platform.python_implementation(),
        "machine": platform.machine(),
        "system": platform.system(),
        "byteorder": sys.byteorder,
        "canonical_encoding_version": CANONICAL_ENCODING_VERSION,
        "ledger_root_version": LEDGER_ROOT_VERSION,
        "reference_hash": hash_v0("d", {"determinism_marker": True, "value": 42}),
    }
    print("ZENO_LEDGER_GOLDEN_FINGERPRINT=" + repr(fingerprint))
    # Just ensure the call succeeds; the assertion is implicit in capsys.
    captured = capsys.readouterr()
    assert "ZENO_LEDGER_GOLDEN_FINGERPRINT" in captured.out

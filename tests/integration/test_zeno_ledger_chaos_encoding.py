"""Chaos tests for ZenoLedger encoding primitives.

These tests attack the foundation layer that every hash, commitment, and
signature in the system stands on:

    canonical_json_bytes  ─┐
    domain_sep_bytes      ─┼─► hash_v0 / sha256_hex ─► all root hashes
    encode_uvarint        ─┤
    encode_bytes          ─┤
    hex_to_bytes_fixed    ─┘

If the Tau Net community changes the canonical JSON rules, varint encoding,
or domain separation conventions, this entire layer's outputs will diverge
silently from prior commitments. The tests in this file ensure:

1. **Adversarial inputs fail closed** — bad data raises, doesn't silently
   produce a hash.
2. **Determinism under adversarial reordering** — sort_keys must hold across
   dict insertion orders, list permutations are NOT equivalent.
3. **Domain separation truly separates** — same data hashed under different
   labels/versions never collides.
4. **Boundary values** — exactly at every documented limit, both sides.
5. **Hash chain integrity** — single-bit mutations in any field flip the
   final hash with overwhelming probability.

These are NOT performance/scale tests; they target *correctness* under
malicious input and *forward compatibility* with possible Tau changes.
"""

from __future__ import annotations

import math
from typing import Any

import pytest

from src.integration.zeno_ledger_v0 import (
    LEDGER_ROOT_VERSION,
    canonical_json_bytes_v0,
    hash_v0,
    merkle_root_v0,
)
from src.state.canonical import (
    CANONICAL_ENCODING_VERSION,
    MAX_UVARINT_BITS,
    bounded_json_utf8_size,
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    encode_bytes,
    encode_uvarint,
    hex_to_bytes_fixed,
    sha256_hex,
)

# -----------------------------------------------------------------------------
# A. canonical_json_bytes — adversarial inputs.
# -----------------------------------------------------------------------------


class TestCanonicalJsonBytesAdversarial:
    """Each test ensures a class of malformed input *raises*, not silently hashes."""

    def test_rejects_top_level_float(self) -> None:
        with pytest.raises(TypeError, match="floats"):
            canonical_json_bytes(3.14)

    def test_rejects_nested_float_in_list(self) -> None:
        with pytest.raises(TypeError, match="floats"):
            canonical_json_bytes([1, 2, 3.0])

    def test_rejects_nested_float_in_dict_value(self) -> None:
        with pytest.raises(TypeError, match="floats"):
            canonical_json_bytes({"a": 1, "b": 2.0})

    def test_rejects_deeply_nested_float(self) -> None:
        with pytest.raises(TypeError, match="floats"):
            canonical_json_bytes({"a": [{"b": [1, [2, 3.5]]}]})

    def test_rejects_nan(self) -> None:
        with pytest.raises(TypeError, match="floats"):
            canonical_json_bytes(float("nan"))

    def test_rejects_infinity(self) -> None:
        with pytest.raises(TypeError, match="floats"):
            canonical_json_bytes(math.inf)

    def test_rejects_negative_infinity(self) -> None:
        with pytest.raises(TypeError, match="floats"):
            canonical_json_bytes(-math.inf)

    def test_rejects_surrogate_in_string(self) -> None:
        # Lone high surrogate.
        bad = "\ud800"
        with pytest.raises(TypeError, match="surrogate"):
            canonical_json_bytes(bad)

    def test_rejects_surrogate_in_dict_key(self) -> None:
        with pytest.raises(TypeError, match="surrogate"):
            canonical_json_bytes({"\udfff": "value"})

    def test_rejects_surrogate_in_nested_list(self) -> None:
        with pytest.raises(TypeError, match="surrogate"):
            canonical_json_bytes(["ok", ["nested", "\ud83d"]])

    def test_rejects_non_string_dict_key(self) -> None:
        with pytest.raises(TypeError, match="dict keys"):
            canonical_json_bytes({1: "value"})

    def test_rejects_tuple_dict_key(self) -> None:
        with pytest.raises(TypeError, match="dict keys"):
            canonical_json_bytes({("a", "b"): "value"})

    def test_rejects_none_dict_key(self) -> None:
        with pytest.raises(TypeError, match="dict keys"):
            canonical_json_bytes({None: "value"})

    def test_accepts_empty_string(self) -> None:
        # Empty string is valid JSON; should not raise.
        assert canonical_json_bytes("") == b'""'

    def test_accepts_empty_dict(self) -> None:
        assert canonical_json_bytes({}) == b"{}"

    def test_accepts_empty_list(self) -> None:
        assert canonical_json_bytes([]) == b"[]"

    def test_accepts_none(self) -> None:
        assert canonical_json_bytes(None) == b"null"

    def test_accepts_true(self) -> None:
        assert canonical_json_bytes(True) == b"true"

    def test_accepts_false(self) -> None:
        assert canonical_json_bytes(False) == b"false"

    def test_accepts_zero(self) -> None:
        assert canonical_json_bytes(0) == b"0"

    def test_accepts_huge_int(self) -> None:
        # int has arbitrary precision; ensure no overflow.
        n = 10**100
        out = canonical_json_bytes(n)
        assert out == str(n).encode()

    def test_accepts_negative_int(self) -> None:
        out = canonical_json_bytes(-12345)
        assert out == b"-12345"

    def test_accepts_unicode_non_ascii_string(self) -> None:
        # Non-surrogate Unicode is fine; ensure_ascii=False preserves it.
        out = canonical_json_bytes("zürich")
        assert out == '"zürich"'.encode("utf-8")

    def test_accepts_embedded_null(self) -> None:
        # Note: JSON allows \\u0000; canonical encoder must too.
        out = canonical_json_bytes("a\x00b")
        # Python's json.dumps escapes \x00 as \u0000.
        assert out == b'"a\\u0000b"'

    def test_zero_width_chars_preserved(self) -> None:
        # Zero-width joiner is real Unicode, must be preserved as bytes.
        out = canonical_json_bytes("a\u200db")
        assert "\u200d".encode() in out


# -----------------------------------------------------------------------------
# A2. canonical_json_bytes — determinism / sort_keys.
# -----------------------------------------------------------------------------


class TestCanonicalJsonBytesDeterminism:
    def test_dict_key_insertion_order_does_not_change_bytes(self) -> None:
        a = {"a": 1, "b": 2, "c": 3}
        b = {"c": 3, "a": 1, "b": 2}
        assert canonical_json_bytes(a) == canonical_json_bytes(b)

    def test_nested_dict_keys_are_sorted_at_every_level(self) -> None:
        a = {"z": {"b": 1, "a": 2}, "a": {"y": 3, "x": 4}}
        b = {"a": {"x": 4, "y": 3}, "z": {"a": 2, "b": 1}}
        assert canonical_json_bytes(a) == canonical_json_bytes(b)

    def test_list_order_is_significant(self) -> None:
        # Lists are ordered; reordering must produce different bytes.
        assert canonical_json_bytes([1, 2, 3]) != canonical_json_bytes([3, 2, 1])

    def test_int_string_distinction_preserved(self) -> None:
        # The string "1" and int 1 must hash to different bytes.
        assert canonical_json_bytes("1") != canonical_json_bytes(1)

    def test_true_string_distinction_preserved(self) -> None:
        assert canonical_json_bytes("true") != canonical_json_bytes(True)

    def test_null_string_distinction_preserved(self) -> None:
        assert canonical_json_bytes("null") != canonical_json_bytes(None)

    def test_no_whitespace_in_output(self) -> None:
        # separators=(',', ':') means no spaces anywhere.
        out = canonical_json_bytes({"a": 1, "b": [2, 3], "c": {"d": 4}})
        assert b" " not in out
        assert b"\t" not in out
        assert b"\n" not in out


# -----------------------------------------------------------------------------
# B. domain_sep_bytes — chaos at the separator boundary.
# -----------------------------------------------------------------------------


class TestDomainSepBytesAdversarial:
    def test_rejects_empty_label(self) -> None:
        with pytest.raises(TypeError, match="non-empty"):
            domain_sep_bytes("")

    def test_rejects_none_label(self) -> None:
        with pytest.raises(TypeError, match="non-empty"):
            domain_sep_bytes(None)  # type: ignore[arg-type]

    def test_rejects_bytes_label(self) -> None:
        with pytest.raises(TypeError, match="non-empty"):
            domain_sep_bytes(b"label")  # type: ignore[arg-type]

    def test_rejects_label_with_nul(self) -> None:
        with pytest.raises(ValueError, match="NUL"):
            domain_sep_bytes("foo\x00bar")

    def test_rejects_non_ascii_label(self) -> None:
        with pytest.raises(ValueError, match="ASCII"):
            domain_sep_bytes("zenoléger")

    def test_rejects_unicode_homoglyph_label(self) -> None:
        # Cyrillic 'а' (U+0430) — looks like ASCII 'a'.
        with pytest.raises(ValueError, match="ASCII"):
            domain_sep_bytes("zeno\u0430")

    def test_rejects_version_zero(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            domain_sep_bytes("label", version=0)

    def test_rejects_version_negative(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            domain_sep_bytes("label", version=-1)

    def test_rejects_version_bool_true(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            domain_sep_bytes("label", version=True)  # type: ignore[arg-type]

    def test_rejects_version_float(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            domain_sep_bytes("label", version=1.0)  # type: ignore[arg-type]

    def test_rejects_version_string(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            domain_sep_bytes("label", version="1")  # type: ignore[arg-type]

    def test_terminates_with_nul(self) -> None:
        out = domain_sep_bytes("alpha")
        assert out.endswith(b"\x00")
        # And NUL appears only once (at the end).
        assert out.count(b"\x00") == 1

    def test_different_labels_produce_different_bytes(self) -> None:
        a = domain_sep_bytes("foo")
        b = domain_sep_bytes("bar")
        assert a != b

    def test_different_versions_produce_different_bytes(self) -> None:
        a = domain_sep_bytes("label", version=1)
        b = domain_sep_bytes("label", version=2)
        assert a != b

    def test_no_label_concat_collision(self) -> None:
        # "a:b" and "a" + ":b" must produce *different* domain prefixes;
        # the NUL terminator must prevent label-vs-label concatenation collisions.
        a = domain_sep_bytes("ab")
        b = domain_sep_bytes("a")
        assert not a.startswith(b[:-1])  # b without NUL is not a prefix of a

    def test_version_99_vs_v9_full_bytes_differ(self) -> None:
        # If versions were concatenated naively without delimiter, hashing
        # `"v99"|payload_A` could collide with `"v9"|"9"+payload_A`. The trailing
        # NUL on the domain prefix prevents this: the NUL falls at a different
        # offset, guaranteeing the *full* hashed byte string differs even when
        # the v9 form is a textual prefix of the v99 form.
        a = domain_sep_bytes("x", version=99)
        b = domain_sep_bytes("x", version=9)
        assert a != b
        # The NUL terminator forces the suffix of `b` to be `b"\x00"`, which is
        # NOT a valid hex digit, so the next byte in `a` (`b"9"`) cannot be
        # mistaken for a continuation of `b`'s version field.
        assert a == b"zenodex:x:v99\x00"
        assert b == b"zenodex:x:v9\x00"


# -----------------------------------------------------------------------------
# B2. hash_v0 — domain separation under chaos.
# -----------------------------------------------------------------------------


class TestHashV0DomainSeparation:
    def test_same_value_different_domains_collide_negligibly(self) -> None:
        v = {"a": 1, "b": [2, 3]}
        h1 = hash_v0("domain_one", v)
        h2 = hash_v0("domain_two", v)
        assert h1 != h2

    def test_same_value_different_byte_input_collide_negligibly(self) -> None:
        h1 = hash_v0("domain", b"abc")
        h2 = hash_v0("domain", b"abd")
        assert h1 != h2

    def test_known_type_ambiguity_bytes_vs_json_path(self) -> None:
        """**Documented finding — TYPE AMBIGUITY IN `hash_v0`.**

        The bytes path (``isinstance(value, bytes|bytearray)``) and the JSON
        path differ only in serialization. Because both go through the same
        ``encode_bytes(payload)`` length-prefix step and there is *no type
        discriminator byte*, a caller who can choose between paths can produce
        a collision: ``hash_v0(d, "hello")`` equals ``hash_v0(d, b'"hello"')``.

        This is a confused-deputy hazard. The current callers in the codebase
        all stick to one path per domain, so this is not exploitable today —
        but a future refactor that lets untrusted input pick the path would
        open it up. A ``hash_v1`` should prepend a type tag byte
        (e.g. ``\\x00`` for bytes, ``\\x01`` for JSON) before the payload.

        This test ASSERTS the collision so a future fix (good) will break it
        and force a deliberate ``v1`` rev.
        """
        h_bytes = hash_v0("d", b'"hello"')
        h_json = hash_v0("d", "hello")
        h_int = hash_v0("d", 42)
        h_int_bytes = hash_v0("d", b"42")
        # Currently equal — bytes path and JSON path collide for matching bytes.
        assert h_bytes == h_json
        assert h_int == h_int_bytes

    def test_returns_canonical_hex(self) -> None:
        h = hash_v0("domain", {"a": 1})
        assert h.startswith("0x")
        assert len(h) == 2 + 64  # 32 bytes = 64 hex chars
        body = h[2:]
        assert all(c in "0123456789abcdef" for c in body)

    def test_deterministic_across_calls(self) -> None:
        v = {"a": 1, "b": [2, 3], "c": {"d": True, "e": None}}
        h1 = hash_v0("d", v)
        h2 = hash_v0("d", v)
        assert h1 == h2

    def test_dict_insertion_order_does_not_change_hash(self) -> None:
        a = {"a": 1, "b": 2, "c": 3}
        b = {"c": 3, "a": 1, "b": 2}
        assert hash_v0("d", a) == hash_v0("d", b)

    def test_list_order_changes_hash(self) -> None:
        # Sanity: list order matters even when sorted dict keys don't.
        assert hash_v0("d", [1, 2, 3]) != hash_v0("d", [3, 2, 1])

    def test_rejects_invalid_domain_characters(self) -> None:
        # _DOMAIN_RE = ^[A-Za-z0-9_.:/-]+$
        with pytest.raises(ValueError, match="unsupported characters"):
            hash_v0("bad domain", {"x": 1})

    def test_rejects_domain_with_space(self) -> None:
        with pytest.raises(ValueError, match="unsupported characters"):
            hash_v0("foo bar", {"x": 1})

    def test_rejects_empty_domain(self) -> None:
        with pytest.raises(TypeError):
            hash_v0("", {"x": 1})

    def test_rejects_unicode_domain(self) -> None:
        with pytest.raises(ValueError):
            hash_v0("zëno", {"x": 1})

    def test_rejects_float_value(self) -> None:
        with pytest.raises(TypeError, match="floats"):
            hash_v0("d", {"x": 1.5})

    def test_collision_resistance_under_field_flip(self) -> None:
        # Single bit flip in a field must change the hash with overwhelming probability.
        a = {"k": "value"}
        b = {"k": "value!"}  # one char difference
        assert hash_v0("d", a) != hash_v0("d", b)

    def test_inputs_differing_only_by_dict_value_type(self) -> None:
        a = {"k": "1"}
        b = {"k": 1}
        assert hash_v0("d", a) != hash_v0("d", b)


# -----------------------------------------------------------------------------
# C. encode_uvarint / encode_bytes — boundary chaos.
# -----------------------------------------------------------------------------


class TestUvarintEncoding:
    def test_zero_encodes_to_single_zero_byte(self) -> None:
        assert encode_uvarint(0) == b"\x00"

    def test_max_single_byte(self) -> None:
        assert encode_uvarint(0x7F) == b"\x7f"

    def test_min_two_byte(self) -> None:
        # 0x80 needs two bytes.
        out = encode_uvarint(0x80)
        assert len(out) == 2
        assert out == b"\x80\x01"

    def test_rejects_negative_values(self) -> None:
        with pytest.raises(ValueError, match="non-negative"):
            encode_uvarint(-1)

    def test_rejects_boolean_input(self) -> None:
        with pytest.raises(ValueError, match="non-negative"):
            encode_uvarint(True)  # type: ignore[arg-type]

    def test_rejects_float_input(self) -> None:
        with pytest.raises(ValueError, match="non-negative"):
            encode_uvarint(1.0)  # type: ignore[arg-type]

    def test_rejects_string_input(self) -> None:
        with pytest.raises(ValueError, match="non-negative"):
            encode_uvarint("1")  # type: ignore[arg-type]

    def test_at_max_bit_boundary_passes(self) -> None:
        # Exactly MAX_UVARINT_BITS should still encode.
        n = (1 << MAX_UVARINT_BITS) - 1  # all bits set, MAX bits long
        assert encode_uvarint(n)  # no exception

    def test_one_bit_past_max_rejected(self) -> None:
        n = 1 << MAX_UVARINT_BITS  # MAX+1 bit length
        with pytest.raises(ValueError, match="exceeds.*-bit limit"):
            encode_uvarint(n)

    def test_uvarint_round_trip_through_decode(self) -> None:
        # Quick check that uvarint encoding is self-consistent.
        for n in [0, 1, 127, 128, 255, 16384, 2**20, 2**100]:
            encoded = encode_uvarint(n)
            decoded = 0
            shift = 0
            for byte in encoded:
                decoded |= (byte & 0x7F) << shift
                if not (byte & 0x80):
                    break
                shift += 7
            assert decoded == n


class TestEncodeBytes:
    def test_empty_bytes_encodes_length_prefix(self) -> None:
        assert encode_bytes(b"") == b"\x00"

    def test_short_bytes_round_trip(self) -> None:
        out = encode_bytes(b"hello")
        assert out == b"\x05hello"

    def test_rejects_string_input(self) -> None:
        with pytest.raises(TypeError, match="value must be bytes"):
            encode_bytes("hello")  # type: ignore[arg-type]

    def test_rejects_int_input(self) -> None:
        with pytest.raises(TypeError, match="value must be bytes"):
            encode_bytes(123)  # type: ignore[arg-type]

    def test_rejects_none_input(self) -> None:
        with pytest.raises(TypeError, match="value must be bytes"):
            encode_bytes(None)  # type: ignore[arg-type]

    def test_accepts_bytearray(self) -> None:
        # bytearray should be accepted (mutable bytes).
        out = encode_bytes(bytearray(b"abc"))
        assert out == b"\x03abc"


# -----------------------------------------------------------------------------
# D. hex_to_bytes_fixed / canonical_hex_fixed_allow_0x — boundary chaos.
# -----------------------------------------------------------------------------


class TestHexToBytesFixed:
    def test_accepts_canonical_form(self) -> None:
        assert hex_to_bytes_fixed("0xabcd", nbytes=2, name="x") == b"\xab\xcd"

    def test_rejects_missing_0x_prefix(self) -> None:
        with pytest.raises(ValueError, match="0x-prefixed"):
            hex_to_bytes_fixed("abcd", nbytes=2, name="x")

    def test_rejects_uppercase_0X_prefix(self) -> None:
        # hex_to_bytes_fixed requires lowercase "0x" exactly.
        with pytest.raises(ValueError, match="0x-prefixed"):
            hex_to_bytes_fixed("0Xabcd", nbytes=2, name="x")

    def test_rejects_mixed_case_hex_body(self) -> None:
        with pytest.raises(ValueError, match="valid hex"):
            hex_to_bytes_fixed("0xAbCd", nbytes=2, name="x")

    def test_rejects_wrong_length_short(self) -> None:
        with pytest.raises(ValueError, match="0x-prefixed"):
            hex_to_bytes_fixed("0xab", nbytes=2, name="x")

    def test_rejects_wrong_length_long(self) -> None:
        with pytest.raises(ValueError, match="0x-prefixed"):
            hex_to_bytes_fixed("0xabcdef", nbytes=2, name="x")

    def test_rejects_non_hex_chars(self) -> None:
        with pytest.raises(ValueError, match="valid hex"):
            hex_to_bytes_fixed("0xgh", nbytes=1, name="x")

    def test_rejects_zero_nbytes(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            hex_to_bytes_fixed("0x", nbytes=0, name="x")

    def test_rejects_negative_nbytes(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            hex_to_bytes_fixed("0xab", nbytes=-1, name="x")

    def test_rejects_bool_nbytes(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            hex_to_bytes_fixed("0xab", nbytes=True, name="x")  # type: ignore[arg-type]

    def test_rejects_bytes_input(self) -> None:
        with pytest.raises(TypeError, match="must be a str"):
            hex_to_bytes_fixed(b"0xabcd", nbytes=2, name="x")  # type: ignore[arg-type]

    def test_rejects_with_leading_whitespace(self) -> None:
        # hex_to_bytes_fixed is strict: no whitespace tolerance.
        with pytest.raises(ValueError):
            hex_to_bytes_fixed(" 0xabcd", nbytes=2, name="x")

    def test_rejects_with_trailing_whitespace(self) -> None:
        with pytest.raises(ValueError):
            hex_to_bytes_fixed("0xabcd ", nbytes=2, name="x")


class TestCanonicalHexFixedAllow0x:
    def test_lowercases_uppercase_input(self) -> None:
        assert canonical_hex_fixed_allow_0x("0xABCD", nbytes=2, name="x") == "0xabcd"

    def test_adds_0x_prefix_when_missing(self) -> None:
        assert canonical_hex_fixed_allow_0x("abcd", nbytes=2, name="x") == "0xabcd"

    def test_strips_leading_whitespace(self) -> None:
        # Note: canonical_hex_fixed_allow_0x calls .strip() before checking prefix.
        # This is intentional but the chaos test confirms behavior.
        assert canonical_hex_fixed_allow_0x("  0xabcd  ", nbytes=2, name="x") == "0xabcd"

    def test_handles_0X_uppercase_prefix(self) -> None:
        # `lower().startswith("0x")` so 0X is normalised.
        assert canonical_hex_fixed_allow_0x("0XABCD", nbytes=2, name="x") == "0xabcd"

    def test_rejects_wrong_length(self) -> None:
        with pytest.raises(ValueError, match="bytes"):
            canonical_hex_fixed_allow_0x("0xabc", nbytes=2, name="x")

    def test_rejects_non_hex(self) -> None:
        with pytest.raises(ValueError, match="valid hex"):
            canonical_hex_fixed_allow_0x("0xZZZZ", nbytes=2, name="x")

    def test_rejects_empty_string(self) -> None:
        with pytest.raises(ValueError, match="bytes"):
            canonical_hex_fixed_allow_0x("", nbytes=2, name="x")

    def test_rejects_just_0x(self) -> None:
        with pytest.raises(ValueError, match="bytes"):
            canonical_hex_fixed_allow_0x("0x", nbytes=2, name="x")

    def test_rejects_non_string(self) -> None:
        with pytest.raises(TypeError):
            canonical_hex_fixed_allow_0x(b"0xabcd", nbytes=2, name="x")  # type: ignore[arg-type]


# -----------------------------------------------------------------------------
# E. bounded_json_utf8_size — DoS resistance.
# -----------------------------------------------------------------------------


class TestBoundedJsonUtf8Size:
    def test_simple_size_estimation(self) -> None:
        size = bounded_json_utf8_size({"a": 1}, max_bytes=1000)
        # Actual size: {"a":1} = 7 bytes.
        assert size >= len(canonical_json_bytes({"a": 1}))

    def test_rejects_when_over_budget(self) -> None:
        # Force a budget too small to fit a non-trivial structure.
        with pytest.raises(ValueError, match="exceeds max_bytes"):
            bounded_json_utf8_size({"a" * 100: "x" * 1000}, max_bytes=10)

    def test_rejects_nesting_over_depth(self) -> None:
        nested: Any = {}
        cursor: Any = nested
        for _ in range(70):
            cursor["k"] = {}
            cursor = cursor["k"]
        with pytest.raises(ValueError, match="max_depth"):
            bounded_json_utf8_size(nested, max_bytes=10**9, max_depth=64)

    def test_rejects_items_over_count(self) -> None:
        big_list = list(range(10))
        with pytest.raises(ValueError, match="max_items"):
            bounded_json_utf8_size(big_list, max_bytes=10**9, max_items=3)

    def test_rejects_float(self) -> None:
        with pytest.raises(TypeError, match="floats"):
            bounded_json_utf8_size({"a": 1.5}, max_bytes=100)

    def test_rejects_surrogate(self) -> None:
        with pytest.raises(TypeError, match="surrogate"):
            bounded_json_utf8_size({"a": "\ud800"}, max_bytes=100)

    def test_rejects_nonstring_dict_key(self) -> None:
        with pytest.raises(TypeError, match="dict keys"):
            bounded_json_utf8_size({1: "x"}, max_bytes=100)

    def test_rejects_invalid_max_bytes(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            bounded_json_utf8_size({"a": 1}, max_bytes=0)
        with pytest.raises(ValueError, match="positive int"):
            bounded_json_utf8_size({"a": 1}, max_bytes=-1)
        with pytest.raises(ValueError, match="positive int"):
            bounded_json_utf8_size({"a": 1}, max_bytes=True)  # type: ignore[arg-type]


# -----------------------------------------------------------------------------
# F. sha256_hex / canonical_json_bytes_v0 — sanity.
# -----------------------------------------------------------------------------


class TestSha256Hex:
    def test_returns_canonical_form(self) -> None:
        h = sha256_hex(b"")
        assert h.startswith("0x")
        assert len(h) == 2 + 64
        # SHA-256 of empty string.
        assert h == "0x" + "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

    def test_deterministic(self) -> None:
        h1 = sha256_hex(b"hello")
        h2 = sha256_hex(b"hello")
        assert h1 == h2

    def test_rejects_string_input(self) -> None:
        # sha256_hex expects bytes.
        with pytest.raises(TypeError):
            sha256_hex("hello")  # type: ignore[arg-type]

    def test_rejects_none_input(self) -> None:
        with pytest.raises(TypeError):
            sha256_hex(None)  # type: ignore[arg-type]


class TestCanonicalJsonBytesV0Wrapper:
    def test_wrapper_matches_underlying_canonical_function(self) -> None:
        v = {"a": 1, "b": [2, 3], "c": {"d": True}}
        assert canonical_json_bytes_v0(v) == canonical_json_bytes(v)


# -----------------------------------------------------------------------------
# G. merkle_root_v0 — chaos at the tree boundary.
# -----------------------------------------------------------------------------


class TestMerkleRootV0:
    @staticmethod
    def _leaf(b: int) -> str:
        return "0x" + f"{b:02x}" * 32

    def test_empty_leaves_is_deterministic(self) -> None:
        # Empty merkle root should be a deterministic constant.
        a = merkle_root_v0("d", [])
        b = merkle_root_v0("d", [])
        assert a == b

    def test_single_leaf(self) -> None:
        out = merkle_root_v0("d", [self._leaf(0xAB)])
        assert out.startswith("0x")

    def test_two_leaves_differs_from_one(self) -> None:
        a = merkle_root_v0("d", [self._leaf(0x01)])
        b = merkle_root_v0("d", [self._leaf(0x01), self._leaf(0x02)])
        assert a != b

    def test_three_leaves_differs_from_two(self) -> None:
        # Odd leaf count needs padding handling. Different from 2 leaves.
        two = merkle_root_v0("d", [self._leaf(0x01), self._leaf(0x02)])
        three = merkle_root_v0("d", [self._leaf(0x01), self._leaf(0x02), self._leaf(0x03)])
        assert two != three

    def test_order_matters(self) -> None:
        a = merkle_root_v0("d", [self._leaf(0x01), self._leaf(0x02)])
        b = merkle_root_v0("d", [self._leaf(0x02), self._leaf(0x01)])
        assert a != b

    def test_duplicate_leaves_distinct_from_single(self) -> None:
        single = merkle_root_v0("d", [self._leaf(0x01)])
        duplicate = merkle_root_v0("d", [self._leaf(0x01), self._leaf(0x01)])
        assert single != duplicate

    def test_different_domains_diverge(self) -> None:
        a = merkle_root_v0("d1", [self._leaf(0x01)])
        b = merkle_root_v0("d2", [self._leaf(0x01)])
        assert a != b

    def test_rejects_uppercase_hex_leaf(self) -> None:
        # ROOT canonical form is lowercase 0x-prefixed.
        with pytest.raises(ValueError):
            merkle_root_v0("d", [self._leaf(0x01).upper()])

    def test_rejects_short_leaf(self) -> None:
        with pytest.raises(ValueError):
            merkle_root_v0("d", ["0xab"])

    def test_rejects_missing_prefix_leaf(self) -> None:
        with pytest.raises(ValueError):
            merkle_root_v0("d", ["ab" * 32])

    def test_rejects_non_string_leaf(self) -> None:
        with pytest.raises((TypeError, ValueError)):
            merkle_root_v0("d", [b"\xab" * 32])  # type: ignore[list-item]

    def test_rejects_invalid_domain(self) -> None:
        with pytest.raises(ValueError, match="unsupported characters"):
            merkle_root_v0("bad domain", [])

    def test_rejects_non_sequence_input(self) -> None:
        with pytest.raises(TypeError):
            merkle_root_v0("d", "leaves")  # type: ignore[arg-type]

    def test_rejects_bytes_as_sequence_input(self) -> None:
        # bytes is technically a Sequence but should be rejected per docstring.
        with pytest.raises(TypeError):
            merkle_root_v0("d", b"abcd")  # type: ignore[arg-type]


# -----------------------------------------------------------------------------
# H. Version pinning — guards against accidental constant drift.
# -----------------------------------------------------------------------------


class TestVersionPinning:
    """If anyone bumps these constants, mutmut won't catch it but this will."""

    def test_canonical_encoding_version_pinned(self) -> None:
        # If this fails, every prior hash commitment is invalidated.
        assert CANONICAL_ENCODING_VERSION == 1

    def test_ledger_root_version_pinned(self) -> None:
        assert LEDGER_ROOT_VERSION == 1

    def test_max_uvarint_bits_pinned(self) -> None:
        assert MAX_UVARINT_BITS == 256

    def test_domain_sep_format_pinned(self) -> None:
        # The literal byte format `zenodex:LABEL:vN\x00`.
        out = domain_sep_bytes("x", version=1)
        assert out == b"zenodex:x:v1\x00"

    def test_sha256_hex_format_pinned(self) -> None:
        # Must be 0x + 64 lowercase hex chars.
        h = sha256_hex(b"abc")
        assert h == "0x" + "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

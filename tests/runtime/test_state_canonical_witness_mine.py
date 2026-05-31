"""Symbolic disaster-witness mine for the ZenoDEX canonical *encoders*.

`src/state/canonical.py` holds the consensus-/audit-critical canonical encoding
primitives that feed state-root hashing, signing preimages, and the Tau-spec
bridge. If any of these encoders is non-deterministic, non-idempotent, or
NON-INJECTIVE on its accepted domain, two genuinely-distinct states can share a
single canonical preimage -> a single state-root -> a CONSENSUS SPLIT / replay
forgery (the state-root-collision disaster class).

This `hypothesis` mine searches each public encoder for a collision witness for
the disaster class:

    CANONICAL ENCODER COLLISION / NON-DETERMINISM
      (a) DETERMINISTIC: canon(x) == canon(x) on repeated calls.
      (b) IDEMPOTENT (where canon's codomain ⊆ its domain, i.e. the hex
          canonicalizer): canon(canon(x)) == canon(x).
      (c) INJECTIVE on accepted inputs: two DISTINCT accepted values never
          produce the SAME canonical form.

Encoders mined:
  * canonical_json_bytes        — injective over the *JSON value model*
                                  (null/bool/int/str/array/object-with-str-keys),
                                  determinism, key-order independence, no-mutation.
  * canonical_hex_fixed_allow_0x — idempotent, deterministic, and injective
                                  *modulo* the documented case/0x-prefix/whitespace
                                  normalization (no two DIFFERENT hex bodies collide).
  * encode_uvarint / encode_bytes — length-prefix framing injectivity.
  * domain_sep_bytes            — (label,version) framing injectivity.

A clean run over thousands of generated values is a bounded NEGATIVE receipt for
this disaster class on the canonical-encoder surface.

SCOPE / NON-CLAIMS:
  * NOT covered: composition with the state_root framing layer (that has its own
    proof in tests/runtime/test_state_root_injectivity_proof.py), cross-module
    sequencing, the Rust shadow differential, or SHA-256 collision resistance
    (sha256_hex is just hashlib).
  * KNOWN, INTENDED many-to-one behaviors that are NOT treated as findings:
      - canonical_json_bytes maps a Python `list` and a Python `tuple` with equal
        elements to the same JSON array (both are the SAME JSON value); the mine
        therefore generates lists only and reasons over the JSON value model, not
        the Python type domain.
      - canonical_hex_fixed_allow_0x intentionally accepts mixed case / optional
        `0x` / surrounding whitespace and folds them to one form; the injectivity
        claim is "no two DIFFERENT hex bodies collide", verified via a normalize()
        model.
  * No crypto is exercised here, so no signature oracle is needed
    (crypto_oracle_stubbed = false).
"""

from __future__ import annotations

import pytest

hypothesis = pytest.importorskip("hypothesis")
from hypothesis import given, settings  # noqa: E402
from hypothesis import strategies as st  # noqa: E402

from src.state import canonical as m  # noqa: E402


# ==========================================================================
# JSON value model
# ==========================================================================
# We mine canonical_json_bytes over the abstract JSON value space, not the
# Python type domain. Each generated leaf/container is a pair:
#     (py_value, jid)
# where `py_value` is what we feed the encoder and `jid` is a *hashable,
# canonical JSON identity* used to decide whether two values are genuinely
# distinct JSON values. This sidesteps Python's `True == 1` / `False == 0`
# foot-gun (the encoder over-distinguishes those — emits `true` vs `1` — which
# is harmless and NOT a collision) and the list/tuple identity caveat (we never
# generate tuples).


def _jstrings():
    # ASCII + a few unicode + control/escape chars; NO surrogates (rejected).
    return st.text(
        alphabet=st.characters(
            min_codepoint=0x20,
            max_codepoint=0x2FF,
            blacklist_categories=("Cs",),  # exclude surrogates
        ),
        max_size=4,
    )


def _json_leaf():
    none = st.just((None, ("null",)))
    booly = st.booleans().map(lambda b: (b, ("bool", b)))
    inty = st.integers(min_value=-(2**40), max_value=2**40).map(
        lambda n: (n, ("int", n))
    )
    stry = _jstrings().map(lambda s: (s, ("str", s)))
    return st.one_of(none, booly, inty, stry)


def _json_value(max_leaves: int = 12, max_depth: int = 3):
    def extend(children):
        arr = st.lists(children, max_size=4).map(
            lambda items: (
                [v for v, _ in items],
                ("arr", tuple(j for _, j in items)),
            )
        )
        # Object keys are str (the only key type the encoder accepts).
        obj = st.dictionaries(_jstrings(), children, max_size=4).map(
            lambda d: (
                {k: v for k, (v, _j) in d.items()},
                ("obj", tuple(sorted((k, j) for k, (_v, j) in d.items()))),
            )
        )
        return st.one_of(arr, obj)

    return st.recursive(_json_leaf(), extend, max_leaves=max_leaves).filter(
        lambda pj: pj[1] != ()  # never the degenerate empty identity
    )


# ==========================================================================
# Invariant helpers (factored out so the teeth test can re-use them).
# `encode` is injected so the teeth test can plant a buggy encoder.
# ==========================================================================


def _assert_json_no_collision(encode, a_py, a_jid, b_py, b_jid):
    """Disaster check for canonical_json_bytes: if two values are DISTINCT JSON
    values (different identities) they must NOT share canonical bytes; and equal
    JSON values must share canonical bytes (well-definedness).

    Raises AssertionError on a state-root-collision witness or a determinism
    break. `encode` is the encoder under test (injected for the teeth test)."""
    ea = encode(a_py)
    eb = encode(b_py)
    # determinism: repeated call is byte-identical
    assert encode(a_py) == ea, f"NON-DETERMINISTIC encode of {a_py!r}"
    if a_jid == b_jid:
        # well-defined: same JSON value -> same canonical bytes (key-order indep.)
        assert ea == eb, (
            f"CANON NON-DETERMINISM: equal JSON value {a_jid!r} produced "
            f"different bytes {ea!r} vs {eb!r}"
        )
    else:
        assert ea != eb, (
            f"STATE-ROOT COLLISION: distinct JSON values {a_jid!r} and {b_jid!r} "
            f"share canonical bytes {ea!r}"
        )


def _normalize_hex(s, *, nbytes):
    """The documented normalization model for canonical_hex_fixed_allow_0x:
    strip() -> drop a leading 0x/0X -> require 2*nbytes hex chars -> lowercase.
    Returns the lowercase hex BODY (no 0x), or None if the input is not accepted."""
    if not isinstance(s, str):
        return None
    t = s.strip()
    if t.lower().startswith("0x"):
        t = t[2:]
    if len(t) != 2 * nbytes:
        return None
    if not all(ch in "0123456789abcdefABCDEF" for ch in t):
        return None
    return t.lower()


def _assert_hex_no_collision(canon, a, b, *, nbytes):
    """Disaster check for canonical_hex_fixed_allow_0x: collision iff same body.

    The encoder is injective *modulo* the case/prefix/whitespace normalization,
    so canon(a)==canon(b) MUST coincide exactly with normalize(a)==normalize(b).
    A collision between two DIFFERENT hex bodies is a state-root forgery; a split
    of one body across two outputs is a determinism break."""
    ca = canon(a)
    cb = canon(b)
    assert canon(a) == ca, f"NON-DETERMINISTIC hex canon of {a!r}"
    # idempotence: the canonical form re-canonicalizes to itself
    assert canon(ca) == ca, f"NON-IDEMPOTENT hex canon: canon({ca!r}) != {ca!r}"
    na, nb = _normalize_hex(a, nbytes=nbytes), _normalize_hex(b, nbytes=nbytes)
    # both accepted here by construction
    assert na is not None and nb is not None
    if na == nb:
        assert ca == cb, f"HEX NON-DETERMINISM: same body {na!r} -> {ca!r} vs {cb!r}"
    else:
        assert ca != cb, (
            f"HEX STATE-ROOT COLLISION: different bodies {na!r} != {nb!r} "
            f"share canonical form {ca!r}"
        )
    # output shape contract
    assert ca == "0x" + na, f"hex canon broke its own form: {ca!r} vs 0x{na}"


# ==========================================================================
# TEETH / non-vacuity: a buggy encoder MUST trip each checker.
# ==========================================================================


def test_teeth_buggy_json_encoder_is_caught():
    """Plant two buggy JSON encoders and assert the injectivity/determinism
    checker RAISES. If these passed silently, the negative receipts below would
    be false receipts."""
    import json

    # (1) NON-INJECTIVE encoder: drops the type tag so int 1 and str "1" collide.
    def collide_int_str(v):
        if isinstance(v, str) and v.isdigit():
            return str(int(v)).encode()  # "1" -> b"1"  same as int 1
        return json.dumps(v, separators=(",", ":")).encode()

    with pytest.raises(AssertionError, match="STATE-ROOT COLLISION"):
        _assert_json_no_collision(
            collide_int_str, 1, ("int", 1), "1", ("str", "1")
        )

    # (2) NON-DETERMINISTIC / non-canonical encoder: does NOT sort keys, so the
    # same JSON object presented in two key orders yields different bytes.
    def unsorted(v):
        return json.dumps(v, sort_keys=False, separators=(",", ":")).encode()

    same_jid = ("obj", (("a", ("int", 1)), ("b", ("int", 2))))
    with pytest.raises(AssertionError, match="CANON NON-DETERMINISM"):
        _assert_json_no_collision(
            unsorted, {"a": 1, "b": 2}, same_jid, {"b": 2, "a": 1}, same_jid
        )


def test_teeth_buggy_hex_canon_is_caught():
    """Plant a buggy hex canonicalizer that collapses EVERY body to one form so
    two DIFFERENT bodies collide (state-root forgery), and one that ignores case
    folding so two presentations of the SAME body split (determinism break)."""
    # Collision: collapse every body to all-zeros -> "ab" and "ac" both -> "0x00".
    # (Stays a valid, idempotent form so ONLY the collision check fires.)
    def collapsing(s):
        body = _normalize_hex(s, nbytes=1)
        assert body is not None  # both teeth inputs are accepted
        return "0x00"

    with pytest.raises(AssertionError, match="HEX STATE-ROOT COLLISION"):
        _assert_hex_no_collision(collapsing, "0xab", "0xac", nbytes=1)

    # Determinism break: a case-sensitive canon splits the SAME body "ab"/"AB".
    def case_sensitive(s):
        t = s.strip()
        if t.lower().startswith("0x"):
            t = t[2:]
        return "0x" + t  # keeps original case -> "0xab" vs "0xAB"

    with pytest.raises(AssertionError, match="HEX NON-DETERMINISM"):
        _assert_hex_no_collision(case_sensitive, "0xab", "0xAB", nbytes=1)


# ==========================================================================
# THE MINES (admits only; reject path is safe — no canonical form produced).
# ==========================================================================


@settings(max_examples=1200)
@given(a=_json_value(), b=_json_value())
def test_canonical_json_has_no_collision_witness(a, b):
    a_py, a_jid = a
    b_py, b_jid = b
    # canonical_json_bytes is total over this typed domain (no floats / non-str
    # keys / surrogates generated), so both encode without reject.
    before_a, before_b = repr(a_py), repr(b_py)
    _assert_json_no_collision(m.canonical_json_bytes, a_py, a_jid, b_py, b_jid)
    # purity: encoding must not mutate the inputs (would be a hidden determinism hazard)
    assert repr(a_py) == before_a and repr(b_py) == before_b, "encoder mutated its input"


@settings(max_examples=1000)
@given(data=st.data(), nbytes=st.integers(min_value=1, max_value=8))
def test_canonical_hex_has_no_collision_witness(data, nbytes):
    # Generate two ACCEPTED hex inputs (random body, random case, optional 0x /
    # whitespace) so we only ever exercise the admit path.
    def gen_input():
        body = data.draw(
            st.lists(st.sampled_from("0123456789abcdef"), min_size=2 * nbytes, max_size=2 * nbytes)
        )
        cased = "".join(
            ch.upper() if data.draw(st.booleans()) else ch for ch in body
        )
        prefix = data.draw(st.sampled_from(["0x", "0X", ""]))
        lead = data.draw(st.sampled_from(["", " ", "\t"]))
        trail = data.draw(st.sampled_from(["", " ", "\n"]))
        return lead + prefix + cased + trail

    a, b = gen_input(), gen_input()
    canon = lambda s: m.canonical_hex_fixed_allow_0x(s, nbytes=nbytes, name="x")  # noqa: E731
    _assert_hex_no_collision(canon, a, b, nbytes=nbytes)


@settings(max_examples=1000)
@given(
    xs=st.lists(st.integers(min_value=0, max_value=2**256 - 1), min_size=2, max_size=12, unique=True)
)
def test_uvarint_framing_is_injective(xs):
    """Distinct non-negative ints in range must map to distinct LEB128 bytes
    (the integer-framing half of the state-root preimage)."""
    seen = {}
    for v in xs:
        e = m.encode_uvarint(v)
        assert m.encode_uvarint(v) == e, f"NON-DETERMINISTIC uvarint of {v}"
        assert e not in seen, f"UVARINT COLLISION: {v} and {seen[e]} share {e!r}"
        seen[e] = v


@settings(max_examples=1000)
@given(
    bs=st.lists(st.binary(max_size=12), min_size=2, max_size=12, unique=True)
)
def test_encode_bytes_framing_is_injective(bs):
    """Distinct byte strings must map to distinct length-prefixed encodings (so
    concatenated state sections cannot be re-framed into a colliding preimage)."""
    seen = {}
    for b in bs:
        e = m.encode_bytes(b)
        assert e not in seen, f"ENCODE_BYTES COLLISION: {b!r} and {seen[e]!r} share {e!r}"
        seen[e] = b


@settings(max_examples=800)
@given(
    labels=st.lists(
        st.text(
            alphabet=st.characters(min_codepoint=0x21, max_codepoint=0x7E),  # printable ASCII, no NUL/space-edge
            min_size=1,
            max_size=8,
        ),
        min_size=2,
        max_size=8,
        unique=True,
    ),
    versions=st.lists(st.integers(min_value=1, max_value=999), min_size=1, max_size=4, unique=True),
)
def test_domain_sep_framing_is_injective(labels, versions):
    """Distinct (label, version) pairs must map to distinct domain-separation
    prefixes (so two ledger sub-domains cannot collide their hash namespaces)."""
    seen = {}
    for lab in labels:
        for ver in versions:
            try:
                e = m.domain_sep_bytes(lab, ver)
            except (ValueError, TypeError):
                continue  # rejected label (non-ASCII / NUL) — safe, no prefix produced
            key = (lab, ver)
            assert m.domain_sep_bytes(lab, ver) == e, f"NON-DETERMINISTIC dsep {key}"
            assert e not in seen, (
                f"DOMAIN-SEP COLLISION: {key} and {seen[e]} share prefix {e!r}"
            )
            seen[e] = key

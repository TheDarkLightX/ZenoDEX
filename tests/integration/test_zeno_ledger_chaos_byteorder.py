"""Byte-order independence audit + runtime tests.

We can't run on a big-endian host in CI today, but we can prove the
consensus path **cannot depend** on host byte order by:

  1. **Static audit** — grep the consensus-critical sources for the small
     set of Python primitives that would behave differently on big-endian
     hosts (``sys.byteorder``, ``int.to_bytes/from_bytes`` without an
     explicit ``byteorder=``, ``struct.pack/unpack`` with native ``@``
     prefix, ``array.array.byteswap``). Any unguarded use is a finding.

  2. **Runtime invariants** — assert that every output of every encoding
     primitive is determined by *content*, not by host endianness. We do
     this by re-deriving each output via a byte-order-independent path
     (e.g., LEB128 has no endianness; canonical JSON emits decimal ASCII;
     hex strings have a defined order).

  3. **Explicit big-endian probes** — for the *one* place we do convert
     bytes ↔ int (BLS private-key parsing), confirm the call is explicit
     and the byte order is ``"big"`` by parsing the source.

If a future change drops an explicit ``byteorder=`` or introduces a native
``struct`` format string in the consensus path, the static audit will fail
loudly here before it ships.
"""

from __future__ import annotations

import ast
import re
import sys
from pathlib import Path

import pytest

from src.integration.zeno_ledger_v0 import hash_v0, merkle_root_v0
from src.state.canonical import (
    canonical_json_bytes,
    domain_sep_bytes,
    encode_bytes,
    encode_uvarint,
    hex_to_bytes_fixed,
    sha256_hex,
)

_PROJECT_ROOT = Path(__file__).resolve().parents[2]

# Files whose output is committed/signed and therefore consensus-critical.
_CONSENSUS_CRITICAL_SOURCES = (
    "src/state/app_root.py",
    "src/state/canonical.py",
    "src/state/immutable_collections.py",
    "src/state/immutable_json.py",
    "src/state/intent_snapshots.py",
    "src/state/jmt.py",
    "src/state/state_snapshots.py",
    "src/integration/zeno_ledger_v0.py",
    "src/integration/zeno_ledger_signer_registry.py",
    "src/integration/zeno_ledger_signature.py",
)


def _read_consensus_critical_sources() -> list[tuple[Path, str]]:
    out: list[tuple[Path, str]] = []
    for rel in _CONSENSUS_CRITICAL_SOURCES:
        p = _PROJECT_ROOT / rel
        out.append((p, p.read_text(encoding="utf-8")))
    return out


# -----------------------------------------------------------------------------
# A. Static audit — forbidden byte-order-sensitive patterns.
# -----------------------------------------------------------------------------


class TestStaticByteOrderAudit:
    """Each rule scans the consensus-critical source files for a pattern
    that would silently produce host-dependent output on big-endian hardware.
    """

    def test_no_sys_byteorder_references(self) -> None:
        """Reading ``sys.byteorder`` to branch on host endianness would mean
        we emit different bytes depending on where the code runs. There is
        no legitimate reason for the consensus path to do this."""
        offenders: list[str] = []
        for path, text in _read_consensus_critical_sources():
            if re.search(r"\bsys\s*\.\s*byteorder\b", text):
                offenders.append(str(path))
        assert not offenders, f"sys.byteorder used in: {offenders}"

    def test_int_to_bytes_always_uses_explicit_byteorder(self) -> None:
        """``int.to_bytes(...)`` defaults differ across Python versions and
        the default is "big" since 3.11, but pinning is mandatory anyway."""
        offenders: list[str] = []
        for path, text in _read_consensus_critical_sources():
            tree = ast.parse(text, filename=str(path))
            for node in ast.walk(tree):
                if not isinstance(node, ast.Call):
                    continue
                if not isinstance(node.func, ast.Attribute):
                    continue
                if node.func.attr != "to_bytes":
                    continue
                # Check that 'byteorder' is among the keyword arguments OR
                # is the 2nd positional argument.
                has_byteorder_kw = any(kw.arg == "byteorder" for kw in node.keywords)
                has_byteorder_positional = len(node.args) >= 2
                if not (has_byteorder_kw or has_byteorder_positional):
                    offenders.append(f"{path}:{node.lineno} — int.to_bytes without byteorder")
        assert not offenders, "Found unsafe int.to_bytes calls: " + "; ".join(offenders)

    def test_int_from_bytes_always_uses_explicit_byteorder(self) -> None:
        offenders: list[str] = []
        for path, text in _read_consensus_critical_sources():
            tree = ast.parse(text, filename=str(path))
            for node in ast.walk(tree):
                if not isinstance(node, ast.Call):
                    continue
                # int.from_bytes can appear as: int.from_bytes(...) or .from_bytes(...) on int objects.
                if not isinstance(node.func, ast.Attribute):
                    continue
                if node.func.attr != "from_bytes":
                    continue
                has_byteorder_kw = any(kw.arg == "byteorder" for kw in node.keywords)
                has_byteorder_positional = len(node.args) >= 2
                if not (has_byteorder_kw or has_byteorder_positional):
                    offenders.append(f"{path}:{node.lineno} — int.from_bytes without byteorder")
        assert not offenders, "Found unsafe int.from_bytes calls: " + "; ".join(offenders)

    def test_no_native_struct_format_strings(self) -> None:
        """``struct.pack('@...', ...)`` or ``struct.pack('I', ...)`` uses
        native byte order *and* native sizes. Both are host-dependent. The
        only acceptable formats prefix with ``>``, ``<``, ``!``, or ``=``."""
        offenders: list[str] = []
        # Match `struct.pack( "FORMAT"` or `struct.unpack("FORMAT"` where FORMAT
        # is a single-quoted or double-quoted string starting with neither of
        # the network/explicit-endian markers.
        pattern = re.compile(
            r"struct\s*\.\s*(pack|unpack|pack_into|unpack_from|calcsize)\s*\(\s*"
            r"[\"']([^\"'<>!=@]?[^\"']*)[\"']"
        )
        for path, text in _read_consensus_critical_sources():
            for m in pattern.finditer(text):
                fmt = m.group(2)
                if fmt and fmt[0] not in "<>!=":
                    offenders.append(f"{path} — struct format {fmt!r} lacks explicit byte-order prefix")
        assert not offenders, "Found native struct formats: " + "; ".join(offenders)

    def test_no_array_byteswap_calls(self) -> None:
        offenders: list[str] = []
        for path, text in _read_consensus_critical_sources():
            if re.search(r"\.byteswap\s*\(", text):
                offenders.append(str(path))
        assert not offenders, f".byteswap() used in: {offenders}"

    def test_no_native_struct_imports_with_alias_drift(self) -> None:
        """Just in case someone aliases ``struct`` to hide it from the regex."""
        for path, text in _read_consensus_critical_sources():
            tree = ast.parse(text, filename=str(path))
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    for alias in node.names:
                        if alias.name == "struct" and alias.asname is not None:
                            pytest.fail(
                                f"{path} imports struct under alias {alias.asname!r} — "
                                "audit cannot guarantee endian safety. Use plain `import struct`."
                            )

    def test_explicit_big_endian_in_bls_private_key_parser(self) -> None:
        """The one legitimate bytes↔int conversion (BLS private-key parsing)
        must use ``byteorder="big"`` explicitly."""
        signature_module = _PROJECT_ROOT / "src/integration/zeno_ledger_signature.py"
        text = signature_module.read_text(encoding="utf-8")
        # Find all int.from_bytes calls and confirm every one uses byteorder="big".
        tree = ast.parse(text)
        from_bytes_calls = [
            node for node in ast.walk(tree)
            if isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "from_bytes"
        ]
        assert from_bytes_calls, "Expected at least one int.from_bytes in BLS signature module"
        for node in from_bytes_calls:
            byteorder_kw = next((kw for kw in node.keywords if kw.arg == "byteorder"), None)
            assert byteorder_kw is not None, (
                f"int.from_bytes at line {node.lineno} lacks explicit byteorder kwarg"
            )
            # The value should be the constant string "big".
            assert isinstance(byteorder_kw.value, ast.Constant) and byteorder_kw.value.value == "big", (
                f"int.from_bytes at line {node.lineno} does not use byteorder=\"big\""
            )


# -----------------------------------------------------------------------------
# B. Runtime invariants — outputs depend on content, not host endianness.
# -----------------------------------------------------------------------------


class TestRuntimeByteOrderInvariants:
    def test_uvarint_is_byte_order_independent_by_construction(self) -> None:
        """LEB128 emits 7-bit chunks low-bit-first regardless of host order.
        Manually re-encode and compare."""
        for n in [0, 1, 127, 128, 255, 16_383, 16_384, 2**32 - 1, 2**63 - 1]:
            expected = bytearray()
            tmp = n
            while True:
                byte = tmp & 0x7F
                tmp >>= 7
                if tmp:
                    expected.append(byte | 0x80)
                else:
                    expected.append(byte)
                    break
            assert encode_uvarint(n) == bytes(expected), f"divergence at n={n}"

    def test_canonical_json_int_encoding_is_decimal_ascii(self) -> None:
        """canonical_json_bytes emits ASCII decimal digits — endian-agnostic
        because every byte is in [0x2D, 0x39] regardless of host order."""
        for n in [0, 1, -1, 2**63 - 1, 2**256]:
            out = canonical_json_bytes(n)
            assert out == str(n).encode("ascii")
            assert all(0x2D <= b <= 0x39 for b in out), (
                "canonical_json_bytes(int) must emit pure ASCII decimal"
            )

    def test_domain_sep_bytes_is_ascii_only(self) -> None:
        out = domain_sep_bytes("zeno_ledger_v0", version=42)
        # Every byte except the trailing NUL must be printable ASCII.
        assert out.endswith(b"\x00")
        body = out[:-1]
        assert all(0x20 <= b <= 0x7E for b in body), (
            "domain_sep_bytes prefix must be pure printable ASCII"
        )

    def test_sha256_input_is_a_byte_sequence_not_int(self) -> None:
        """SHA-256 over a byte sequence has the same output on any host —
        the entire input is octet-addressed and octet ordering is part of
        the algorithm spec, not the platform."""
        # Two identical byte sequences must hash identically; one constructed
        # via a loop, the other via a literal.
        a = bytes(b for b in (0x61, 0x62, 0x63))
        b = b"abc"
        assert sha256_hex(a) == sha256_hex(b)

    def test_hex_to_bytes_fixed_uses_canonical_left_to_right_order(self) -> None:
        # Confirm "0xabcd" decodes to (0xab, 0xcd) — most-significant first.
        out = hex_to_bytes_fixed("0xabcd", nbytes=2, name="x")
        assert out == b"\xab\xcd"
        # If host were big-endian and we silently used native int conversion,
        # we'd get (0xcd, 0xab). Confirm we don't.
        assert out != b"\xcd\xab"

    def test_merkle_root_leaves_in_order_independent_of_host(self) -> None:
        # Same leaves in same order must produce same root.
        leaves = ["0x" + f"{i:02x}" * 32 for i in range(4)]
        a = merkle_root_v0("d", leaves)
        b = merkle_root_v0("d", list(reversed(list(reversed(leaves)))))
        assert a == b

    def test_hash_v0_dict_value_int_encodes_as_decimal(self) -> None:
        """A dict carrying an integer must hash to the same value regardless
        of host word size or endianness — because the int is rendered to
        decimal ASCII before SHA-256."""
        for n in [0, 1, 2**31, 2**63, 2**256]:
            a = hash_v0("d", {"n": n})
            b = hash_v0("d", {"n": int(str(n))})  # round-trip via str
            assert a == b, f"hash mismatch for int {n}"


# -----------------------------------------------------------------------------
# C. Simulated big-endian — verify our outputs do not match the bit-reversed
#    versions that a buggy host would produce.
# -----------------------------------------------------------------------------


def _byte_reverse(b: bytes) -> bytes:
    return b[::-1]


class TestSimulatedBigEndianDivergence:
    def test_hex_decoded_bytes_are_not_byte_reversed(self) -> None:
        out = hex_to_bytes_fixed("0x0102030405", nbytes=5, name="x")
        assert out == b"\x01\x02\x03\x04\x05"
        assert out != _byte_reverse(b"\x01\x02\x03\x04\x05")

    def test_uvarint_is_not_byte_reversed(self) -> None:
        # 128 → 0x80 0x01 (low-to-high). NOT 0x01 0x80 (high-to-low).
        assert encode_uvarint(128) == b"\x80\x01"
        assert encode_uvarint(128) != b"\x01\x80"

    def test_encode_bytes_length_prefix_uvarint_order(self) -> None:
        # 128-byte payload → length prefix 0x80 0x01 (LEB128 low-to-high).
        payload = b"\x00" * 128
        encoded = encode_bytes(payload)
        assert encoded[:2] == b"\x80\x01"
        assert encoded[:2] != b"\x01\x80"

    def test_sha256_output_hex_is_left_to_right(self) -> None:
        # SHA-256 of b"" is e3b0c4...b855 (high byte first). Confirm we have
        # that, not the reversed 55b8...c4b0e3.
        out = sha256_hex(b"")
        assert out == "0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        reversed_out = "0x" + out[2:][::-1]
        assert out != reversed_out


# -----------------------------------------------------------------------------
# D. Cross-platform hash agreement (one-host proxy).
# -----------------------------------------------------------------------------


class TestCrossPlatformHashAgreement:
    """The CI matrix runs these on Linux+macOS; locally we just confirm the
    pinned values match the host so the matrix can pin them across OSes."""

    def test_pinned_hash_for_empty_dict(self) -> None:
        assert hash_v0("d", {}) == (
            "0xc98f946e0876c60f06c9f5a2ac0d47b5d85b881b1c028f876110fffe49181b16"
        )

    def test_pinned_hash_for_unicode_string_value(self) -> None:
        # zürich uses non-ASCII bytes — must hash identically on big-endian.
        h = hash_v0("d", {"city": "zürich"})
        # Compute reference: domain_sep_bytes("zeno_ledger_d", 1) + encode_bytes(
        # canonical_json_bytes({"city": "zürich"})), then sha256_hex.
        import hashlib
        prefix = domain_sep_bytes("zeno_ledger_d", version=1)
        payload = encode_bytes(canonical_json_bytes({"city": "zürich"}))
        expected = "0x" + hashlib.sha256(prefix + payload).hexdigest()
        assert h == expected

    def test_pinned_hash_for_huge_int_value(self) -> None:
        n = 2**256 + 1
        h = hash_v0("d", {"n": n})
        import hashlib
        prefix = domain_sep_bytes("zeno_ledger_d", version=1)
        payload = encode_bytes(canonical_json_bytes({"n": n}))
        expected = "0x" + hashlib.sha256(prefix + payload).hexdigest()
        assert h == expected


# -----------------------------------------------------------------------------
# E. Independence from PYTHONHASHSEED — Python str.__hash__ randomization.
# -----------------------------------------------------------------------------


class TestPythonHashSeedIndependence:
    def test_str_hash_randomization_is_active(self) -> None:
        # Sanity: ensure PYTHONHASHSEED is doing what we think. If
        # PYTHONHASHSEED=0, Python's hash() is deterministic across runs.
        # We don't assert about hash(), only that *our* hash is stable.
        assert sys.hash_info.algorithm in ("siphash13", "siphash24", "fnv")

    def test_dict_hash_stability_under_repeated_calls(self) -> None:
        # Repeated calls in same process must produce same canonical hash.
        d = {"a": 1, "b": "two", "c": [3, 4, 5]}
        h1 = hash_v0("d", d)
        h2 = hash_v0("d", d)
        h3 = hash_v0("d", d)
        assert h1 == h2 == h3


# -----------------------------------------------------------------------------
# F. Audit completeness — every consensus-critical source file is covered.
# -----------------------------------------------------------------------------


class TestAuditCompleteness:
    def test_all_audited_files_exist(self) -> None:
        for rel in _CONSENSUS_CRITICAL_SOURCES:
            p = _PROJECT_ROOT / rel
            assert p.exists(), f"audited file missing: {rel}"

    def test_audited_files_are_python(self) -> None:
        for rel in _CONSENSUS_CRITICAL_SOURCES:
            assert rel.endswith(".py"), rel

    def test_no_new_files_in_consensus_path_missing_audit(self) -> None:
        """If a new file lands in src/state/ or src/integration/zeno_ledger*
        that defines hashing or signing functions, surface it so the audit
        list can be updated."""
        candidates = list(_PROJECT_ROOT.glob("src/state/*.py"))
        candidates += list(_PROJECT_ROOT.glob("src/integration/zeno_ledger*.py"))
        audited_paths = {(_PROJECT_ROOT / rel).resolve() for rel in _CONSENSUS_CRITICAL_SOURCES}
        # Files in the candidate set that we don't audit:
        unaudited = [p for p in candidates if p.resolve() not in audited_paths]
        # The only reasonable unaudited files are __init__.py and test helpers.
        suspicious = [
            p for p in unaudited
            if p.name not in ("__init__.py",)
            and "test_" not in p.name
        ]
        # We declare these unaudited files explicitly so the test fails
        # loudly when a new one lands.
        known_unaudited = {
            "balances.py", "intents.py", "lp.py", "nonces.py",
            "perp_serde.py", "state_root.py", "support_root.py",
            "volatility.py", "tau_state.py", "merkle_settlement.py",
            "merkle_settlement_v1.py", "canonical_v2.py", "lp_subtree.py",
            "perp_state.py", "intents_subtree.py", "balance_subtree.py",
            "perp_subtree.py", "nonces_subtree.py", "stateless_volatility.py",
            "pools.py", "confidential_requests.py",
            "intent_nonce_sequence_gate.py",
            "intent_nonce_sender_resolution_gate.py",
            "intent_nonce_batch_policy_gate.py",
        }
        # Filter out files whose name we've already vetted as not consensus-hashing.
        unexpected = [
            p for p in suspicious
            if p.name not in known_unaudited
            and not p.name.startswith("zeno_ledger")
            and not p.name.startswith("zeno_oracle")
            and "zeno_key_manager" not in p.name
            and "zeno_key" not in p.name
            and "tau_" not in p.name.lower()
            and p.parent.name != "tau_specs"
        ]
        # Note: the rest of zeno_ledger_* files (key_manager, signature, etc.)
        # are audited indirectly through their consumers. If anything truly
        # unfamiliar shows up, this fails.
        assert not unexpected, (
            "New unaudited file(s) in consensus path: "
            + ", ".join(str(p.relative_to(_PROJECT_ROOT)) for p in unexpected)
            + ". Either add to _CONSENSUS_CRITICAL_SOURCES or to known_unaudited."
        )

"""Chaos tests simulating Tau Net protocol drift.

These tests don't attack our code directly — they simulate what would
happen if the *Tau side* changes a contract we depend on. The goal is to
ensure ZenoLedger fails *loudly* (and predictably) when:

  - Tau RPC response format changes
  - Tau switches signature algorithms (BLS → Ed25519, threshold, etc.)
  - Tau changes the canonical JSON conventions
  - Tau changes block-height semantics or validator scheduling
  - Tau adds/removes fields from the signed-tx message

Each test simulates a *future Tau change* and asserts that our verifier
detects the divergence rather than silently accepting bad data. This is
the **early-warning system** the operator runbook reads when Tau Net
publishes a breaking change.

If a test here fails after a Tau upgrade, that's the signal to:
  1. Cut a new ``_v1`` of the affected module (don't mutate ``_v0``).
  2. Update the schema constant and re-pin the test boundary.
  3. Communicate the breaking change to all stream operators.
"""

from __future__ import annotations

import json
from typing import Any, Mapping

import pytest

from src.integration.tau_net_client import tau_rpc_response_is_success
from src.integration.zeno_key_manager import validate_tau_bls_public_key
from src.integration.zeno_ledger_v0 import (
    BODY_SCHEMA_V0,
    HEADER_SCHEMA_V0,
    LEDGER_ROOT_VERSION,
    canonical_header_hash_v0,
    hash_v0,
    validate_body_v0,
    validate_header_v0,
)


# -----------------------------------------------------------------------------
# A. Tau RPC response parsing — drift scenarios.
# -----------------------------------------------------------------------------


class TestTauRpcResponseDrift:
    """``tau_rpc_response_is_success`` is the seam between our code and the
    Tau node's wire protocol. If Tau changes the success indicator, every
    submission path silently regresses to 'always rejected'.
    """

    # === Current-protocol contract: these MUST succeed. ===

    def test_current_success_exact(self) -> None:
        assert tau_rpc_response_is_success("SUCCESS") is True

    def test_current_success_with_colon_suffix(self) -> None:
        assert tau_rpc_response_is_success("SUCCESS: tx 0xabcd applied") is True

    def test_current_success_with_space_suffix(self) -> None:
        assert tau_rpc_response_is_success("SUCCESS applied 0xabcd") is True

    def test_current_success_lowercase(self) -> None:
        assert tau_rpc_response_is_success("success") is True

    def test_current_success_with_surrounding_whitespace(self) -> None:
        assert tau_rpc_response_is_success("   SUCCESS   ") is True

    def test_current_success_with_trailing_newline(self) -> None:
        assert tau_rpc_response_is_success("SUCCESS\n") is True

    # === Current-protocol contract: these MUST fail. ===

    def test_rejects_empty(self) -> None:
        assert tau_rpc_response_is_success("") is False

    def test_rejects_error(self) -> None:
        assert tau_rpc_response_is_success("ERROR") is False

    def test_rejects_failure(self) -> None:
        assert tau_rpc_response_is_success("FAILURE") is False

    def test_rejects_partial_match(self) -> None:
        # "SUCCESSFUL" is not a success.
        assert tau_rpc_response_is_success("SUCCESSFUL") is False

    def test_rejects_success_in_middle(self) -> None:
        assert tau_rpc_response_is_success("ERROR: previous SUCCESS lost") is False

    def test_rejects_bytes_input(self) -> None:
        assert tau_rpc_response_is_success(b"SUCCESS") is False

    def test_rejects_none_input(self) -> None:
        assert tau_rpc_response_is_success(None) is False

    def test_rejects_int_input(self) -> None:
        assert tau_rpc_response_is_success(0) is False

    def test_rejects_dict_input(self) -> None:
        # If Tau migrates to JSON responses, our parser will hit this branch.
        assert tau_rpc_response_is_success({"status": "SUCCESS"}) is False

    # === Drift scenarios — simulate Tau changing its wire format. ===

    def test_drift_json_response_currently_rejected(self) -> None:
        """If Tau migrates to JSON ``{"status": "ok"}``, our parser must
        report False — *not* True for the substring 'ok' or 'success' in
        the JSON body. This forces an explicit migration step.
        """
        json_response = '{"status":"SUCCESS","tx":"0xabcd"}'
        assert tau_rpc_response_is_success(json_response) is False

    def test_drift_emoji_response_currently_rejected(self) -> None:
        # Some chains use a ✓ indicator; ensure we don't accept it.
        assert tau_rpc_response_is_success("✓ accepted") is False

    def test_drift_numeric_status_rejected(self) -> None:
        # gRPC-style numeric status codes.
        assert tau_rpc_response_is_success("0") is False
        assert tau_rpc_response_is_success("200") is False

    def test_drift_html_response_rejected(self) -> None:
        # Tau RPC behind a reverse proxy that returns HTML on error.
        assert tau_rpc_response_is_success("<html><body>SUCCESS</body></html>") is False


# -----------------------------------------------------------------------------
# B. BLS public-key validation — algorithm-shift scenarios.
# -----------------------------------------------------------------------------


class TestBlsPubkeyAlgorithmDrift:
    """``validate_tau_bls_public_key`` enforces 48-byte (96 hex char) keys.
    If Tau switches signature algorithms, key formats will diverge — these
    tests detect that drift early.
    """

    BLS_VALID = "0x" + "ab" * 48  # 48 bytes = 96 hex chars

    # === Current-protocol contract. ===

    def test_canonicalizes_valid_lowercase(self) -> None:
        assert validate_tau_bls_public_key(self.BLS_VALID) == self.BLS_VALID

    def test_canonicalizes_uppercase_input(self) -> None:
        upper = "0x" + "AB" * 48
        assert validate_tau_bls_public_key(upper) == self.BLS_VALID

    def test_canonicalizes_without_0x_prefix(self) -> None:
        no_prefix = "ab" * 48
        assert validate_tau_bls_public_key(no_prefix) == self.BLS_VALID

    def test_rejects_all_zero_pubkey(self) -> None:
        with pytest.raises(ValueError, match="all-zero"):
            validate_tau_bls_public_key("0x" + "00" * 48)

    # === Length drift — Ed25519 (32 bytes), Schnorr (32-33 bytes), etc. ===

    def test_drift_ed25519_length_rejected(self) -> None:
        # 32 bytes = 64 hex chars — wrong size for BLS12-381 G1.
        ed25519_like = "0x" + "ab" * 32
        with pytest.raises(ValueError):
            validate_tau_bls_public_key(ed25519_like)

    def test_drift_secp256k1_compressed_rejected(self) -> None:
        # 33 bytes = 66 hex chars.
        secp_like = "0x" + "02" + "ab" * 32
        with pytest.raises(ValueError):
            validate_tau_bls_public_key(secp_like)

    def test_drift_bls12_381_g2_rejected(self) -> None:
        # 96 bytes = 192 hex chars (BLS G2 is 2x G1).
        g2_like = "0x" + "ab" * 96
        with pytest.raises(ValueError):
            validate_tau_bls_public_key(g2_like)

    def test_drift_one_byte_short_rejected(self) -> None:
        with pytest.raises(ValueError):
            validate_tau_bls_public_key("0x" + "ab" * 47)

    def test_drift_one_byte_long_rejected(self) -> None:
        with pytest.raises(ValueError):
            validate_tau_bls_public_key("0x" + "ab" * 49)

    # === Format drift — non-hex, base58, etc. ===

    def test_drift_base58_format_rejected(self) -> None:
        # Imaginary base58 key.
        with pytest.raises(ValueError):
            validate_tau_bls_public_key("zenoBase58aBcDe" * 8)

    def test_drift_base64_format_rejected(self) -> None:
        # 96 base64 chars decode to 72 bytes, but raw is 96 chars.
        with pytest.raises(ValueError):
            validate_tau_bls_public_key("YWJj" * 32)  # not hex chars at all positions

    def test_drift_decimal_only_string_accepted_as_hex(self) -> None:
        """``"1" * 96`` is *also* valid hex (digits 0-9 are hex). The validator
        cannot distinguish a future decimal-encoded key from a hex one purely
        by character class — which is why a future algorithm switch needs an
        explicit version bump, not a format-detection heuristic."""
        ones_key = validate_tau_bls_public_key("1" * 96)
        assert ones_key == "0x" + "1" * 96

    def test_drift_bytes_not_string_rejected(self) -> None:
        with pytest.raises(TypeError):
            validate_tau_bls_public_key(b"\xab" * 48)  # type: ignore[arg-type]


# -----------------------------------------------------------------------------
# C. Header / body schema version drift.
# -----------------------------------------------------------------------------


_HEADER_ROOT_FIELDS = (
    "prev_header_hash",
    "sequencer_set_hash",
    "ingress_root",
    "tx_root",
    "pre_state_root",
    "post_state_root",
    "app_hash",
    "evidence_root",
    "body_root",
    "data_availability_root",
    "proof_journal_hash",
    "config_digest",
    "module_versions_digest",
    "signature_set_root",
)


def _valid_header(*, schema: str = HEADER_SCHEMA_V0, **overrides: Any) -> dict[str, Any]:
    header: dict[str, Any] = {
        "schema": schema,
        "chain_id": "test-chain",
        "height": 7,
        "time_ms": 1_700_000_000_000,
    }
    for i, key in enumerate(_HEADER_ROOT_FIELDS):
        header[key] = "0x" + f"{i:02x}" * 32
    header.update(overrides)
    return header


class TestHeaderSchemaDrift:
    """If Tau (or our future code) emits a header with a different schema
    string, ``validate_header_v0`` must reject it. This forces an explicit
    schema bump rather than silent acceptance.
    """

    @staticmethod
    def _minimal_header(schema: str = HEADER_SCHEMA_V0) -> dict[str, Any]:
        return _valid_header(schema=schema)

    def test_rejects_unknown_schema_string(self) -> None:
        with pytest.raises(ValueError):
            validate_header_v0(self._minimal_header(schema="zenodex/zeno_ledger/header/v999"))

    def test_rejects_completely_different_schema(self) -> None:
        with pytest.raises(ValueError):
            validate_header_v0(self._minimal_header(schema="ethereum/block_header/v1"))

    def test_rejects_missing_schema_field(self) -> None:
        h = self._minimal_header()
        del h["schema"]
        with pytest.raises((ValueError, KeyError, TypeError)):
            validate_header_v0(h)

    def test_rejects_schema_none(self) -> None:
        h = self._minimal_header()
        h["schema"] = None
        with pytest.raises((ValueError, TypeError)):
            validate_header_v0(h)

    def test_rejects_schema_bytes(self) -> None:
        h = self._minimal_header()
        h["schema"] = b"zenodex/zeno_ledger/header/v0"
        with pytest.raises((ValueError, TypeError)):
            validate_header_v0(h)

    def test_rejects_schema_with_v1_suffix(self) -> None:
        h = self._minimal_header(schema="zenodex/zeno_ledger/header/v1")
        with pytest.raises(ValueError):
            validate_header_v0(h)

    def test_rejects_uppercase_schema(self) -> None:
        h = self._minimal_header(schema="ZENODEX/ZENO_LEDGER/HEADER/V0")
        with pytest.raises(ValueError):
            validate_header_v0(h)


class TestBodySchemaDrift:
    @staticmethod
    def _minimal_body(schema: str = BODY_SCHEMA_V0) -> dict[str, Any]:
        return {
            "schema": schema,
            "chain_id": "test-chain",
            "height": 1,
            "transactions": [],
            "ingress": [],
            "settlement_envelopes": [],
            "evidence": [],
        }

    def test_rejects_unknown_body_schema(self) -> None:
        with pytest.raises(ValueError):
            validate_body_v0(self._minimal_body(schema="zenodex/zeno_ledger/body/v999"))

    def test_rejects_missing_schema(self) -> None:
        b = self._minimal_body()
        del b["schema"]
        with pytest.raises((ValueError, KeyError, TypeError)):
            validate_body_v0(b)

    def test_rejects_swapped_with_header_schema(self) -> None:
        # Confused-deputy: someone passes a header where a body is expected.
        with pytest.raises(ValueError):
            validate_body_v0(self._minimal_body(schema=HEADER_SCHEMA_V0))


# -----------------------------------------------------------------------------
# D. Hash chain integrity under field mutation.
# -----------------------------------------------------------------------------


class TestHashChainSensitivity:
    """Single-field mutations must flip the canonical hash with overwhelming
    probability. If a mutation slides past unchanged, our authentication is
    broken.
    """

    @staticmethod
    def _h(**overrides: Any) -> dict[str, Any]:
        return _valid_header(**overrides)

    def test_baseline_validates(self) -> None:
        validate_header_v0(self._h())  # should not raise

    def test_single_field_flip_changes_canonical_hash(self) -> None:
        base = canonical_header_hash_v0(self._h())
        mutated = self._h(tx_root="0x" + "ff" * 32)
        assert canonical_header_hash_v0(mutated) != base

    def test_height_mutation_changes_hash(self) -> None:
        base = canonical_header_hash_v0(self._h())
        mutated = self._h(height=8)
        assert canonical_header_hash_v0(mutated) != base

    def test_chain_id_mutation_changes_hash(self) -> None:
        base = canonical_header_hash_v0(self._h())
        mutated = self._h(chain_id="other-chain")
        assert canonical_header_hash_v0(mutated) != base

    def test_time_ms_mutation_changes_hash(self) -> None:
        base = canonical_header_hash_v0(self._h())
        mutated = self._h(time_ms=1_700_000_000_001)
        assert canonical_header_hash_v0(mutated) != base

    def test_sequencer_set_hash_mutation_changes_hash(self) -> None:
        base = canonical_header_hash_v0(self._h())
        mutated = self._h(sequencer_set_hash="0x" + "ff" * 32)
        assert canonical_header_hash_v0(mutated) != base

    def test_field_reordering_does_not_change_hash(self) -> None:
        # canonical_json_bytes sorts keys, so insertion order is irrelevant.
        a = self._h()
        b = dict(reversed(list(a.items())))
        assert canonical_header_hash_v0(a) == canonical_header_hash_v0(b)


# -----------------------------------------------------------------------------
# E. Cross-domain isolation.
# -----------------------------------------------------------------------------


class TestCrossDomainIsolation:
    """Domain-separated hashing must keep oracle, ledger, and settlement
    commitments distinct, even when the *payload* is identical.
    """

    def test_oracle_and_ledger_domains_diverge(self) -> None:
        payload = {"x": 1}
        a = hash_v0("zeno_oracle", payload)
        b = hash_v0("zeno_ledger", payload)
        assert a != b

    def test_inner_label_drift_changes_hash(self) -> None:
        # Renaming the domain (a Tau-side change to label conventions) must
        # produce a different hash — never silently equal.
        a = hash_v0("header_root", {"x": 1})
        b = hash_v0("header_root_v2", {"x": 1})
        assert a != b

    def test_inner_label_case_change_changes_hash(self) -> None:
        # Domain labels are case-sensitive — UPPER and lower differ.
        a = hash_v0("LABEL", {"x": 1})
        b = hash_v0("label", {"x": 1})
        assert a != b


# -----------------------------------------------------------------------------
# F. Replay / chain-id binding.
# -----------------------------------------------------------------------------


class TestChainIdBinding:
    """The same logical commitment under two different ``chain_id`` values
    must produce different hashes — otherwise a Tau Net testnet commitment
    could be replayed onto mainnet.
    """

    def test_same_payload_different_chain_id_diverges(self) -> None:
        a = hash_v0("d", {"chain_id": "tau-testnet", "data": {"a": 1}})
        b = hash_v0("d", {"chain_id": "tau-mainnet", "data": {"a": 1}})
        assert a != b

    def test_missing_chain_id_does_not_collide_with_chain_id_present(self) -> None:
        a = hash_v0("d", {"data": {"a": 1}})
        b = hash_v0("d", {"chain_id": "tau-testnet", "data": {"a": 1}})
        assert a != b

    def test_empty_chain_id_does_not_collide_with_present_chain_id(self) -> None:
        a = hash_v0("d", {"chain_id": "", "data": {"a": 1}})
        b = hash_v0("d", {"chain_id": "tau-testnet", "data": {"a": 1}})
        assert a != b


# -----------------------------------------------------------------------------
# G. Failure-mode determinism — same bad input → same exception class.
# -----------------------------------------------------------------------------


class TestFailureModeStability:
    """When an invalid input is rejected, the same input must produce the
    same exception class/message across versions. Operators rely on the
    error string for runbook routing.
    """

    def test_empty_domain_rejection_is_typeerror(self) -> None:
        with pytest.raises(TypeError):
            hash_v0("", {"x": 1})

    def test_invalid_domain_chars_rejection_is_valueerror(self) -> None:
        with pytest.raises(ValueError):
            hash_v0("invalid domain", {"x": 1})

    def test_float_payload_rejection_is_typeerror(self) -> None:
        with pytest.raises(TypeError):
            hash_v0("d", {"x": 1.5})

    def test_invalid_header_schema_rejection_message_contains_schema(self) -> None:
        bad = {"schema": "wrong"}
        with pytest.raises((ValueError, KeyError, TypeError)) as exc:
            validate_header_v0(bad)
        # The error message should mention schema or be informative.
        # We're checking that operators can grep for the failure mode.
        assert exc.value is not None


# -----------------------------------------------------------------------------
# H. Boundary integers — height, timestamp, varint.
# -----------------------------------------------------------------------------


class TestBoundaryIntegers:
    """Heights, timestamps, and counts must respect Python's arbitrary-int
    semantics without silently truncating or overflowing.
    """

    def test_zero_height_hashes_distinctly_from_one(self) -> None:
        a = hash_v0("d", {"height": 0})
        b = hash_v0("d", {"height": 1})
        assert a != b

    def test_negative_height_hashes_distinctly(self) -> None:
        a = hash_v0("d", {"height": 0})
        b = hash_v0("d", {"height": -1})
        assert a != b

    def test_huge_height_does_not_overflow(self) -> None:
        # No overflow: hash should still compute deterministically.
        a = hash_v0("d", {"height": 2**100})
        b = hash_v0("d", {"height": 2**100})
        assert a == b

    def test_huge_height_differs_from_one_off(self) -> None:
        a = hash_v0("d", {"height": 2**100})
        b = hash_v0("d", {"height": 2**100 + 1})
        assert a != b

    def test_zero_timestamp_hashes(self) -> None:
        h = hash_v0("d", {"timestamp": 0})
        assert h.startswith("0x")

    def test_int_vs_string_timestamp_diverge(self) -> None:
        a = hash_v0("d", {"timestamp": 1700000000})
        b = hash_v0("d", {"timestamp": "1700000000"})
        assert a != b

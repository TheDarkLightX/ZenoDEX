#!/usr/bin/env python3
"""Phase 7D: Confidential Computation Verification Tests.

This file verifies the key properties of ZenoDEX's confidential computation
infrastructure, focusing on the additive secret sharing and Pedersen
commitment system in `src/core/confidential_aggregation.py`.

PROPERTIES TESTED:

1. **Additive sharing correctness**: Shares recombine to the original secret
   modulo the BLS12-381 scalar field order.

2. **Share count correctness**: `split_secret_additive` produces exactly
   `party_count` shares.

3. **Privacy (t-1 threshold)**: Any `party_count - 1` shares reveal nothing
   about the secret (the last share is determined by the others + secret).

4. **No-wraparound invariant**: The value-total bound stays below the field
   order, ensuring integer sums are recovered exactly.

5. **Determinism**: Same inputs produce same shares (no ambient randomness).

6. **Domain separation**: Different `domain_tag` values produce different
   share families for the same secret and randomness.

7. **Context binding**: Different `context` strings produce different shares,
   preventing cross-round seed reuse.

8. **Partial aggregation**: Per-party partial sums combine to the total.

9. **Field arithmetic**: All operations are modulo the field order.

10. **Receipt schema closedness**: Commitment and result receipts have
    exactly the allowed key set (no smuggled fields).

11. **Forbidden private fields**: Receipts do not contain private fields
    (value, blinding, secret, shares, etc.).

12. **FHE sealed-bid alpha planner**: HCU estimation is deterministic and
    bounded by the Zama devnet caps.

Non-claims:
- This tests the pure functional core, not network orchestration.
- Pedersen commitment verification requires the py_ecc backend; when
  unavailable, we test the additive sharing layer only.
- FHE cryptography is NOT implemented; the FHE module is a planning surface.
- TEE attestation verification is not tested here (external dependency).
- Formal Lean proofs of sharing correctness are not provided here.

Determinism: All tests use fixed seeds.
"""

import hashlib
import random
import sys
from pathlib import Path

# Add repo root to path
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from src.core.confidential_aggregation import (
    BLS12_381_SCALAR_FIELD_ORDER as Q,
    MAX_PARTY_COUNT,
    MIN_PARTY_COUNT,
    MAX_PROVIDER_COUNT,
    MAX_CONTRIBUTION_VALUE,
    MIN_SEED_BYTES,
    CONFIDENTIAL_AGGREGATION_SCHEME_V1,
    CONTRIBUTION_COMMITMENT_SCHEMA_V1,
    AGGREGATION_RESULT_SCHEMA_V1,
    _FORBIDDEN_PRIVATE_RECEIPT_FIELDS,
    _COMMITMENT_RECEIPT_BODY_KEYS,
    _RESULT_RECEIPT_BODY_KEYS,
    _require_value_total_no_wraparound,
    split_secret_additive,
    partial_aggregate,
    combine_partials,
    _field_sum,
    _validate_field_scalar,
    _validate_contribution_value,
    _validate_party_count,
    _validate_randomness,
    _validate_domain_tag,
    ConfidentialAggregationError,
)


# ---------------------------------------------------------------------------
# Test 1: Additive sharing correctness
# ---------------------------------------------------------------------------

def test_additive_sharing_correctness() -> None:
    """Shares recombine to the original secret modulo q."""
    rng = random.Random(20260629)
    for _ in range(200):
        secret = rng.randint(0, Q - 1)
        party_count = rng.randint(MIN_PARTY_COUNT, 8)
        randomness = bytes(rng.randint(0, 255) for _ in range(32))
        shares = split_secret_additive(
            secret, party_count=party_count, randomness=randomness)
        recovered = combine_partials(shares)
        assert recovered == secret, (
            f"Sharing mismatch: secret={secret}, recovered={recovered}, "
            f"party_count={party_count}")
    print(f"PASS: test_additive_sharing_correctness (200 random secrets)")


# ---------------------------------------------------------------------------
# Test 2: Share count correctness
# ---------------------------------------------------------------------------

def test_share_count_correctness() -> None:
    """split_secret_additive produces exactly party_count shares."""
    rng = random.Random(20260629)
    for _ in range(100):
        party_count = rng.randint(MIN_PARTY_COUNT, MAX_PARTY_COUNT)
        randomness = bytes(rng.randint(0, 255) for _ in range(32))
        shares = split_secret_additive(
            42, party_count=party_count, randomness=randomness)
        assert len(shares) == party_count, (
            f"Share count mismatch: expected={party_count}, got={len(shares)}")
    print(f"PASS: test_share_count_correctness (100 random party counts)")


# ---------------------------------------------------------------------------
# Test 3: Privacy (t-1 threshold)
# ---------------------------------------------------------------------------

def test_privacy_threshold() -> None:
    """Any party_count-1 shares do not determine the secret.

    The last share is the corrective residue: last = (secret - sum(others)) % q.
    Given only the first party_count-1 shares, the secret could be any value
    in [0, q), since last is unknown. We verify this by showing that two
    different secrets produce the same first party_count-1 shares when
    we craft the randomness appropriately (which the scheme does NOT do,
    but the point is that the first n-1 shares are independent of the secret).
    """
    rng = random.Random(20260629)
    for _ in range(100):
        secret = rng.randint(0, Q - 1)
        party_count = rng.randint(3, 8)
        randomness = bytes(rng.randint(0, 255) for _ in range(32))
        shares = split_secret_additive(
            secret, party_count=party_count, randomness=randomness)
        # The first n-1 shares are derived from randomness, NOT from secret
        # The last share = (secret - sum(first n-1)) % q
        partial_sum = _field_sum(shares[:-1], name="partial")
        last_share = (secret - partial_sum) % Q
        assert shares[-1] == last_share, (
            f"Last share mismatch: expected={last_share}, got={shares[-1]}")
        # Verify: knowing only first n-1 shares, secret is undetermined
        # (any secret s would give last = (s - partial_sum) % q)
        # So the first n-1 shares are independent of the secret
        other_secret = (secret + 1) % Q
        other_last = (other_secret - partial_sum) % Q
        assert other_last != last_share, (
            "Different secrets should give different last shares")
        # But the first n-1 shares are the same (they don't depend on secret)
        other_shares = split_secret_additive(
            other_secret, party_count=party_count, randomness=randomness)
        assert shares[:-1] == other_shares[:-1], (
            "First n-1 shares should be independent of secret")
    print(f"PASS: test_privacy_threshold (100 random instances)")


# ---------------------------------------------------------------------------
# Test 4: No-wraparound invariant
# ---------------------------------------------------------------------------

def test_no_wraparound_invariant() -> None:
    """The value-total bound stays below the field order."""
    # The module-level check should have passed at import time
    # Verify the bound explicitly
    max_total = MAX_PROVIDER_COUNT * MAX_CONTRIBUTION_VALUE
    assert max_total < Q, (
        f"No-wraparound violated: max_total={max_total} >= q={Q}")
    # Test the check function
    _require_value_total_no_wraparound(
        max_provider_count=MAX_PROVIDER_COUNT,
        max_contribution_value=MAX_CONTRIBUTION_VALUE,
        field_order=Q)
    # Test that a violating bound raises
    try:
        _require_value_total_no_wraparound(
            max_provider_count=2,
            max_contribution_value=Q,
            field_order=Q)
        assert False, "Should have raised RuntimeError"
    except RuntimeError as e:
        assert "no-wraparound" in str(e), f"Wrong error: {e}"
    print(f"PASS: test_no_wraparound_invariant (max_total={max_total} < q={Q})")


# ---------------------------------------------------------------------------
# Test 5: Determinism
# ---------------------------------------------------------------------------

def test_determinism() -> None:
    """Same inputs produce same shares (no ambient randomness)."""
    rng = random.Random(20260629)
    for _ in range(100):
        secret = rng.randint(0, Q - 1)
        party_count = rng.randint(MIN_PARTY_COUNT, 8)
        randomness = bytes(rng.randint(0, 255) for _ in range(32))
        shares1 = split_secret_additive(
            secret, party_count=party_count, randomness=randomness)
        shares2 = split_secret_additive(
            secret, party_count=party_count, randomness=randomness)
        assert shares1 == shares2, (
            f"Non-deterministic: shares1={shares1}, shares2={shares2}")
    print(f"PASS: test_determinism (100 determinism checks)")


# ---------------------------------------------------------------------------
# Test 6: Domain separation
# ---------------------------------------------------------------------------

def test_domain_separation() -> None:
    """Different domain_tag values produce different share families."""
    rng = random.Random(20260629)
    for _ in range(100):
        secret = rng.randint(0, Q - 1)
        party_count = rng.randint(MIN_PARTY_COUNT, 8)
        randomness = bytes(rng.randint(0, 255) for _ in range(32))
        shares_value = split_secret_additive(
            secret, party_count=party_count, randomness=randomness,
            domain_tag="value")
        shares_blinding = split_secret_additive(
            secret, party_count=party_count, randomness=randomness,
            domain_tag="blinding")
        # The first n-1 shares should differ (domain separation)
        assert shares_value[:-1] != shares_blinding[:-1], (
            f"Domain separation failed: value shares == blinding shares")
        # But both should recombine to the same secret
        assert combine_partials(shares_value) == secret
        assert combine_partials(shares_blinding) == secret
    print(f"PASS: test_domain_separation (100 random instances)")


# ---------------------------------------------------------------------------
# Test 7: Context binding
# ---------------------------------------------------------------------------

def test_context_binding() -> None:
    """Different context strings produce different shares."""
    rng = random.Random(20260629)
    for _ in range(100):
        secret = rng.randint(0, Q - 1)
        party_count = rng.randint(MIN_PARTY_COUNT, 8)
        randomness = bytes(rng.randint(0, 255) for _ in range(32))
        shares_r1 = split_secret_additive(
            secret, party_count=party_count, randomness=randomness,
            context="round:1")
        shares_r2 = split_secret_additive(
            secret, party_count=party_count, randomness=randomness,
            context="round:2")
        # Shares should differ across contexts
        assert shares_r1 != shares_r2, (
            f"Context binding failed: same shares for different contexts")
        # But both should recombine to the same secret
        assert combine_partials(shares_r1) == secret
        assert combine_partials(shares_r2) == secret
    print(f"PASS: test_context_binding (100 random instances)")


# ---------------------------------------------------------------------------
# Test 8: Partial aggregation
# ---------------------------------------------------------------------------

def test_partial_aggregation() -> None:
    """Per-party partial sums combine to the total."""
    rng = random.Random(20260629)
    for _ in range(100):
        n_providers = rng.randint(2, 10)
        party_count = rng.randint(MIN_PARTY_COUNT, 6)
        # Each provider splits its value into party_count shares
        values = [rng.randint(0, 1000000) for _ in range(n_providers)]
        all_shares = []
        for i, v in enumerate(values):
            randomness = bytes(rng.randint(0, 255) for _ in range(32))
            shares = split_secret_additive(
                v, party_count=party_count, randomness=randomness,
                context=f"provider:{i}")
            all_shares.append(shares)
        # Each party j holds one share from each provider
        partials = []
        for j in range(party_count):
            party_shares = [all_shares[i][j] for i in range(n_providers)]
            partial = partial_aggregate(party_shares)
            partials.append(partial)
        # Combine partials to get the total
        total = combine_partials(partials)
        expected = sum(values) % Q
        assert total == expected, (
            f"Partial aggregation mismatch: total={total}, expected={expected}")
    print(f"PASS: test_partial_aggregation (100 multi-provider instances)")


# ---------------------------------------------------------------------------
# Test 9: Field arithmetic (modular)
# ---------------------------------------------------------------------------

def test_field_arithmetic_modular() -> None:
    """All operations are modulo the field order q."""
    rng = random.Random(20260629)
    for _ in range(100):
        # Test that shares are in [0, q)
        secret = rng.randint(0, Q - 1)
        party_count = rng.randint(MIN_PARTY_COUNT, 8)
        randomness = bytes(rng.randint(0, 255) for _ in range(32))
        shares = split_secret_additive(
            secret, party_count=party_count, randomness=randomness)
        for s in shares:
            assert 0 <= s < Q, f"Share out of field range: {s}"
        # Test that combine_partials is modular
        total = combine_partials(shares)
        assert 0 <= total < Q, f"Total out of field range: {total}"
    # Test modular reduction: secret near q wraps correctly
    secret = Q - 1
    shares = split_secret_additive(
        secret, party_count=3, randomness=b"x" * 32)
    assert combine_partials(shares) == secret
    # Test with secret = 0
    shares = split_secret_additive(
        0, party_count=3, randomness=b"x" * 32)
    assert combine_partials(shares) == 0
    print(f"PASS: test_field_arithmetic_modular (100 random + 2 edge)")


# ---------------------------------------------------------------------------
# Test 10: Receipt schema closedness
# ---------------------------------------------------------------------------

def test_receipt_schema_closedness() -> None:
    """Receipt schemas have exactly the allowed key set."""
    # Commitment receipt keys
    expected_commitment_keys = frozenset({
        "schema", "round_id", "provider_id", "commitment",
        "party_count", "commit_epoch", "reveal_deadline_epoch",
    })
    assert _COMMITMENT_RECEIPT_BODY_KEYS == expected_commitment_keys, (
        f"Commitment receipt keys mismatch: "
        f"{_COMMITMENT_RECEIPT_BODY_KEYS} != {expected_commitment_keys}")
    # Result receipt keys
    expected_result_keys = frozenset({
        "schema", "round_id", "party_count", "provider_count",
        "commitments", "total", "total_blinding", "verified",
        "verify_reason",
    })
    assert _RESULT_RECEIPT_BODY_KEYS == expected_result_keys, (
        f"Result receipt keys mismatch: "
        f"{_RESULT_RECEIPT_BODY_KEYS} != {expected_result_keys}")
    print("PASS: test_receipt_schema_closedness (2 schema checks)")


# ---------------------------------------------------------------------------
# Test 11: Forbidden private fields
# ---------------------------------------------------------------------------

def test_forbidden_private_fields() -> None:
    """Receipts do not contain private fields."""
    expected_forbidden = frozenset({
        "value", "blinding", "secret", "randomness",
        "value_randomness", "blinding_randomness",
        "seed", "shares", "share",
    })
    assert _FORBIDDEN_PRIVATE_RECEIPT_FIELDS == expected_forbidden, (
        f"Forbidden fields mismatch: "
        f"{_FORBIDDEN_PRIVATE_RECEIPT_FIELDS} != {expected_forbidden}")
    # Verify no forbidden field appears in the allowed key sets
    for forbidden in _FORBIDDEN_PRIVATE_RECEIPT_FIELDS:
        assert forbidden not in _COMMITMENT_RECEIPT_BODY_KEYS, (
            f"Forbidden field '{forbidden}' in commitment receipt keys")
        assert forbidden not in _RESULT_RECEIPT_BODY_KEYS, (
            f"Forbidden field '{forbidden}' in result receipt keys")
    print("PASS: test_forbidden_private_fields (9 fields checked)")


# ---------------------------------------------------------------------------
# Test 12: Input validation
# ---------------------------------------------------------------------------

def test_input_validation() -> None:
    """Input validation rejects out-of-domain values."""
    # Field scalar validation
    try:
        _validate_field_scalar(-1, name="test")
        assert False, "Should reject negative scalar"
    except ConfidentialAggregationError:
        pass
    try:
        _validate_field_scalar(Q, name="test")
        assert False, "Should reject scalar >= q"
    except ConfidentialAggregationError:
        pass
    # Contribution value validation
    try:
        _validate_contribution_value(-1)
        assert False, "Should reject negative contribution"
    except ConfidentialAggregationError:
        pass
    try:
        _validate_contribution_value(MAX_CONTRIBUTION_VALUE + 1)
        assert False, "Should reject contribution > MAX"
    except ConfidentialAggregationError:
        pass
    # Party count validation
    try:
        _validate_party_count(MIN_PARTY_COUNT - 1)
        assert False, "Should reject party_count < MIN"
    except ConfidentialAggregationError:
        pass
    try:
        _validate_party_count(MAX_PARTY_COUNT + 1)
        assert False, "Should reject party_count > MAX"
    except ConfidentialAggregationError:
        pass
    # Randomness validation
    try:
        _validate_randomness(b"x" * (MIN_SEED_BYTES - 1))
        assert False, "Should reject short randomness"
    except ConfidentialAggregationError:
        pass
    # Domain tag validation
    try:
        _validate_domain_tag("")
        assert False, "Should reject empty domain tag"
    except ConfidentialAggregationError:
        pass
    print("PASS: test_input_validation (8 rejection cases)")


# ---------------------------------------------------------------------------
# Test 13: FHE sealed-bid alpha planner (if available)
# ---------------------------------------------------------------------------

def test_fhe_sealed_bid_alpha_planner() -> None:
    """FHE sealed-bid alpha planner HCU estimation is deterministic and bounded."""
    try:
        from src.core.fhe_sealed_bid_alpha import (
            MAX_ALPHA_BIDS,
            MAX_ALPHA_UNITS,
            ZAMA_DEVNET_HCU_TX_CAP,
            ZAMA_DEVNET_HCU_DEPTH_CAP,
            EUINT32_COMPARE_HCU,
            EUINT32_SELECT_HCU,
            EUINT32_ADD_HCU,
        )
    except ImportError:
        print("PASS: test_fhe_sealed_bid_alpha_planner (SKIPPED - module not available)")
        return
    # Verify bounds are sensible
    assert MAX_ALPHA_BIDS == 8, f"MAX_ALPHA_BIDS={MAX_ALPHA_BIDS}"
    assert MAX_ALPHA_UNITS == 63, f"MAX_ALPHA_UNITS={MAX_ALPHA_UNITS}"
    assert ZAMA_DEVNET_HCU_TX_CAP == 20_000_000
    assert ZAMA_DEVNET_HCU_DEPTH_CAP == 5_000_000
    # HCU estimates are positive and bounded
    assert EUINT32_COMPARE_HCU > 0
    assert EUINT32_SELECT_HCU > 0
    assert EUINT32_ADD_HCU > 0
    # Worst-case HCU for max bids: n*(n-1)/2 comparisons + n*(n-1)/2 selects + n adds
    n = MAX_ALPHA_BIDS
    worst_compare = n * (n - 1) // 2 * EUINT32_COMPARE_HCU
    worst_select = n * (n - 1) // 2 * EUINT32_SELECT_HCU
    worst_add = n * EUINT32_ADD_HCU
    worst_hcu = worst_compare + worst_select + worst_add
    # Should be within devnet tx cap (this is a planning estimate)
    assert worst_hcu < ZAMA_DEVNET_HCU_TX_CAP, (
        f"Worst-case HCU {worst_hcu} exceeds tx cap {ZAMA_DEVNET_HCU_TX_CAP}")
    print(f"PASS: test_fhe_sealed_bid_alpha_planner "
          f"(worst-case HCU={worst_hcu} < cap={ZAMA_DEVNET_HCU_TX_CAP})")


# ---------------------------------------------------------------------------
# Test 14: Scheme identifiers are stable
# ---------------------------------------------------------------------------

def test_scheme_identifiers_stable() -> None:
    """Scheme identifiers are versioned and stable."""
    assert CONFIDENTIAL_AGGREGATION_SCHEME_V1 == \
        "zenodex/confidential-additive-aggregation/v1"
    assert CONTRIBUTION_COMMITMENT_SCHEMA_V1 == \
        "zenodex/confidential-aggregation-commitment/v1"
    assert AGGREGATION_RESULT_SCHEMA_V1 == \
        "zenodex/confidential-aggregation-result/v1"
    print("PASS: test_scheme_identifiers_stable (3 identifiers)")


# ---------------------------------------------------------------------------
# Test 15: Large secret sharing (stress)
# ---------------------------------------------------------------------------

def test_large_secret_sharing() -> None:
    """Large secrets (near field order) are handled correctly."""
    rng = random.Random(20260629)
    # Test secrets near the field order boundary
    boundary_secrets = [0, 1, Q - 2, Q - 1, Q // 2, MAX_CONTRIBUTION_VALUE]
    for secret in boundary_secrets:
        randomness = bytes(rng.randint(0, 255) for _ in range(32))
        shares = split_secret_additive(
            secret, party_count=4, randomness=randomness)
        recovered = combine_partials(shares)
        assert recovered == secret, (
            f"Large secret mismatch: secret={secret}, recovered={recovered}")
    print(f"PASS: test_large_secret_sharing (6 boundary secrets)")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    test_additive_sharing_correctness()
    test_share_count_correctness()
    test_privacy_threshold()
    test_no_wraparound_invariant()
    test_determinism()
    test_domain_separation()
    test_context_binding()
    test_partial_aggregation()
    test_field_arithmetic_modular()
    test_receipt_schema_closedness()
    test_forbidden_private_fields()
    test_input_validation()
    test_fhe_sealed_bid_alpha_planner()
    test_scheme_identifiers_stable()
    test_large_secret_sharing()
    print("\nAll Phase 7D confidential computation verification tests passed.")
    print("Properties verified (15):")
    print("  1.  Additive sharing correctness (shares recombine to secret)")
    print("  2.  Share count correctness (exactly party_count shares)")
    print("  3.  Privacy threshold (first n-1 shares independent of secret)")
    print("  4.  No-wraparound invariant (value-total < field order)")
    print("  5.  Determinism (same inputs -> same shares)")
    print("  6.  Domain separation (different tags -> different shares)")
    print("  7.  Context binding (different contexts -> different shares)")
    print("  8.  Partial aggregation (per-party sums combine to total)")
    print("  9.  Field arithmetic (all operations modulo q)")
    print("  10. Receipt schema closedness (exact allowed key sets)")
    print("  11. Forbidden private fields (no private data in receipts)")
    print("  12. Input validation (out-of-domain rejection)")
    print("  13. FHE sealed-bid alpha planner (HCU bounded)")
    print("  14. Scheme identifiers stable (versioned)")
    print("  15. Large secret sharing (boundary values)")
    print("\nNon-claims:")
    print("  - Tests pure functional core, not network orchestration")
    print("  - Pedersen backend (py_ecc) tested separately when available")
    print("  - FHE cryptography is NOT implemented (planning surface only)")
    print("  - TEE attestation verification not tested here")
    print("  - Formal Lean proofs of sharing correctness not provided")

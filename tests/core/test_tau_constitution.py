# [TESTER] v1
"""Tests for the TAU-CONSTITUTION v1 registry, policy_hash, and receipt binding.

ALWAYS-GREEN deterministic core: no Tau binary required.
"""

from __future__ import annotations

import dataclasses
import hashlib
import re

import pytest

from src.core.tau_constitution import (
    SWAP_EXACT_IN_WITNESS_ENCODING_V1,
    TAU_CONSTITUTION_RECEIPT_SCHEMA,
    ConstitutionEntry,
    ConstitutionReceiptBody,
    SettlementSurface,
    _policy_hash_from_fields,
    all_surfaces,
    bind_constitution_into_receipt,
    constitution_policy_hash,
    get_entry,
    make_constitution_receipt,
    policy_hash_for,
    spec_bytes_sha256,
    validate_constitution_receipt_body,
    verify_constitution_receipt,
)

_HEX_32_RE = re.compile(r"^0x[0-9a-f]{64}$")
_ZERO = "0x" + "00" * 32
_ONE = "0x" + "01" * 32
_TWO = "0x" + "02" * 32


# ---------------------------------------------------------------------------
# (a) Registry integrity
# ---------------------------------------------------------------------------


def test_registry_has_spot_swap_exact_in_entry():
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    assert entry.spec_id == "swap_exact_in_v1"
    assert entry.spec_path.name == "swap_exact_in_v1.tau"
    assert "recommended" in entry.spec_path.parts
    assert entry.gate_output == "o1"
    assert entry.witness_encoding_version == SWAP_EXACT_IN_WITNESS_ENCODING_V1
    assert entry.wired_e2e is True


def test_registry_non_swap_surfaces_are_registry_only():
    for surface in (
        SettlementSurface.SPOT_SWAP_EXACT_OUT,
        SettlementSurface.ADD_LIQUIDITY,
        SettlementSurface.REMOVE_LIQUIDITY,
        SettlementSurface.CREATE_POOL,
    ):
        entry = get_entry(surface)
        assert entry.wired_e2e is False


def test_all_registered_spec_files_exist_and_nonempty():
    for surface in all_surfaces():
        entry = get_entry(surface)
        assert entry.spec_path.exists(), f"missing spec: {entry.spec_path}"
        assert entry.spec_path.stat().st_size > 0, f"empty spec: {entry.spec_path}"


def test_entry_is_frozen_typed():
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    with pytest.raises(dataclasses.FrozenInstanceError):
        entry.spec_id = "tampered"  # type: ignore[misc]


def test_surface_id_property():
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    assert entry.surface_id == "spot_swap_exact_in"


# ---------------------------------------------------------------------------
# (b) policy_hash determinism + shape
# ---------------------------------------------------------------------------


def test_policy_hash_is_0x_32_byte_hash():
    digest = policy_hash_for(SettlementSurface.SPOT_SWAP_EXACT_IN)
    assert _HEX_32_RE.fullmatch(digest), digest


def test_policy_hash_is_deterministic():
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    a = constitution_policy_hash(entry)
    b = constitution_policy_hash(entry)
    assert a == b
    assert a == policy_hash_for(SettlementSurface.SPOT_SWAP_EXACT_IN)


def test_spec_bytes_sha256_matches_raw_file_bytes():
    """policy_hash hashes RAW file bytes — a user can reproduce this exactly."""
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    raw = entry.spec_path.read_bytes()
    expected = "0x" + hashlib.sha256(raw).hexdigest()
    assert spec_bytes_sha256(entry.spec_path) == expected


def test_each_surface_has_distinct_policy_hash():
    hashes = {policy_hash_for(s) for s in all_surfaces()}
    assert len(hashes) == len(all_surfaces())


# ---------------------------------------------------------------------------
# (c) policy_hash binding is REAL: tamper spec bytes / gate / encoding => differs
# ---------------------------------------------------------------------------


def _base_fields():
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    return {
        "surface_id": entry.surface_id,
        "spec_id": entry.spec_id,
        "gate_output": entry.gate_output,
        "witness_encoding_version": entry.witness_encoding_version,
        "spec_bytes_digest": spec_bytes_sha256(entry.spec_path),
    }


def test_policy_hash_changes_when_spec_bytes_change(tmp_path):
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    original = constitution_policy_hash(entry)

    # Mutate one byte of a temp copy of the spec and re-hash the bytes.
    raw = entry.spec_path.read_bytes()
    mutated = bytearray(raw)
    mutated[-2] ^= 0x01  # flip a bit near the end (still inside the file)
    mutated_path = tmp_path / "swap_exact_in_v1_mutated.tau"
    mutated_path.write_bytes(bytes(mutated))

    mutated_entry = dataclasses.replace(entry, spec_path=mutated_path)
    assert constitution_policy_hash(mutated_entry) != original


def test_policy_hash_changes_when_gate_output_changes():
    base = _base_fields()
    h1 = _policy_hash_from_fields(**base)
    h2 = _policy_hash_from_fields(**{**base, "gate_output": "o2"})
    assert h1 != h2


def test_policy_hash_changes_when_witness_encoding_version_changes():
    base = _base_fields()
    h1 = _policy_hash_from_fields(**base)
    h2 = _policy_hash_from_fields(
        **{**base, "witness_encoding_version": "swap_exact_in_v1/REENCODED"}
    )
    assert h1 != h2


def test_policy_hash_changes_when_spec_digest_changes():
    base = _base_fields()
    h1 = _policy_hash_from_fields(**base)
    other = "0x" + "ab" * 32
    h2 = _policy_hash_from_fields(**{**base, "spec_bytes_digest": other})
    assert h1 != h2


# ---------------------------------------------------------------------------
# (d) Receipt body: validate / make / verify round-trip + reject-is-no-op
# ---------------------------------------------------------------------------


def _accept_body() -> ConstitutionReceiptBody:
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    return ConstitutionReceiptBody(
        surface_id=entry.surface_id,
        policy_id=entry.spec_id,
        policy_hash=constitution_policy_hash(entry),
        gate_output=entry.gate_output,
        claimed_verdict=1,
        pre_state_root=_ONE,
        post_state_root=_TWO,
        witness_hash=_ONE,
        accepted=True,
    )


def test_receipt_make_verify_round_trip():
    receipt = make_constitution_receipt(_accept_body())
    ok, code = verify_constitution_receipt(receipt)
    assert ok and code == "ok"
    assert receipt["schema"] == TAU_CONSTITUTION_RECEIPT_SCHEMA


def test_receipt_tampered_hash_fails_verify():
    receipt = make_constitution_receipt(_accept_body())
    receipt["receipt_hash"] = "0x" + "ff" * 32
    ok, code = verify_constitution_receipt(receipt)
    assert not ok and code == "receipt_hash"


def test_receipt_rejected_must_be_no_op():
    """A rejected receipt with post != pre must be invalid (reject-is-no-op)."""
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    body = ConstitutionReceiptBody(
        surface_id=entry.surface_id,
        policy_id=entry.spec_id,
        policy_hash=constitution_policy_hash(entry),
        gate_output=entry.gate_output,
        claimed_verdict=0,
        pre_state_root=_ONE,
        post_state_root=_TWO,  # changed => must be rejected
        witness_hash=_ONE,
        accepted=False,
        rejection_code="verdict_mismatch",
    )
    ok, code = validate_constitution_receipt_body(body.to_dict())
    assert not ok and code == "rejected_state_changed"


def test_receipt_rejected_no_op_is_valid():
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    body = ConstitutionReceiptBody(
        surface_id=entry.surface_id,
        policy_id=entry.spec_id,
        policy_hash=constitution_policy_hash(entry),
        gate_output=entry.gate_output,
        claimed_verdict=0,
        pre_state_root=_ONE,
        post_state_root=_ONE,  # no-op
        witness_hash=_ONE,
        accepted=False,
        rejection_code="verdict_mismatch",
    )
    ok, code = validate_constitution_receipt_body(body.to_dict())
    assert ok and code == "ok"


def test_receipt_bad_verdict_rejected():
    body = _accept_body().to_dict()
    body["claimed_verdict"] = 2
    ok, code = validate_constitution_receipt_body(body)
    assert not ok and code == "claimed_verdict"


def test_receipt_bad_policy_hash_shape_rejected():
    body = _accept_body().to_dict()
    body["policy_hash"] = "not-a-hash"
    ok, code = validate_constitution_receipt_body(body)
    assert not ok and code == "policy_hash"


def test_receipt_accepted_with_rejection_code_rejected():
    body = _accept_body().to_dict()
    body["rejection_code"] = "should_not_be_here"
    ok, code = validate_constitution_receipt_body(body)
    assert not ok and code == "accepted_rejection_code"


def test_receipt_accepted_true_but_verdict_zero_rejected():
    """accepted MUST equal (claimed_verdict == 1) — decoupling is rejected."""
    body = _accept_body().to_dict()
    body["claimed_verdict"] = 0  # accepted stays True => inconsistent
    ok, code = validate_constitution_receipt_body(body)
    assert not ok and code == "accepted_verdict_mismatch"


def test_receipt_accepted_false_but_verdict_one_rejected():
    body = _accept_body().to_dict()
    body["accepted"] = False
    body["post_state_root"] = body["pre_state_root"]  # satisfy no-op
    body["rejection_code"] = "some_reason"
    # claimed_verdict still 1 while accepted False => inconsistent
    ok, code = validate_constitution_receipt_body(body)
    assert not ok and code == "accepted_verdict_mismatch"


def test_receipt_decided_scope_overclaim_rejected():
    """A receipt cannot claim a richer scope than the rule decides."""
    body = _accept_body().to_dict()
    body["decided_scope"] = "pricing_correctness"  # well-formed token, but wrong
    ok, code = validate_constitution_receipt_body(body)
    assert not ok and code == "decided_scope"


def test_receipt_body_is_frozen():
    body = _accept_body()
    with pytest.raises(dataclasses.FrozenInstanceError):
        body.claimed_verdict = 0  # type: ignore[misc]


# ---------------------------------------------------------------------------
# (e) bind_constitution_into_receipt — additive, pure, mirrors batch_cutoff
# ---------------------------------------------------------------------------


def test_bind_constitution_is_additive_and_pure():
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    tx_body = {"tx_hash": _ONE, "status": "applied"}
    bound = bind_constitution_into_receipt(tx_body, entry, 1)
    # input not mutated
    assert "constitution" not in tx_body
    # additive binding present
    c = bound["constitution"]
    assert c["surface_id"] == entry.surface_id
    assert c["policy_id"] == entry.spec_id
    assert c["policy_hash"] == constitution_policy_hash(entry)
    assert c["gate_output"] == entry.gate_output
    assert c["claimed_verdict"] == 1
    assert c["decided_scope"] == "admission_only_not_pricing"
    # original fields preserved
    assert bound["tx_hash"] == _ONE
    assert bound["status"] == "applied"


def test_bind_constitution_rejects_bad_verdict():
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    with pytest.raises(ValueError):
        bind_constitution_into_receipt({}, entry, 5)

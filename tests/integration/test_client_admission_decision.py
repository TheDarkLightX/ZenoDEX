"""Adversarial corpus for the WS2 trustless refuse-by-default client decision.

Covers the ACCEPT path + EVERY stable REFUSE code, including the red-team attacks the
design workflow surfaced: echo/non-pinned verifier, self-cert image, cross-chain replay,
the pre_app_hash_present=false echo bypass, cheap-for-expensive operation replay,
omitted/null binding, weaker-than-required and over- claim levels, Stage-0 not-proof-
gated admission, and the non-trust clause (host asserts verified but ships no proof).
"""

from __future__ import annotations

import copy
from typing import Any, Mapping

import pytest

from src.integration.client_admission_decision import (
    AdmissionDecision,
    ConsensusContract,
    HeadRef,
    OperationPins,
    PinnedRegistry,
    ReceiptVerifierPort,
    ReceiptVerifyResult,
    RefuseCode,
    RequestedOperation,
    VerifierIdentity,
    VerifyStatus,
    decide_admission,
)

# 32-byte fixtures
HEAD = b"H" * 32
POST = b"P" * 32
OP_HASH = b"O" * 32
COLLAT_H = b"C" * 32
ORACLE_H = b"R" * 32
IMAGE = (1, 2, 3, 4, 5, 6, 7, 8)
PROOF_TYPE = "risc0.zenodex_perps_np_transition.v1"
SURFACE, OPERATION = "perps_np", "deposit_collateral"
CLAIM_ORDER = (
    "core_equivalent",
    "modeled_envelope_equivalent",
    "live_replay_authority_equivalent",
    "live_equivalent",
)


def _valid_journal() -> dict[str, Any]:
    return {
        "proof_type": PROOF_TYPE,
        "risc0_image_id": list(IMAGE),
        "chain_id": "devnet",
        "pre_app_hash_present": True,
        "pre_app_hash": HEAD,
        "post_app_hash": POST,
        "operation_hash": OP_HASH,
        "state_hash": b"S" * 32,
        "state_delta_hash": b"D" * 32,
        "collateral_binding_hash": COLLAT_H,
        "oracle_binding_hash": ORACLE_H,
        "participant_set_hash": b"G" * 32,
    }


class _FakeVerifier:
    """A fake receipt verifier port. In production this performs a REAL STARK verify
    against the client-pinned image id; here it returns a scripted result so the pure
    decision core can be exercised exhaustively."""

    def __init__(self, status: VerifyStatus, journal: Mapping[str, Any] | None):
        self._status = status
        self._journal = journal
        self.seen_image_id: tuple[int, ...] | None = None

    def verify_receipt(self, proof_bytes, pinned_image_id, *, blessed_verifier):
        self.seen_image_id = tuple(pinned_image_id)
        return ReceiptVerifyResult(status=self._status, journal=self._journal)


def _rebind(_op: RequestedOperation) -> Mapping[str, bytes]:
    return {"operation_hash": OP_HASH, "collateral_binding_hash": COLLAT_H, "oracle_binding_hash": ORACLE_H}


def _pins(**overrides: Any) -> OperationPins:
    base = dict(
        surface=SURFACE,
        operation=OPERATION,
        pinned_image_id=IMAGE,
        pinned_proof_type=PROOF_TYPE,
        pinned_chain_id="devnet",
        blessed_verifier=VerifierIdentity(expected_cmd_hash="abc123", binary_path="/usr/bin/r0vm", allow_path_lookup=False),
        required_journal_fields=("collateral_binding_hash", "oracle_binding_hash"),
        expected_static={},
        recomputed_fields=("collateral_binding_hash", "oracle_binding_hash"),
        cross_field_equal=(),
        head_equal_fields=(),
        claim_level="live_replay_authority_equivalent",
        ceiling_level="live_replay_authority_equivalent",
        admission_threshold_level="live_replay_authority_equivalent",
        admission_proof_gated_statuses=("bound_proof_required",),
    )
    base.update(overrides)
    return OperationPins(**base)


def _registry(pins: OperationPins | None = None) -> PinnedRegistry:
    p = pins or _pins()
    return PinnedRegistry(by_op={(SURFACE, OPERATION): p})


CLOB_PT = "risc0.zenodex_clob_transition.v1"
LIVE_PT = "risc0.zenodex_live_equiv.v1"


def _contract(
    required: str = "live_replay_authority_equivalent",
    binding_status: str | None = "bound_proof_required",
    level_by_proof_type: Mapping[str, str] | None = None,
) -> ConsensusContract:
    return ConsensusContract(
        claim_levels_order=CLAIM_ORDER,
        required_level_by_op={(SURFACE, OPERATION): required, ("clob", "place_limit_order"): "core_equivalent"},
        admission_binding_status_by_op={(SURFACE, OPERATION): binding_status},
        level_by_proof_type=level_by_proof_type
        or {
            PROOF_TYPE: "live_replay_authority_equivalent",
            CLOB_PT: "core_equivalent",
            LIVE_PT: "live_equivalent",
        },
    )


def _host(journal_present: bool = True, **extra: Any) -> dict[str, Any]:
    h: dict[str, Any] = {}
    if journal_present:
        h["zk_proof"] = b"real-proof-bytes"
    h.update(extra)
    return h


def _decide(
    *,
    host: dict[str, Any] | None = None,
    pins: OperationPins | None = None,
    contract: ConsensusContract | None = None,
    journal: Mapping[str, Any] | None = "DEFAULT",  # type: ignore[assignment]
    status: VerifyStatus = VerifyStatus.VERIFIED,
    head: bytes = HEAD,
    rebind=_rebind,
    surface: str = SURFACE,
    operation: str = OPERATION,
) -> AdmissionDecision:
    j = _valid_journal() if journal == "DEFAULT" else journal
    return decide_admission(
        surface,
        operation,
        host if host is not None else _host(),
        RequestedOperation(surface=surface, operation=operation, fields={"amount_e8": 100, "nonce": 1}),
        HeadRef(surface=surface, current_head=head),
        registry=_registry(pins),
        contract=contract or _contract(),
        verifier=_FakeVerifier(status, j),
        rebind=rebind,
    )


# --------------------------------------------------------------------------- #
# ACCEPT path
# --------------------------------------------------------------------------- #
def test_accept_path() -> None:
    d = _decide()
    assert d.accepted is True
    assert d.refuse_code is None
    assert d.claim_level == "live_replay_authority_equivalent"
    assert d.head_advance is not None
    assert d.head_advance.new_head == POST
    assert d.head_advance.retire_preroot == HEAD
    assert all(d.gate_results.values())


def test_nonprogress_transition_refused_at_gate12() -> None:
    # A transition whose post_app_hash equals the head (== pre, gate 7) does not
    # move the head, so it would re-pass every gate forever and defeat
    # anti-double-accept. Gate 12 refuses it fail-closed.
    journal = _valid_journal()
    journal["post_app_hash"] = HEAD
    d = _decide(journal=journal)
    assert d.accepted is False
    assert d.refuse_code is RefuseCode.HEAD_NONPROGRESS
    assert d.gate_results.get("g12_head_progress") is False
    assert d.head_advance is None


def test_accept_verifies_against_client_pinned_image_not_journal() -> None:
    # The verifier must be asked to verify against the CLIENT pin, never the proof's.
    fake = _FakeVerifier(VerifyStatus.VERIFIED, _valid_journal())
    decide_admission(
        SURFACE, OPERATION, _host(),
        RequestedOperation(surface=SURFACE, operation=OPERATION, fields={}),
        HeadRef(surface=SURFACE, current_head=HEAD),
        registry=_registry(), contract=_contract(), verifier=fake, rebind=_rebind,
    )
    assert fake.seen_image_id == IMAGE


# --------------------------------------------------------------------------- #
# Non-trust clause: host asserts verified but ships no/!= proof
# --------------------------------------------------------------------------- #
def test_host_claims_verified_but_no_proof_refuses() -> None:
    d = _decide(host=_host(journal_present=False, ok=True, proof_status="proof_verified", production_security_claim=True, is_final=True))
    assert d.accepted is False
    assert d.refuse_code is RefuseCode.NO_PROOF


def test_accept_records_tripwire_when_host_asserts_status() -> None:
    d = _decide(host=_host(ok=True, production_security_claim=True))
    assert d.accepted is True  # accepted on our OWN evidence
    assert d.tripwire is not None and "host_asserted_fields_ignored" in d.tripwire


# --------------------------------------------------------------------------- #
# Every REFUSE code (ordered gates)
# --------------------------------------------------------------------------- #
def test_unmapped_operation() -> None:
    d = decide_admission(
        "unknown", "op", _host(),
        RequestedOperation(surface="unknown", operation="op", fields={}),
        HeadRef(surface="unknown", current_head=HEAD),
        registry=_registry(), contract=_contract(), verifier=_FakeVerifier(VerifyStatus.VERIFIED, _valid_journal()), rebind=_rebind,
    )
    assert d.refuse_code is RefuseCode.UNMAPPED_OPERATION


def test_no_proof() -> None:
    assert _decide(host=_host(journal_present=False)).refuse_code is RefuseCode.NO_PROOF


def test_verifier_not_pinned_path_lookup() -> None:
    p = _pins(blessed_verifier=VerifierIdentity(expected_cmd_hash="abc", binary_path="/usr/bin/r0vm", allow_path_lookup=True))
    assert _decide(pins=p).refuse_code is RefuseCode.VERIFIER_NOT_PINNED


def test_verifier_not_pinned_relative_path() -> None:
    p = _pins(blessed_verifier=VerifierIdentity(expected_cmd_hash="abc", binary_path="r0vm", allow_path_lookup=False))
    assert _decide(pins=p).refuse_code is RefuseCode.VERIFIER_NOT_PINNED


@pytest.mark.parametrize("status", [VerifyStatus.FAILED, VerifyStatus.UNKNOWN, VerifyStatus.TIMEOUT, VerifyStatus.ERROR])
def test_receipt_verify_failed_all_non_verified(status: VerifyStatus) -> None:
    # The echo/wrapper attack manifests here: a non-real verifier cannot produce VERIFIED.
    assert _decide(status=status, journal=None).refuse_code is RefuseCode.RECEIPT_VERIFY_FAILED


def test_proof_type_mismatch_cross_surface_reuse() -> None:
    j = _valid_journal()
    j["proof_type"] = "risc0.zenodex_clob_transition.v1"  # a CLOB proof in a perps slot
    assert _decide(journal=j).refuse_code is RefuseCode.PROOF_TYPE_MISMATCH


def test_image_id_zero() -> None:
    j = _valid_journal()
    j["risc0_image_id"] = [0, 0, 0, 0, 0, 0, 0, 0]
    assert _decide(journal=j).refuse_code is RefuseCode.IMAGE_ID_MISMATCH


def test_image_id_mismatch() -> None:
    j = _valid_journal()
    j["risc0_image_id"] = [9, 9, 9, 9, 9, 9, 9, 9]
    assert _decide(journal=j).refuse_code is RefuseCode.IMAGE_ID_MISMATCH


def test_chain_id_mismatch_cross_chain_replay() -> None:
    j = _valid_journal()
    j["chain_id"] = "mainnet"  # genuinely-valid proof from another chain
    assert _decide(journal=j).refuse_code is RefuseCode.CHAIN_ID_MISMATCH


def test_chain_id_empty() -> None:
    j = _valid_journal()
    j["chain_id"] = ""
    assert _decide(journal=j).refuse_code is RefuseCode.CHAIN_ID_MISMATCH


def test_prestate_unbound_present_flag_false_echo_bypass() -> None:
    # The guest skips the pre-root binding when present=False yet echoes pre_app_hash.
    j = _valid_journal()
    j["pre_app_hash_present"] = False  # but pre_app_hash still == HEAD (attacker echo)
    assert _decide(journal=j).refuse_code is RefuseCode.PRESTATE_UNBOUND


def test_prestate_mismatch_stale_head() -> None:
    j = _valid_journal()
    j["pre_app_hash"] = b"X" * 32  # proof from an unrelated/stale pre-state
    assert _decide(journal=j).refuse_code is RefuseCode.PRESTATE_MISMATCH


def test_operation_mismatch_cheap_for_expensive_replay() -> None:
    # A real proof of operation A replayed for the requested operation B.
    j = _valid_journal()
    j["operation_hash"] = b"Z" * 32  # journal binds a different operation
    assert _decide(journal=j).refuse_code is RefuseCode.OPERATION_MISMATCH


def test_operation_mismatch_rebind_returns_nothing() -> None:
    assert _decide(rebind=lambda op: {}).refuse_code is RefuseCode.OPERATION_MISMATCH


def test_binding_incomplete_journal_field_absent() -> None:
    j = _valid_journal()
    del j["oracle_binding_hash"]
    assert _decide(journal=j).refuse_code is RefuseCode.BINDING_INCOMPLETE_OR_NULL


def test_binding_incomplete_expected_null() -> None:
    # rebind omits a required recomputed field -> no trusted expected value.
    def rb(_op: RequestedOperation) -> Mapping[str, bytes]:
        return {"operation_hash": OP_HASH, "collateral_binding_hash": COLLAT_H}  # oracle missing

    assert _decide(rebind=rb).refuse_code is RefuseCode.BINDING_INCOMPLETE_OR_NULL


def test_binding_mismatch() -> None:
    j = _valid_journal()
    j["collateral_binding_hash"] = b"W" * 32  # present but != recomputed
    assert _decide(journal=j).refuse_code is RefuseCode.BINDING_MISMATCH


def test_registry_inconsistent_claim_level() -> None:
    # pins claim live_replay but the contract maps the pinned proof_type to core -> refuse.
    c = _contract(level_by_proof_type={PROOF_TYPE: "core_equivalent"})
    assert _decide(contract=c).refuse_code is RefuseCode.UNMAPPED_OPERATION


def test_claim_too_weak() -> None:
    # The VERIFIED proof_type demonstrates a weaker lane than the operation requires
    # (independent lookups; consistent at gate 0: pinned proof_type's level == claim_level).
    p = _pins(pinned_proof_type=CLOB_PT, claim_level="core_equivalent", ceiling_level="live_replay_authority_equivalent")
    j = {**_valid_journal(), "proof_type": CLOB_PT}
    assert _decide(pins=p, journal=j).refuse_code is RefuseCode.CLAIM_TOO_WEAK


def test_claim_overclaim() -> None:
    p = _pins(pinned_proof_type=LIVE_PT, claim_level="live_equivalent", ceiling_level="live_replay_authority_equivalent")
    j = {**_valid_journal(), "proof_type": LIVE_PT}
    assert _decide(pins=p, journal=j).refuse_code is RefuseCode.CLAIM_OVERCLAIM


def test_admission_below_threshold() -> None:
    # required level below the admission threshold -> not admissible even if proven.
    p = _pins(pinned_proof_type=CLOB_PT, claim_level="core_equivalent", ceiling_level="core_equivalent", admission_threshold_level="live_replay_authority_equivalent")
    j = {**_valid_journal(), "proof_type": CLOB_PT}
    d = _decide(pins=p, journal=j, contract=_contract(required="core_equivalent"))
    assert d.refuse_code is RefuseCode.ADMISSION_NOT_PROOF_GATED


def test_admission_not_bound_stage0() -> None:
    # A genuinely-verified proof for a Stage-0 (not-proof-gated) op is correct-but-not-admissible.
    d = _decide(contract=_contract(binding_status="not_bound_stage0_api_does_not_invoke_guest"))
    assert d.refuse_code is RefuseCode.ADMISSION_NOT_PROOF_GATED


def test_admission_status_none_fails_closed() -> None:
    # The honest current state: no op has a proof-gated admission status -> refuse (not fail-open).
    assert _decide(contract=_contract(binding_status=None)).refuse_code is RefuseCode.ADMISSION_NOT_PROOF_GATED


def test_admission_status_unknown_fails_closed() -> None:
    # An unrecognised/typo status must NOT be treated as admissible.
    assert _decide(contract=_contract(binding_status="bound_someday_typo")).refuse_code is RefuseCode.ADMISSION_NOT_PROOF_GATED


def test_empty_required_fields_refuses() -> None:
    # An empty/incomplete required-field schema would make gate 9 vacuously pass.
    assert _decide(pins=_pins(required_journal_fields=())).refuse_code is RefuseCode.UNMAPPED_OPERATION


def test_requested_operation_surface_mismatch_refuses() -> None:
    d = decide_admission(
        SURFACE, OPERATION, _host(),
        RequestedOperation(surface="other", operation=OPERATION, fields={}),
        HeadRef(surface=SURFACE, current_head=HEAD),
        registry=_registry(), contract=_contract(), verifier=_FakeVerifier(VerifyStatus.VERIFIED, _valid_journal()), rebind=_rebind,
    )
    assert d.refuse_code is RefuseCode.UNMAPPED_OPERATION


def test_head_surface_mismatch_refuses() -> None:
    d = decide_admission(
        SURFACE, OPERATION, _host(),
        RequestedOperation(surface=SURFACE, operation=OPERATION, fields={}),
        HeadRef(surface="other", current_head=HEAD),
        registry=_registry(), contract=_contract(), verifier=_FakeVerifier(VerifyStatus.VERIFIED, _valid_journal()), rebind=_rebind,
    )
    assert d.refuse_code is RefuseCode.UNMAPPED_OPERATION


# --------------------------------------------------------------------------- #
# Reject-is-no-op: every refuse returns no head_advance (no mutation signalled)
# --------------------------------------------------------------------------- #
def test_every_refuse_emits_no_head_advance() -> None:
    refusing = [
        _decide(host=_host(journal_present=False)),
        _decide(status=VerifyStatus.FAILED, journal=None),
        _decide(journal={**_valid_journal(), "chain_id": "mainnet"}),
        _decide(journal={**_valid_journal(), "pre_app_hash_present": False}),
    ]
    for d in refusing:
        assert d.accepted is False
        assert d.head_advance is None
        assert d.claim_level is None
        assert d.refuse_code is not None


def test_first_failure_wins_ordering() -> None:
    # No proof AND a bad chain id -> NO_PROOF wins (earlier gate).
    d = _decide(host=_host(journal_present=False), journal={**_valid_journal(), "chain_id": "mainnet"})
    assert d.refuse_code is RefuseCode.NO_PROOF


# --------------------------------------------------------------------------- #
# Property-based (hypothesis) fuzz: the fail-closed invariants over random input.
# These assert the GLOBAL properties the hand-written cases only sample.
# --------------------------------------------------------------------------- #
from hypothesis import given, settings  # noqa: E402
from hypothesis import strategies as st  # noqa: E402

_HOST_ASSERTED = [
    "ok", "proof_status", "status", "production_security_claim",
    "is_final", "promotion_ready", "artifact_binding_complete", "latest_proven_height",
]
# Fields CHECKED AGAINST A CLIENT-TRUSTED EXPECTED VALUE (pins / head / recomputed).
# Mutating any of these to a non-equal value MUST refuse, even under a (fake) VERIFIED
# journal. This is the set whose integrity does NOT depend on the verifier being real.
#
# Deliberately EXCLUDED: the OUTPUT fields the proof PRODUCES rather than the client
# pins -- post_app_hash (becomes the new head), state_hash, state_delta_hash,
# participant_set_hash. The decision trusts these BECAUSE gate 3 cryptographically
# verified the journal; a real receipt cannot carry a tampered output (it would fail
# receipt.verify). The fake verifier here returns a tampered journal as VERIFIED, so a
# mutated output "passes" -- that is a fake-verifier artifact, exactly the gate-3 /
# real-ReceiptVerifierPort trust root documented in WS2_TRUSTLESS_REFUSE_BY_DEFAULT.md,
# NOT a gap in the decision core. (A wrong post_app_hash also self-corrects: it becomes
# the next transition's pre_app_hash and fails gate 7 on the following step.)
_LOAD_BEARING = [
    "proof_type", "risc0_image_id", "chain_id", "pre_app_hash_present",
    "pre_app_hash", "operation_hash", "collateral_binding_hash", "oracle_binding_hash",
]
_FUZZ_VALUES = st.one_of(
    st.none(), st.booleans(), st.integers(min_value=-3, max_value=1 << 70),
    st.text(max_size=10), st.binary(max_size=40),
    st.lists(st.integers(min_value=0, max_value=9), max_size=10),
)


@given(extra=st.dictionaries(st.sampled_from(_HOST_ASSERTED), _FUZZ_VALUES))
@settings(max_examples=250, deadline=None)
def test_property_host_asserted_fields_never_change_decision(extra: dict) -> None:
    # Non-trust clause: NO host-asserted field, at ANY value, flips the decision.
    baseline = _decide()
    d = _decide(host=_host(**extra))
    assert d.accepted == baseline.accepted is True
    assert d.refuse_code == baseline.refuse_code  # both None


@given(status=st.sampled_from([VerifyStatus.FAILED, VerifyStatus.UNKNOWN, VerifyStatus.TIMEOUT, VerifyStatus.ERROR]),
       journal=st.one_of(st.none(), st.just(_valid_journal())))
@settings(max_examples=50, deadline=None)
def test_property_non_verified_status_never_accepts(status: VerifyStatus, journal) -> None:
    # A non-VERIFIED verifier result can NEVER yield ACCEPT, regardless of the journal.
    d = _decide(status=status, journal=journal)
    assert d.accepted is False
    assert d.refuse_code is RefuseCode.RECEIPT_VERIFY_FAILED


@given(field=st.sampled_from(_LOAD_BEARING), val=_FUZZ_VALUES)
@settings(max_examples=400, deadline=None)
def test_property_load_bearing_mutation_never_spuriously_accepts(field: str, val) -> None:
    if val == _valid_journal()[field]:
        return  # no-op mutation: may legitimately still ACCEPT
    j = _valid_journal()
    j[field] = val
    d = _decide(journal=j)
    assert d.accepted is False, f"spurious ACCEPT after mutating load-bearing {field}={val!r}"
    assert d.refuse_code is not None
    assert d.head_advance is None  # reject-is-no-op


@given(
    host=st.dictionaries(st.text(max_size=8), _FUZZ_VALUES, max_size=5),
    journal=st.one_of(st.none(), st.dictionaries(st.text(max_size=20), _FUZZ_VALUES, max_size=8)),
    status=st.sampled_from(list(VerifyStatus)),
)
@settings(max_examples=400, deadline=None)
def test_property_arbitrary_input_never_raises_and_fails_closed(host: dict, journal, status: VerifyStatus) -> None:
    # Total function: arbitrary garbage -> always an AdmissionDecision, never an exception,
    # and a garbage journal can never produce ACCEPT.
    d = decide_admission(
        SURFACE, OPERATION, dict(host),
        RequestedOperation(surface=SURFACE, operation=OPERATION, fields={}),
        HeadRef(surface=SURFACE, current_head=HEAD),
        registry=_registry(), contract=_contract(),
        verifier=_FakeVerifier(status, journal), rebind=_rebind,
    )
    assert isinstance(d, AdmissionDecision)
    if d.accepted:
        # the only way garbage accepts is if it happens to be the fully-valid journal
        assert journal == _valid_journal() and status is VerifyStatus.VERIFIED
    else:
        assert d.refuse_code is not None and d.head_advance is None

"""Python side of the shared GlobalAccountingAllocationCertificateV1 parity vector.

Obligation: for every recorded (state, certificate) pair the Python checker's exact
outcome (ACCEPT or closed code + detail + message) and every derived root equal the
fixture, the fixture equals its renderer, the reject-message table and check order
are shared with Rust, the producer registry is exhaustive over LaneIdV1 with no
receipt-backed lane, and every declared mutation killer names a recorded vector with
the outcome it declares. The Rust test
``zk/global_settlement_abi_v1/tests/global_accounting_allocation_certificate_golden.rs``
replays the same fixture. Authority: NONE.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from src.core import global_accounting_allocation_certificate_v1 as cert
from src.core.global_settlement_types_v1 import ALL_LANE_IDS_V1, LaneIdV1, canonical_global_bytes_v1
from tools import render_global_accounting_allocation_certificate_v1_golden as renderer

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "tests/data/global_accounting_allocation_certificate_v1_golden.json"


def _fixture() -> dict[str, Any]:
    value = json.loads(FIXTURE.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_fixture_is_the_renderer_output() -> None:
    assert FIXTURE.read_bytes() == renderer.render_bytes_v1()


def test_fixture_header_tables_are_shared() -> None:
    fixture = _fixture()
    assert fixture["fixture_schema"] == renderer.FIXTURE_SCHEMA_V1
    assert fixture["authority"] == "NONE"
    assert fixture["certificate_schema"] == cert.GLOBAL_ACCOUNTING_ALLOCATION_CERTIFICATE_SCHEMA_V1
    assert fixture["reject_messages"] == {
        code.value: message for code, message in cert.ALLOCATION_CERTIFICATE_REJECT_MESSAGE_BY_CODE_V1.items()
    }
    assert list(cert.ALLOCATION_CERTIFICATE_REJECT_MESSAGE_BY_CODE_V1) == list(cert.AllocationCertificateRejectCodeV1)
    assert fixture["check_order"] == list(cert.CHECK_ORDER_V1)


def test_producer_registry_is_exhaustive_and_has_no_receipt_backed_lane() -> None:
    fixture = _fixture()
    assert list(fixture["producer_registry"]) == sorted(lane.value for lane in ALL_LANE_IDS_V1)
    assert set(cert.LANE_ALLOCATION_PRODUCER_REGISTRY_V1) == set(LaneIdV1)
    kinds = {lane: entry["producer_kind"] for lane, entry in fixture["producer_registry"].items()}
    assert cert.LaneProducerKindV1.RECEIPT_BACKED.value not in kinds.values()
    assert kinds["EXTERNAL_CUSTODY"] == "REGISTERED_EMPTY_DISABLED"
    assert kinds["PROOF_REWARDS"] == "REGISTERED_EMPTY_BLOCKED"
    for entry in fixture["producer_registry"].values():
        assert entry["blocked_on"]


@pytest.mark.parametrize("name", sorted(renderer.VECTORS_V1))
def test_vector_replays_outcome_and_derived_roots(name: str) -> None:
    vector = _fixture()["vectors"][name]
    obligation, spec, mutation = renderer.VECTORS_V1[name]
    assert vector["obligation"] == obligation and vector["certificate_mutation"] == mutation
    state = renderer.build_state_v1(spec)
    certificate = renderer._mutate(mutation, cert.build_registered_empty_certificate_v1(state), state)
    assert json.loads(canonical_global_bytes_v1(state)) == vector["state"]
    assert state.state_root == vector["expected_state_root"]
    assert json.loads(canonical_global_bytes_v1(certificate)) == vector["certificate"]
    fragments = certificate.ordered_lane_fragments
    assert [f.fragment_root for f in fragments] == vector["derived"]["lane_fragment_roots"]
    assert cert.derive_field_ownership_root_v1(fragments) == vector["derived"]["field_ownership_root"]
    assert cert.derive_terminal_binding_root_v1(fragments) == vector["derived"]["terminal_binding_root"]
    rows = cert.derive_canonical_allocation_rows_v1(fragments)
    assert cert.derive_allocation_root_v1(fragments, rows) == vector["derived"]["allocation_root"]
    outcome = cert.check_global_accounting_allocation_certificate_v1(certificate, state)
    if vector["expected_outcome"]["status"] == "ACCEPT":
        assert isinstance(outcome, cert.AllocationCertificateAcceptedV1)
        assert list(outcome.lane_fragment_roots) == vector["expected_outcome"]["lane_fragment_roots"]
        assert outcome.allocation_root == vector["derived"]["allocation_root"]
    else:
        assert isinstance(outcome, cert.AllocationCertificateRejectedV1)
        assert outcome.code.value == vector["expected_outcome"]["code"]
        assert outcome.detail == vector["expected_outcome"]["detail"]
        assert outcome.message == vector["expected_outcome"]["message"]
        assert outcome.pre_state_root == outcome.post_state_root == state.state_root


def test_reject_never_mutates_and_accept_needs_all_lanes_disabled() -> None:
    state = renderer.build_state_v1(renderer._spec(lanes_enabled=renderer.ALL_ENABLED))
    before = state.state_root
    outcome = cert.check_global_accounting_allocation_certificate_v1(cert.build_registered_empty_certificate_v1(state), state)
    assert isinstance(outcome, cert.AllocationCertificateRejectedV1)
    assert outcome.code is cert.AllocationCertificateRejectCodeV1.BLOCKED_LANE_PRODUCER_MISSING
    assert state.state_root == before
    empty = renderer.build_state_v1(renderer._spec())
    accepted = cert.check_global_accounting_allocation_certificate_v1(cert.build_registered_empty_certificate_v1(empty), empty)
    assert isinstance(accepted, cert.AllocationCertificateAcceptedV1) and accepted.authority == "NONE"


def test_mutation_killers_name_recorded_vectors_with_the_expected_polarity() -> None:
    fixture = _fixture()
    killers = fixture["mutation_killers"]
    assert set(killers) == set(renderer.MUTATION_KILLERS_V1)
    seen: set[str] = set()
    for mutation, killer in killers.items():
        outcome = fixture["vectors"][killer["vector"]]["expected_outcome"]
        if killer["expected_code"] == "ACCEPT":
            assert outcome["status"] == "ACCEPT", mutation
        else:
            assert outcome["status"] == "REJECT" and outcome["code"] == killer["expected_code"], mutation
            seen.add(killer["expected_code"])
    reachable = {c.value for c in cert.AllocationCertificateRejectCodeV1} - {
        # Reachable only through a receipt-backed producer, which the current profile lacks.
        cert.AllocationCertificateRejectCodeV1.ALLOCATION_TOTAL_OVERFLOW.value,
        cert.AllocationCertificateRejectCodeV1.SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE.value,
    }
    assert seen == reachable


def test_row_level_checks_are_exercised_on_synthetic_fragments() -> None:
    """The exactly-once and overflow checks are unreachable through the registry gate today; exercise them directly."""

    state = renderer.build_state_v1(renderer._spec())
    base = cert.build_registered_empty_certificate_v1(state)
    lane = base.ordered_lane_fragments[0]
    unassigned = renderer._fragment_with_rows(lane, controlled_locations=(cert.ControlledLocationRowV1("USD", "pool-a", "spot-pool", 5),))
    with pytest.raises(cert._Reject) as captured:
        cert._check_exactly_once(renderer._certificate_with_fragments(base, (unassigned, *base.ordered_lane_fragments[1:])))
    assert captured.value.code is cert.AllocationCertificateRejectCodeV1.SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE
    alice_max = cert.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", renderer.MAX)
    overflow = renderer._fragment_with_rows(
        lane, claimant_entitlements=(alice_max, cert.ClaimantEntitlementRowV1("USD", "bob", "spot-pool", 1))
    )
    alice_one = renderer._fragment_with_rows(
        base.ordered_lane_fragments[1], claimant_entitlements=(cert.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", 1),)
    )
    with pytest.raises(OverflowError):
        cert.derive_canonical_allocation_rows_v1((renderer._fragment_with_rows(lane, claimant_entitlements=(alice_max,)), alice_one))
    with pytest.raises(cert._Reject) as overflowed:
        cert._check_exactly_once(_certificate_for(base, overflow))
    assert overflowed.value.code is cert.AllocationCertificateRejectCodeV1.ALLOCATION_TOTAL_OVERFLOW


def test_duplicate_effect_id_across_lanes_is_rejected() -> None:
    """Opus P10 P2-A1: a pending external row repeated across lanes is a double-counted obligation."""

    state = renderer.build_state_v1(renderer._spec(outbox=[("0x" + "ab" * 32, "bridge-a", "0x" + "cd" * 32, "0x" + "ef" * 32, "PENDING")]))
    base = cert.build_registered_empty_certificate_v1(state)
    row = cert.PendingExternalObligationRowV1("0x" + "ab" * 32, "USD", 7, "bridge-a", "0x" + "cd" * 32, "spot-pool", "pool-a")
    first = renderer._fragment_with_rows(base.ordered_lane_fragments[0], pending_external_obligations=(row,))
    second = renderer._fragment_with_rows(base.ordered_lane_fragments[1], pending_external_obligations=(row,))
    duplicated = renderer._certificate_with_fragments(base, (first, second, *base.ordered_lane_fragments[2:]))
    with pytest.raises(cert._Reject) as captured:
        cert._check_external_obligations(duplicated, state)
    assert captured.value.code is cert.AllocationCertificateRejectCodeV1.EXTERNAL_OBLIGATION_BINDING_DRIFT
    assert captured.value.detail == "duplicate 0x" + "ab" * 32
    single = renderer._certificate_with_fragments(base, (first, *base.ordered_lane_fragments[1:]))
    cert._check_external_obligations(single, state)


def _certificate_for(base: cert.GlobalAccountingAllocationCertificateV1, fragment: cert.LaneAllocationFragmentV1) -> cert.GlobalAccountingAllocationCertificateV1:
    from dataclasses import replace

    return replace(base, ordered_lane_fragments=(fragment, *base.ordered_lane_fragments[1:]))


def test_terminal_rows_are_bounded_in_aggregate_per_entitlement_cell() -> None:
    """Opus P13 P2-1: two OPEN claims of 2 against an entitlement of 3 reject; per-row comparison would accept."""

    state = renderer.build_state_v1(renderer._spec())
    base = cert.build_registered_empty_certificate_v1(state)
    lane = base.ordered_lane_fragments[0]
    root = lane.lane_state_root

    def _claim(obligation_id: str, amount: int) -> cert.TerminalBindingRowV1:
        return cert.TerminalBindingRowV1(obligation_id, "alice", "USD", amount, "spot-pool", "pool-a", lane.lane_id, root)

    def _fragment(*claims: cert.TerminalBindingRowV1) -> cert.LaneAllocationFragmentV1:
        return renderer._fragment_with_rows(
            lane,
            controlled_locations=(cert.ControlledLocationRowV1("USD", "pool-a", "spot-pool", 3),),
            claimant_entitlements=(cert.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", 3),),
            terminal_bindings=claims,
        )

    cert._check_terminal_totals(_certificate_for(base, _fragment(_claim("t1", 2), _claim("t2", 1))))
    with pytest.raises(cert._Reject) as captured:
        cert._check_terminal_totals(_certificate_for(base, _fragment(_claim("t1", 2), _claim("t2", 2))))
    assert captured.value.code is cert.AllocationCertificateRejectCodeV1.TERMINAL_BINDING_DRIFT
    assert captured.value.detail == f"{lane.lane_id.value} terminal total USD:alice:spot-pool"
    with pytest.raises(cert._Reject) as unentitled:
        cert._check_terminal_totals(
            _certificate_for(base, renderer._fragment_with_rows(lane, terminal_bindings=(_claim("t1", 1),)))
        )
    assert unentitled.value.code is cert.AllocationCertificateRejectCodeV1.TERMINAL_BINDING_DRIFT

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
from dataclasses import replace
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


def test_producer_registry_is_exhaustive_and_registers_only_asset_transfer_receipt_backed() -> None:
    fixture = _fixture()
    assert list(fixture["producer_registry"]) == sorted(lane.value for lane in ALL_LANE_IDS_V1)
    assert set(cert.LANE_ALLOCATION_PRODUCER_REGISTRY_V1) == set(LaneIdV1)
    kinds = {lane: entry["producer_kind"] for lane, entry in fixture["producer_registry"].items()}
    assert [lane for lane, kind in kinds.items() if kind == "RECEIPT_BACKED"] == ["ASSET_TRANSFER"]
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
    outcome = cert.check_global_accounting_allocation_certificate_v1(certificate, state, cert.EMPTY_LANE_WITNESS_SLOTS_V1)
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
    outcome = cert.check_global_accounting_allocation_certificate_v1(cert.build_registered_empty_certificate_v1(state), state, cert.EMPTY_LANE_WITNESS_SLOTS_V1)
    assert isinstance(outcome, cert.AllocationCertificateRejectedV1)
    assert outcome.code is cert.AllocationCertificateRejectCodeV1.BLOCKED_LANE_PRODUCER_MISSING
    assert state.state_root == before
    empty = renderer.build_state_v1(renderer._spec())
    accepted = cert.check_global_accounting_allocation_certificate_v1(cert.build_registered_empty_certificate_v1(empty), empty, cert.EMPTY_LANE_WITNESS_SLOTS_V1)
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
        # A JSON vector carries no sealed witness: REQUIRED is rendered (the enabled receipt-backed
        # lane with an empty slot); UNEXPECTED, FRAGMENT_DRIFT, and HEADER_DRIFT are exercised
        # in-process by the witnessed tests below with a real minted witness.
        cert.AllocationCertificateRejectCodeV1.RECEIPT_WITNESS_UNEXPECTED.value,
        cert.AllocationCertificateRejectCodeV1.RECEIPT_WITNESS_FRAGMENT_DRIFT.value,
        cert.AllocationCertificateRejectCodeV1.RECEIPT_WITNESS_HEADER_DRIFT.value,
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


def test_fold_overflow_details_match_the_shared_labels() -> None:
    """Opus P15 P2-2: the fold sites are unreachable through the registry gate, so their reject
    details are pinned cross-language by exercising each fold directly against the fixture labels."""

    labels = _fixture()["fold_overflow_labels"]
    assert labels == list(renderer.FOLD_OVERFLOW_LABELS_V1)
    state = renderer.build_state_v1(renderer._spec())
    base = cert.build_registered_empty_certificate_v1(state)
    lane = base.ordered_lane_fragments[0]
    lane_label = lane.lane_id.value

    def _controlled(*amounts: int) -> cert.LaneAllocationFragmentV1:
        return renderer._fragment_with_rows(
            lane,
            controlled_locations=tuple(
                cert.ControlledLocationRowV1("USD", f"pool-{i}", "spot-pool", amount) for i, amount in enumerate(amounts)
            ),
        )

    with pytest.raises(cert._Reject) as controlled:
        cert._check_exactly_once(_certificate_for(base, _controlled(renderer.MAX, renderer.MAX)))
    assert (controlled.value.code, controlled.value.detail) == (
        cert.AllocationCertificateRejectCodeV1.ALLOCATION_TOTAL_OVERFLOW,
        labels[0].format(lane=lane_label),
    )
    assigned = renderer._fragment_with_rows(
        _controlled(renderer.MAX),
        claimant_entitlements=(
            cert.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", renderer.MAX),
            cert.ClaimantEntitlementRowV1("USD", "bob", "spot-pool", renderer.MAX),
        ),
    )
    with pytest.raises(cert._Reject) as assignments:
        cert._check_exactly_once(_certificate_for(base, assigned))
    assert (assignments.value.code, assignments.value.detail) == (
        cert.AllocationCertificateRejectCodeV1.ALLOCATION_TOTAL_OVERFLOW,
        labels[1].format(lane=lane_label),
    )
    reserve = renderer._fragment_with_rows(
        lane,
        unencumbered_reserves=(cert.UnencumberedReserveRowV1("USD", "protocol:fee-unallocated-reserve", "spot-pool", renderer.MAX),),
    )
    second = renderer._fragment_with_rows(
        base.ordered_lane_fragments[1],
        unencumbered_reserves=(cert.UnencumberedReserveRowV1("USD", "protocol:fee-unallocated-reserve", "spot-pool", renderer.MAX),),
    )
    from dataclasses import replace

    with pytest.raises(cert._Reject) as reserves:
        cert._check_reserve_rows(
            replace(base, ordered_lane_fragments=(reserve, second, *base.ordered_lane_fragments[2:])), state
        )
    assert (reserves.value.code, reserves.value.detail) == (
        cert.AllocationCertificateRejectCodeV1.ALLOCATION_TOTAL_OVERFLOW,
        labels[2],
    )
    claims = tuple(
        cert.TerminalBindingRowV1(f"t{i}", "alice", "USD", renderer.MAX, "spot-pool", "pool-a", lane.lane_id, lane.lane_state_root)
        for i in (1, 2)
    )
    with pytest.raises(cert._Reject) as totals:
        cert._check_terminal_totals(_certificate_for(base, renderer._fragment_with_rows(lane, terminal_bindings=claims)))
    assert (totals.value.code, totals.value.detail) == (
        cert.AllocationCertificateRejectCodeV1.ALLOCATION_TOTAL_OVERFLOW,
        labels[3],
    )
    with pytest.raises(cert._Reject) as custody:
        cert._check_lane_aggregates(
            replace(base, ordered_lane_fragments=(_controlled(renderer.MAX), _controlled(renderer.MAX), *base.ordered_lane_fragments[2:])),
            state,
        )
    assert (custody.value.code, custody.value.detail) == (
        cert.AllocationCertificateRejectCodeV1.ALLOCATION_TOTAL_OVERFLOW,
        labels[4],
    )


# --- C9b-2a: the witness slots gate, inert while no lane is registered receipt-backed --------------


def test_witness_slots_refuse_a_witness_for_an_unregistered_lane_and_bad_shapes() -> None:
    """C9b-2a: a presented witness in a slot whose lane cannot use one (here the disabled
    ASSET_TRANSFER lane of the registered-empty certificate) is RECEIPT_WITNESS_UNEXPECTED,
    checked before any row; the slot shape and the exact witness class are type-boundary
    refusals."""

    from src.core.asset_transfer_receipt_admission_v1 import (
        verify_asset_transfer_fragment_receipt_v1,
    )
    from tests.core.test_asset_transfer_receipt_admission_v1 import _admission_fixture

    accepted, module_witness, lane_root, prior = _admission_fixture()
    witness = verify_asset_transfer_fragment_receipt_v1(module_witness, accepted, lane_root, prior, ())
    assert isinstance(witness, cert.VerifiedLaneAllocationFragmentV1)
    empty = renderer.build_state_v1(renderer._spec())
    certificate = cert.build_registered_empty_certificate_v1(empty)
    index = ALL_LANE_IDS_V1.index(LaneIdV1.ASSET_TRANSFER)
    slots = list(cert.EMPTY_LANE_WITNESS_SLOTS_V1)
    slots[index] = witness
    outcome = cert.check_global_accounting_allocation_certificate_v1(certificate, empty, tuple(slots))
    assert isinstance(outcome, cert.AllocationCertificateRejectedV1)
    assert outcome.code is cert.AllocationCertificateRejectCodeV1.RECEIPT_WITNESS_UNEXPECTED
    assert outcome.detail == "ASSET_TRANSFER"
    assert outcome.pre_state_root == outcome.post_state_root == empty.state_root
    accepted_outcome = cert.check_global_accounting_allocation_certificate_v1(
        certificate, empty, cert.EMPTY_LANE_WITNESS_SLOTS_V1
    )
    assert isinstance(accepted_outcome, cert.AllocationCertificateAcceptedV1)

    class SpoofedWitness(cert.VerifiedLaneAllocationFragmentV1):
        """A plain subclass carrying the genuine fields: the slot gate is exact, so it is refused."""

    spoofed = object.__new__(SpoofedWitness)
    object.__setattr__(spoofed, "_fields", witness._fields)
    spoofed_slots = list(cert.EMPTY_LANE_WITNESS_SLOTS_V1)
    spoofed_slots[index] = spoofed
    bare_slots = list(cert.EMPTY_LANE_WITNESS_SLOTS_V1)
    bare_slots[index] = witness.fragment
    for shape in (
        cert.EMPTY_LANE_WITNESS_SLOTS_V1[:11],
        cert.EMPTY_LANE_WITNESS_SLOTS_V1 + (None,),
        list(cert.EMPTY_LANE_WITNESS_SLOTS_V1),
        tuple(bare_slots),
        tuple(spoofed_slots),
    ):
        with pytest.raises(TypeError, match="witness slot"):
            cert.check_global_accounting_allocation_certificate_v1(certificate, empty, shape)  # type: ignore[arg-type]
    assert len(cert.EMPTY_LANE_WITNESS_SLOTS_V1) == len(ALL_LANE_IDS_V1) == 12
    assert cert.CHECK_ORDER_V1.index("receipt_witness_slots_bind_fragment_and_header") == cert.CHECK_ORDER_V1.index(
        "enabled_lane_supported_receipt_backed_producer"
    ) + 1


# --- C9b-2b: ASSET_TRANSFER registered receipt-backed; the witnessed acceptance path -------------


def _witnessed(authority_epoch: int | None = None):
    """A real admitted witness and a state/certificate pair built around it: the enabled
    ASSET_TRANSFER lane sits at the admitted post root under the witness's own header, the
    other eleven lanes are disabled and empty, and the certificate carries the witness's
    fragment in the first slot."""

    from src.core.asset_transfer_receipt_admission_v1 import (
        verify_asset_transfer_fragment_receipt_v1,
    )
    from tests.core.test_asset_transfer_receipt_admission_v1 import _fixture as admission_fixture

    accepted, module_witness, lane_root, prior = (
        admission_fixture() if authority_epoch is None else admission_fixture(authority_epoch=authority_epoch)
    )
    witness = verify_asset_transfer_fragment_receipt_v1(module_witness, accepted, lane_root, prior, ())
    assert isinstance(witness, cert.VerifiedLaneAllocationFragmentV1)
    base = renderer.build_state_v1(renderer._spec(lanes_enabled=renderer.ONE_ENABLED))
    lane_roots = (lane_root, *base.lane_roots[1:])
    state = replace(
        base,
        chain_id=witness.chain_id,
        deployment_root=witness.deployment_root,
        profile_root=witness.profile_root,
        writer_epoch=witness.writer_epoch,
        lane_roots=lane_roots,
    )
    registered = cert.build_registered_empty_certificate_v1(state)
    certificate = renderer._certificate_with_fragments(registered, (witness.fragment, *registered.ordered_lane_fragments[1:]))
    slots = (witness, *cert.EMPTY_LANE_WITNESS_SLOTS_V1[1:])
    return witness, state, certificate, slots


def test_enabled_asset_transfer_lane_is_accepted_only_through_its_witness() -> None:
    """C9b-2b: the registered receipt-backed lane accepts with its sealed witness in the slot and
    rejects RECEIPT_WITNESS_REQUIRED without it; the accepted fragment root is the witness's."""

    witness, state, certificate, slots = _witnessed()
    outcome = cert.check_global_accounting_allocation_certificate_v1(certificate, state, slots)
    assert isinstance(outcome, cert.AllocationCertificateAcceptedV1), outcome
    assert outcome.lane_fragment_roots[0] == witness.fragment.fragment_root
    required = cert.check_global_accounting_allocation_certificate_v1(certificate, state, cert.EMPTY_LANE_WITNESS_SLOTS_V1)
    assert isinstance(required, cert.AllocationCertificateRejectedV1)
    assert required.code is cert.AllocationCertificateRejectCodeV1.RECEIPT_WITNESS_REQUIRED
    assert required.detail == "ASSET_TRANSFER"
    assert required.pre_state_root == required.post_state_root == state.state_root


def test_witnessed_fragment_must_equal_the_certificate_fragment() -> None:
    """C9b-2b: a certificate fragment that differs from the admitted one (here claiming the
    lane-root binding instead of the receipt root) rejects RECEIPT_WITNESS_FRAGMENT_DRIFT."""

    witness, state, certificate, slots = _witnessed()
    forged = replace(witness.fragment, binding_root=witness.fragment.lane_state_root)
    drifted = renderer._certificate_with_fragments(certificate, (forged, *certificate.ordered_lane_fragments[1:]))
    outcome = cert.check_global_accounting_allocation_certificate_v1(drifted, state, slots)
    assert isinstance(outcome, cert.AllocationCertificateRejectedV1)
    assert outcome.code is cert.AllocationCertificateRejectCodeV1.RECEIPT_WITNESS_FRAGMENT_DRIFT
    assert outcome.detail == "ASSET_TRANSFER"


def test_witness_minted_under_another_header_is_refused() -> None:
    """C9b-2b: a witness minted under another writer epoch for the same module transition binds
    the same lane root (the module state is epoch-free) but not this state's header, so it
    rejects RECEIPT_WITNESS_HEADER_DRIFT even though its fragment is the certificate's."""

    witness, state, _certificate, _slots = _witnessed()
    foreign, _foreign_state, foreign_certificate, foreign_slots = _witnessed(authority_epoch=witness.writer_epoch + 1)
    assert foreign.writer_epoch == witness.writer_epoch + 1
    assert foreign.fragment.lane_state_root == witness.fragment.lane_state_root
    lane_roots = (replace(state.lane_roots[0], module_release_id=foreign.fragment.module_release_id), *state.lane_roots[1:])
    host = replace(state, lane_roots=lane_roots)
    hosted = replace(
        foreign_certificate,
        global_state_root=host.state_root,
        profile_root=host.profile_root,
        writer_epoch=host.writer_epoch,
        chain_context=cert.ChainContextV1(host.chain_id, host.deployment_root),
    )
    outcome = cert.check_global_accounting_allocation_certificate_v1(hosted, host, foreign_slots)
    assert isinstance(outcome, cert.AllocationCertificateRejectedV1)
    assert outcome.code is cert.AllocationCertificateRejectCodeV1.RECEIPT_WITNESS_HEADER_DRIFT
    assert outcome.detail == "ASSET_TRANSFER"


def test_witness_passes_fire_in_the_documented_order() -> None:
    """Opus P36 F-5: FRAGMENT_DRIFT precedes HEADER_DRIFT at runtime (a foreign-epoch witness in a
    certificate built for the base witness differs in both), and the four witness codes appear in the
    documented order in both the Python and the Rust lane-binding pass."""

    import re
    from pathlib import Path

    witness, state, certificate, _slots = _witnessed()
    foreign, _fs, _fc, foreign_slots = _witnessed(authority_epoch=witness.writer_epoch + 1)
    assert foreign.fragment != witness.fragment and foreign.writer_epoch != state.writer_epoch
    outcome = cert.check_global_accounting_allocation_certificate_v1(certificate, state, foreign_slots)
    assert isinstance(outcome, cert.AllocationCertificateRejectedV1)
    assert outcome.code is cert.AllocationCertificateRejectCodeV1.RECEIPT_WITNESS_FRAGMENT_DRIFT

    root = Path(__file__).resolve().parents[2]
    order = ("RECEIPT_WITNESS_REQUIRED", "RECEIPT_WITNESS_UNEXPECTED", "RECEIPT_WITNESS_FRAGMENT_DRIFT", "RECEIPT_WITNESS_HEADER_DRIFT")
    python = (root / "src/core/global_accounting_allocation_certificate_v1.py").read_text()
    body = python.split("def _check_lane_bindings(", 1)[1].split("\ndef ", 1)[0]
    assert tuple(re.findall(r"AllocationCertificateRejectCodeV1\.(RECEIPT_WITNESS_[A-Z_]+)", body)) == order
    rust = (root / "zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs").read_text()
    rbody = rust.split("fn check_lane_bindings(", 1)[1].split("\nfn ", 1)[0]
    camel = {"RECEIPT_WITNESS_REQUIRED": "ReceiptWitnessRequired", "RECEIPT_WITNESS_UNEXPECTED": "ReceiptWitnessUnexpected",
             "RECEIPT_WITNESS_FRAGMENT_DRIFT": "ReceiptWitnessFragmentDrift", "RECEIPT_WITNESS_HEADER_DRIFT": "ReceiptWitnessHeaderDrift"}
    assert tuple(re.findall(r"AllocationCertificateRejectCodeV1::(ReceiptWitness[A-Za-z]+)", rbody)) == tuple(camel[c] for c in order)

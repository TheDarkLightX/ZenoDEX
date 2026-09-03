"""The allocation certificate is derived from the state, not assembled by hand (C9c-1).

SCOPE, corrected after the P38 reviews. The fixture partition below is a statement
about the twenty-nine golden states and nothing more: every fixture state that carries
economic rows has all lanes disabled, so the projected certificates are row-empty and
the row inversions are not exercised there. The general statement "the projection never
yields a certificate that fails a row check" was FALSE and is not made here; the states
that falsified it (an over-claiming terminal, a claimant with no entitlement, an
entitlement exceeding custody) are now refused as UNRECONCILABLE, each with its own
closed code and a test below.

What is claimed, and tested with rows rather than vacuously:
1. the projection derives ONE certificate from the state, and where V1 state admits more
   than one accepted certificate it refuses rather than choosing (the AMBIGUOUS codes);
2. where no certificate over the state can be accepted, it refuses rather than deriving
   one the checker must reject (the remaining codes);
3. given the one scalar the state does not carry, the receipt root, it reproduces the
   witnessed certificate byte-for-byte, INCLUDING a witness whose receipt proved custody
   rows, so "the witness contributes its binding root and its header, not its rows" is
   no longer a claim about an empty witness.
"""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core import global_accounting_allocation_certificate_v1 as cert
from src.core.global_accounting_allocation_projection_v1 import (
    ALLOCATION_PROJECTION_REJECT_CODES_V1,
    AllocationProjectionRejectCodeV1,
    AllocationProjectionRejectedV1,
    project_allocation_certificate_v1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    EconomicAmountV1,
    LaneIdV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
    canonical_global_bytes_v1,
)
from tests.core.test_global_accounting_allocation_certificate_v1_golden import _fixture, _witnessed
from tools import render_global_accounting_allocation_certificate_v1_golden as renderer


def _project(state, roots=()):
    return project_allocation_certificate_v1(state, roots)


# The two fixture states no certificate can reconcile, with the state-level gate that
# refuses them: an enabled lane whose registry entry has no producer, and a
# registered-empty lane committed at a foreign root. Neither is a row, aggregate or
# derived-root defect, so neither is something a derived certificate could avoid.
_STATE_LEVEL_REFUSALS = {
    "rejects_enabled_lane_without_receipt_backed_producer": "BLOCKED_LANE_PRODUCER_MISSING",
    "rejects_registered_empty_lane_with_foreign_root": "REGISTERED_EMPTY_ROOT_DRIFT",
}


@pytest.mark.parametrize("name", sorted(renderer.VECTORS_V1))
def test_no_fixture_state_projects_to_a_row_or_root_defect(name: str) -> None:
    """Totality against the fixture, stated precisely.

    For every state the fixture renders, the projection either refuses with a closed
    code (rows with no lane to own them, more than one enabled lane, or a missing
    receipt root), or produces a certificate the checker ACCEPTS, or produces one the
    checker refuses on a STATE-level gate that no certificate can avoid. It never
    produces a certificate that fails a row, aggregate, or derived-root check: those
    twenty fixture rejections are certificate forgeries a derived certificate cannot
    express.
    """

    _obligation, spec, _mutation = renderer.VECTORS_V1[name]
    state = renderer.build_state_v1(spec)
    projected = _project(state)
    if isinstance(projected, AllocationProjectionRejectedV1):
        assert projected.code.value in ALLOCATION_PROJECTION_REJECT_CODES_V1
        assert projected.state_root == state.state_root
        assert projected.code in {
            AllocationProjectionRejectCodeV1.PROJECTION_NO_LANE_FOR_ROWS,
            AllocationProjectionRejectCodeV1.PROJECTION_MULTIPLE_ENABLED_LANES,
            AllocationProjectionRejectCodeV1.PROJECTION_BINDING_ROOT_MISSING,
        }, projected
        assert name not in _STATE_LEVEL_REFUSALS
        return
    outcome = cert.check_global_accounting_allocation_certificate_v1(
        projected, state, cert.EMPTY_LANE_WITNESS_SLOTS_V1
    )
    if name in _STATE_LEVEL_REFUSALS:
        assert isinstance(outcome, cert.AllocationCertificateRejectedV1), (name, outcome)
        assert outcome.code.value == _STATE_LEVEL_REFUSALS[name], (name, outcome.code)
        return
    assert isinstance(outcome, cert.AllocationCertificateAcceptedV1), (name, outcome)


def test_the_fixture_partition_of_states_is_pinned() -> None:
    """The three buckets above, counted, with the accepted bucket CHECKED.

    The count alone would pass while the derived certificates were wrong, so the
    accepted bucket is counted only when the checker actually accepts the projection.
    """

    buckets: dict[str, int] = {"accept": 0, "projection_refusal": 0, "state_level": 0}
    for name in renderer.VECTORS_V1:
        _obligation, spec, _mutation = renderer.VECTORS_V1[name]
        state = renderer.build_state_v1(spec)
        projected = _project(state)
        if isinstance(projected, AllocationProjectionRejectedV1):
            buckets["projection_refusal"] += 1
            continue
        outcome = cert.check_global_accounting_allocation_certificate_v1(
            projected, state, cert.EMPTY_LANE_WITNESS_SLOTS_V1
        )
        if name in _STATE_LEVEL_REFUSALS:
            assert isinstance(outcome, cert.AllocationCertificateRejectedV1), name
            assert outcome.code.value == _STATE_LEVEL_REFUSALS[name], (name, outcome.code)
            buckets["state_level"] += 1
            continue
        assert isinstance(outcome, cert.AllocationCertificateAcceptedV1), (name, outcome)
        buckets["accept"] += 1
    assert buckets == {"accept": 20, "projection_refusal": 7, "state_level": 2}
    assert sum(buckets.values()) == len(renderer.VECTORS_V1)


def test_accepted_fixture_vectors_are_reproduced_byte_for_byte() -> None:
    """Where the fixture accepts, the projection is that exact certificate."""

    fixture = _fixture()
    accepted = [
        name
        for name, vector in fixture["vectors"].items()
        if vector["expected_outcome"]["status"] == "ACCEPT"
    ]
    assert accepted, "the fixture must carry accepted vectors"
    for name in accepted:
        _obligation, spec, _mutation = renderer.VECTORS_V1[name]
        state = renderer.build_state_v1(spec)
        projected = _project(state)
        assert isinstance(projected, cert.GlobalAccountingAllocationCertificateV1), (name, projected)
        assert canonical_global_bytes_v1(projected) == canonical_global_bytes_v1(
            cert.build_registered_empty_certificate_v1(state)
        ), name
        assert projected.allocation_root == fixture["vectors"][name]["derived"]["allocation_root"]


def test_witnessed_certificate_is_the_projection_plus_one_receipt_root() -> None:
    """C9c-1: the sealed witness carries no row the state does not already carry.

    Given the receipt root the admission proved, the projection reproduces the
    witnessed certificate exactly, and the checker accepts it in the witnessed slot.
    Without that root the projection refuses rather than substituting the lane root,
    which is what makes the root the witness's only row-level contribution.
    """

    witness, state, certificate, slots = _witnessed()
    projected = _project(state, ((LaneIdV1.ASSET_TRANSFER, witness.fragment.binding_root),))
    assert isinstance(projected, cert.GlobalAccountingAllocationCertificateV1), projected
    assert canonical_global_bytes_v1(projected) == canonical_global_bytes_v1(certificate)
    outcome = cert.check_global_accounting_allocation_certificate_v1(projected, state, slots)
    assert isinstance(outcome, cert.AllocationCertificateAcceptedV1), outcome
    assert outcome.allocation_root == certificate.allocation_root

    missing = _project(state)
    assert isinstance(missing, AllocationProjectionRejectedV1)
    assert missing.code is AllocationProjectionRejectCodeV1.PROJECTION_BINDING_ROOT_MISSING
    assert missing.detail == LaneIdV1.ASSET_TRANSFER.value


def test_binding_root_for_an_unwitnessed_lane_is_refused() -> None:
    """A binding root may be supplied only for an enabled receipt-backed lane."""

    empty = renderer.build_state_v1(renderer._spec())
    rejected = _project(empty, ((LaneIdV1.ASSET_TRANSFER, empty.lane_roots[0].state_root),))
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_BINDING_ROOT_UNEXPECTED
    assert rejected.detail == LaneIdV1.ASSET_TRANSFER.value


def test_more_than_one_enabled_lane_is_refused_before_any_row_is_read() -> None:
    """Multi-lane field ownership is undecided, so two enabled lanes are refused."""

    two = [False] * 12
    two[0] = True
    two[1] = True
    state = renderer.build_state_v1(renderer._spec(lanes_enabled=two))
    rejected = _project(state)
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_MULTIPLE_ENABLED_LANES
    assert rejected.detail == "ASSET_TRANSFER,SPOT_LIQUIDITY"


def test_rows_without_an_enabled_lane_are_refused() -> None:
    """A state carrying economic rows with every lane disabled reconciles to nothing."""

    state = renderer.build_state_v1(renderer._spec(custody=[("pool-a", "USD", "spot-pool", 10)]))
    rejected = _project(state)
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_NO_LANE_FOR_ROWS
    registered_empty = cert.build_registered_empty_certificate_v1(state)
    outcome = cert.check_global_accounting_allocation_certificate_v1(
        registered_empty, state, cert.EMPTY_LANE_WITNESS_SLOTS_V1
    )
    assert isinstance(outcome, cert.AllocationCertificateRejectedV1), "the refusal is not a projection defect"


def _one_enabled_state(**tables):
    one = [False] * 12
    one[0] = True
    return renderer.build_state_v1(renderer._spec(lanes_enabled=one, **tables))


def test_two_hidden_domain_preimages_are_refused_not_guessed() -> None:
    """The declared gap made executable: a V1 terminal names no control domain, so a
    claimant entitled in two domains leaves the row's domain undetermined."""

    state = _one_enabled_state(
        custody=[("pool-a", "USD", "spot-pool", 6), ("pool-a", "USD", "vault", 4)],
        liabilities=[("alice", "USD", "spot-pool", 6), ("alice", "USD", "vault", 4)],
    )
    state = replace(
        state,
        terminal_obligations=(
            TerminalObligationV1(
                obligation_id="terminal-1",
                lane_id=LaneIdV1.ASSET_TRANSFER,
                claimant="alice",
                asset="USD",
                amount_atoms=3,
                status=TerminalObligationStatusV1.OPEN,
            ),
        ),
    )
    rejected = _project(state, ((LaneIdV1.ASSET_TRANSFER, state.lane_roots[0].state_root),))
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS
    assert "2 entitlement domains" in rejected.detail

    single = replace(
        state,
        custody=(EconomicAmountV1(owner="pool-a", asset="USD", custody_domain="spot-pool", amount_atoms=6),),
        liabilities=(EconomicAmountV1(owner="alice", asset="USD", custody_domain="spot-pool", amount_atoms=6),),
    )
    projected = _project(single, ((LaneIdV1.ASSET_TRANSFER, single.lane_roots[0].state_root),))
    assert isinstance(projected, cert.GlobalAccountingAllocationCertificateV1), projected
    row = projected.ordered_lane_fragments[0].terminal_bindings[0]
    assert (row.control_domain, row.controlling_principal) == ("spot-pool", "pool-a")
    outcome = cert.check_global_accounting_allocation_certificate_v1(
        projected, single, cert.EMPTY_LANE_WITNESS_SLOTS_V1
    )
    assert isinstance(outcome, cert.AllocationCertificateRejectedV1)
    assert outcome.code is cert.AllocationCertificateRejectCodeV1.RECEIPT_WITNESS_REQUIRED


def test_two_pending_obligations_over_one_residual_cell_are_refused() -> None:
    """A V1 outbox entry carries no asset or amount, so two PENDING entries over one
    residual cell can be split in more than one way."""

    state = _one_enabled_state(
        custody=[("pool-a", "USD", "spot-pool", 10)],
        outbox=[
            (renderer._root(9_001), "dest-1", renderer._root(9_002), renderer._root(9_003), "PENDING"),
            (renderer._root(9_011), "dest-2", renderer._root(9_012), renderer._root(9_013), "PENDING"),
        ],
    )
    rejected = _project(state, ((LaneIdV1.ASSET_TRANSFER, state.lane_roots[0].state_root),))
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS
    assert rejected.detail == "2 pending rows for 1 residual cells"


def test_one_pending_obligation_takes_the_residual_and_the_checker_accepts_the_rows() -> None:
    """With one PENDING entry the residual is determined, and the projected external
    row satisfies the checker's outbox binding and the exactly-once partition."""

    state = _one_enabled_state(
        custody=[("pool-a", "USD", "spot-pool", 10)],
        liabilities=[("alice", "USD", "spot-pool", 4)],
        outbox=[(renderer._root(9_001), "dest-1", renderer._root(9_002), renderer._root(9_003), "PENDING")],
    )
    projected = _project(state, ((LaneIdV1.ASSET_TRANSFER, state.lane_roots[0].state_root),))
    assert isinstance(projected, cert.GlobalAccountingAllocationCertificateV1), projected
    external = projected.ordered_lane_fragments[0].pending_external_obligations
    assert len(external) == 1
    assert (external[0].asset, external[0].amount_atoms, external[0].source_principal) == ("USD", 6, "pool-a")
    assert external[0].commitment_root == state.outbox[0].payload_hash
    outcome = cert.check_global_accounting_allocation_certificate_v1(
        projected, state, cert.EMPTY_LANE_WITNESS_SLOTS_V1
    )
    assert isinstance(outcome, cert.AllocationCertificateRejectedV1)
    assert outcome.code is cert.AllocationCertificateRejectCodeV1.RECEIPT_WITNESS_REQUIRED


def test_projection_type_boundary_is_exact() -> None:
    """The state and the lane/root pairs are exact-typed; a lane named twice is refused."""

    empty = renderer.build_state_v1(renderer._spec())
    with pytest.raises(TypeError, match="exact typed state"):
        project_allocation_certificate_v1(object(), ())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="exact tuple"):
        project_allocation_certificate_v1(empty, [])  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="exact \\(lane, root\\) pairs"):
        project_allocation_certificate_v1(empty, ((LaneIdV1.ASSET_TRANSFER,),))  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="exact lane and exact text"):
        project_allocation_certificate_v1(empty, (("ASSET_TRANSFER", "0x" + "11" * 32),))  # type: ignore[arg-type]
    root = empty.lane_roots[0].state_root
    with pytest.raises(ValueError, match="at most once"):
        project_allocation_certificate_v1(
            empty, ((LaneIdV1.ASSET_TRANSFER, root), (LaneIdV1.ASSET_TRANSFER, root))
        )


def test_reject_codes_are_closed_and_ordered() -> None:
    """The reject family is the declaration order of the enum, and every code is reachable
    by a test in this module."""

    assert ALLOCATION_PROJECTION_REJECT_CODES_V1 == tuple(
        code.value for code in AllocationProjectionRejectCodeV1
    )
    assert len(ALLOCATION_PROJECTION_REJECT_CODES_V1) == 10
    assert len(ALL_LANE_IDS_V1) == 12


# --- P38 repairs: rows, unreconcilable states, and the guards that had no test ----------


def test_witnessed_certificate_with_rows_is_reproduced_byte_for_byte() -> None:
    """Opus P38 P2-2 and opus2 P2-2: the byte-for-byte claim was made about a witness with
    no rows. This witness's receipt proved a custody row, and the projection still
    reproduces the witnessed certificate exactly from the state plus the receipt root."""

    witness, state, certificate, slots = _witnessed(with_rows=True)
    assert not witness.fragment.is_empty
    projected = _project(state, ((LaneIdV1.ASSET_TRANSFER, witness.fragment.binding_root),))
    assert isinstance(projected, cert.GlobalAccountingAllocationCertificateV1), projected
    fragment = projected.ordered_lane_fragments[0]
    assert fragment.controlled_locations and fragment.claimant_entitlements
    assert canonical_global_bytes_v1(projected) == canonical_global_bytes_v1(certificate)
    outcome = cert.check_global_accounting_allocation_certificate_v1(projected, state, slots)
    assert isinstance(outcome, cert.AllocationCertificateAcceptedV1), outcome


def _terminal(obligation_id: str, amount: int, *, claimant: str = "alice", lane: LaneIdV1 = LaneIdV1.ASSET_TRANSFER):
    return TerminalObligationV1(
        obligation_id=obligation_id,
        lane_id=lane,
        claimant=claimant,
        asset="USD",
        amount_atoms=amount,
        status=TerminalObligationStatusV1.OPEN,
    )


def _backed_state(terminals=(), *, custody=(("pool-a", "USD", "spot-pool", 10),), liabilities=(("alice", "USD", "spot-pool", 10),), outbox=()):
    state = _one_enabled_state(custody=list(custody), liabilities=list(liabilities), outbox=list(outbox))
    return replace(state, terminal_obligations=tuple(terminals))


def _root_of(state):
    return ((LaneIdV1.ASSET_TRANSFER, state.lane_roots[0].state_root),)


def test_over_claiming_terminals_are_refused_as_unreconcilable() -> None:
    """Opus P38 P2-1: the checker bounds the SUM of a fragment's terminal rows against the
    entitlement, so both a single over-claim and two rows that together over-claim
    reconcile to nothing. Before this repair the projection derived a certificate that
    failed _check_terminal_bindings, which is what falsified the general claim."""

    single = _backed_state((_terminal("terminal-1", 99),))
    rejected = _project(single, _root_of(single))
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT
    assert "claims 99 of 10" in rejected.detail

    pair = _backed_state(
        (_terminal("terminal-1", 2), _terminal("terminal-2", 2)),
        custody=(("pool-a", "USD", "spot-pool", 3),),
        liabilities=(("alice", "USD", "spot-pool", 3),),
    )
    rejected_pair = _project(pair, _root_of(pair))
    assert isinstance(rejected_pair, AllocationProjectionRejectedV1)
    assert rejected_pair.code is AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT
    assert "claims 4 of 3" in rejected_pair.detail

    exact = _backed_state((_terminal("terminal-1", 10),))
    projected = _project(exact, _root_of(exact))
    assert isinstance(projected, cert.GlobalAccountingAllocationCertificateV1), projected
    assert projected.ordered_lane_fragments[0].terminal_bindings[0].amount_atoms == 10


def test_a_terminal_with_no_entitlement_is_refused_separately_from_an_ambiguous_one() -> None:
    """A claimant with no entitlement reconciles to nothing; a claimant entitled in two
    domains is merely undetermined. They are different failures and carry different codes."""

    orphan = _backed_state((_terminal("terminal-1", 1, claimant="mallory"),))
    rejected = _project(orphan, _root_of(orphan))
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_WITHOUT_ENTITLEMENT
    assert "no entitlement for mallory" in rejected.detail


def test_entitlements_exceeding_custody_are_refused() -> None:
    """More claimed than controlled is unreconcilable, not an ambiguity about the split."""

    state = _backed_state(
        custody=(("pool-a", "USD", "spot-pool", 3),),
        liabilities=(("alice", "USD", "spot-pool", 5),),
        outbox=((renderer._root(9_001), "dest-1", renderer._root(9_002), renderer._root(9_003), "PENDING"),),
    )
    rejected = _project(state, _root_of(state))
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_NEGATIVE_RESIDUAL
    assert "exceed custody for USD:spot-pool" in rejected.detail


def test_unassigned_atoms_without_a_pending_obligation_are_refused() -> None:
    """Controlled atoms that no entitlement, reserve or pending obligation claims leave the
    normative partition open, so the projection refuses rather than inventing a row."""

    state = _backed_state(liabilities=(("alice", "USD", "spot-pool", 4),))
    rejected = _project(state, _root_of(state))
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS
    assert rejected.detail == "unassigned controlled atoms with no pending obligation"


def test_two_principals_over_one_residual_cell_are_refused() -> None:
    """The external row names a source principal, which the checker now binds to a
    controlled location; two principals control the residual cell, so it is undetermined."""

    state = _backed_state(
        custody=(("pool-a", "USD", "spot-pool", 6), ("pool-b", "USD", "spot-pool", 4)),
        liabilities=(),
        outbox=((renderer._root(9_001), "dest-1", renderer._root(9_002), renderer._root(9_003), "PENDING"),),
    )
    rejected = _project(state, _root_of(state))
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS
    assert rejected.detail == "2 principals control USD:spot-pool"


def test_two_controlling_principals_make_a_terminal_row_undetermined() -> None:
    """One entitlement domain but two principals controlling it leaves the terminal row's
    controlling principal open."""

    state = _backed_state(
        (_terminal("terminal-1", 3),),
        custody=(("pool-a", "USD", "spot-pool", 6), ("pool-b", "USD", "spot-pool", 4)),
        liabilities=(("alice", "USD", "spot-pool", 10),),
    )
    rejected = _project(state, _root_of(state))
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS
    assert "2 principals" in rejected.detail


def test_a_terminal_naming_another_lane_is_refused() -> None:
    """An OPEN obligation on a lane other than the single enabled one has no fragment to
    live in, so it is refused rather than attached to the wrong lane."""

    state = _backed_state((_terminal("terminal-1", 1, lane=LaneIdV1.SPOT_LIQUIDITY),))
    rejected = _project(state, _root_of(state))
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_NO_LANE_FOR_ROWS
    assert "names SPOT_LIQUIDITY" in rejected.detail


def test_terminal_row_ordering_is_defensive_because_the_state_already_guarantees_it() -> None:
    """The projection sorts its terminal rows, but a state cannot present them out of order:
    GlobalEconomicStateV1 refuses a non-canonical obligation tuple at construction. The sort
    is therefore defensive, and this test records that rather than claiming a killer for it."""

    state = _backed_state((_terminal("terminal-1", 6), _terminal("terminal-9", 4)))
    projected = _project(state, _root_of(state))
    assert isinstance(projected, cert.GlobalAccountingAllocationCertificateV1), projected
    ids = [row.obligation_id for row in projected.ordered_lane_fragments[0].terminal_bindings]
    assert ids == ["terminal-1", "terminal-9"]
    with pytest.raises(ValueError, match="canonically ordered"):
        replace(state, terminal_obligations=(_terminal("terminal-9", 4), _terminal("terminal-1", 6)))


def test_both_checked_folds_refuse_a_u128_overflow() -> None:
    """The checker's folds are checked u128, so the projection's must be too: a controlled
    cell and a terminal cell that overflow are refused rather than derived into a
    certificate whose fold raises inside the checker."""

    maximum = (1 << 128) - 1
    base = _one_enabled_state()
    roots = ((LaneIdV1.ASSET_TRANSFER, base.lane_roots[0].state_root),)

    controlled = replace(
        base,
        custody=(
            EconomicAmountV1("pool-a", "USD", "spot-pool", maximum),
            EconomicAmountV1("pool-b", "USD", "spot-pool", maximum),
        ),
    )
    rejected = _project(controlled, roots)
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_ROW_TOTAL_OVERFLOW
    assert rejected.detail == "controlled totals for USD:spot-pool"

    terminals = replace(
        base,
        custody=(EconomicAmountV1("pool-a", "USD", "spot-pool", maximum),),
        liabilities=(EconomicAmountV1("alice", "USD", "spot-pool", maximum),),
        terminal_obligations=(_terminal("terminal-1", maximum), _terminal("terminal-2", maximum)),
    )
    overflowed = _project(terminals, roots)
    assert isinstance(overflowed, AllocationProjectionRejectedV1)
    assert overflowed.code is AllocationProjectionRejectCodeV1.PROJECTION_ROW_TOTAL_OVERFLOW
    assert overflowed.detail == "terminal totals for USD:alice:spot-pool"

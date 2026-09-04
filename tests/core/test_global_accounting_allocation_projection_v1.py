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
1. the projection derives ONE certificate from the state, and where the state does not pin
   the row content it refuses rather than choosing (the AMBIGUOUS codes). Not "where more
   than one row-checked certificate exists": for two sub-cases exactly one did, and those
   are now derived (a terminal's domains are filtered by the entitlement that must carry
   the row) or given their own UNSUPPORTED code (opus2 P41 P1-2). Not "more than one ACCEPTED certificate":
   under the current registry none of those states has an accepted certificate at all,
   because the only receipt-backed lane needs a witness whose fragment must equal the
   certificate's. A test exhibits the two row-checked certificates and shows the full
   checker refusing both;
2. where no certificate over the state can be accepted, it refuses rather than deriving
   one the checker must reject (the remaining codes), and for each such row case a test
   builds the certificate the state implies and shows the checker refusing it;
3. given the one scalar the state does not carry, the receipt root, it reproduces the
   witnessed certificate byte-for-byte, INCLUDING a witness whose receipt proved custody
   rows, so "the witness contributes its binding root and its header, not its rows" is
   no longer a claim about an empty witness.
"""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core import global_accounting_allocation_certificate_v1 as cert
from src.core import global_accounting_allocation_projection_v1 as proj
from src.core.global_accounting_allocation_projection_v1 import (
    ALLOCATION_PROJECTION_REFUSAL_KINDS_V1,
    ALLOCATION_PROJECTION_REJECT_CODES_V1,
    AllocationProjectionRejectCodeV1,
    AllocationProjectionRejectedV1,
    _external_rows_v1,
    _Reject,
    _terminal_rows_v1,
    project_allocation_certificate_v1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    EconomicAmountV1,
    LaneIdV1,
    OutboxStatusV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
    canonical_global_bytes_v1,
)
from tests.core.test_global_accounting_allocation_certificate_v1_golden import _fixture, _witnessed
from tools import render_global_accounting_allocation_certificate_v1_golden as renderer


def _project(state, roots=()):
    return project_allocation_certificate_v1(state, roots)


# The two fixture states no certificate can reconcile for a reason that is not allocation:
# an enabled lane whose registry entry has no producer, and a registered-empty lane
# committed at a foreign root. The projection now REFUSES both (it used to derive a
# certificate and leave the checker to reject it, which is what the second P39 reviewer
# found: the module's claim carried no exception, and the exception lived only here). Each
# maps its projection code to the checker code the state would have raised, and every test
# below proves the second by running the checker rather than trusting the first.
_STATE_LEVEL_REFUSALS = {
    "rejects_enabled_lane_without_receipt_backed_producer": (
        "PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER",
        "BLOCKED_LANE_PRODUCER_MISSING",
    ),
    "rejects_registered_empty_lane_with_foreign_root": (
        "PROJECTION_REGISTERED_EMPTY_ROOT_DRIFT",
        "REGISTERED_EMPTY_ROOT_DRIFT",
    ),
}



def _derive_rows(state):
    """Run the row derivation the way the entry point does, and return its refusal code.

    Under the current registry the only receipt-backed lane's producer emits controlled and
    entitlement rows only, so the entry point refuses a state that puts a reserve, a pending
    obligation or an open terminal on that lane BEFORE this logic runs
    (PROJECTION_ROWS_BEYOND_PRODUCER). TWELVE of the fourteen row cases are masked that way and
    exercise the helpers directly: they are the contract a future producer that can emit such
    rows would have to satisfy. TWO are not masked and reach their own code through the public
    entry point -- entitlements exceeding custody, and controlled atoms no obligation can
    absorb -- which is pinned as a partition by
    test_which_row_cases_the_entry_point_reaches_is_pinned rather than restated here. The
    earlier wording said none of the twelve was reachable, which was false for those two
    (Opus P40 P1-2, still standing in this docstring at P41).
    """

    controlled = tuple(
        cert.ControlledLocationRowV1(r.asset, r.owner, r.custody_domain, r.amount_atoms) for r in state.custody
    )
    entitlements = tuple(
        cert.ClaimantEntitlementRowV1(r.asset, r.owner, r.custody_domain, r.amount_atoms) for r in state.liabilities
    )
    reserves = tuple(
        cert.UnencumberedReserveRowV1(r.asset, r.owner, r.custody_domain, r.amount_atoms) for r in state.reserves
    )
    # Opus P40 P3-4: this harness stands in for the entry point, so it must select the lane
    # the way the entry point does -- the ENABLED one -- not lane zero. They agree for every
    # fixture here, and the case that would expose a difference is precisely the lane-identity
    # one (an OPEN obligation naming another lane).
    enabled = [root for root in state.lane_roots if root.enabled]
    assert len(enabled) <= 1, "the harness stands in for a single-owning-lane entry point"
    lane_root = enabled[0] if enabled else state.lane_roots[0]
    try:
        external = _external_rows_v1(state, controlled, entitlements, reserves)
        terminals = _terminal_rows_v1(state, lane_root.lane_id, lane_root.state_root, controlled, entitlements)
    except _Reject as rejected:
        return rejected.code, rejected.detail
    return external, terminals


def _state_consistent_candidate(state, *, source_principal: str | None = None, zero_residual: bool = False):
    """A certificate the state implies, built without the projection.

    Every field a fragment can carry is copied from the state, so a checker refusal of
    this candidate is a fact about the state and not about how the projection chose to
    derive. ``source_principal`` supplies the one field V1 state does not carry: a PENDING
    outbox entry names no principal, so where the state leaves that open this builder makes
    the choice explicit and the caller can enumerate it. With it set, the single PENDING
    entry becomes an external row over the single open residual cell.

    WHAT THIS DOES NOT COVER: it CHOOSES the first control domain and controlling principal
    in canonical order, so for a state with an OPEN terminal obligation it is one candidate
    among more than one, and a refusal of it is not by itself a statement about every
    certificate over that state. The earlier wording gave a false reason -- "it builds no
    terminal binding rows", which it has built since C9c-4 -- and both P41 reviewers found
    that independently (Opus P42 P2-4).
    """

    base = cert.build_registered_empty_certificate_v1(state)
    # The same lane selection as the entry point (Opus P40 P3-4), and the fragment slot that
    # goes with it, so the candidate is built on the lane the state actually enables.
    enabled = [
        (index, root) for index, root in enumerate(state.lane_roots) if root.enabled
    ]
    assert len(enabled) <= 1, "the candidate builder assumes a single owning lane"
    slot, lane_root = enabled[0] if enabled else (0, state.lane_roots[0])
    fragment = replace(
        base.ordered_lane_fragments[slot],
        enabled=lane_root.enabled,
        lane_state_root=lane_root.state_root,
        binding_root=lane_root.state_root,
        producer_kind=cert.LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane_root.lane_id][0],
        controlled_locations=tuple(
            cert.ControlledLocationRowV1(r.asset, r.owner, r.custody_domain, r.amount_atoms)
            for r in state.custody
        ),
        claimant_entitlements=tuple(
            cert.ClaimantEntitlementRowV1(r.asset, r.owner, r.custody_domain, r.amount_atoms)
            for r in state.liabilities
        ),
        unencumbered_reserves=tuple(
            cert.UnencumberedReserveRowV1(r.asset, r.owner, r.custody_domain, r.amount_atoms)
            for r in state.reserves
        ),
    )
    terminal_rows = []
    for terminal in state.terminal_obligations:
        if terminal.status is not TerminalObligationStatusV1.OPEN:
            continue
        # The two fields V1 state does not carry are taken from the state where it names
        # exactly one, and from the first candidate in canonical order where it names
        # several: a candidate must exist for the checker to refuse, and where the choice
        # is open ANY choice is a candidate. Where no candidate exists at all (no
        # entitlement, no controlling principal) the row is built with the claimant's own
        # name and an empty domain, which the checker refuses on the binding check.
        domains = sorted(
            {
                row.control_domain
                for row in fragment.claimant_entitlements
                if row.asset == terminal.asset and row.claimant == terminal.claimant
            }
        )
        # A row type refuses an empty control domain, so where the state entitles the
        # claimant nowhere the candidate borrows a domain the fragment actually controls
        # (and failing that, a syntactically valid placeholder). The checker then refuses
        # the binding, which is the point: a candidate has to be constructible for its
        # refusal to be evidence.
        fallback = sorted({row.control_domain for row in fragment.controlled_locations})
        domain = domains[0] if domains else (fallback[0] if fallback else "unbound")
        principals = sorted(
            {
                row.controlling_principal
                for row in fragment.controlled_locations
                if (row.asset, row.control_domain) == (terminal.asset, domain)
            }
        )
        terminal_rows.append(
            cert.TerminalBindingRowV1(
                obligation_id=terminal.obligation_id,
                asset=terminal.asset,
                claimant=terminal.claimant,
                amount_atoms=terminal.amount_atoms,
                control_domain=domain,
                controlling_principal=principals[0] if principals else terminal.claimant,
                lane_id=terminal.lane_id,
                lane_state_root=lane_root.state_root,
            )
        )
    if terminal_rows:
        fragment = replace(
            fragment, terminal_bindings=tuple(sorted(terminal_rows, key=lambda row: row.obligation_id))
        )
    if source_principal is not None:
        controlled_rows = fragment.controlled_locations
        claimed: dict[tuple[str, str], int] = {}
        for row in fragment.claimant_entitlements:
            key = (row.asset, row.control_domain)
            claimed[key] = claimed.get(key, 0) + row.amount_atoms
        for row in fragment.unencumbered_reserves:
            key = (row.asset, row.control_domain)
            claimed[key] = claimed.get(key, 0) + row.amount_atoms
        open_cells = {}
        for row in controlled_rows:
            key = (row.asset, row.control_domain)
            open_cells[key] = open_cells.get(key, 0) + row.amount_atoms
        residual = {k: v - claimed.get(k, 0) for k, v in open_cells.items()}
        pending = tuple(r for r in state.outbox if r.status is OutboxStatusV1.PENDING)
        if zero_residual:
            # The single controlled cell, carrying zero atoms: the only row the state admits
            # when nothing is left over (Opus P41 P2-3).
            cells = sorted({(row.asset, row.control_domain) for row in controlled_rows})
            assert len(cells) == 1 and len(pending) == 1, (cells, len(pending))
            (asset, control_domain), amount = cells[0], 0
        else:
            open_cells = {k: v for k, v in residual.items() if v > 0}
            assert len(pending) == 1 and len(open_cells) == 1, (len(pending), open_cells)
            (asset, control_domain), amount = next(iter(open_cells.items()))
        assert any(
            (r.asset, r.control_domain, r.controlling_principal) == (asset, control_domain, source_principal)
            for r in controlled_rows
        ), source_principal
        fragment = replace(
            fragment,
            pending_external_obligations=(
                cert.PendingExternalObligationRowV1(
                    effect_id=pending[0].effect_id,
                    asset=asset,
                    amount_atoms=amount,
                    destination_id=pending[0].destination_id,
                    commitment_root=pending[0].payload_hash,
                    control_domain=control_domain,
                    source_principal=source_principal,
                ),
            ),
        )
    fragments = tuple(
        fragment if index == slot else existing
        for index, existing in enumerate(base.ordered_lane_fragments)
    )
    return renderer._certificate_with_fragments(base, fragments)


def _no_certificate_reconciles(state) -> str:
    """Return the checker code that refuses the state-consistent candidate's rows.

    Opus P39 P1-1's method, adopted as this suite's standard: a refusal is called
    UNRECONCILABLE only when the certificate the state itself implies is shown to be
    refused, never because the projection said so.
    """

    candidate = _state_consistent_candidate(state)
    for check in (cert._check_exactly_once,):
        try:
            check(candidate)
        except cert._Reject as rejected:
            return rejected.code.value
    for check in (
        cert._check_entitlement_rows,
        cert._check_external_obligations,
        cert._check_terminal_bindings,
        cert._check_lane_aggregates,
    ):
        try:
            check(candidate, state)
        except cert._Reject as rejected:
            return rejected.code.value
    try:
        cert._check_terminal_totals(candidate)
    except cert._Reject as rejected:
        return rejected.code.value
    return "ACCEPTED"


def _no_certificate_binds(state) -> str:
    """Return the checker code that refuses the state-consistent candidate's lane bindings.

    The lane-binding pass is where the two state-level gates live, and neither depends on
    any field the projection chooses: the candidate copies ``enabled``, ``lane_state_root``
    and the registered producer kind straight off the state. So a code returned here under
    EMPTY witness slots is a code no arrangement of rows can avoid, which is what justifies
    the projection refusing instead of deriving.

    It is NOT necessarily the code every certificate over the state receives: the witness
    pass runs between the two gates, so a state that also enables the receipt-backed lane
    can receive RECEIPT_WITNESS_REQUIRED here while the projection reports the drift code
    (Opus P41 P2-6). Both refuse; they differ in which obligation they name first.
    """

    candidate = _state_consistent_candidate(state)
    try:
        cert._check_lane_bindings(candidate, state, cert.EMPTY_LANE_WITNESS_SLOTS_V1)
    except cert._Reject as rejected:
        return rejected.code.value
    return "BOUND"


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
        if name in _STATE_LEVEL_REFUSALS:
            projection_code, checker_code = _STATE_LEVEL_REFUSALS[name]
            assert projected.code.value == projection_code, (name, projected.code)
            # The refusal is justified here, not asserted: the candidate the state itself
            # implies gets exactly this code from the checker's lane-binding pass.
            assert _no_certificate_binds(state) == checker_code, name
            return
        assert projected.code in {
            AllocationProjectionRejectCodeV1.PROJECTION_NO_LANE_FOR_ROWS,
            AllocationProjectionRejectCodeV1.PROJECTION_MULTIPLE_ENABLED_LANES,
            AllocationProjectionRejectCodeV1.PROJECTION_BINDING_ROOT_MISSING,
        }, projected
        return
    assert name not in _STATE_LEVEL_REFUSALS, name
    outcome = cert.check_global_accounting_allocation_certificate_v1(
        projected, state, cert.EMPTY_LANE_WITNESS_SLOTS_V1
    )
    assert isinstance(outcome, cert.AllocationCertificateAcceptedV1), (name, outcome)


def test_the_fixture_partition_of_states_is_pinned() -> None:
    """The three buckets above, counted, with the accepted bucket CHECKED.

    The count alone would pass while the derived certificates were wrong, so the
    accepted bucket is counted only when the checker actually accepts the projection.
    """

    buckets: dict[str, int] = {"accept": 0, "projection_refusal": 0, "state_level_refusal": 0}
    for name in renderer.VECTORS_V1:
        _obligation, spec, _mutation = renderer.VECTORS_V1[name]
        state = renderer.build_state_v1(spec)
        projected = _project(state)
        if isinstance(projected, AllocationProjectionRejectedV1):
            if name in _STATE_LEVEL_REFUSALS:
                assert _no_certificate_binds(state) == _STATE_LEVEL_REFUSALS[name][1], name
                buckets["state_level_refusal"] += 1
            else:
                buckets["projection_refusal"] += 1
            continue
        outcome = cert.check_global_accounting_allocation_certificate_v1(
            projected, state, cert.EMPTY_LANE_WITNESS_SLOTS_V1
        )
        assert isinstance(outcome, cert.AllocationCertificateAcceptedV1), (name, outcome)
        buckets["accept"] += 1
    assert buckets == {"accept": 20, "projection_refusal": 7, "state_level_refusal": 2}
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


def test_a_terminal_with_no_controlling_principal_is_unreconcilable_not_ambiguous() -> None:
    """Opus P40 P2-3: zero candidate principals was reported with an UNDETERMINED code.

    Zero candidates means no controlled location can bind the row, so no certificate over
    the state is acceptable -- the same misclassification P39 P1-1 found for unassignable
    atoms, surviving inside its repair. It now raises PROJECTION_TERMINAL_WITHOUT_BACKING,
    which the kinds table places in the UNRECONCILABLE kind.

    The branch is unreachable through the PUBLIC ENTRY POINT on all twelve lanes: on
    ASSET_TRANSFER an OPEN terminal is masked by PROJECTION_ROWS_BEYOND_PRODUCER, and on the
    other eleven by PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER.

    Through the row harness it IS reachable, by exactly one shape: a zero-atom entitlement in
    the claimant's ONLY entitled domain, with a zero-atom obligation. The residual for that
    cell is zero so the negative-residual check does not fire, and with one candidate domain
    the capacity filter has nothing to reject (opus2 P42 P2-3 found this after the filter
    closed the previous route, and it is a _ROW_CASES entry now, so this code has a case in
    the table like every other). This test additionally calls the builder directly and checks
    that the entry point reports something else.
    """

    state = _backed_state((_terminal("terminal-1", 1),))
    controlled = (proj.ControlledLocationRowV1("USD", "pool-a", "vault", 10),)
    entitlements = (proj.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", 10),)
    with pytest.raises(proj._Reject) as raised:
        proj._terminal_rows_v1(
            state, state.lane_roots[0].lane_id, state.lane_roots[0].state_root, controlled, entitlements
        )
    assert raised.value.code is AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_WITHOUT_BACKING
    assert "no controlled location in spot-pool" in raised.value.detail
    assert (
        AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_WITHOUT_BACKING
        in ALLOCATION_PROJECTION_REFUSAL_KINDS_V1["unreconcilable"]
    )
    # The unreachability claim, checked rather than asserted: the same shape through the
    # entry point reports the code that actually fires first.
    unreachable = _backed_state(
        (_terminal("terminal-1", 1),),
        custody=(("pool-a", "USD", "vault", 10),),
        liabilities=(("alice", "USD", "spot-pool", 10),),
    )
    projected = _project(unreachable, _root_of(unreachable))
    assert isinstance(projected, AllocationProjectionRejectedV1)
    assert projected.code is not AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_WITHOUT_BACKING


def test_a_witnessed_lane_whose_rows_drift_from_its_receipt_is_refused() -> None:
    """opus2 P40 P2-7, closed where the caller can close it.

    A minted witness is determined by the committed lane root: the producer folds the
    custody the receipt admitted. So a state whose ASSET_TRANSFER rows differ from that
    receipt's has NO accepted certificate -- one extra atom on a custody row is enough --
    and the projection used to derive one anyway, because V1 state does not carry the
    receipt's rows and the state alone cannot reveal the difference.

    It can when the caller supplies the witness, which is the same object the checker
    requires. With the witness the projection refuses; without it the derivation still
    happens and the checker's witness pass is what refuses -- so the limit is a property of
    what the caller passes, not a silent carve-out. Both halves are asserted here.
    """

    witness, state, _certificate, slots = _witnessed(with_rows=True)
    roots = ((LaneIdV1.ASSET_TRANSFER, witness.fragment.binding_root),)
    drifted = replace(
        state,
        custody=tuple(
            replace(row, amount_atoms=row.amount_atoms + 1) if index == 0 else row
            for index, row in enumerate(state.custody)
        ),
        liabilities=tuple(
            replace(row, amount_atoms=row.amount_atoms + 1) if index == 0 else row
            for index, row in enumerate(state.liabilities)
        ),
    )

    # Without the witness: derived, and the checker's witness pass is what refuses.
    derived = project_allocation_certificate_v1(drifted, roots)
    assert isinstance(derived, cert.GlobalAccountingAllocationCertificateV1), derived
    outcome = cert.check_global_accounting_allocation_certificate_v1(derived, drifted, slots)
    assert isinstance(outcome, cert.AllocationCertificateRejectedV1), outcome
    assert outcome.code is cert.AllocationCertificateRejectCodeV1.RECEIPT_WITNESS_FRAGMENT_DRIFT

    # With the witness: refused before anything is derived from it.
    refused = project_allocation_certificate_v1(drifted, roots, slots)
    assert isinstance(refused, AllocationProjectionRejectedV1), refused
    assert refused.code is AllocationProjectionRejectCodeV1.PROJECTION_WITNESS_FRAGMENT_DRIFT
    assert refused.detail.startswith(LaneIdV1.ASSET_TRANSFER.value)
    assert refused.state_root == drifted.state_root

    # And the undrifted state still projects to exactly the witness's fragment, so the new
    # check refuses drift rather than refusing witnesses.
    agreed = project_allocation_certificate_v1(state, roots, slots)
    assert isinstance(agreed, cert.GlobalAccountingAllocationCertificateV1), agreed
    assert agreed.ordered_lane_fragments[0] == witness.fragment


def test_the_witness_slots_are_exactly_typed() -> None:
    """The witness input takes the checker's own slot shape and nothing else."""

    witness, state, _certificate, slots = _witnessed(with_rows=True)
    roots = ((LaneIdV1.ASSET_TRANSFER, witness.fragment.binding_root),)
    with pytest.raises(TypeError, match="exact tuple"):
        project_allocation_certificate_v1(state, roots, list(slots))  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="one slot per lane"):
        project_allocation_certificate_v1(state, roots, (None,))
    with pytest.raises(TypeError, match="exact minted witness"):
        project_allocation_certificate_v1(state, roots, (witness.fragment,) + (None,) * 11)  # type: ignore[arg-type]


def test_a_state_level_code_is_not_always_the_checkers_first_code() -> None:
    """Opus P41 P2-6, pinned as a counterexample rather than restated as a caveat.

    The receipt-witness check runs BETWEEN the two state-level gates, so a state that
    enables the receipt-backed lane and also drifts a registered-empty root gets
    RECEIPT_WITNESS_REQUIRED from the checker under empty slots while the projection reports
    the drift code. The refusal is sound either way -- no arrangement of rows or witnesses
    makes this state acceptable -- and what this pins is that the two codes may differ, so
    the docstrings claim ordering only among the two gates.
    """

    state = _backed_state()
    foreign = "0x" + "ab" * 32
    drifted = replace(
        state,
        lane_roots=tuple(
            replace(root, state_root=foreign) if root.lane_id is LaneIdV1.PROOF_REWARDS else root
            for root in state.lane_roots
        ),
    )
    projected = _project(drifted, _root_of(drifted))
    assert isinstance(projected, AllocationProjectionRejectedV1)
    assert projected.code is AllocationProjectionRejectCodeV1.PROJECTION_REGISTERED_EMPTY_ROOT_DRIFT
    assert _no_certificate_binds(drifted) == "RECEIPT_WITNESS_REQUIRED"


def test_a_pending_row_over_no_residual_cell_is_declined_not_called_ambiguous() -> None:
    """Opus P41 P2-3: this branch reported an ambiguity for a DETERMINED state.

    One controlled cell, fully claimed, one PENDING entry: the residual is empty, so any
    certificate's external row must carry zero atoms, over the only cell the fragment
    controls, sourced by the only principal that controls it. Exactly one certificate passes
    the row checks, which this test exhibits -- so the state is determined and the old
    ..._AMBIGUOUS code said otherwise. The projection still declines to derive a zero-atom
    row (no producer has ever emitted one), and now says so with a code in its own kind.
    """

    state = _backed_state(
        (),
        custody=(("pool-a", "USD", "vault", 10),),
        liabilities=(("alice", "USD", "vault", 10),),
        outbox=((renderer._root(9_001), "dest-1", renderer._root(9_002), renderer._root(9_003), "PENDING"),),
    )
    observed, detail = _derive_rows(state)
    assert observed is AllocationProjectionRejectCodeV1.PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED
    assert "no residual cells" in detail
    assert (
        AllocationProjectionRejectCodeV1.PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED
        in ALLOCATION_PROJECTION_REFUSAL_KINDS_V1["unsupported"]
    )

    # The state is determined: the one candidate the state implies passes every row check.
    candidate = _state_consistent_candidate(state, source_principal="pool-a", zero_residual=True)
    for check in (cert._check_exactly_once,):
        check(candidate)
    for check in (
        cert._check_entitlement_rows,
        cert._check_reserve_rows,
        cert._check_external_obligations,
        cert._check_terminal_bindings,
        cert._check_lane_aggregates,
    ):
        check(candidate, state)


def test_only_a_domain_that_can_carry_the_amount_is_a_candidate() -> None:
    """opus2 P41 P1-2 (B): two entitled domains were called an ambiguity when only one could
    host the row, so a DETERMINED state was reported as undetermined.

    The checker bounds each (asset, claimant, domain) key's terminal total by that key's
    entitlement, so a domain entitled below the amount cannot carry the row at all. With that
    filter the state determines the domain and the projection derives it; the reviewer's own
    state is the fixture. The two-candidate case still refuses, so the filter narrows the
    ambiguity rather than removing it.
    """

    determined = _backed_state(
        (_terminal("terminal-1", 5),),
        custody=(("pool-a", "USD", "spot-pool", 10), ("pool-b", "USD", "vault", 1)),
        liabilities=(("alice", "USD", "spot-pool", 10), ("alice", "USD", "vault", 1)),
    )
    _external, terminals = _derive_rows(determined)
    assert len(terminals) == 1
    assert terminals[0].control_domain == "spot-pool"
    assert terminals[0].amount_atoms == 5

    # Both domains can carry it: still refused, and still as an ambiguity.
    ambiguous = _backed_state(
        (_terminal("terminal-1", 1),),
        custody=(("pool-a", "USD", "spot-pool", 10), ("pool-b", "USD", "vault", 10)),
        liabilities=(("alice", "USD", "spot-pool", 10), ("alice", "USD", "vault", 10)),
    )
    observed, detail = _derive_rows(ambiguous)
    assert observed is AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS
    assert "2 entitlement domains" in detail


def test_the_terminal_domain_assignment_is_searched_not_decided_row_by_row() -> None:
    """Opus P42 P1-2: the per-row capacity filter still called two shapes ambiguous.

    The checker bounds the SUM of terminal rows per (asset, claimant, domain), so domains
    cannot be chosen one row at a time: a domain that fits one row may not fit it once
    another is placed there. A sweep found six misclassified states of two shapes. Both are
    fixtures here.

    Shape one, DETERMINED: two domains, two obligations, and exactly one assignment that
    fits. Shape two, UNRECONCILABLE: three obligations of 10 against two domains entitled 10
    each -- no assignment fits, so no certificate over the state is acceptable and calling it
    an ambiguity was false.
    """

    determined = _backed_state(
        (_terminal("t1", 10), _terminal("t2", 4)),
        custody=(("pool-a", "USD", "spot-pool", 10), ("pool-b", "USD", "vault", 4)),
        liabilities=(("alice", "USD", "spot-pool", 10), ("alice", "USD", "vault", 4)),
    )
    _external, terminals = _derive_rows(determined)
    assert {row.obligation_id: row.control_domain for row in terminals} == {
        "t1": "spot-pool",
        "t2": "vault",
    }

    unreconcilable = _backed_state(
        (_terminal("t1", 10), _terminal("t2", 10), _terminal("t3", 10)),
        custody=(("pool-a", "USD", "spot-pool", 10), ("pool-b", "USD", "vault", 10)),
        liabilities=(("alice", "USD", "spot-pool", 10), ("alice", "USD", "vault", 10)),
    )
    observed, detail = _derive_rows(unreconcilable)
    assert observed is AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT
    assert "no assignment of 3 obligations fits" in detail

    # And a genuine ambiguity still refuses as one: two obligations that fit either way.
    ambiguous = _backed_state(
        (_terminal("t1", 1), _terminal("t2", 1)),
        custody=(("pool-a", "USD", "spot-pool", 10), ("pool-b", "USD", "vault", 10)),
        liabilities=(("alice", "USD", "spot-pool", 10), ("alice", "USD", "vault", 10)),
    )
    observed, detail = _derive_rows(ambiguous)
    assert observed is AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS


def test_an_unsearchable_terminal_assignment_is_refused_not_truncated() -> None:
    """The cap is a refusal, not a truncation: a refusal must not depend on how much of the
    assignment space was examined."""

    import src.core.global_accounting_allocation_projection_v1 as module

    terminals = tuple(_terminal(f"t{index}", 1) for index in range(4))
    domains = tuple(f"domain-{index}" for index in range(9))
    capacity = {domain: 10 for domain in domains}
    assert len(domains) ** len(terminals) > module.TERMINAL_ASSIGNMENT_SEARCH_CAP_V1
    with pytest.raises(module._Reject) as raised:
        module._terminal_domain_assignment_v1(terminals, domains, capacity)
    assert raised.value.code is AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_ASSIGNMENT_UNSEARCHED


@pytest.mark.parametrize(
    "field",
    ["chain_id", "deployment_root", "profile_root", "writer_epoch"],
)
def test_a_witness_minted_under_another_header_is_refused(field: str) -> None:
    """The external reviewer's P1 against C9c-5, still firing at C9c-6's tip.

    The checker binds the witness's HEADER to the state in the pass immediately after the
    fragment comparison. C9c-5 copied the fragment comparison and not the header comparison
    beside it, so a witness minted under another deployment passed the projection and the
    checker then refused RECEIPT_WITNESS_HEADER_DRIFT -- a derive-then-reject at the public
    entry point, on the very argument the witness feature was added to check. Ten in-family
    reviews did not find it; one external review did, and named the shape: the repair copies
    the named field and not its neighbours.

    All four header fields are covered here rather than the one the reviewer exhibited.
    """

    witness, state, _certificate, slots = _witnessed(with_rows=True)
    roots = ((LaneIdV1.ASSET_TRANSFER, witness.fragment.binding_root),)
    assert isinstance(
        project_allocation_certificate_v1(state, roots, slots),
        cert.GlobalAccountingAllocationCertificateV1,
    ), "the undrifted state must still derive, or this test proves nothing"

    value = getattr(state, field)
    other = value + 1 if isinstance(value, int) else "0x" + "cd" * 32
    drifted = replace(state, **{field: other})
    refused = project_allocation_certificate_v1(drifted, roots, slots)
    assert isinstance(refused, AllocationProjectionRejectedV1), refused
    assert refused.code is AllocationProjectionRejectCodeV1.PROJECTION_WITNESS_HEADER_DRIFT
    assert refused.state_root == drifted.state_root

    # Without the guard the checker is what refuses, which is the defect: the projection
    # derived an object the checker must reject. Pinned so a regression is visible as the
    # thing it is.
    assert _no_certificate_binds(drifted) in {"RECEIPT_WITNESS_HEADER_DRIFT", "RECEIPT_WITNESS_REQUIRED"}


def test_an_empty_slot_on_an_enabled_receipt_backed_lane_is_refused() -> None:
    """The third derive-then-reject, found reviewing C9c-6 at its own tip.

    Supplying the twelve slots is a claim that they are the ones the checker requires, so an
    empty slot on an enabled receipt-backed lane is an incomplete argument -- not the
    disclosed no-witness residue, which is the caller passing NO slots at all. Before this
    guard the comparison loop skipped the empty slot, the projection derived, and the checker
    refused RECEIPT_WITNESS_REQUIRED.
    """

    witness, state, _certificate, _slots = _witnessed(with_rows=True)
    roots = ((LaneIdV1.ASSET_TRANSFER, witness.fragment.binding_root),)
    refused = project_allocation_certificate_v1(state, roots, cert.EMPTY_LANE_WITNESS_SLOTS_V1)
    assert isinstance(refused, AllocationProjectionRejectedV1), refused
    assert refused.code is AllocationProjectionRejectCodeV1.PROJECTION_WITNESS_REQUIRED
    assert LaneIdV1.ASSET_TRANSFER.value in refused.detail

    # Passing NO slots is the documented residue and still derives, so the new code refuses an
    # incomplete argument rather than the absence of one.
    assert isinstance(
        project_allocation_certificate_v1(state, roots),
        cert.GlobalAccountingAllocationCertificateV1,
    )


@pytest.mark.parametrize(
    ("label", "tables"),
    [
        pytest.param("zero-custody", {"custody": (("alice", "USD", "d1", 0),), "liabilities": ()}, id="zero-custody-row"),
        pytest.param("zero-liability", {"custody": (), "liabilities": (("alice", "USD", "d1", 0),)}, id="zero-liability-row"),
        pytest.param(
            "cross-key",
            {"custody": (("alice", "USD", "d1", 0),), "liabilities": (("alice", "USD", "d2", 0),)},
            id="cross-key-zero-rows",
        ),
    ],
)
def test_a_zero_amount_economic_row_is_refused_not_derived(label: str, tables: dict) -> None:
    """Codex's metamorphic matrix, P2-1: absent and zero support are not interchangeable.

    The checker compares support DICTIONARIES, so a zero-amount row is a present key with
    value zero on one side and no key at all on the other. The projection derived, and the
    derived certificate failed SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE. Sixteen invocation
    cases over twelve state roots in that matrix; these are its three minima.

    Both halves are pinned: the state is refused now, AND the certificate that used to be
    derived is shown to fail the checker's partition pass, so the refusal is justified rather
    than asserted. At the public entry point the witness gate masked the row failure, which is
    why this is checked against the row passes directly.
    """

    state = _backed_state((), outbox=(), **tables)
    refused = _project(state, _root_of(state))
    assert isinstance(refused, AllocationProjectionRejectedV1), refused
    assert refused.code is AllocationProjectionRejectCodeV1.PROJECTION_NONCANONICAL_ZERO_ECONOMIC_ROW
    assert (
        AllocationProjectionRejectCodeV1.PROJECTION_NONCANONICAL_ZERO_ECONOMIC_ROW
        in ALLOCATION_PROJECTION_REFUSAL_KINDS_V1["unreconcilable"]
    )

    # The refusal is justified: the candidate the state implies fails the partition pass.
    candidate = _state_consistent_candidate(state)
    with pytest.raises(cert._Reject) as raised:
        cert._check_exactly_once(candidate)
    assert raised.value.code.value == "SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE"


def test_a_caller_input_refusal_says_nothing_about_the_state() -> None:
    """Codex C9c-5 P2-3, pinned rather than argued.

    Under a state-existential reading, a projection that refuses a state which HAS an accepted
    certificate is a counterexample. Four such invocations exist and all four are refusals of
    the ARGUMENT: an unexpected binding root on a state whose registered-empty certificate the
    checker accepts. The claim is over a well-formed invocation, and this exhibits both sides
    of that distinction in one test so the scoping cannot quietly become a universal claim.
    """

    state = renderer.build_state_v1(renderer._spec())
    accepted = cert.build_registered_empty_certificate_v1(state)
    outcome = cert.check_global_accounting_allocation_certificate_v1(
        accepted, state, cert.EMPTY_LANE_WITNESS_SLOTS_V1
    )
    assert isinstance(outcome, cert.AllocationCertificateAcceptedV1), outcome

    # The same state, with a binding root no enabled receipt-backed lane asked for.
    refused = _project(state, ((LaneIdV1.ASSET_TRANSFER, state.lane_roots[0].state_root),))
    assert isinstance(refused, AllocationProjectionRejectedV1), refused
    assert refused.code is AllocationProjectionRejectCodeV1.PROJECTION_BINDING_ROOT_UNEXPECTED
    assert refused.code in ALLOCATION_PROJECTION_REFUSAL_KINDS_V1["caller_input"]

    # And the well-formed invocation over the same state derives.
    assert isinstance(_project(state), cert.GlobalAccountingAllocationCertificateV1)


def test_the_three_refusal_kinds_partition_the_family() -> None:
    """Both P40 reviews, P3-1: the prose split omitted three of its thirteen codes,
    PROJECTION_ROWS_BEYOND_PRODUCER among them -- the guard the candidate was named for.
    The kinds are data now, and this pins them as a partition so the docstring cannot
    describe a family it does not cover."""

    kinds = ALLOCATION_PROJECTION_REFUSAL_KINDS_V1
    assert set(kinds) == {"caller_input", "undetermined", "unsupported", "unreconcilable"}
    flat = [code for members in kinds.values() for code in members]
    assert len(flat) == len(set(flat)), "a code appears in two kinds"
    assert set(flat) == set(AllocationProjectionRejectCodeV1), "kinds do not cover the family"
    assert {c.name for c in kinds["undetermined"]} == {
        "PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS",
        "PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS",
    }
    # Every code named in the family docstring's three kinds is a real member, and every
    # member is named there: the docstring is the claim, so it is scanned.
    doc = AllocationProjectionRejectCodeV1.__doc__ or ""
    for code in AllocationProjectionRejectCodeV1:
        assert code.name.replace("PROJECTION_", "..._") in doc, code.name


def test_reject_codes_are_closed_and_ordered() -> None:
    """The reject family is the declaration order of the enum, and every code is NAMED
    somewhere in this module.

    Opus P40 P3-6: the previous docstring said "asserted by a test" and "scanning this
    file's own assertions", which is stronger than what runs. The scan is textual over the
    whole file, so a code named only in a comment or a docstring would satisfy it. What
    this establishes is that no code can be added to the family without appearing here at
    all; that each code has a test which REACHES it is established by the tests above, one
    per code, not by this scan."""

    assert ALLOCATION_PROJECTION_REJECT_CODES_V1 == tuple(
        code.value for code in AllocationProjectionRejectCodeV1
    )
    assert len(ALLOCATION_PROJECTION_REJECT_CODES_V1) == 22
    import re as _re
    from pathlib import Path as _Path

    source = _Path(__file__).read_text(encoding="utf-8")
    asserted = set(_re.findall(r"AllocationProjectionRejectCodeV1\.([A-Z_]+)", source))
    missing = {code.name for code in AllocationProjectionRejectCodeV1} - asserted
    assert not missing, sorted(missing)
    assert len(ALL_LANE_IDS_V1) == 12


@pytest.mark.parametrize(
    ("vector", "code", "checker_code"),
    [
        pytest.param(
            "rejects_enabled_lane_without_receipt_backed_producer",
            AllocationProjectionRejectCodeV1.PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER,
            "BLOCKED_LANE_PRODUCER_MISSING",
            id="enabled-lane-without-producer",
        ),
        pytest.param(
            "rejects_registered_empty_lane_with_foreign_root",
            AllocationProjectionRejectCodeV1.PROJECTION_REGISTERED_EMPTY_ROOT_DRIFT,
            "REGISTERED_EMPTY_ROOT_DRIFT",
            id="registered-empty-root-drift",
        ),
    ],
)
def test_the_two_state_level_shapes_are_refused_not_derived(vector, code, checker_code) -> None:
    """opus2 P39 P2-5: these two used to be derived and left for the checker to reject.

    The claim "a derived certificate is accepted" carried no exception, and the exception
    lived in this file. Now the projection refuses both, through the public entry point,
    with a code that names which state-level gate the state fails; and the refusal is
    justified by running the checker's lane-binding pass over the candidate the state
    itself implies, which no certificate over this state can avoid.
    """

    _obligation, spec, _mutation = renderer.VECTORS_V1[vector]
    state = renderer.build_state_v1(spec)
    projected = _project(state)
    assert isinstance(projected, AllocationProjectionRejectedV1), projected
    assert projected.code is code
    assert projected.state_root == state.state_root
    assert _no_certificate_binds(state) == checker_code


def test_a_state_level_refusal_precedes_the_allocation_refusals() -> None:
    """The two families are ordered, and the order is the checker's own.

    A blocked lane that ALSO carries rows a receipt producer could not source must report
    the state-level code, because that is the code the checker raises first: reporting the
    allocation code would name a repair (move the rows) that cannot make the state
    acceptable.
    """

    _obligation, blocked_spec, _mutation = renderer.VECTORS_V1[
        "rejects_enabled_lane_without_receipt_backed_producer"
    ]
    spec = dict(blocked_spec)
    spec["custody"] = [("pool-a", "USD", "vault", 100)]
    spec["reserves"] = [("pool-a", "USD", "vault", 100)]
    state = renderer.build_state_v1(spec)
    assert state.custody and state.reserves, "the constructed state must carry both kinds of row"
    projected = _project(state)
    assert isinstance(projected, AllocationProjectionRejectedV1)
    assert projected.code is AllocationProjectionRejectCodeV1.PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER
    assert _no_certificate_binds(state) == "BLOCKED_LANE_PRODUCER_MISSING"



# --- P38 repairs: rows, unreconcilable states, and the guards that had no test ----------


def test_witnessed_certificate_with_rows_is_reproduced_byte_for_byte() -> None:
    """Opus P38 P2-2 and opus2 P2-2: the byte-for-byte claim was made about a witness with
    no rows. This witness's receipt proved a custody row, and the projection still
    reproduces the witnessed certificate exactly from the state plus the receipt root."""

    witness, state, certificate, slots = _witnessed(with_rows=True)
    assert not witness.fragment.is_empty
    # The shape this covers, stated rather than implied (Opus P39 P3-5): one custody row and
    # one entitlement row whose claimant equals the controlling principal, and no reserve,
    # external or terminal rows. Wider shapes need a witness the admission fixture cannot mint
    # yet, so the byte-for-byte claim is established for this shape only.
    assert len(witness.fragment.controlled_locations) == 1
    assert len(witness.fragment.claimant_entitlements) == 1
    assert not witness.fragment.unencumbered_reserves
    assert not witness.fragment.pending_external_obligations
    assert not witness.fragment.terminal_bindings
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


_ROW_CASES = [
        (
            "one terminal over-claiming its entitlement",
            {}, (("terminal-1", 99),),
            AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT,
            "no assignment of 1 obligations fits",
        ),
        (
            "two terminals over-claiming together",
            {"custody": (("pool-a", "USD", "spot-pool", 3),), "liabilities": (("alice", "USD", "spot-pool", 3),)},
            (("terminal-1", 2), ("terminal-2", 2)),
            AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT,
            "no assignment of 2 obligations fits",
        ),
        (
            "a claimant with no entitlement at all",
            {}, (("terminal-1", 1, {"claimant": "mallory"}),),
            AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_WITHOUT_ENTITLEMENT,
            "no entitlement for mallory",
        ),
        (
            "a claimant entitled in two domains",
            {
                "custody": (("pool-a", "USD", "spot-pool", 6), ("pool-a", "USD", "vault", 4)),
                "liabilities": (("alice", "USD", "spot-pool", 6), ("alice", "USD", "vault", 4)),
            },
            (("terminal-1", 3),),
            AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS,
            "2 entitlement domains",
        ),
        (
            "two principals controlling the terminal's domain",
            {
                "custody": (("pool-a", "USD", "spot-pool", 6), ("pool-b", "USD", "spot-pool", 4)),
                "liabilities": (("alice", "USD", "spot-pool", 10),),
            },
            (("terminal-1", 3),),
            AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS,
            "2 principals",
        ),
        (
            "entitlements exceeding custody",
            {"custody": (("pool-a", "USD", "spot-pool", 3),), "liabilities": (("alice", "USD", "spot-pool", 5),)},
            (),
            AllocationProjectionRejectCodeV1.PROJECTION_NEGATIVE_RESIDUAL,
            "exceed custody for USD:spot-pool",
        ),
        (
            "controlled atoms no obligation can absorb",
            {"liabilities": (("alice", "USD", "spot-pool", 4),)},
            (),
            AllocationProjectionRejectCodeV1.PROJECTION_UNASSIGNED_CONTROLLED_ATOMS,
            "1 residual cells for 0 pending obligations",
        ),
        (
            "two residual cells for one obligation",
            {
                "custody": (("pool-a", "USD", "spot-pool", 6), ("pool-a", "EUR", "spot-pool", 4)),
                "liabilities": (),
                "outbox": ((renderer._root(9_001), "dest-1", renderer._root(9_002), renderer._root(9_003), "PENDING"),),
            },
            (),
            AllocationProjectionRejectCodeV1.PROJECTION_UNASSIGNED_CONTROLLED_ATOMS,
            "2 residual cells for 1 pending obligations",
        ),
        (
            "an obligation with no controlled location behind it",
            {
                "custody": (),
                "liabilities": (),
                "outbox": ((renderer._root(9_001), "dest-1", renderer._root(9_002), renderer._root(9_003), "PENDING"),),
            },
            (),
            AllocationProjectionRejectCodeV1.PROJECTION_PENDING_WITHOUT_BACKING,
            "1 pending obligations with no controlled location",
        ),
        (
            "two obligations over one residual cell",
            {
                "custody": (("pool-a", "USD", "spot-pool", 10),),
                "liabilities": (),
                "outbox": (
                    (renderer._root(9_001), "dest-1", renderer._root(9_002), renderer._root(9_003), "PENDING"),
                    (renderer._root(9_011), "dest-2", renderer._root(9_012), renderer._root(9_013), "PENDING"),
                ),
            },
            (),
            AllocationProjectionRejectCodeV1.PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS,
            "2 pending rows for 1 residual cells",
        ),
        (
            "two principals controlling the residual cell",
            {
                "custody": (("pool-a", "USD", "spot-pool", 6), ("pool-b", "USD", "spot-pool", 4)),
                "liabilities": (),
                "outbox": ((renderer._root(9_001), "dest-1", renderer._root(9_002), renderer._root(9_003), "PENDING"),),
            },
            (),
            AllocationProjectionRejectCodeV1.PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS,
            "2 principals control USD:spot-pool",
        ),
        (
            "a zero-atom entitlement cannot host a positive claim",
            {
                "custody": (("pool-a", "USD", "vault", 10),),
                "liabilities": (("bob", "USD", "vault", 10), ("alice", "USD", "spot-pool", 0)),
            },
            (("terminal-1", 1),),
            AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT,
            "no assignment of 1 obligations fits",
        ),
        (
            "a zero-atom entitlement in the claimant's only entitled domain, backed nowhere",
            {
                "custody": (("pool-a", "USD", "spot-pool", 10),),
                "liabilities": (("bob", "USD", "spot-pool", 10), ("alice", "USD", "vault", 0)),
            },
            (("terminal-1", 0),),
            AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_WITHOUT_BACKING,
            "no controlled location in vault",
        ),
        (
            "an OPEN obligation naming another lane",
            {}, (("terminal-1", 1, {"lane": LaneIdV1.SPOT_LIQUIDITY}),),
            AllocationProjectionRejectCodeV1.PROJECTION_NO_LANE_FOR_ROWS,
            "names SPOT_LIQUIDITY",
        ),
    ]


@pytest.mark.parametrize(
    ("label", "tables", "terminals", "code", "detail"),
    _ROW_CASES,
    ids=[case[0].replace(" ", "-") for case in _ROW_CASES],
)
def test_row_derivation_refuses_every_shape_the_state_leaves_open_or_impossible(
    label: str, tables: dict, terminals: tuple, code, detail: str
) -> None:
    """The row-derivation contract, exercised through the helpers.

    Each case names one shape and the code it must produce. They run through _derive_rows
    rather than the entry point because the entry refuses earlier for the only registered
    receipt-backed lane (see the harness docstring): today no producer can emit a reserve,
    external or terminal row, so this is the contract a future one would have to meet.
    """

    state = _backed_state(
        tuple(_terminal(t[0], t[1], **(t[2] if len(t) > 2 else {})) for t in terminals), **tables
    )
    observed, observed_detail = _derive_rows(state)
    assert observed is code, (label, observed, observed_detail)
    assert detail in observed_detail, (label, observed_detail)


_UNRECONCILABLE_ROW_CODES = {
    AllocationProjectionRejectCodeV1.PROJECTION_NEGATIVE_RESIDUAL,
    AllocationProjectionRejectCodeV1.PROJECTION_UNASSIGNED_CONTROLLED_ATOMS,
    AllocationProjectionRejectCodeV1.PROJECTION_PENDING_WITHOUT_BACKING,
    AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_WITHOUT_ENTITLEMENT,
    AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT,
    AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_WITHOUT_BACKING,
    AllocationProjectionRejectCodeV1.PROJECTION_NO_LANE_FOR_ROWS,
}


@pytest.mark.parametrize(
    ("label", "tables", "terminals", "code"),
    [(c[0], c[1], c[2], c[3]) for c in _ROW_CASES if c[3] in _UNRECONCILABLE_ROW_CODES],
    ids=[c[0].replace(" ", "-") for c in _ROW_CASES if c[3] in _UNRECONCILABLE_ROW_CODES],
)
def test_an_unreconcilable_row_case_has_its_state_consistent_candidate_refused(
    label: str, tables: dict, terminals: tuple, code
) -> None:
    """The evidence standard this suite claims, actually run (both P40 reviews, P1).

    ``_no_certificate_reconciles`` was defined and never called, while three places said
    the suite establishes UNRECONCILABLE by building the certificate the state implies and
    having the checker refuse it. Here it is called: for every row case classified
    UNRECONCILABLE, the state-consistent candidate is built without the projection and the
    checker's row, partition and aggregate passes refuse it.

    What this shows is exactly one thing: THAT candidate is refused. For a state with an
    OPEN terminal obligation the builder CHOOSES the first domain and principal in canonical
    order, so other candidates exist and this is evidence about one of them, not a quantifier
    over all (the earlier wording said the builder omits terminal rows, which is false). The states with neither a
    PENDING entry nor an OPEN terminal are the ones where the built candidate IS the only
    certificate the state implies up to the choices the checker itself pins.
    """

    state = _backed_state(
        tuple(_terminal(t[0], t[1], **(t[2] if len(t) > 2 else {})) for t in terminals), **tables
    )
    observed = _no_certificate_reconciles(state)
    assert observed != "ACCEPTED", (label, code)
    assert observed in {c.value for c in cert.AllocationCertificateRejectCodeV1}, observed


def test_an_undetermined_state_admits_two_row_checked_certificates_with_different_roots() -> None:
    """The other half of the standard, and the correction opus2 P40 P1-1 asked for.

    UNDETERMINED does NOT mean two ACCEPTED certificates exist: under the current registry
    no accepted certificate can carry an external row at all, because the only receipt-backed
    lane needs a minted witness whose fragment must EQUAL the certificate's. What it means is
    that the state does not determine the answer, and that is exhibited here: two different
    source principals both pass every row, partition and aggregate check, with DIFFERENT
    allocation roots, so nothing in the state picks one. The full checker then refuses both,
    for the structural reason, which is why the projection refuses too.
    """

    state = _backed_state(
        (),
        custody=(("pool-a", "USD", "spot-pool", 6), ("pool-b", "USD", "spot-pool", 4)),
        liabilities=(),
        outbox=((renderer._root(9_001), "dest-1", renderer._root(9_002), renderer._root(9_003), "PENDING"),),
    )
    roots = set()
    full = set()
    for principal in ("pool-a", "pool-b"):
        candidate = _state_consistent_candidate(state, source_principal=principal)
        for check in (cert._check_exactly_once,):
            check(candidate)
        for check in (
            cert._check_entitlement_rows,
            cert._check_reserve_rows,
            cert._check_external_obligations,
            cert._check_terminal_bindings,
            cert._check_lane_aggregates,
        ):
            check(candidate, state)
        # opus2 P42 P3-3: the sentence says "every row, partition and aggregate check" and the
        # test ran four of the seven. The partition check is _check_reserve_rows.
        cert._check_terminal_totals(candidate)
        roots.add(candidate.allocation_root)
        outcome = cert.check_global_accounting_allocation_certificate_v1(
            candidate, state, cert.EMPTY_LANE_WITNESS_SLOTS_V1
        )
        assert isinstance(outcome, cert.AllocationCertificateRejectedV1), principal
        full.add(outcome.code.value)
    assert len(roots) == 2, roots
    assert full == {"RECEIPT_WITNESS_REQUIRED"}, full
    projected = _project(state, _root_of(state))
    assert isinstance(projected, AllocationProjectionRejectedV1)
    assert projected.code is AllocationProjectionRejectCodeV1.PROJECTION_ROWS_BEYOND_PRODUCER


@pytest.mark.parametrize(
    ("label", "tables", "terminals", "code"),
    [(c[0], c[1], c[2], c[3]) for c in _ROW_CASES],
    ids=[c[0].replace(" ", "-") for c in _ROW_CASES],
)
def test_which_row_cases_the_entry_point_reaches_is_pinned(
    label: str, tables: dict, terminals: tuple, code
) -> None:
    """Opus P40 P1-2 A: "unreachable through the entry point" was false for two of twelve.

    The blanket claim justified routing every row case through the helpers. It is true for
    the ten cases that need a reserve, a PENDING entry or an OPEN terminal, because the
    receipt-backed producer emits none of those and PROJECTION_ROWS_BEYOND_PRODUCER fires
    first. It is false for the two that need none of them. Rather than restate the claim and
    hope, this pins the partition: each case must reach EITHER its own code through the
    public entry point, or PROJECTION_ROWS_BEYOND_PRODUCER, and the set that reaches its own
    code is fixed here.
    """

    reaches_entry = {"entitlements exceeding custody", "controlled atoms no obligation can absorb"}
    # Two cases carry a zero-amount economic row, which the entry point now refuses before the
    # producer guard: zero-present and absent differ to the checker, so no certificate over
    # such a state is acceptable (Codex C9c-5 P2-1). They are still row cases -- the harness
    # reaches their own code -- but the entry point reports the earlier fact.
    refused_as_noncanonical = {
        "a zero-atom entitlement cannot host a positive claim",
        "a zero-atom entitlement in the claimant's only entitled domain, backed nowhere",
    }
    assert len(_ROW_CASES) == 14, "the counts in the docstrings above are over all of them"
    state = _backed_state(
        tuple(_terminal(t[0], t[1], **(t[2] if len(t) > 2 else {})) for t in terminals), **tables
    )
    projected = _project(state, _root_of(state))
    assert isinstance(projected, AllocationProjectionRejectedV1), label
    if label in refused_as_noncanonical:
        assert (
            projected.code
            is AllocationProjectionRejectCodeV1.PROJECTION_NONCANONICAL_ZERO_ECONOMIC_ROW
        ), (label, projected.code)
    elif label in reaches_entry:
        assert projected.code is code, (label, projected.code)
    else:
        assert projected.code is AllocationProjectionRejectCodeV1.PROJECTION_ROWS_BEYOND_PRODUCER, (
            label,
            projected.code,
        )


def test_row_derivation_accepts_the_determined_shapes() -> None:
    """The complements of the refusals above: exactly one obligation over exactly one
    residual cell, and terminal rows within their entitlement, are derived and ordered."""

    single = _backed_state(
        (),
        custody=(("pool-a", "USD", "spot-pool", 10),),
        liabilities=(("alice", "USD", "spot-pool", 4),),
        outbox=((renderer._root(9_001), "dest-1", renderer._root(9_002), renderer._root(9_003), "PENDING"),),
    )
    external, terminals = _derive_rows(single)
    assert len(external) == 1
    assert (external[0].asset, external[0].amount_atoms, external[0].source_principal) == ("USD", 6, "pool-a")
    assert external[0].commitment_root == single.outbox[0].payload_hash
    assert terminals == ()

    ordered = _backed_state((_terminal("terminal-1", 6), _terminal("terminal-9", 4)))
    _external, rows = _derive_rows(ordered)
    assert [row.obligation_id for row in rows] == ["terminal-1", "terminal-9"]
    assert all(row.control_domain == "spot-pool" and row.controlling_principal == "pool-a" for row in rows)
    # The sort is defensive: a state cannot present its obligations out of order.
    with pytest.raises(ValueError, match="canonically ordered"):
        replace(ordered, terminal_obligations=(_terminal("terminal-9", 4), _terminal("terminal-1", 6)))


def test_a_witnessed_lane_carrying_rows_no_producer_emits_is_refused() -> None:
    """Opus P39 (second review): a witnessed lane's fragment must EQUAL the one its witness
    carries, and the single registered receipt-backed producer emits controlled and
    entitlement rows only. So a state putting a reserve, a pending obligation or an open
    terminal on that lane admits no accepted certificate at all, and the entry point refuses
    it rather than deriving one that can only fail the witness check."""

    witness, state, _certificate, slots = _witnessed(with_rows=True)
    roots = ((LaneIdV1.ASSET_TRANSFER, witness.fragment.binding_root),)
    assert isinstance(_project(state, roots), cert.GlobalAccountingAllocationCertificateV1)
    custody_row = state.custody[0]
    with_terminal = replace(
        state,
        terminal_obligations=(
            TerminalObligationV1(
                obligation_id="terminal-1",
                lane_id=LaneIdV1.ASSET_TRANSFER,
                claimant=custody_row.owner,
                asset=custody_row.asset,
                amount_atoms=1,
                status=TerminalObligationStatusV1.OPEN,
            ),
        ),
    )
    rejected = _project(with_terminal, roots)
    assert isinstance(rejected, AllocationProjectionRejectedV1)
    assert rejected.code is AllocationProjectionRejectCodeV1.PROJECTION_ROWS_BEYOND_PRODUCER
    assert rejected.detail == "ASSET_TRANSFER carries open terminal obligations"
    # And the reason it is unreconcilable: the derived certificate could only fail the
    # witness check, because the witness the producer minted carries no terminal row.
    assert not witness.fragment.terminal_bindings


def test_both_checked_folds_refuse_a_u128_overflow() -> None:
    """The checker's folds are checked u128, so the derivation's must be too."""

    maximum = (1 << 128) - 1
    controlled = replace(
        _one_enabled_state(),
        custody=(
            EconomicAmountV1("pool-a", "USD", "spot-pool", maximum),
            EconomicAmountV1("pool-b", "USD", "spot-pool", maximum),
        ),
    )
    code, detail = _derive_rows(controlled)
    assert code is AllocationProjectionRejectCodeV1.PROJECTION_ROW_TOTAL_OVERFLOW
    assert detail == "controlled totals for USD:spot-pool"

    terminals = replace(
        _one_enabled_state(),
        custody=(EconomicAmountV1("pool-a", "USD", "spot-pool", maximum),),
        liabilities=(EconomicAmountV1("alice", "USD", "spot-pool", maximum),),
        terminal_obligations=(_terminal("terminal-1", maximum), _terminal("terminal-2", maximum)),
    )
    code2, detail2 = _derive_rows(terminals)
    assert code2 is AllocationProjectionRejectCodeV1.PROJECTION_ROW_TOTAL_OVERFLOW
    assert detail2 == "terminal totals for USD:alice:spot-pool"

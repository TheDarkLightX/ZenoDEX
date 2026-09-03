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
   than one certificate that passes every row, partition and aggregate check it refuses
   rather than choosing (the AMBIGUOUS codes). Not "more than one ACCEPTED certificate":
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
    (PROJECTION_ROWS_BEYOND_PRODUCER). These cases therefore exercise the helpers directly:
    they are the contract a future producer that can emit such rows would have to satisfy,
    and they are not reachable through the public entry today. That is stated here rather
    than hidden behind a lane whose registry entry would make every such state trivially
    unreconcilable.
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
    lane_root = state.lane_roots[0]
    try:
        external = _external_rows_v1(state, controlled, entitlements, reserves)
        terminals = _terminal_rows_v1(state, lane_root.lane_id, lane_root.state_root, controlled, entitlements)
    except _Reject as rejected:
        return rejected.code, rejected.detail
    return external, terminals


def _state_consistent_candidate(state, *, source_principal: str | None = None):
    """A certificate the state implies, built without the projection.

    Every field a fragment can carry is copied from the state, so a checker refusal of
    this candidate is a fact about the state and not about how the projection chose to
    derive. ``source_principal`` supplies the one field V1 state does not carry: a PENDING
    outbox entry names no principal, so where the state leaves that open this builder makes
    the choice explicit and the caller can enumerate it. With it set, the single PENDING
    entry becomes an external row over the single open residual cell.

    WHAT THIS DOES NOT COVER, stated because the previous wording of the claim did not
    (Opus P39 primary, P1-1 second half): it builds no terminal binding rows, so for a state
    with an OPEN terminal obligation it is one candidate among more than one, and a refusal
    of it is not by itself a statement about every certificate over that state.
    """

    base = cert.build_registered_empty_certificate_v1(state)
    lane_root = state.lane_roots[0]
    fragment = replace(
        base.ordered_lane_fragments[0],
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
        open_cells = {k: v - claimed.get(k, 0) for k, v in open_cells.items() if v - claimed.get(k, 0) > 0}
        pending = tuple(r for r in state.outbox if r.status is OutboxStatusV1.PENDING)
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
    return renderer._certificate_with_fragments(base, (fragment, *base.ordered_lane_fragments[1:]))


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
    and the registered producer kind straight off the state. So a code returned here is the
    code EVERY certificate over this state receives, which is what justifies the projection
    refusing instead of deriving.
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

    The branch is DEFENSIVE: it cannot be reached through the entry point or through the
    row harness, because a state entitling a claimant in a domain it controls nowhere fails
    the negative-residual check first, and that check runs before the terminal rows. So it
    is exercised where it lives, by calling the terminal row builder directly with the
    controlled and entitlement tuples that reach it. That is stated here rather than left
    for a reviewer to discover.
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


def test_the_three_refusal_kinds_partition_the_family() -> None:
    """Both P40 reviews, P3-1: the prose split omitted three of its thirteen codes,
    PROJECTION_ROWS_BEYOND_PRODUCER among them -- the guard the candidate was named for.
    The kinds are data now, and this pins them as a partition so the docstring cannot
    describe a family it does not cover."""

    kinds = ALLOCATION_PROJECTION_REFUSAL_KINDS_V1
    assert set(kinds) == {"caller_input", "undetermined", "unreconcilable"}
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
    """The reject family is the declaration order of the enum, and every code is asserted by
    a test in this module: the claim is checked here by scanning this file's own assertions
    (Opus P39 P3-4 found the sentence stated but not established)."""

    assert ALLOCATION_PROJECTION_REJECT_CODES_V1 == tuple(
        code.value for code in AllocationProjectionRejectCodeV1
    )
    assert len(ALLOCATION_PROJECTION_REJECT_CODES_V1) == 16
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
            "claims 99 of 10",
        ),
        (
            "two terminals over-claiming together",
            {"custody": (("pool-a", "USD", "spot-pool", 3),), "liabilities": (("alice", "USD", "spot-pool", 3),)},
            (("terminal-1", 2), ("terminal-2", 2)),
            AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT,
            "claims 4 of 3",
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
    OPEN terminal obligation the builder omits terminal rows, so other candidates exist and
    this is evidence about one of them, not a quantifier over all. The states with neither a
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
        for check in (cert._check_entitlement_rows, cert._check_external_obligations, cert._check_lane_aggregates):
            check(candidate, state)
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
    state = _backed_state(
        tuple(_terminal(t[0], t[1], **(t[2] if len(t) > 2 else {})) for t in terminals), **tables
    )
    projected = _project(state, _root_of(state))
    assert isinstance(projected, AllocationProjectionRejectedV1), label
    if label in reaches_entry:
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

"""The allocation certificate is derived from the state, not assembled by hand (C9c-1).

Two properties are executable here for the first time. TOTALITY AGAINST THE FIXTURE:
for every state the golden fixture renders, the projection either produces a
certificate the checker ACCEPTS or refuses with a closed code, and the states it
refuses are exactly the ones no certificate can reconcile (every lane disabled while
economic rows exist). WHAT A WITNESS ADDS: for the registered receipt-backed lane, the
projection reproduces the witnessed certificate byte-for-byte once it is given the one
scalar the state does not carry, the receipt root; so the sealed witness contributes
its binding root and its header, not its rows.
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
    assert len(ALLOCATION_PROJECTION_REJECT_CODES_V1) == 6
    assert len(ALL_LANE_IDS_V1) == 12

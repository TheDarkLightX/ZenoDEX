"""Projection of the allocation certificate from a verified global economic state (C9c-4).

``project_allocation_certificate_v1`` derives one certificate for one exact
``GlobalEconomicStateV1`` by inverting the checker's own expectations: the controlled
rows are the state's custody, the entitlement rows its liabilities, the reserve rows
its reserve partition, the external rows its PENDING outbox, and the terminal rows its
OPEN terminal obligations. It is pure, takes no witness, and never mutates its inputs.

WHY THIS EXISTS. Nothing else computes a certificate; every caller either builds the
registered-empty projection or assembles one by hand in a test. A checker whose input
is hand-assembled proves that some object passes; a checker whose input is *derived*
from the state proves something about the state.

WHAT IS CLAIMED, and what three reviews have already falsified in earlier wordings.

1. The projection derives ONE certificate, and where V1 state leaves the answer open it
   refuses rather than guessing (the ``..._AMBIGUOUS`` codes). It does NOT follow that
   a derived certificate is the only one the checker's row checks would take. The
   checker binds a pending row's source principal, and a terminal row's controlling
   principal, to SOME controlled location of the same fragment rather than to a
   determined one, so a cell controlled by two principals admits two certificates that
   pass every row, partition and aggregate check with DIFFERENT allocation roots. That
   is what UNDETERMINED means here, and a test exhibits the two.

   It does NOT mean two ACCEPTED certificates exist. Under the current registry no
   accepted certificate can carry an external, reserve or terminal row at all: the only
   receipt-backed lane needs a minted witness whose fragment must EQUAL the
   certificate's, that producer emits controlled and entitlement rows only, and a
   disabled lane carrying any row fails DISABLED_LANE_NOT_EMPTY. So every state that
   reaches an ``..._AMBIGUOUS`` code today is also one no accepted certificate exists
   for. The distinction the two kinds draw is about what the STATE determines, not about
   what the checker would accept, and it becomes observable when a producer that can
   emit those rows is registered. Two earlier wordings of this paragraph were falsified
   for saying otherwise: the certificate is not a function of the state (P39), and
   UNDETERMINED does not mean two accepted certificates (P40).
2. Where NO certificate over the state can be accepted, the projection refuses rather
   than deriving an object the checker must reject. That includes the structural case:
   a witnessed lane's fragment must equal the one its witness carries, and the single
   registered receipt-backed producer emits controlled and entitlement rows only, so a
   state placing a reserve, a pending obligation or an open terminal on that lane is
   unreconcilable however its rows are arranged. It also includes the two gates that are
   not about allocation at all: an enabled lane whose registry entry has no producer, and
   a registered-empty lane committed at a foreign root. Both are functions of the state
   alone -- the projection copies ``enabled`` and ``state_root`` off the state into every
   fragment it builds -- so no certificate over such a state is acceptable, and they are
   refused here with their own codes rather than derived and left to the checker. The
   earlier wording carried this claim with no exception while a test file carried the
   exception (opus2 P39 P2-5); the exception is now closed in the code instead.

   One case is closed only when the caller helps. A witnessed lane's minted witness is
   determined by the committed lane root -- the producer folds the custody that root's
   receipt admitted -- so a state whose rows differ from the receipt's has no acceptable
   certificate, and one extra atom on a custody row is enough. V1 state does not carry
   the receipt's rows, so from the state alone the projection cannot see it and derives.
   Given ``lane_witnesses``, the same slots the checker requires, it refuses with
   ``..._WITNESS_FRAGMENT_DRIFT`` instead (opus2 P40 P2-7, whose minimal fix was to
   disclose this; disclosed AND closed for the caller who passes the witness). Without
   the witness the derived object is refused by the checker's witness pass, so nothing
   unsound is admitted either way -- what differs is which layer says no.
3. Given the one scalar the state does not carry, the receipt root, the projection
   reproduces a witnessed certificate byte-for-byte, including a witness whose receipt
   proved a custody row. That evidence covers one row shape, stated in the test.

NONCLAIMS. This is a projection, not a consumer: no publisher, verifier, or client
calls it, so it refuses nothing at runtime. It verifies no receipt; a binding root it
accepts is bound to a receipt only where the caller obtained it from an admission
witness, and the projection cannot tell the difference. It does not establish that the
state is correct, only what a certificate over it would have to say. Multi-lane field
ownership is undecided: more than one enabled lane is refused outright. There is no
Rust twin. Research-only evidence; authority NONE.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_accounting_allocation_certificate_v1 import (
    LANE_ALLOCATION_PRODUCER_REGISTRY_V1,
    MAX_ATOMS_U128_V1,
    REGISTERED_EMPTY_LANE_ROOTS_V1,
    ChainContextV1,
    ClaimantEntitlementRowV1,
    ControlledLocationRowV1,
    GlobalAccountingAllocationCertificateV1,
    LaneAllocationFragmentV1,
    LaneProducerKindV1,
    PendingExternalObligationRowV1,
    TerminalBindingRowV1,
    UnencumberedReserveRowV1,
    VerifiedLaneAllocationFragmentV1,
    derive_allocation_root_v1,
    derive_canonical_allocation_rows_v1,
    derive_field_ownership_root_v1,
    derive_terminal_binding_root_v1,
)
from .global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    GlobalEconomicStateV1,
    LaneIdV1,
    OutboxStatusV1,
    TerminalObligationStatusV1,
    _require_root,
)

ALLOCATION_PROJECTION_SCHEMA_V1: Final = "zenodex/global-accounting-allocation-projection/v1"


class AllocationProjectionRejectCodeV1(str, Enum):
    """The closed projection reject family, in declaration order.

    Declaration order is the family order the packet pins; it is NOT the order the
    projection evaluates them (Opus P38 P3: ``PROJECTION_NO_LANE_FOR_ROWS`` is raised at
    two sites, one of them after the residual codes). The evaluation order is documented
    on ``project_allocation_certificate_v1``.

    FOUR kinds of refusal share this family. Both P40 reviews found the previous
    two-kind wording wrong twice over: it omitted three of its own codes, including the
    headline one, and it said UNDETERMINED means two ACCEPTED certificates exist.

    CALLER INPUT -- the supplied binding roots do not match the enabled receipt-backed
    lanes: ``..._BINDING_ROOT_UNEXPECTED``, ``..._BINDING_ROOT_MISSING``. These are about
    the caller's argument, not about the state.

    UNDETERMINED -- the state does not pin the row content, so the projection refuses rather
    than choosing: ``..._EXTERNAL_RESIDUAL_AMBIGUOUS``, ``..._TERMINAL_DOMAIN_AMBIGUOUS``.
    Two things this does NOT mean, both of which earlier wordings claimed and reviewers
    falsified. It does not mean two ACCEPTED certificates exist: under the current registry
    none of these states has one, as the module docstring sets out (opus2 P40 P1-1). And it
    does not follow that more than one ROW-CHECKED certificate exists either: for the
    sub-cases where exactly one did, this candidate made the projection complete
    (a terminal's candidate domains are now filtered by the entitlement that must carry the
    row) or gave the case its own UNSUPPORTED code (a pending row over no residual cell), so
    what is left under these two codes is a state that genuinely leaves the content open
    (opus2 P41 P1-2). A future counterexample of the same shape would be a defect in this
    classification, not in the refusal: nothing unsound is derived either way.

    UNSUPPORTED -- the state determines the answer and this module declines to derive it:
    ``..._ZERO_RESIDUAL_ROW_UNSUPPORTED``, a pending obligation over no residual cell, whose
    only candidate row carries zero atoms.

    UNRECONCILABLE -- no certificate over this state can be accepted, so deriving one
    would produce an object the checker must reject. From the allocation itself:
    ``..._NEGATIVE_RESIDUAL``, ``..._UNASSIGNED_CONTROLLED_ATOMS``,
    ``..._PENDING_WITHOUT_BACKING``, ``..._TERMINAL_WITHOUT_ENTITLEMENT``,
    ``..._TERMINAL_WITHOUT_BACKING``, ``..._TERMINAL_EXCEEDS_ENTITLEMENT``,
    ``..._ROW_TOTAL_OVERFLOW``,
    ``..._NO_LANE_FOR_ROWS``, ``..._MULTIPLE_ENABLED_LANES``. From what the owning lane's
    producer can source: ``..._ROWS_BEYOND_PRODUCER``. From the lane configuration, which
    no arrangement of rows can repair, evaluated before the rows and in the checker's own
    order so the projection names the code the checker would raise first:
    ``..._ENABLED_LANE_WITHOUT_PRODUCER``, ``..._REGISTERED_EMPTY_ROOT_DRIFT``. And from
    the receipt behind a witnessed lane, when the caller supplies the witness the checker
    would require: ``..._WITNESS_FRAGMENT_DRIFT``, raised when the fragment the state
    implies differs from the one the lane root's receipt admitted.

    For each row case in the UNRECONCILABLE kind a test BUILDS the certificate the state
    implies and shows the checker refusing it, rather than asserting the classification;
    for the UNDETERMINED kind a test exhibits the two row-checked certificates with
    different allocation roots. The three kinds are a partition of all eighteen codes and
    a test pins that partition against this enum.
    """

    PROJECTION_MULTIPLE_ENABLED_LANES = "PROJECTION_MULTIPLE_ENABLED_LANES"
    PROJECTION_BINDING_ROOT_UNEXPECTED = "PROJECTION_BINDING_ROOT_UNEXPECTED"
    PROJECTION_BINDING_ROOT_MISSING = "PROJECTION_BINDING_ROOT_MISSING"
    PROJECTION_NO_LANE_FOR_ROWS = "PROJECTION_NO_LANE_FOR_ROWS"
    PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS = "PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS"
    PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS = "PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS"
    PROJECTION_NEGATIVE_RESIDUAL = "PROJECTION_NEGATIVE_RESIDUAL"
    PROJECTION_UNASSIGNED_CONTROLLED_ATOMS = "PROJECTION_UNASSIGNED_CONTROLLED_ATOMS"
    PROJECTION_PENDING_WITHOUT_BACKING = "PROJECTION_PENDING_WITHOUT_BACKING"
    PROJECTION_ROWS_BEYOND_PRODUCER = "PROJECTION_ROWS_BEYOND_PRODUCER"
    PROJECTION_TERMINAL_WITHOUT_ENTITLEMENT = "PROJECTION_TERMINAL_WITHOUT_ENTITLEMENT"
    PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT = "PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT"
    PROJECTION_ROW_TOTAL_OVERFLOW = "PROJECTION_ROW_TOTAL_OVERFLOW"
    PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER = "PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER"
    PROJECTION_REGISTERED_EMPTY_ROOT_DRIFT = "PROJECTION_REGISTERED_EMPTY_ROOT_DRIFT"
    PROJECTION_TERMINAL_WITHOUT_BACKING = "PROJECTION_TERMINAL_WITHOUT_BACKING"
    PROJECTION_WITNESS_FRAGMENT_DRIFT = "PROJECTION_WITNESS_FRAGMENT_DRIFT"
    PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED = "PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED"


ALLOCATION_PROJECTION_REJECT_CODES_V1: Final[tuple[str, ...]] = tuple(
    code.value for code in AllocationProjectionRejectCodeV1
)


# The three kinds the family docstring names, as data so a test can pin the partition
# against the enum (both P40 reviews, P3-1: the previous prose split omitted three codes,
# one of them the headline guard). Membership is a claim about WHY a code is raised, not
# about the checker's own families.
ALLOCATION_PROJECTION_REFUSAL_KINDS_V1: Final[dict[str, tuple[AllocationProjectionRejectCodeV1, ...]]] = {
    "caller_input": (
        AllocationProjectionRejectCodeV1.PROJECTION_BINDING_ROOT_UNEXPECTED,
        AllocationProjectionRejectCodeV1.PROJECTION_BINDING_ROOT_MISSING,
    ),
    "undetermined": (
        AllocationProjectionRejectCodeV1.PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS,
        AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS,
    ),
    "unsupported": (
        # The state DETERMINES the answer and the projection declines to derive it. Kept
        # separate from UNDETERMINED because calling a determined state ambiguous is the
        # error three reviews have now found in this family (Opus P41 P2-3).
        AllocationProjectionRejectCodeV1.PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED,
    ),
    "unreconcilable": (
        AllocationProjectionRejectCodeV1.PROJECTION_MULTIPLE_ENABLED_LANES,
        AllocationProjectionRejectCodeV1.PROJECTION_NO_LANE_FOR_ROWS,
        AllocationProjectionRejectCodeV1.PROJECTION_NEGATIVE_RESIDUAL,
        AllocationProjectionRejectCodeV1.PROJECTION_UNASSIGNED_CONTROLLED_ATOMS,
        AllocationProjectionRejectCodeV1.PROJECTION_PENDING_WITHOUT_BACKING,
        AllocationProjectionRejectCodeV1.PROJECTION_ROWS_BEYOND_PRODUCER,
        AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_WITHOUT_ENTITLEMENT,
        AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT,
        AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_WITHOUT_BACKING,
        AllocationProjectionRejectCodeV1.PROJECTION_ROW_TOTAL_OVERFLOW,
        AllocationProjectionRejectCodeV1.PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER,
        AllocationProjectionRejectCodeV1.PROJECTION_REGISTERED_EMPTY_ROOT_DRIFT,
        AllocationProjectionRejectCodeV1.PROJECTION_WITNESS_FRAGMENT_DRIFT,
    ),
}


@dataclass(frozen=True, slots=True)
class AllocationProjectionRejectedV1:
    """A projection refusal: nothing is produced and the state is left unchanged."""

    code: AllocationProjectionRejectCodeV1
    detail: str
    state_root: str

    def __post_init__(self) -> None:
        if type(self.code) is not AllocationProjectionRejectCodeV1:
            raise TypeError("allocation projection reject code is not closed")
        if type(self.detail) is not str or not self.detail or len(self.detail) > 200:
            raise ValueError("allocation projection detail must be a short non-empty string")
        _require_root(self.state_root, name="allocation projection state root")


class _Reject(Exception):
    def __init__(self, code: AllocationProjectionRejectCodeV1, detail: str) -> None:
        super().__init__(detail)
        self.code = code
        self.detail = detail


def _fail(code: AllocationProjectionRejectCodeV1, detail: str) -> None:
    raise _Reject(code, detail)


def asset_domain(key: tuple[str, str]) -> str:
    """``asset:control_domain`` for a reject detail."""

    return ":".join(key)


def _witnessed_lanes_v1(state: GlobalEconomicStateV1) -> tuple[LaneIdV1, ...]:
    """The lanes whose fragment the certificate will require a witness for."""

    return tuple(
        lane_root.lane_id
        for lane_root in state.lane_roots
        if lane_root.enabled
        and LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane_root.lane_id][0]
        is LaneProducerKindV1.RECEIPT_BACKED
    )


def _binding_roots_v1(
    state: GlobalEconomicStateV1,
    lane_binding_roots: tuple[tuple[LaneIdV1, str], ...],
) -> dict[LaneIdV1, str]:
    supplied: dict[LaneIdV1, str] = {}
    for entry in lane_binding_roots:
        if type(entry) is not tuple or len(entry) != 2:
            raise TypeError("lane binding roots must be exact (lane, root) pairs")
        lane, root = entry
        if type(lane) is not LaneIdV1 or type(root) is not str:
            raise TypeError("lane binding root pair must carry the exact lane and exact text")
        _require_root(root, name="lane binding root")
        if lane in supplied:
            raise ValueError("lane binding roots must name each lane at most once")
        supplied[lane] = root
    required = set(_witnessed_lanes_v1(state))
    for lane in supplied:
        if lane not in required:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_BINDING_ROOT_UNEXPECTED,
                lane.value,
            )
    for lane in sorted(required, key=lambda item: item.value):
        if lane not in supplied:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_BINDING_ROOT_MISSING,
                lane.value,
            )
    return supplied


def _single_owning_lane_v1(state: GlobalEconomicStateV1) -> LaneIdV1 | None:
    enabled = tuple(lane_root.lane_id for lane_root in state.lane_roots if lane_root.enabled)
    if len(enabled) > 1:
        _fail(
            AllocationProjectionRejectCodeV1.PROJECTION_MULTIPLE_ENABLED_LANES,
            ",".join(lane.value for lane in enabled),
        )
    return enabled[0] if enabled else None


def _state_level_refusals_v1(state: GlobalEconomicStateV1, owning_lane: LaneIdV1 | None) -> None:
    """Refuse the two states no certificate survives for reasons that are not allocation.

    Both conditions are functions of the state alone: the projection copies ``enabled`` and
    ``state_root`` from ``state.lane_roots`` into every fragment it builds, so whatever
    certificate it would derive carries them unchanged and the checker refuses it. The
    previous version derived one anyway and let the checker reject it, which is what the
    second P39 reviewer found: the module claimed a derived certificate is accepted, and
    these two states were carved out in a test rather than stated in the claim.

    Evaluated in the checker's order AMONG THESE TWO: ``BLOCKED_LANE_PRODUCER_MISSING`` (an
    enabled lane whose registered kind is not receipt-backed has no producer that could have
    written it) and then ``REGISTERED_EMPTY_ROOT_DRIFT`` (a lane pinned to a registered empty
    root whose committed root is not that root), which is checked over ALL twelve lanes
    because the checker checks it over all twelve, not only the enabled one.

    NOT "the code the checker would raise first" in general: ``RECEIPT_WITNESS_REQUIRED``
    runs between them, so a state that enables the receipt-backed lane AND drifts a
    registered-empty root gets the witness code from the checker with empty slots and this
    code from the projection (Opus P41 P2-6). The refusal stays sound -- no arrangement of
    rows or witnesses makes such a state acceptable -- but which code names it depends on
    whether the lane's witness obligation is discharged.
    """

    if owning_lane is not None:
        registered_kind, blocked_on = LANE_ALLOCATION_PRODUCER_REGISTRY_V1[owning_lane]
        if registered_kind is not LaneProducerKindV1.RECEIPT_BACKED:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER,
                f"{owning_lane.value} is enabled with {registered_kind.value} ({blocked_on})",
            )
    for lane_root in state.lane_roots:
        registered_root = REGISTERED_EMPTY_LANE_ROOTS_V1.get(lane_root.lane_id)
        if registered_root is not None and lane_root.state_root != registered_root:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_REGISTERED_EMPTY_ROOT_DRIFT,
                lane_root.lane_id.value,
            )


def _external_rows_v1(
    state: GlobalEconomicStateV1,
    controlled: tuple[ControlledLocationRowV1, ...],
    entitlements: tuple[ClaimantEntitlementRowV1, ...],
    reserves: tuple[UnencumberedReserveRowV1, ...],
) -> tuple[PendingExternalObligationRowV1, ...]:
    """The PENDING outbox rows, with the residual controlled atoms they must carry.

    V1 outbox entries carry no asset, amount, control domain or source principal, so
    the row content comes from the residual of the normative partition. That residual
    is unique only when exactly one (asset, control domain) cell is unassigned and one
    principal controls it; anything else is refused rather than guessed.
    """

    pending = tuple(row for row in state.outbox if row.status is OutboxStatusV1.PENDING)
    residual: dict[tuple[str, str], int] = {}
    for row in controlled:
        key = (row.asset, row.control_domain)
        total = residual.get(key, 0) + row.amount_atoms
        if total > MAX_ATOMS_U128_V1:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_ROW_TOTAL_OVERFLOW,
                f"controlled totals for {asset_domain(key)}",
            )
        residual[key] = total
    for entitlement in entitlements:
        key = (entitlement.asset, entitlement.control_domain)
        residual[key] = residual.get(key, 0) - entitlement.amount_atoms
    for reserve in reserves:
        key = (reserve.asset, reserve.control_domain)
        residual[key] = residual.get(key, 0) - reserve.amount_atoms
    # Classify the residual BEFORE the pending count is consulted (Opus P39 P1-1): more claimed
    # than controlled is unreconcilable whatever the outbox holds, and the previous order made
    # this code reachable only when an outbox entry happened to exist.
    negative = sorted(key for key, amount in residual.items() if amount < 0)
    if negative:
        _fail(
            AllocationProjectionRejectCodeV1.PROJECTION_NEGATIVE_RESIDUAL,
            f"entitlements and reserves exceed custody for {asset_domain(negative[0])}",
        )
    open_cells = {key: amount for key, amount in residual.items() if amount > 0}
    if not open_cells and not pending:
        return ()
    if len(open_cells) > len(pending):
        # No assignment exists: each PENDING obligation carries at most one (asset, domain) cell,
        # so fewer obligations than open cells leaves controlled atoms no row can absorb and the
        # checker's exactly-once partition must reject every certificate over this state.
        _fail(
            AllocationProjectionRejectCodeV1.PROJECTION_UNASSIGNED_CONTROLLED_ATOMS,
            f"{len(open_cells)} residual cells for {len(pending)} pending obligations",
        )
    if not controlled and pending:
        # Every external row binds its source principal to a controlled location of the same
        # fragment, so an obligation with no controlled location behind it cannot be written.
        _fail(
            AllocationProjectionRejectCodeV1.PROJECTION_PENDING_WITHOUT_BACKING,
            f"{len(pending)} pending obligations with no controlled location",
        )
    if not open_cells:
        # Opus P41 P2-3: with no residual cell every pending row must carry zero atoms, so
        # when the fragment controls exactly one cell with exactly one principal the answer
        # is DETERMINED and calling it an ambiguity was false. The projection still does not
        # derive it -- a zero-atom external row is a row the producer has never emitted and
        # this module will not invent one -- so it refuses with a code that says declined
        # rather than undetermined. With more than one controlled cell or principal the row's
        # own (asset, domain, principal) is genuinely open, and that is the ambiguity below.
        cells = {(row.asset, row.control_domain) for row in controlled}
        controlling = {row.controlling_principal for row in controlled}
        if len(cells) == 1 and len(controlling) == 1:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED,
                f"{len(pending)} pending rows over no residual cells",
            )
    if len(pending) != 1 or len(open_cells) != 1:
        # A genuine ambiguity: more than one assignment of residual cells to effect ids exists
        # (a surplus obligation may carry zero atoms), so deriving one would be a guess.
        _fail(
            AllocationProjectionRejectCodeV1.PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS,
            f"{len(pending)} pending rows for {len(open_cells)} residual cells",
        )
    (asset, control_domain), amount = next(iter(open_cells.items()))
    principals = sorted(
        {row.controlling_principal for row in controlled if (row.asset, row.control_domain) == (asset, control_domain)}
    )
    if len(principals) != 1:
        _fail(
            AllocationProjectionRejectCodeV1.PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS,
            f"{len(principals)} principals control {asset}:{control_domain}",
        )
    entry = pending[0]
    return (
        PendingExternalObligationRowV1(
            effect_id=entry.effect_id,
            asset=asset,
            amount_atoms=amount,
            destination_id=entry.destination_id,
            commitment_root=entry.payload_hash,
            control_domain=control_domain,
            source_principal=principals[0],
        ),
    )


def _terminal_rows_v1(
    state: GlobalEconomicStateV1,
    lane_id: LaneIdV1,
    lane_state_root: str,
    controlled: tuple[ControlledLocationRowV1, ...],
    entitlements: tuple[ClaimantEntitlementRowV1, ...],
) -> tuple[TerminalBindingRowV1, ...]:
    """The OPEN terminal obligations, with the control domain the state implies.

    A V1 terminal obligation names an obligation id, lane, claimant, asset and amount;
    the certificate row additionally names a control domain and a controlling
    principal, which the checker binds to an entitlement and a controlled location of
    the same fragment. The state determines them only when exactly one entitlement
    cell and one controlling principal match; two hidden domain preimages are the
    campaign's declared gap, refused here instead of guessed.
    """

    rows: list[TerminalBindingRowV1] = []
    for terminal in state.terminal_obligations:
        if terminal.status is not TerminalObligationStatusV1.OPEN:
            continue
        if terminal.lane_id is not lane_id:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_NO_LANE_FOR_ROWS,
                f"terminal {terminal.obligation_id} names {terminal.lane_id.value}",
            )
        domains = sorted(
            {
                entitlement.control_domain
                for entitlement in entitlements
                if entitlement.asset == terminal.asset and entitlement.claimant == terminal.claimant
            }
        )
        if not domains:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_WITHOUT_ENTITLEMENT,
                f"{terminal.obligation_id}: no entitlement for {terminal.claimant}",
            )
        # opus2 P41 P1-2 (B): naming two candidate domains is not the same as leaving the
        # answer open. The checker bounds each (asset, claimant, domain) key's terminal total
        # by that key's entitlement, so a domain entitled below this row's amount cannot host
        # it and is not a candidate at all. Filtering by that capacity is the checker's own
        # rule, not a preference: where it leaves exactly one domain the state DOES determine
        # the row, and reporting an ambiguity there was false.
        capacity = {
            entitlement.control_domain: entitlement.amount_atoms
            for entitlement in entitlements
            if entitlement.asset == terminal.asset and entitlement.claimant == terminal.claimant
        }
        hosting = [domain for domain in domains if capacity.get(domain, 0) >= terminal.amount_atoms]
        if not hosting:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT,
                f"{terminal.obligation_id}: {terminal.amount_atoms} exceeds every entitled domain",
            )
        if len(hosting) != 1:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS,
                f"{terminal.obligation_id}: {len(hosting)} entitlement domains",
            )
        control_domain = hosting[0]
        principals = sorted(
            {
                location.controlling_principal
                for location in controlled
                if location.asset == terminal.asset and location.control_domain == control_domain
            }
        )
        if not principals:
            # Opus P40 P2-3: zero candidates is not an ambiguity. No controlled location can
            # bind this row, so no certificate over the state is acceptable -- the same
            # misclassification P39 P1-1 found for unassignable atoms, surviving inside its
            # repair.
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_WITHOUT_BACKING,
                f"{terminal.obligation_id}: no controlled location in {control_domain}",
            )
        if len(principals) != 1:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS,
                f"{terminal.obligation_id}: {len(principals)} principals",
            )
        rows.append(
            TerminalBindingRowV1(
                obligation_id=terminal.obligation_id,
                claimant=terminal.claimant,
                asset=terminal.asset,
                amount_atoms=terminal.amount_atoms,
                control_domain=control_domain,
                controlling_principal=principals[0],
                lane_id=lane_id,
                lane_state_root=lane_state_root,
            )
        )
    # Opus P38 P2-1: the checker bounds the SUM of a fragment's terminal rows per
    # (asset, claimant, control_domain) against the entitlement, so a state whose OPEN
    # obligations over-claim reconciles to nothing and is refused here rather than
    # derived into a certificate the checker must reject.
    claimed: dict[tuple[str, str, str], int] = {}
    for row in rows:
        key = (row.asset, row.claimant, row.control_domain)
        total = claimed.get(key, 0) + row.amount_atoms
        if total > MAX_ATOMS_U128_V1:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_ROW_TOTAL_OVERFLOW,
                f"terminal totals for {':'.join(key)}",
            )
        claimed[key] = total
    entitled = {
        (row.asset, row.claimant, row.control_domain): row.amount_atoms for row in entitlements
    }
    for key, total in sorted(claimed.items()):
        if total > entitled.get(key, 0):
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT,
                f"{':'.join(key)} claims {total} of {entitled.get(key, 0)}",
            )
    return tuple(sorted(rows, key=lambda row: row.obligation_id))


def project_allocation_certificate_v1(
    state: GlobalEconomicStateV1,
    lane_binding_roots: tuple[tuple[LaneIdV1, str], ...] = (),
    lane_witnesses: tuple[VerifiedLaneAllocationFragmentV1 | None, ...] = (),
) -> GlobalAccountingAllocationCertificateV1 | AllocationProjectionRejectedV1:
    """Derive the certificate for one exact state, or refuse with a closed code.

    Check order: (0) the type boundary (the exact state, exact lane/root pairs, exact
    witness slots, each lane named at most once); (1) at most one lane is enabled; (1b) the two state-level
    gates, in the checker's order: an enabled lane with no producer, then a
    registered-empty lane at a foreign root; (2) the supplied
    binding roots are exactly the enabled receipt-backed lanes'; (2b) the owning lane's
    registered producer can source the row families the state puts on it, or the state is
    refused (PROJECTION_ROWS_BEYOND_PRODUCER -- omitted from this list until opus2 P41
    P3-4, though it is the gate the previous candidate was named for); (3) every row of the
    state's economic tables is placed on the single enabled lane, the external
    residual and terminal domains being refused where the state leaves them open;
    (4) the twelve fragments are assembled in lane order, every fragment bound to its
    committed lane root and the registered producer kind; (5) where a witness slot is
    supplied, the assembled fragment must EQUAL the one that witness carries; and the
    three derived roots are computed. Every refusal is a value carrying the unchanged
    state root.
    """

    if type(state) is not GlobalEconomicStateV1:
        raise TypeError("allocation projection requires the exact typed state")
    if type(lane_binding_roots) is not tuple:
        raise TypeError("lane binding roots must be an exact tuple")
    if type(lane_witnesses) is not tuple:
        raise TypeError("lane witnesses must be an exact tuple")
    if lane_witnesses and len(lane_witnesses) != len(ALL_LANE_IDS_V1):
        raise TypeError("lane witnesses must carry one slot per lane in canonical order")
    for slot in lane_witnesses:
        if slot is not None and type(slot) is not VerifiedLaneAllocationFragmentV1:
            raise TypeError("a lane witness slot holds the exact minted witness or nothing")
    state_root = state.state_root
    try:
        owning_lane = _single_owning_lane_v1(state)
        _state_level_refusals_v1(state, owning_lane)
        binding_roots = _binding_roots_v1(state, lane_binding_roots)
        controlled = tuple(
            ControlledLocationRowV1(
                asset=row.asset,
                controlling_principal=row.owner,
                control_domain=row.custody_domain,
                amount_atoms=row.amount_atoms,
            )
            for row in state.custody
        )
        entitlements = tuple(
            ClaimantEntitlementRowV1(
                asset=row.asset,
                claimant=row.owner,
                control_domain=row.custody_domain,
                amount_atoms=row.amount_atoms,
            )
            for row in state.liabilities
        )
        reserves = tuple(
            UnencumberedReserveRowV1(
                asset=row.asset,
                reserve_principal=row.owner,
                control_domain=row.custody_domain,
                amount_atoms=row.amount_atoms,
            )
            for row in state.reserves
        )
        open_terminals = tuple(
            row for row in state.terminal_obligations if row.status is TerminalObligationStatusV1.OPEN
        )
        pending_outbox = tuple(row for row in state.outbox if row.status is OutboxStatusV1.PENDING)
        if owning_lane is None:
            if controlled or entitlements or reserves or open_terminals or pending_outbox:
                _fail(
                    AllocationProjectionRejectCodeV1.PROJECTION_NO_LANE_FOR_ROWS,
                    "economic rows with every lane disabled",
                )
        external = ()
        terminals = ()
        if owning_lane is not None:
            lane_root = next(root for root in state.lane_roots if root.lane_id is owning_lane)
            # A witnessed lane's fragment must EQUAL the one its minted witness carries, and the
            # single registered receipt-backed producer emits controlled locations and claimant
            # entitlements only, so a state putting a reserve, a pending obligation or an open
            # terminal on such a lane admits NO accepted certificate however its rows are
            # arranged (Opus P39, second review).
            if LANE_ALLOCATION_PRODUCER_REGISTRY_V1[owning_lane][0] is LaneProducerKindV1.RECEIPT_BACKED:
                beyond = [
                    name
                    for name, rows in (
                        ("reserves", reserves),
                        ("pending external obligations", pending_outbox),
                        ("open terminal obligations", open_terminals),
                    )
                    if rows
                ]
                if beyond:
                    _fail(
                        AllocationProjectionRejectCodeV1.PROJECTION_ROWS_BEYOND_PRODUCER,
                        f"{owning_lane.value} carries {', '.join(beyond)}",
                    )
            external = _external_rows_v1(state, controlled, entitlements, reserves)
            terminals = _terminal_rows_v1(
                state, owning_lane, lane_root.state_root, controlled, entitlements
            )
        fragments = tuple(
            LaneAllocationFragmentV1(
                lane_id=lane_root.lane_id,
                module_release_id=lane_root.module_release_id,
                enabled=lane_root.enabled,
                lane_state_root=lane_root.state_root,
                producer_kind=LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane_root.lane_id][0],
                binding_root=binding_roots.get(lane_root.lane_id, lane_root.state_root),
                controlled_locations=controlled if lane_root.lane_id is owning_lane else (),
                claimant_entitlements=entitlements if lane_root.lane_id is owning_lane else (),
                unencumbered_reserves=reserves if lane_root.lane_id is owning_lane else (),
                pending_external_obligations=external if lane_root.lane_id is owning_lane else (),
                terminal_bindings=terminals if lane_root.lane_id is owning_lane else (),
            )
            for lane_root in state.lane_roots
        )
        # opus2 P40 P2-7, closed where the caller can close it. A witnessed lane's
        # fragment must EQUAL the one its minted witness carries, and the witness is
        # determined by the committed lane root: the producer folds the custody the
        # receipt admitted. So a state whose rows differ from the ones that root's
        # receipt admitted has no accepted certificate however it is derived -- one extra
        # atom on a custody row is enough. V1 state does not carry the receipt's rows, so
        # the projection cannot detect that from the state alone. It CAN when the caller
        # supplies the witness, which is the same object the checker requires, and then
        # it refuses instead of deriving an object the witness check must reject.
        if lane_witnesses:
            for fragment, witness in zip(fragments, lane_witnesses, strict=True):
                if witness is None:
                    continue
                if witness.fragment != fragment:
                    _fail(
                        AllocationProjectionRejectCodeV1.PROJECTION_WITNESS_FRAGMENT_DRIFT,
                        f"{fragment.lane_id.value} differs from its minted witness",
                    )
    except _Reject as rejected:
        return AllocationProjectionRejectedV1(rejected.code, rejected.detail, state_root)
    rows = derive_canonical_allocation_rows_v1(fragments)
    return GlobalAccountingAllocationCertificateV1(
        global_state_root=state_root,
        profile_root=state.profile_root,
        writer_epoch=state.writer_epoch,
        chain_context=ChainContextV1(state.chain_id, state.deployment_root),
        ordered_lane_fragments=fragments,
        canonical_allocation_rows=rows,
        field_ownership_root=derive_field_ownership_root_v1(fragments),
        terminal_binding_root=derive_terminal_binding_root_v1(fragments),
        allocation_root=derive_allocation_root_v1(fragments, rows),
    )


__all__ = [
    "ALLOCATION_PROJECTION_REFUSAL_KINDS_V1",
    "ALLOCATION_PROJECTION_REJECT_CODES_V1",
    "ALLOCATION_PROJECTION_SCHEMA_V1",
    "AllocationProjectionRejectCodeV1",
    "AllocationProjectionRejectedV1",
    "project_allocation_certificate_v1",
]

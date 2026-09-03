"""Projection of the allocation certificate from a verified global economic state (C9c-1).

``project_allocation_certificate_v1`` computes the certificate the checker would
accept for one exact ``GlobalEconomicStateV1``, by inverting the checker's own
expectations: the controlled rows are the state's custody, the entitlement rows are
its liabilities, the reserve rows its reserve partition, the external rows its
PENDING outbox, and the terminal rows its OPEN terminal obligations. It is pure,
takes no witness, and never mutates its inputs.

WHY THIS EXISTS. Until now nothing computed a certificate; every caller either built
the registered-empty projection or assembled one by hand in a test. A checker whose
input is hand-assembled proves that some object passes; a checker whose input is
*derived* from the state proves that the state itself reconciles. This module is the
derivation, and it makes two properties executable that were previously prose:

1. WHAT THE STATE DETERMINES. For a profile with at most one enabled lane, the
   certificate is a function of the state except for one scalar per witnessed lane
   (its ``binding_root``, which is the receipt root the admission proved and which no
   state field carries). The caller supplies exactly those scalars in
   ``lane_binding_roots``; everything else is derived. This is the precise form of
   the claim that the twelve sealed witness slots carry no row information: a witness
   contributes its binding root and its header, not its rows.
2. WHERE THE STATE DETERMINES NOTHING. Three certificate shapes are not recoverable
   from V1 state, and each is a closed reject code rather than a guess:
   ``PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS`` (a V1 terminal obligation carries no
   control domain or controlling principal, so the row's domain is recoverable only
   when the state's own tables name exactly one candidate: the accepted known gap
   ``domainless_terminal_with_two_distinct_hidden_domain_preimages``, now executable),
   ``PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS`` (a V1 outbox entry carries no asset,
   amount, domain or source principal, so the residual controlled atoms can be split
   across two PENDING entries in more than one way), and
   ``PROJECTION_NO_LANE_FOR_ROWS`` (rows exist with no enabled lane to own them).

NONCLAIMS. This is a projection, not a consumer: no publisher, verifier, or client
calls it, so it refuses nothing at runtime. It verifies no receipt; the binding roots
it accepts are supplied by the caller and are bound to a receipt only where the caller
obtained them from an admission witness. It does not establish that the state is
itself correct, only that a certificate over it reconciles. Multi-lane field ownership
(which lane owns which controlled column when several lanes are enabled) is not
decided here: more than one enabled lane is refused outright. Research-only evidence;
authority NONE.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_accounting_allocation_certificate_v1 import (
    LANE_ALLOCATION_PRODUCER_REGISTRY_V1,
    ChainContextV1,
    ClaimantEntitlementRowV1,
    ControlledLocationRowV1,
    GlobalAccountingAllocationCertificateV1,
    LaneAllocationFragmentV1,
    LaneProducerKindV1,
    PendingExternalObligationRowV1,
    TerminalBindingRowV1,
    UnencumberedReserveRowV1,
    derive_allocation_root_v1,
    derive_canonical_allocation_rows_v1,
    derive_field_ownership_root_v1,
    derive_terminal_binding_root_v1,
)
from .global_settlement_types_v1 import (
    GlobalEconomicStateV1,
    LaneIdV1,
    OutboxStatusV1,
    TerminalObligationStatusV1,
    _require_root,
)

ALLOCATION_PROJECTION_SCHEMA_V1: Final = "zenodex/global-accounting-allocation-projection/v1"


class AllocationProjectionRejectCodeV1(str, Enum):
    """Closed projection rejects, in the order the projection checks them."""

    PROJECTION_MULTIPLE_ENABLED_LANES = "PROJECTION_MULTIPLE_ENABLED_LANES"
    PROJECTION_BINDING_ROOT_UNEXPECTED = "PROJECTION_BINDING_ROOT_UNEXPECTED"
    PROJECTION_BINDING_ROOT_MISSING = "PROJECTION_BINDING_ROOT_MISSING"
    PROJECTION_NO_LANE_FOR_ROWS = "PROJECTION_NO_LANE_FOR_ROWS"
    PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS = "PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS"
    PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS = "PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS"


ALLOCATION_PROJECTION_REJECT_CODES_V1: Final[tuple[str, ...]] = tuple(
    code.value for code in AllocationProjectionRejectCodeV1
)


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
        residual[key] = residual.get(key, 0) + row.amount_atoms
    for entitlement in entitlements:
        key = (entitlement.asset, entitlement.control_domain)
        residual[key] = residual.get(key, 0) - entitlement.amount_atoms
    for reserve in reserves:
        key = (reserve.asset, reserve.control_domain)
        residual[key] = residual.get(key, 0) - reserve.amount_atoms
    open_cells = {key: amount for key, amount in residual.items() if amount != 0}
    if not pending:
        if open_cells:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS,
                "unassigned controlled atoms with no pending obligation",
            )
        return ()
    if len(pending) != 1 or len(open_cells) != 1:
        _fail(
            AllocationProjectionRejectCodeV1.PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS,
            f"{len(pending)} pending rows for {len(open_cells)} residual cells",
        )
    (asset, control_domain), amount = next(iter(open_cells.items()))
    if amount < 0:
        _fail(
            AllocationProjectionRejectCodeV1.PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS,
            f"negative residual for {asset}:{control_domain}",
        )
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
        if len(domains) != 1:
            _fail(
                AllocationProjectionRejectCodeV1.PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS,
                f"{terminal.obligation_id}: {len(domains)} entitlement domains",
            )
        control_domain = domains[0]
        principals = sorted(
            {
                location.controlling_principal
                for location in controlled
                if location.asset == terminal.asset and location.control_domain == control_domain
            }
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
    return tuple(sorted(rows, key=lambda row: row.obligation_id))


def project_allocation_certificate_v1(
    state: GlobalEconomicStateV1,
    lane_binding_roots: tuple[tuple[LaneIdV1, str], ...] = (),
) -> GlobalAccountingAllocationCertificateV1 | AllocationProjectionRejectedV1:
    """Derive the certificate for one exact state, or refuse with a closed code.

    Check order: (0) the type boundary (the exact state, exact lane/root pairs, each
    lane named at most once); (1) at most one lane is enabled; (2) the supplied
    binding roots are exactly the enabled receipt-backed lanes'; (3) every row of the
    state's economic tables is placed on the single enabled lane, the external
    residual and terminal domains being refused where the state leaves them open;
    (4) the twelve fragments are assembled in lane order, every fragment bound to its
    committed lane root and the registered producer kind, and the three derived roots
    are computed. Every refusal is a value carrying the unchanged state root.
    """

    if type(state) is not GlobalEconomicStateV1:
        raise TypeError("allocation projection requires the exact typed state")
    if type(lane_binding_roots) is not tuple:
        raise TypeError("lane binding roots must be an exact tuple")
    state_root = state.state_root
    try:
        owning_lane = _single_owning_lane_v1(state)
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
    "ALLOCATION_PROJECTION_REJECT_CODES_V1",
    "ALLOCATION_PROJECTION_SCHEMA_V1",
    "AllocationProjectionRejectCodeV1",
    "AllocationProjectionRejectedV1",
    "project_allocation_certificate_v1",
]

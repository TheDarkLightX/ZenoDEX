"""GlobalAccountingAllocationCertificateV1: the sidecar contract of the O-008 formal cycle.

The certificate carries, for one exact ``GlobalEconomicStateV1``, twelve ordered lane
fragments that classify every controlled source atom exactly once under the normative
partition

    controlled_atoms = claimant_entitlements + named_unencumbered_reserves
                       + pending_registered_external_obligations

using the control-domain vocabulary (``control_domain``, ``controlled_location``,
``controlling_principal``, ``claimant_entitlement``, ``unencumbered_reserve``,
``pending_external_obligation``). V1 wire names stay byte-stable: the certificate is
a sibling schema and never renames a V1 field.

Functional core: ``check_global_accounting_allocation_certificate_v1(certificate,
state)`` is a total function ``Accept | Reject(code)`` with a closed, ordered reject
precedence. Rejects carry the unchanged pre-state root and no effects. Every fold uses
checked u128 arithmetic; every table is canonically ordered and unique.

Current profile: no lane has a receipt-backed fragment producer (the registry below is
exhaustive over ``LaneIdV1`` and names the blocking obligation), so an enabled lane
fragment rejects with ``BLOCKED_LANE_PRODUCER_MISSING`` naming the lane; only the
all-lanes-disabled certificate over an empty economic state can be accepted today. That
is the honest content of this candidate: the contract and its checks are executable
and pinned, the producers are not. Authority: NONE. The checker verifies no receipt
and grants no publication, settlement, or value-moving authority.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from enum import Enum
from typing import TYPE_CHECKING, Final, Protocol, TypeVar, cast

if TYPE_CHECKING:
    from _typeshed import SupportsRichComparison

from .external_custody_disabled_lane_v1 import ExternalCustodyDisabledStateV1
from .global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    GlobalEconomicStateV1,
    LaneIdV1,
    OutboxStatusV1,
    TerminalObligationStatusV1,
    _require_atoms_u128,
    _require_bool,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    _require_tuple,
    hash_global_v1,
)
from .proof_rewards_policy_blocked_lane_v1 import ProofRewardsPolicyBlockedStateV1

GLOBAL_ACCOUNTING_ALLOCATION_CERTIFICATE_SCHEMA_V1: Final = (
    "zenodex/global-accounting-allocation-certificate/v1"
)
ALLOCATION_ROOT_DOMAIN_V1: Final = "global-accounting-allocation-certificate-v1"
FIELD_OWNERSHIP_ROOT_DOMAIN_V1: Final = "global-accounting-field-ownership-v1"
TERMINAL_BINDING_ROOT_DOMAIN_V1: Final = "global-accounting-terminal-binding-v1"
LANE_FRAGMENT_ROOT_DOMAIN_V1: Final = "global-accounting-lane-fragment-v1"
MAX_ATOMS_U128_V1: Final = (1 << 128) - 1
MAX_FRAGMENT_ROWS_V1: Final = 4_096

NORMATIVE_PARTITION_V1: Final = (
    "controlled_atoms = claimant_entitlements + named_unencumbered_reserves"
    " + pending_registered_external_obligations"
)


class ReserveInterpretationV1(str, Enum):
    """The single reserve interpretation decided on 2026-09-01: reserves are claimant-free."""

    NAMED_UNENCUMBERED_NO_CLAIMANT = "NAMED_UNENCUMBERED_NO_CLAIMANT"


class LaneProducerKindV1(str, Enum):
    """How a lane's allocation fragment is produced in the current profile."""

    NO_PRODUCER = "NO_PRODUCER"
    REGISTERED_EMPTY_DISABLED = "REGISTERED_EMPTY_DISABLED"
    REGISTERED_EMPTY_BLOCKED = "REGISTERED_EMPTY_BLOCKED"
    RECEIPT_BACKED = "RECEIPT_BACKED"


# Exhaustive over LaneIdV1: the producer kind the registry supports today and the
# obligation that blocks a receipt-backed producer. No lane is receipt-backed yet.
# The unique empty typed lane state each registered-empty lane must be committed at: a
# registered-empty fragment is exact-empty because the lane's own state is the empty state,
# and the certificate binds the committed lane root to that state's root (C5, wave A).
REGISTERED_EMPTY_LANE_ROOTS_V1: Final[dict[LaneIdV1, str]] = {
    LaneIdV1.EXTERNAL_CUSTODY: ExternalCustodyDisabledStateV1().state_root,
    LaneIdV1.PROOF_REWARDS: ProofRewardsPolicyBlockedStateV1().state_root,
}
LANE_ALLOCATION_PRODUCER_REGISTRY_V1: Final[dict[LaneIdV1, tuple[LaneProducerKindV1, str]]] = {
    LaneIdV1.ASSET_TRANSFER: (LaneProducerKindV1.NO_PRODUCER, "VM-04 wave B asset-transfer fragment producer"),
    LaneIdV1.SPOT_LIQUIDITY: (LaneProducerKindV1.NO_PRODUCER, "VM-04 wave C spot-liquidity producer; UP-01 UP-12 UP-14"),
    LaneIdV1.FARM_INCENTIVES: (LaneProducerKindV1.NO_PRODUCER, "VM-11 wave D no-writer proof; UP-03"),
    LaneIdV1.ZDEX_TOKENOMICS: (LaneProducerKindV1.NO_PRODUCER, "VM-04 wave C tokenomics producer; UP-01 UP-15"),
    LaneIdV1.ZUSD_MONETARY: (LaneProducerKindV1.NO_PRODUCER, "VM-11 wave E no-writer proof; UP-04"),
    LaneIdV1.PERPS_MARKET: (LaneProducerKindV1.NO_PRODUCER, "VM-05 wave B narrow perps producer; UP-05"),
    LaneIdV1.ORACLE_MARKET: (LaneProducerKindV1.NO_PRODUCER, "VM-11 wave D no-writer proof; UP-06"),
    LaneIdV1.SEALED_AUCTION: (LaneProducerKindV1.NO_PRODUCER, "VM-11 wave D no-writer proof; UP-07"),
    LaneIdV1.STRATEGY_ESCROW: (LaneProducerKindV1.NO_PRODUCER, "VM-11 wave E no-writer proof; UP-08"),
    LaneIdV1.PROOF_REWARDS: (LaneProducerKindV1.REGISTERED_EMPTY_BLOCKED, "UP-09 proof-reward funding and claimant eligibility"),
    LaneIdV1.EXTERNAL_CUSTODY: (LaneProducerKindV1.REGISTERED_EMPTY_DISABLED, "UP-11 external finality; registry empty by construction"),
    LaneIdV1.GOVERNANCE_MIGRATION: (LaneProducerKindV1.NO_PRODUCER, "VM-11 wave E migration-journal predecessor rows; UP-10"),
}


class AllocationCertificateRejectCodeV1(str, Enum):
    """Closed reject codes.

    The realised precedence is ``CHECK_ORDER_V1``: the first failing check wins, each
    lane-binding check (state root, producer kind, blocked producer, disabled lane
    rows) runs over all twelve lanes before the next one starts, and
    ``ALLOCATION_TOTAL_OVERFLOW`` is raised by whichever checked fold overflows first
    (the exactly-once fold, the reserve fold, or the custody fold).
    """

    HEADER_BINDING_DRIFT = "HEADER_BINDING_DRIFT"
    LANE_ORDER_DRIFT = "LANE_ORDER_DRIFT"
    LANE_STATE_ROOT_DRIFT = "LANE_STATE_ROOT_DRIFT"
    PRODUCER_KIND_DRIFT = "PRODUCER_KIND_DRIFT"
    BLOCKED_LANE_PRODUCER_MISSING = "BLOCKED_LANE_PRODUCER_MISSING"
    DISABLED_LANE_NOT_EMPTY = "DISABLED_LANE_NOT_EMPTY"
    REGISTERED_EMPTY_ROOT_DRIFT = "REGISTERED_EMPTY_ROOT_DRIFT"
    ALLOCATION_TOTAL_OVERFLOW = "ALLOCATION_TOTAL_OVERFLOW"
    SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE = "SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE"
    ENTITLEMENT_ROWS_DRIFT = "ENTITLEMENT_ROWS_DRIFT"
    RESERVE_ROWS_DRIFT = "RESERVE_ROWS_DRIFT"
    EXTERNAL_OBLIGATION_BINDING_DRIFT = "EXTERNAL_OBLIGATION_BINDING_DRIFT"
    TERMINAL_BINDING_DRIFT = "TERMINAL_BINDING_DRIFT"
    LANE_AGGREGATE_DRIFT = "LANE_AGGREGATE_DRIFT"
    DERIVED_ROOT_DRIFT = "DERIVED_ROOT_DRIFT"


ALLOCATION_CERTIFICATE_REJECT_MESSAGE_BY_CODE_V1: Final[dict[AllocationCertificateRejectCodeV1, str]] = {
    AllocationCertificateRejectCodeV1.HEADER_BINDING_DRIFT: "allocation certificate header does not bind the exact global state",
    AllocationCertificateRejectCodeV1.LANE_ORDER_DRIFT: "allocation certificate lane fragments are not the twelve ABI V1 lanes in canonical order",
    AllocationCertificateRejectCodeV1.LANE_STATE_ROOT_DRIFT: "allocation certificate lane fragment does not bind the committed lane state root",
    AllocationCertificateRejectCodeV1.PRODUCER_KIND_DRIFT: "allocation certificate lane fragment producer kind differs from the registry",
    AllocationCertificateRejectCodeV1.BLOCKED_LANE_PRODUCER_MISSING: "allocation certificate enabled lane has no receipt-backed fragment producer",
    AllocationCertificateRejectCodeV1.DISABLED_LANE_NOT_EMPTY: "allocation certificate disabled lane fragment carries rows",
    AllocationCertificateRejectCodeV1.REGISTERED_EMPTY_ROOT_DRIFT: "allocation certificate registered-empty lane is not bound to its empty lane state root",
    AllocationCertificateRejectCodeV1.ALLOCATION_TOTAL_OVERFLOW: "allocation certificate total overflows",
    AllocationCertificateRejectCodeV1.SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE: "allocation certificate controlled source atoms are not assigned exactly once",
    AllocationCertificateRejectCodeV1.ENTITLEMENT_ROWS_DRIFT: "allocation certificate claimant entitlement rows differ from the V1 liabilities",
    AllocationCertificateRejectCodeV1.RESERVE_ROWS_DRIFT: "allocation certificate unencumbered reserve rows differ from the V1 reserve partition",
    AllocationCertificateRejectCodeV1.EXTERNAL_OBLIGATION_BINDING_DRIFT: "allocation certificate pending external obligations do not bind the V1 outbox",
    AllocationCertificateRejectCodeV1.TERMINAL_BINDING_DRIFT: "allocation certificate terminal binding rows do not bind the OPEN V1 terminal obligations",
    AllocationCertificateRejectCodeV1.LANE_AGGREGATE_DRIFT: "allocation certificate lane aggregates differ from the global economic tables",
    AllocationCertificateRejectCodeV1.DERIVED_ROOT_DRIFT: "allocation certificate derived roots differ from the recomputed roots",
}


# ---------------------------------------------------------------------------
# Rows
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True, order=True)
class ControlledLocationRowV1:
    """Atoms in a protocol-controlled accounting location (V1 custody row)."""

    asset: str
    controlling_principal: str
    control_domain: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token(self.asset, name="controlled location asset")
        _require_token(self.controlling_principal, name="controlled location principal")
        _require_token(self.control_domain, name="controlled location control domain")
        _require_atoms_u128(self.amount_atoms, name="controlled location atoms")

    @property
    def key(self) -> tuple[str, str, str]:
        return (self.asset, self.controlling_principal, self.control_domain)

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "controlling_principal": self.controlling_principal,
            "control_domain": self.control_domain,
            "amount_atoms": self.amount_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class ClaimantEntitlementRowV1:
    """Atoms a claimant may withdraw from a control domain (V1 liability row)."""

    asset: str
    claimant: str
    control_domain: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token(self.asset, name="claimant entitlement asset")
        _require_token(self.claimant, name="claimant entitlement claimant")
        _require_token(self.control_domain, name="claimant entitlement control domain")
        _require_atoms_u128(self.amount_atoms, name="claimant entitlement atoms")

    @property
    def key(self) -> tuple[str, str, str]:
        return (self.asset, self.claimant, self.control_domain)

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "claimant": self.claimant,
            "control_domain": self.control_domain,
            "amount_atoms": self.amount_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class UnencumberedReserveRowV1:
    """Named protocol-owned atoms with no claimant (V1 reserve row)."""

    asset: str
    reserve_principal: str
    control_domain: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token(self.asset, name="unencumbered reserve asset")
        _require_token(self.reserve_principal, name="unencumbered reserve principal")
        _require_token(self.control_domain, name="unencumbered reserve control domain")
        _require_atoms_u128(self.amount_atoms, name="unencumbered reserve atoms")

    @property
    def key(self) -> tuple[str, str, str]:
        return (self.asset, self.reserve_principal, self.control_domain)

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "reserve_principal": self.reserve_principal,
            "control_domain": self.control_domain,
            "amount_atoms": self.amount_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class PendingExternalObligationRowV1:
    """A registered external delivery awaiting acknowledgment, with the atoms the V1 outbox omits."""

    effect_id: str
    asset: str
    amount_atoms: int
    destination_id: str
    commitment_root: str
    control_domain: str
    source_principal: str

    def __post_init__(self) -> None:
        _require_root(self.effect_id, name="pending external obligation effect id")
        _require_token(self.asset, name="pending external obligation asset")
        _require_atoms_u128(self.amount_atoms, name="pending external obligation atoms")
        _require_token(self.destination_id, name="pending external obligation destination")
        _require_root(self.commitment_root, name="pending external obligation commitment")
        _require_token(self.control_domain, name="pending external obligation control domain")
        _require_token(self.source_principal, name="pending external obligation source principal")

    @property
    def key(self) -> str:
        return self.effect_id

    def to_canonical(self) -> dict[str, object]:
        return {
            "effect_id": self.effect_id,
            "asset": self.asset,
            "amount_atoms": self.amount_atoms,
            "destination_id": self.destination_id,
            "commitment_root": self.commitment_root,
            "control_domain": self.control_domain,
            "source_principal": self.source_principal,
        }


@dataclass(frozen=True, slots=True, order=True)
class TerminalBindingRowV1:
    """An OPEN V1 terminal obligation with the control domain and principal the V1 row omits."""

    obligation_id: str
    claimant: str
    asset: str
    amount_atoms: int
    control_domain: str
    controlling_principal: str
    lane_id: LaneIdV1
    lane_state_root: str

    def __post_init__(self) -> None:
        _require_token(self.obligation_id, name="terminal binding obligation id")
        _require_token(self.claimant, name="terminal binding claimant")
        _require_token(self.asset, name="terminal binding asset")
        _require_atoms_u128(self.amount_atoms, name="terminal binding atoms")
        _require_token(self.control_domain, name="terminal binding control domain")
        _require_token(self.controlling_principal, name="terminal binding principal")
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("terminal binding lane is not closed")
        _require_root(self.lane_state_root, name="terminal binding lane state root", allow_zero=True)

    @property
    def key(self) -> str:
        return self.obligation_id

    def to_canonical(self) -> dict[str, object]:
        return {
            "obligation_id": self.obligation_id,
            "claimant": self.claimant,
            "asset": self.asset,
            "amount_atoms": self.amount_atoms,
            "control_domain": self.control_domain,
            "controlling_principal": self.controlling_principal,
            "lane_id": self.lane_id,
            "lane_state_root": self.lane_state_root,
        }


class _KeyedRowV1(Protocol):
    @property
    def key(self) -> SupportsRichComparison: ...


_RowT = TypeVar("_RowT", bound=_KeyedRowV1)


def _ordered_rows(values: object, *, name: str, expected_type: type[_RowT]) -> tuple[_RowT, ...]:
    items: tuple[object, ...] = _require_tuple(values, name=name)
    if len(items) > MAX_FRAGMENT_ROWS_V1:
        raise ValueError(f"{name} exceeds its {MAX_FRAGMENT_ROWS_V1}-row ceiling")
    if any(type(item) is not expected_type for item in items):
        raise TypeError(f"{name} contains an invalid row")
    rows = cast(tuple[_RowT, ...], items)
    keys = tuple(row.key for row in rows)
    if keys != tuple(sorted(set(keys))):
        raise ValueError(f"{name} must be canonically ordered and unique")
    return rows


# ---------------------------------------------------------------------------
# Fragments, context, certificate
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class LaneAllocationFragmentV1:
    """One lane's classification of the atoms it controls, bound to its committed lane root."""

    lane_id: LaneIdV1
    module_release_id: str
    enabled: bool
    lane_state_root: str
    producer_kind: LaneProducerKindV1
    binding_root: str
    controlled_locations: tuple[ControlledLocationRowV1, ...] = ()
    claimant_entitlements: tuple[ClaimantEntitlementRowV1, ...] = ()
    unencumbered_reserves: tuple[UnencumberedReserveRowV1, ...] = ()
    pending_external_obligations: tuple[PendingExternalObligationRowV1, ...] = ()
    terminal_bindings: tuple[TerminalBindingRowV1, ...] = ()

    def __post_init__(self) -> None:
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("lane fragment lane is not closed")
        _require_root(self.module_release_id, name="lane fragment module release id")
        _require_bool(self.enabled, name="lane fragment enabled")
        _require_root(self.lane_state_root, name="lane fragment state root", allow_zero=True)
        if type(self.producer_kind) is not LaneProducerKindV1:
            raise TypeError("lane fragment producer kind is not closed")
        _require_root(self.binding_root, name="lane fragment binding root", allow_zero=True)
        _ordered_rows(self.controlled_locations, name="lane fragment controlled locations", expected_type=ControlledLocationRowV1)
        _ordered_rows(self.claimant_entitlements, name="lane fragment claimant entitlements", expected_type=ClaimantEntitlementRowV1)
        _ordered_rows(self.unencumbered_reserves, name="lane fragment unencumbered reserves", expected_type=UnencumberedReserveRowV1)
        _ordered_rows(
            self.pending_external_obligations,
            name="lane fragment pending external obligations",
            expected_type=PendingExternalObligationRowV1,
        )
        _ordered_rows(self.terminal_bindings, name="lane fragment terminal bindings", expected_type=TerminalBindingRowV1)

    @property
    def is_empty(self) -> bool:
        return not (
            self.controlled_locations
            or self.claimant_entitlements
            or self.unencumbered_reserves
            or self.pending_external_obligations
            or self.terminal_bindings
        )

    @property
    def fragment_root(self) -> str:
        root: str = hash_global_v1(LANE_FRAGMENT_ROOT_DOMAIN_V1, self.to_canonical())
        return root

    def to_canonical(self) -> dict[str, object]:
        return {
            "lane_id": self.lane_id,
            "module_release_id": self.module_release_id,
            "enabled": self.enabled,
            "lane_state_root": self.lane_state_root,
            "producer_kind": self.producer_kind,
            "binding_root": self.binding_root,
            "controlled_locations": self.controlled_locations,
            "claimant_entitlements": self.claimant_entitlements,
            "unencumbered_reserves": self.unencumbered_reserves,
            "pending_external_obligations": self.pending_external_obligations,
            "terminal_bindings": self.terminal_bindings,
        }


@dataclass(frozen=True, slots=True)
class ChainContextV1:
    chain_id: str
    deployment_root: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="chain context chain id")
        _require_root(self.deployment_root, name="chain context deployment root")

    def to_canonical(self) -> dict[str, object]:
        return {"chain_id": self.chain_id, "deployment_root": self.deployment_root}


@dataclass(frozen=True, slots=True)
class GlobalAccountingAllocationCertificateV1:
    """The nine required sidecar fields; the three roots are derived and re-checked."""

    global_state_root: str
    profile_root: str
    writer_epoch: int
    chain_context: ChainContextV1
    ordered_lane_fragments: tuple[LaneAllocationFragmentV1, ...]
    canonical_allocation_rows: tuple[ClaimantEntitlementRowV1, ...]
    field_ownership_root: str
    terminal_binding_root: str
    allocation_root: str
    reserve_interpretation: ReserveInterpretationV1 = ReserveInterpretationV1.NAMED_UNENCUMBERED_NO_CLAIMANT

    def __post_init__(self) -> None:
        _require_root(self.global_state_root, name="certificate global state root")
        _require_root(self.profile_root, name="certificate profile root")
        _require_nonnegative_int(self.writer_epoch, name="certificate writer epoch")
        if type(self.chain_context) is not ChainContextV1:
            raise TypeError("certificate chain context is not the exact typed value")
        fragments = _require_tuple(self.ordered_lane_fragments, name="certificate lane fragments")
        if any(type(item) is not LaneAllocationFragmentV1 for item in fragments):
            raise TypeError("certificate contains an invalid lane fragment")
        _ordered_rows(self.canonical_allocation_rows, name="certificate canonical allocation rows", expected_type=ClaimantEntitlementRowV1)
        _require_root(self.field_ownership_root, name="certificate field ownership root", allow_zero=True)
        _require_root(self.terminal_binding_root, name="certificate terminal binding root", allow_zero=True)
        _require_root(self.allocation_root, name="certificate allocation root", allow_zero=True)
        if type(self.reserve_interpretation) is not ReserveInterpretationV1:
            raise TypeError("certificate reserve interpretation is not closed")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_ACCOUNTING_ALLOCATION_CERTIFICATE_SCHEMA_V1,
            "global_state_root": self.global_state_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "chain_context": self.chain_context,
            "ordered_lane_fragments": self.ordered_lane_fragments,
            "canonical_allocation_rows": self.canonical_allocation_rows,
            "field_ownership_root": self.field_ownership_root,
            "terminal_binding_root": self.terminal_binding_root,
            "allocation_root": self.allocation_root,
            "reserve_interpretation": self.reserve_interpretation,
        }


# ---------------------------------------------------------------------------
# Derived roots (pure)
# ---------------------------------------------------------------------------


def derive_field_ownership_root_v1(fragments: Sequence[LaneAllocationFragmentV1]) -> str:
    """Commit to which lane owns each (asset, control_domain) controlled-location column."""

    ownership = [
        {"asset": row.asset, "control_domain": row.control_domain, "lane_id": fragment.lane_id}
        for fragment in fragments
        for row in fragment.controlled_locations
    ]
    ordered = sorted(ownership, key=lambda item: (str(item["asset"]), str(item["control_domain"]), str(item["lane_id"])))
    root: str = hash_global_v1(FIELD_OWNERSHIP_ROOT_DOMAIN_V1, ordered)
    return root


def derive_terminal_binding_root_v1(fragments: Sequence[LaneAllocationFragmentV1]) -> str:
    rows = tuple(sorted((row for fragment in fragments for row in fragment.terminal_bindings), key=lambda row: row.key))
    root: str = hash_global_v1(TERMINAL_BINDING_ROOT_DOMAIN_V1, rows)
    return root


def derive_allocation_root_v1(
    fragments: Sequence[LaneAllocationFragmentV1], canonical_rows: Sequence[ClaimantEntitlementRowV1]
) -> str:
    root: str = hash_global_v1(
        ALLOCATION_ROOT_DOMAIN_V1,
        {
            "fragment_roots": [fragment.fragment_root for fragment in fragments],
            "canonical_allocation_rows": tuple(canonical_rows),
        },
    )
    return root


def derive_canonical_allocation_rows_v1(
    fragments: Sequence[LaneAllocationFragmentV1],
) -> tuple[ClaimantEntitlementRowV1, ...]:
    """Fold every lane's claimant entitlements by (asset, claimant, control_domain) with checked u128."""

    totals: dict[tuple[str, str, str], int] = {}
    for fragment in fragments:
        for row in fragment.claimant_entitlements:
            total = totals.get(row.key, 0) + row.amount_atoms
            if total > MAX_ATOMS_U128_V1:
                raise OverflowError(ALLOCATION_CERTIFICATE_REJECT_MESSAGE_BY_CODE_V1[AllocationCertificateRejectCodeV1.ALLOCATION_TOTAL_OVERFLOW])
            totals[row.key] = total
    return tuple(
        ClaimantEntitlementRowV1(asset, claimant, domain, amount)
        for (asset, claimant, domain), amount in sorted(totals.items())
    )


# ---------------------------------------------------------------------------
# Outcome types
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class AllocationCertificateAcceptedV1:
    global_state_root: str
    allocation_root: str
    field_ownership_root: str
    terminal_binding_root: str
    lane_fragment_roots: tuple[str, ...]
    authority: str = "NONE"

    def to_canonical(self) -> dict[str, object]:
        return {
            "global_state_root": self.global_state_root,
            "allocation_root": self.allocation_root,
            "field_ownership_root": self.field_ownership_root,
            "terminal_binding_root": self.terminal_binding_root,
            "lane_fragment_roots": self.lane_fragment_roots,
            "authority": self.authority,
        }


@dataclass(frozen=True, slots=True)
class AllocationCertificateRejectedV1:
    code: AllocationCertificateRejectCodeV1
    detail: str
    pre_state_root: str
    post_state_root: str

    def __post_init__(self) -> None:
        if type(self.code) is not AllocationCertificateRejectCodeV1:
            raise TypeError("allocation certificate reject code is not closed")
        _require_root(self.pre_state_root, name="rejected certificate pre-state root")
        if self.post_state_root != self.pre_state_root:
            raise ValueError("rejected certificate must preserve the exact pre-state root")

    @property
    def message(self) -> str:
        return ALLOCATION_CERTIFICATE_REJECT_MESSAGE_BY_CODE_V1[self.code]

    def to_canonical(self) -> dict[str, object]:
        return {
            "code": self.code,
            "detail": self.detail,
            "message": self.message,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
        }


class _Reject(Exception):
    def __init__(self, code: AllocationCertificateRejectCodeV1, detail: str) -> None:
        super().__init__(detail)
        self.code = code
        self.detail = detail


def _fail(code: AllocationCertificateRejectCodeV1, detail: str) -> None:
    raise _Reject(code, detail)


# ---------------------------------------------------------------------------
# Checks in fixed precedence
# ---------------------------------------------------------------------------


def _check_header(certificate: GlobalAccountingAllocationCertificateV1, state: GlobalEconomicStateV1) -> None:
    if certificate.global_state_root != state.state_root:
        _fail(AllocationCertificateRejectCodeV1.HEADER_BINDING_DRIFT, "global_state_root")
    if certificate.profile_root != state.profile_root:
        _fail(AllocationCertificateRejectCodeV1.HEADER_BINDING_DRIFT, "profile_root")
    if certificate.writer_epoch != state.writer_epoch:
        _fail(AllocationCertificateRejectCodeV1.HEADER_BINDING_DRIFT, "writer_epoch")
    if certificate.chain_context != ChainContextV1(state.chain_id, state.deployment_root):
        _fail(AllocationCertificateRejectCodeV1.HEADER_BINDING_DRIFT, "chain_context")


def _check_lane_order(certificate: GlobalAccountingAllocationCertificateV1) -> None:
    lanes = tuple(fragment.lane_id for fragment in certificate.ordered_lane_fragments)
    if lanes != ALL_LANE_IDS_V1:
        _fail(AllocationCertificateRejectCodeV1.LANE_ORDER_DRIFT, ",".join(lane.value for lane in lanes))


def _check_lane_bindings(certificate: GlobalAccountingAllocationCertificateV1, state: GlobalEconomicStateV1) -> None:
    """Check-major: every lane passes one binding check before any lane is tried against the next."""

    pairs = tuple(zip(certificate.ordered_lane_fragments, state.lane_roots, strict=True))
    for fragment, lane_root in pairs:
        if (fragment.module_release_id, fragment.enabled, fragment.lane_state_root) != (
            lane_root.module_release_id,
            lane_root.enabled,
            lane_root.state_root,
        ):
            _fail(AllocationCertificateRejectCodeV1.LANE_STATE_ROOT_DRIFT, fragment.lane_id.value)
    for fragment, _ in pairs:
        registered_kind, _ = LANE_ALLOCATION_PRODUCER_REGISTRY_V1[fragment.lane_id]
        if fragment.producer_kind != registered_kind:
            _fail(AllocationCertificateRejectCodeV1.PRODUCER_KIND_DRIFT, f"{fragment.lane_id.value}:{fragment.producer_kind.value}")
    for fragment, _ in pairs:
        registered_kind, blocked_on = LANE_ALLOCATION_PRODUCER_REGISTRY_V1[fragment.lane_id]
        if fragment.enabled and registered_kind is not LaneProducerKindV1.RECEIPT_BACKED:
            _fail(AllocationCertificateRejectCodeV1.BLOCKED_LANE_PRODUCER_MISSING, f"{fragment.lane_id.value}:{blocked_on}")
    for fragment, _ in pairs:
        if not fragment.enabled and not fragment.is_empty:
            _fail(AllocationCertificateRejectCodeV1.DISABLED_LANE_NOT_EMPTY, fragment.lane_id.value)
    for fragment, _ in pairs:
        registered_root = REGISTERED_EMPTY_LANE_ROOTS_V1.get(fragment.lane_id)
        if registered_root is not None and fragment.lane_state_root != registered_root:
            _fail(AllocationCertificateRejectCodeV1.REGISTERED_EMPTY_ROOT_DRIFT, fragment.lane_id.value)


def _fold(rows: Iterable[tuple[tuple[str, ...], int]], label: str = "fold") -> dict[tuple[str, ...], int]:
    totals: dict[tuple[str, ...], int] = {}
    for key, amount in rows:
        total = totals.get(key, 0) + amount
        if total > MAX_ATOMS_U128_V1:
            _fail(AllocationCertificateRejectCodeV1.ALLOCATION_TOTAL_OVERFLOW, label)
        totals[key] = total
    return totals


def _check_exactly_once(certificate: GlobalAccountingAllocationCertificateV1) -> None:
    """Per lane and (asset, control_domain): controlled = entitlements + reserves + pending external."""

    for fragment in certificate.ordered_lane_fragments:
        controlled = _fold(((r.asset, r.control_domain), r.amount_atoms) for r in fragment.controlled_locations)
        assigned = _fold(
            [((r.asset, r.control_domain), r.amount_atoms) for r in fragment.claimant_entitlements]
            + [((r.asset, r.control_domain), r.amount_atoms) for r in fragment.unencumbered_reserves]
            + [((r.asset, r.control_domain), r.amount_atoms) for r in fragment.pending_external_obligations],
            f"{fragment.lane_id.value} assignments",
        )
        if controlled != assigned:
            _fail(AllocationCertificateRejectCodeV1.SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE, fragment.lane_id.value)


def _check_entitlement_rows(certificate: GlobalAccountingAllocationCertificateV1, state: GlobalEconomicStateV1) -> None:
    derived = derive_canonical_allocation_rows_v1(certificate.ordered_lane_fragments)
    if derived != certificate.canonical_allocation_rows:
        _fail(AllocationCertificateRejectCodeV1.ENTITLEMENT_ROWS_DRIFT, "canonical_allocation_rows")
    liabilities = tuple((row.asset, row.owner, row.custody_domain, row.amount_atoms) for row in state.liabilities)
    rows = tuple((row.asset, row.claimant, row.control_domain, row.amount_atoms) for row in derived)
    if rows != liabilities:
        _fail(AllocationCertificateRejectCodeV1.ENTITLEMENT_ROWS_DRIFT, "liabilities")


def _check_reserve_rows(certificate: GlobalAccountingAllocationCertificateV1, state: GlobalEconomicStateV1) -> None:
    totals = _fold(
        ((r.asset, r.reserve_principal, r.control_domain), r.amount_atoms)
        for fragment in certificate.ordered_lane_fragments
        for r in fragment.unencumbered_reserves
    )
    reserves = tuple((row.asset, row.owner, row.custody_domain, row.amount_atoms) for row in state.reserves)
    rows = tuple((asset, principal, domain, amount) for (asset, principal, domain), amount in sorted(totals.items()))
    if rows != reserves:
        _fail(AllocationCertificateRejectCodeV1.RESERVE_ROWS_DRIFT, "reserves")


def _check_external_obligations(certificate: GlobalAccountingAllocationCertificateV1, state: GlobalEconomicStateV1) -> None:
    pending: dict[str, PendingExternalObligationRowV1] = {}
    for fragment in certificate.ordered_lane_fragments:
        for row in fragment.pending_external_obligations:
            if row.effect_id in pending:
                _fail(AllocationCertificateRejectCodeV1.EXTERNAL_OBLIGATION_BINDING_DRIFT, f"duplicate {row.effect_id}")
            pending[row.effect_id] = row
    outbox = {row.effect_id: row for row in state.outbox if row.status is OutboxStatusV1.PENDING}
    if set(pending) != set(outbox):
        _fail(AllocationCertificateRejectCodeV1.EXTERNAL_OBLIGATION_BINDING_DRIFT, "effect_id set")
    for effect_id, row in pending.items():
        entry = outbox[effect_id]
        if row.destination_id != entry.destination_id or row.commitment_root != entry.payload_hash:
            _fail(AllocationCertificateRejectCodeV1.EXTERNAL_OBLIGATION_BINDING_DRIFT, effect_id)


def _check_terminal_bindings(certificate: GlobalAccountingAllocationCertificateV1, state: GlobalEconomicStateV1) -> None:
    bindings: dict[str, tuple[TerminalBindingRowV1, LaneAllocationFragmentV1]] = {}
    for fragment in certificate.ordered_lane_fragments:
        for row in fragment.terminal_bindings:
            if row.obligation_id in bindings:
                _fail(AllocationCertificateRejectCodeV1.TERMINAL_BINDING_DRIFT, f"duplicate {row.obligation_id}")
            bindings[row.obligation_id] = (row, fragment)
    open_terminals = {row.obligation_id: row for row in state.terminal_obligations if row.status is TerminalObligationStatusV1.OPEN}
    if set(bindings) != set(open_terminals):
        _fail(AllocationCertificateRejectCodeV1.TERMINAL_BINDING_DRIFT, "obligation_id set")
    for obligation_id, (row, fragment) in bindings.items():
        terminal = open_terminals[obligation_id]
        if (row.claimant, row.asset, row.amount_atoms, row.lane_id) != (
            terminal.claimant,
            terminal.asset,
            terminal.amount_atoms,
            terminal.lane_id,
        ):
            _fail(AllocationCertificateRejectCodeV1.TERMINAL_BINDING_DRIFT, obligation_id)
        if row.lane_id != fragment.lane_id or row.lane_state_root != fragment.lane_state_root:
            _fail(AllocationCertificateRejectCodeV1.TERMINAL_BINDING_DRIFT, f"{obligation_id} lane binding")
        entitled = any(
            entitlement.asset == row.asset
            and entitlement.claimant == row.claimant
            and entitlement.control_domain == row.control_domain
            and entitlement.amount_atoms >= row.amount_atoms
            for entitlement in fragment.claimant_entitlements
        )
        controlled = any(
            location.asset == row.asset
            and location.controlling_principal == row.controlling_principal
            and location.control_domain == row.control_domain
            for location in fragment.controlled_locations
        )
        if not entitled or not controlled:
            _fail(AllocationCertificateRejectCodeV1.TERMINAL_BINDING_DRIFT, f"{obligation_id} domain binding")


def _check_lane_aggregates(certificate: GlobalAccountingAllocationCertificateV1, state: GlobalEconomicStateV1) -> None:
    custody = _fold(
        ((r.asset, r.controlling_principal, r.control_domain), r.amount_atoms)
        for fragment in certificate.ordered_lane_fragments
        for r in fragment.controlled_locations
    )
    expected = tuple((row.asset, row.owner, row.custody_domain, row.amount_atoms) for row in state.custody)
    rows = tuple((asset, principal, domain, amount) for (asset, principal, domain), amount in sorted(custody.items()))
    if rows != expected:
        _fail(AllocationCertificateRejectCodeV1.LANE_AGGREGATE_DRIFT, "custody")


def _check_derived_roots(certificate: GlobalAccountingAllocationCertificateV1) -> None:
    fragments = certificate.ordered_lane_fragments
    if certificate.field_ownership_root != derive_field_ownership_root_v1(fragments):
        _fail(AllocationCertificateRejectCodeV1.DERIVED_ROOT_DRIFT, "field_ownership_root")
    if certificate.terminal_binding_root != derive_terminal_binding_root_v1(fragments):
        _fail(AllocationCertificateRejectCodeV1.DERIVED_ROOT_DRIFT, "terminal_binding_root")
    if certificate.allocation_root != derive_allocation_root_v1(fragments, certificate.canonical_allocation_rows):
        _fail(AllocationCertificateRejectCodeV1.DERIVED_ROOT_DRIFT, "allocation_root")


CHECK_ORDER_V1: Final[tuple[str, ...]] = (
    "header_binding",
    "exact_twelve_lane_order",
    "enabled_lane_supported_receipt_backed_producer",
    "disabled_lane_registered_empty_state_root",
    "every_controlled_source_atom_assigned_exactly_once",
    "claimant_entitlement_rows_equal_v1_liabilities",
    "unencumbered_reserve_rows_equal_v1_reserve_partition",
    "external_obligations_bind_asset_amount_destination_and_commitment",
    "terminal_rows_bind_claimant_asset_amount_control_domain_principal_lane_and_state_root",
    "lane_aggregates_equal_global_economic_tables",
    "checked_u128_arithmetic_and_canonical_order",
    "derived_roots",
)


def check_global_accounting_allocation_certificate_v1(
    certificate: GlobalAccountingAllocationCertificateV1, state: GlobalEconomicStateV1
) -> AllocationCertificateAcceptedV1 | AllocationCertificateRejectedV1:
    """Total function: accept with derived roots, or reject with the first failing closed code.

    Checked u128 arithmetic and canonical order are enforced by construction of every
    row and fold (``ALLOCATION_TOTAL_OVERFLOW`` fires inside the first fold that
    overflows), so the tenth sidecar check is discharged by the types and folds rather
    than by a separate pass. A reject never mutates and carries the pre-state root.
    """

    if type(certificate) is not GlobalAccountingAllocationCertificateV1:
        raise TypeError("certificate must be the exact typed value")
    if type(state) is not GlobalEconomicStateV1:
        raise TypeError("state must be the exact typed value")
    pre_state_root = state.state_root
    try:
        _check_header(certificate, state)
        _check_lane_order(certificate)
        _check_lane_bindings(certificate, state)
        _check_exactly_once(certificate)
        _check_entitlement_rows(certificate, state)
        _check_reserve_rows(certificate, state)
        _check_external_obligations(certificate, state)
        _check_terminal_bindings(certificate, state)
        _check_lane_aggregates(certificate, state)
        _check_derived_roots(certificate)
    except _Reject as rejected:
        return AllocationCertificateRejectedV1(rejected.code, rejected.detail, pre_state_root, pre_state_root)
    except OverflowError as overflow:
        return AllocationCertificateRejectedV1(
            AllocationCertificateRejectCodeV1.ALLOCATION_TOTAL_OVERFLOW, str(overflow), pre_state_root, pre_state_root
        )
    return AllocationCertificateAcceptedV1(
        global_state_root=certificate.global_state_root,
        allocation_root=certificate.allocation_root,
        field_ownership_root=certificate.field_ownership_root,
        terminal_binding_root=certificate.terminal_binding_root,
        lane_fragment_roots=tuple(fragment.fragment_root for fragment in certificate.ordered_lane_fragments),
    )


def build_registered_empty_certificate_v1(state: GlobalEconomicStateV1) -> GlobalAccountingAllocationCertificateV1:
    """Project the only certificate the current profile can produce: twelve empty registered fragments.

    This is a pure projection of the state's lane roots; it accepts only when the
    state's custody, liabilities, reserves, OPEN terminals, and PENDING outbox are
    empty and every lane is disabled, and it rejects with a typed code otherwise.
    """

    fragments = tuple(
        LaneAllocationFragmentV1(
            lane_id=lane_root.lane_id,
            module_release_id=lane_root.module_release_id,
            enabled=lane_root.enabled,
            lane_state_root=lane_root.state_root,
            producer_kind=LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane_root.lane_id][0],
            binding_root=lane_root.state_root,
        )
        for lane_root in state.lane_roots
    )
    rows = derive_canonical_allocation_rows_v1(fragments)
    return GlobalAccountingAllocationCertificateV1(
        global_state_root=state.state_root,
        profile_root=state.profile_root,
        writer_epoch=state.writer_epoch,
        chain_context=ChainContextV1(state.chain_id, state.deployment_root),
        ordered_lane_fragments=fragments,
        canonical_allocation_rows=rows,
        field_ownership_root=derive_field_ownership_root_v1(fragments),
        terminal_binding_root=derive_terminal_binding_root_v1(fragments),
        allocation_root=derive_allocation_root_v1(fragments, rows),
    )


def certificate_registry_view_v1() -> Mapping[str, dict[str, str]]:
    """Exhaustive, ordered view of the producer registry for evidence packets."""

    return {
        lane.value: {"producer_kind": kind.value, "blocked_on": blocked_on}
        for lane, (kind, blocked_on) in ((lane, LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane]) for lane in ALL_LANE_IDS_V1)
    }


__all__ = [
    "ALLOCATION_CERTIFICATE_REJECT_MESSAGE_BY_CODE_V1",
    "ALLOCATION_ROOT_DOMAIN_V1",
    "AllocationCertificateAcceptedV1",
    "AllocationCertificateRejectCodeV1",
    "AllocationCertificateRejectedV1",
    "CHECK_ORDER_V1",
    "ChainContextV1",
    "ClaimantEntitlementRowV1",
    "ControlledLocationRowV1",
    "FIELD_OWNERSHIP_ROOT_DOMAIN_V1",
    "GLOBAL_ACCOUNTING_ALLOCATION_CERTIFICATE_SCHEMA_V1",
    "GlobalAccountingAllocationCertificateV1",
    "LANE_ALLOCATION_PRODUCER_REGISTRY_V1",
    "REGISTERED_EMPTY_LANE_ROOTS_V1",
    "LANE_FRAGMENT_ROOT_DOMAIN_V1",
    "LaneAllocationFragmentV1",
    "LaneProducerKindV1",
    "NORMATIVE_PARTITION_V1",
    "PendingExternalObligationRowV1",
    "ReserveInterpretationV1",
    "TERMINAL_BINDING_ROOT_DOMAIN_V1",
    "TerminalBindingRowV1",
    "UnencumberedReserveRowV1",
    "build_registered_empty_certificate_v1",
    "certificate_registry_view_v1",
    "check_global_accounting_allocation_certificate_v1",
    "derive_allocation_root_v1",
    "derive_canonical_allocation_rows_v1",
    "derive_field_ownership_root_v1",
    "derive_terminal_binding_root_v1",
]

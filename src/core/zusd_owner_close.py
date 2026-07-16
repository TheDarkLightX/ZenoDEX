"""Unmounted Liquity V1 F04/F21 owner-close functional core.

The baseline behavior is pinned to Liquity V1 commit
``8f52f2906f99414c0b1c3a84c95c74c319b7a8c6``. In that source,
``BorrowerOperations.closeTrove`` requires an active owner trove, Normal Mode,
the owner's exact net-debt balance, and a post-close TCR at least the CCR. It
then removes stake and the sorted-list entry, closes the lifecycle, burns net
debt from the owner and the fixed reserve from the Gas Pool, and returns all
collateral. ``TroveManager._closeTrove`` additionally forbids removal of the
last active trove.

This module evaluates that behavior over immutable, typed projections. The
active lifecycle derives composite debt as ``net debt + 200e18``; a zero-debt
active vault or a differently sized embedded reserve cannot be constructed.
The surrounding state is an assembled F04/F17/F21 projection, so cross-root
inconsistencies remain representable only long enough to produce a typed
no-op rejection. Acceptance constructs every debit, burn, lifecycle, stake,
index-count, and collateral-credit leg from the same active vault.

Every result retains its complete replay input. Result construction checks the
exact guard evaluation, effect plan, and poststate; ``committed_state`` then
reruns and compares the full transition before projecting state. The
module-level result token is therefore only an additional nominal API guard.

The Normal/Recovery relation is checked from the supplied aggregate at
construction, including the exact CCR boundary and the zero-debt convention.
Pending-reward application, exact F25 source projection, F17 effect
application, F19 stake accounting, F21 nullifiers, F23 decision production,
F24 authentication, F15 composition, F16 CAS/outbox commit, concrete sorted
link removal, canonical serialization, shell mounting, and Python-to-Lean or
Rust refinement remain explicit external obligations. The decision objects in
this file retain trusted source projections; relation checking is not evidence
that a decision root or actor was authenticated.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import KW_ONLY, InitVar, dataclass
from enum import Enum
from typing import TypeAlias, cast

U256_MODULUS = 1 << 256
U256_MAX = U256_MODULUS - 1
ZUSD_SCALE = 10**18
PRICE_SCALE_E18 = 10**18
LIQUITY_V1_CCR_E18 = 1_500_000_000_000_000_000
LIQUITY_V1_GAS_RESERVE_ATOMS = 200 * ZUSD_SCALE
LIQUITY_V1_MIN_NET_DEBT_ATOMS = 1_800 * ZUSD_SCALE
LIQUITY_V1_MIN_COMPOSITE_DEBT_ATOMS = (
    LIQUITY_V1_MIN_NET_DEBT_ATOMS + LIQUITY_V1_GAS_RESERVE_ATOMS
)

_RESULT_CONSTRUCTION_TOKEN = object()


def _require_u256(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    if value < 0 or value >= U256_MODULUS:
        raise ValueError(f"{name} must be in the unsigned 256-bit domain")
    return value


def _require_positive_u256(value: object, *, name: str) -> int:
    checked = _require_u256(value, name=name)
    if checked == 0:
        raise ValueError(f"{name} must be positive")
    return checked


def _require_exact_type(value: object, expected: type[object], *, name: str) -> None:
    if type(value) is not expected:
        raise TypeError(f"{name} must be {expected.__name__}")


@dataclass(frozen=True, slots=True, order=True)
class ZUSDAtoms:
    value: int

    def __post_init__(self) -> None:
        _require_u256(self.value, name="ZUSDAtoms.value")


@dataclass(frozen=True, slots=True, order=True)
class CollateralAtoms:
    value: int

    def __post_init__(self) -> None:
        _require_u256(self.value, name="CollateralAtoms.value")


@dataclass(frozen=True, slots=True, order=True)
class StakeAtoms:
    value: int

    def __post_init__(self) -> None:
        _require_u256(self.value, name="StakeAtoms.value")


@dataclass(frozen=True, slots=True, order=True)
class PriceE18:
    value: int

    def __post_init__(self) -> None:
        _require_positive_u256(self.value, name="PriceE18.value")


@dataclass(frozen=True, slots=True, order=True)
class SequenceNumber:
    value: int

    def __post_init__(self) -> None:
        _require_u256(self.value, name="SequenceNumber.value")


@dataclass(frozen=True, slots=True, order=True)
class ActiveVaultCount:
    value: int

    def __post_init__(self) -> None:
        _require_u256(self.value, name="ActiveVaultCount.value")


@dataclass(frozen=True, slots=True, order=True)
class AccountIdentity:
    value: int

    def __post_init__(self) -> None:
        _require_positive_u256(self.value, name="AccountIdentity.value")


@dataclass(frozen=True, slots=True, order=True)
class VaultIdentity:
    value: int

    def __post_init__(self) -> None:
        _require_positive_u256(self.value, name="VaultIdentity.value")


@dataclass(frozen=True, slots=True)
class CommitmentDigest:
    value: bytes

    def __post_init__(self) -> None:
        if type(self.value) is not bytes:
            raise TypeError("CommitmentDigest.value must be bytes")
        if len(self.value) != 32:
            raise ValueError("CommitmentDigest.value must contain exactly 32 bytes")


@dataclass(frozen=True, slots=True)
class ActiveWithCompositeDebt:
    """F04 active lifecycle with a source-fixed reserve and positive net debt."""

    vault_identity: VaultIdentity
    owner_identity: AccountIdentity
    collateral_atoms: CollateralAtoms
    net_debt_atoms: ZUSDAtoms
    reserve_debt_atoms: ZUSDAtoms
    stake_atoms: StakeAtoms

    def __post_init__(self) -> None:
        _require_exact_type(self.vault_identity, VaultIdentity, name="vault_identity")
        _require_exact_type(self.owner_identity, AccountIdentity, name="owner_identity")
        _require_exact_type(self.collateral_atoms, CollateralAtoms, name="collateral_atoms")
        _require_exact_type(self.net_debt_atoms, ZUSDAtoms, name="net_debt_atoms")
        _require_exact_type(self.reserve_debt_atoms, ZUSDAtoms, name="reserve_debt_atoms")
        _require_exact_type(self.stake_atoms, StakeAtoms, name="stake_atoms")
        if self.collateral_atoms.value == 0:
            raise ValueError("an active vault must have positive collateral")
        if self.net_debt_atoms.value < LIQUITY_V1_MIN_NET_DEBT_ATOMS:
            raise ValueError("Liquity V1 active net debt must be at least 1800e18")
        if self.reserve_debt_atoms.value != LIQUITY_V1_GAS_RESERVE_ATOMS:
            raise ValueError("Liquity V1 active reserve must equal 200e18 zUSD atoms")
        if self.net_debt_atoms.value > U256_MAX - self.reserve_debt_atoms.value:
            raise ValueError("active composite debt must fit in the u256 source domain")

    @property
    def composite_debt_atoms(self) -> ZUSDAtoms:
        return ZUSDAtoms(self.net_debt_atoms.value + self.reserve_debt_atoms.value)


@dataclass(frozen=True, slots=True)
class ClosedByOwner:
    """F04 terminal-for-this-occurrence lifecycle with no active value fields."""

    vault_identity: VaultIdentity
    owner_identity: AccountIdentity
    close_occurrence: SequenceNumber

    def __post_init__(self) -> None:
        _require_exact_type(self.vault_identity, VaultIdentity, name="vault_identity")
        _require_exact_type(self.owner_identity, AccountIdentity, name="owner_identity")
        _require_exact_type(self.close_occurrence, SequenceNumber, name="close_occurrence")
        if self.close_occurrence.value == 0:
            raise ValueError("owner-close occurrence must be positive")


OwnerCloseLifecycle: TypeAlias = ActiveWithCompositeDebt | ClosedByOwner


@dataclass(frozen=True, slots=True)
class SystemAggregateProjection:
    collateral_atoms: CollateralAtoms
    composite_debt_atoms: ZUSDAtoms
    total_active_stake_atoms: StakeAtoms
    active_vault_and_index_count: ActiveVaultCount

    def __post_init__(self) -> None:
        _require_exact_type(self.collateral_atoms, CollateralAtoms, name="collateral_atoms")
        _require_exact_type(
            self.composite_debt_atoms,
            ZUSDAtoms,
            name="composite_debt_atoms",
        )
        _require_exact_type(
            self.total_active_stake_atoms,
            StakeAtoms,
            name="total_active_stake_atoms",
        )
        _require_exact_type(
            self.active_vault_and_index_count,
            ActiveVaultCount,
            name="active_vault_and_index_count",
        )


@dataclass(frozen=True, slots=True)
class OwnerWalletProjection:
    owner_identity: AccountIdentity
    zusd_balance_atoms: ZUSDAtoms
    collateral_balance_atoms: CollateralAtoms

    def __post_init__(self) -> None:
        _require_exact_type(self.owner_identity, AccountIdentity, name="owner_identity")
        _require_exact_type(self.zusd_balance_atoms, ZUSDAtoms, name="zusd_balance_atoms")
        _require_exact_type(
            self.collateral_balance_atoms,
            CollateralAtoms,
            name="collateral_balance_atoms",
        )


@dataclass(frozen=True, slots=True)
class GasReserveProjection:
    target_vault_identity: VaultIdentity
    target_reserve_atoms: ZUSDAtoms
    gas_pool_custody_atoms: ZUSDAtoms

    def __post_init__(self) -> None:
        _require_exact_type(
            self.target_vault_identity,
            VaultIdentity,
            name="target_vault_identity",
        )
        _require_exact_type(
            self.target_reserve_atoms,
            ZUSDAtoms,
            name="target_reserve_atoms",
        )
        _require_exact_type(
            self.gas_pool_custody_atoms,
            ZUSDAtoms,
            name="gas_pool_custody_atoms",
        )


@dataclass(frozen=True, slots=True)
class SupplyProjection:
    """Acceptance-critical live zUSD supply.

    Exact per-transition burns are emitted in ``OwnerCloseEffects``. Historical
    zUSD burn totals are replay/chunk-derived audit data and cannot gate a
    Liquity V1 owner close, so no finite cumulative counter is represented
    here.
    """

    total_zusd_supply_atoms: ZUSDAtoms

    def __post_init__(self) -> None:
        _require_exact_type(
            self.total_zusd_supply_atoms,
            ZUSDAtoms,
            name="total_zusd_supply_atoms",
        )


@dataclass(frozen=True, slots=True)
class OwnerCloseState:
    """Immutable pointwise bundle; cross-machine equalities are transition guards."""

    lifecycle: OwnerCloseLifecycle
    system: SystemAggregateProjection
    owner_wallet: OwnerWalletProjection
    gas_reserve: GasReserveProjection
    supply: SupplyProjection
    transition_sequence: SequenceNumber

    def __post_init__(self) -> None:
        if type(self.lifecycle) not in (ActiveWithCompositeDebt, ClosedByOwner):
            raise TypeError("lifecycle must be ActiveWithCompositeDebt or ClosedByOwner")
        _require_exact_type(self.system, SystemAggregateProjection, name="system")
        _require_exact_type(self.owner_wallet, OwnerWalletProjection, name="owner_wallet")
        _require_exact_type(self.gas_reserve, GasReserveProjection, name="gas_reserve")
        _require_exact_type(self.supply, SupplyProjection, name="supply")
        _require_exact_type(
            self.transition_sequence,
            SequenceNumber,
            name="transition_sequence",
        )


@dataclass(frozen=True, slots=True)
class OwnerCloseContext:
    """Exact roots/sequencing supplied by the future F15/F16 shell binding."""

    vault_state_root: CommitmentDigest
    asset_ledger_root: CommitmentDigest
    gas_reserve_root: CommitmentDigest
    risk_decision_root: CommitmentDigest
    owner_close_sequence: SequenceNumber

    def __post_init__(self) -> None:
        for name in (
            "vault_state_root",
            "asset_ledger_root",
            "gas_reserve_root",
            "risk_decision_root",
        ):
            _require_exact_type(getattr(self, name), CommitmentDigest, name=name)
        _require_exact_type(
            self.owner_close_sequence,
            SequenceNumber,
            name="owner_close_sequence",
        )


@dataclass(frozen=True, slots=True)
class AuthenticatedOwnerCapability:
    """Trusted F24 occurrence retained with actor, target, state, and sequence."""

    actor_identity: AccountIdentity
    target_vault_identity: VaultIdentity
    authenticated_command_occurrence: SequenceNumber
    expected_context: OwnerCloseContext
    expected_owner_close_sequence: SequenceNumber

    def __post_init__(self) -> None:
        _require_exact_type(self.actor_identity, AccountIdentity, name="actor_identity")
        _require_exact_type(
            self.target_vault_identity,
            VaultIdentity,
            name="target_vault_identity",
        )
        _require_exact_type(
            self.authenticated_command_occurrence,
            SequenceNumber,
            name="authenticated_command_occurrence",
        )
        if self.authenticated_command_occurrence.value == 0:
            raise ValueError("authenticated command occurrence must be positive")
        _require_exact_type(self.expected_context, OwnerCloseContext, name="expected_context")
        _require_exact_type(
            self.expected_owner_close_sequence,
            SequenceNumber,
            name="expected_owner_close_sequence",
        )


def _validate_risk_inputs(
    source_context: OwnerCloseContext,
    system_collateral_atoms: CollateralAtoms,
    system_composite_debt_atoms: ZUSDAtoms,
    price_e18: PriceE18,
) -> None:
    _require_exact_type(source_context, OwnerCloseContext, name="source_context")
    _require_exact_type(
        system_collateral_atoms,
        CollateralAtoms,
        name="system_collateral_atoms",
    )
    _require_exact_type(
        system_composite_debt_atoms,
        ZUSDAtoms,
        name="system_composite_debt_atoms",
    )
    _require_exact_type(price_e18, PriceE18, name="price_e18")


def _is_at_or_above_ccr(
    collateral_atoms: CollateralAtoms,
    composite_debt_atoms: ZUSDAtoms,
    price_e18: PriceE18,
) -> bool:
    if composite_debt_atoms.value == 0:
        return True
    numerator = collateral_atoms.value * price_e18.value
    if numerator >= U256_MODULUS:
        raise ValueError("TCR collateral-price numerator exceeds u256")
    return numerator // composite_debt_atoms.value >= LIQUITY_V1_CCR_E18


def _validate_risk_mode_inputs(
    source_context: OwnerCloseContext,
    system_collateral_atoms: CollateralAtoms,
    system_composite_debt_atoms: ZUSDAtoms,
    price_e18: PriceE18,
    *,
    expected_normal_mode: bool,
) -> None:
    _validate_risk_inputs(
        source_context,
        system_collateral_atoms,
        system_composite_debt_atoms,
        price_e18,
    )
    actual_normal_mode = _is_at_or_above_ccr(
        system_collateral_atoms,
        system_composite_debt_atoms,
        price_e18,
    )
    if actual_normal_mode is not expected_normal_mode:
        relation = "at or above" if expected_normal_mode else "below"
        raise ValueError(
            f"system TCR inputs must be {relation} the Liquity V1 CCR"
        )


@dataclass(frozen=True, slots=True)
class NormalModeDecision:
    source_context: OwnerCloseContext
    system_collateral_atoms: CollateralAtoms
    system_composite_debt_atoms: ZUSDAtoms
    price_e18: PriceE18

    def __post_init__(self) -> None:
        _validate_risk_mode_inputs(
            self.source_context,
            self.system_collateral_atoms,
            self.system_composite_debt_atoms,
            self.price_e18,
            expected_normal_mode=True,
        )


@dataclass(frozen=True, slots=True)
class RecoveryModeDecision:
    source_context: OwnerCloseContext
    system_collateral_atoms: CollateralAtoms
    system_composite_debt_atoms: ZUSDAtoms
    price_e18: PriceE18

    def __post_init__(self) -> None:
        _validate_risk_mode_inputs(
            self.source_context,
            self.system_collateral_atoms,
            self.system_composite_debt_atoms,
            self.price_e18,
            expected_normal_mode=False,
        )


RiskModeDecision: TypeAlias = NormalModeDecision | RecoveryModeDecision


def derive_risk_mode_decision(
    source_context: OwnerCloseContext,
    system_collateral_atoms: CollateralAtoms,
    system_composite_debt_atoms: ZUSDAtoms,
    price_e18: PriceE18,
) -> RiskModeDecision:
    """Construct the unique Liquity V1 mode for an exact aggregate projection."""

    _validate_risk_inputs(
        source_context,
        system_collateral_atoms,
        system_composite_debt_atoms,
        price_e18,
    )
    decision_type = (
        NormalModeDecision
        if _is_at_or_above_ccr(
            system_collateral_atoms,
            system_composite_debt_atoms,
            price_e18,
        )
        else RecoveryModeDecision
    )
    return decision_type(
        source_context,
        system_collateral_atoms,
        system_composite_debt_atoms,
        price_e18,
    )


def _candidate_is_at_or_above_ccr(
    collateral_atoms: CollateralAtoms,
    composite_debt_atoms: ZUSDAtoms,
    price_e18: PriceE18,
) -> bool:
    try:
        return _is_at_or_above_ccr(
            collateral_atoms,
            composite_debt_atoms,
            price_e18,
        )
    except ValueError as error:
        raise ValueError(
            "candidate TCR collateral-price numerator exceeds u256"
        ) from error


def _validate_candidate_tcr_inputs(
    source_context: OwnerCloseContext,
    candidate_system_collateral_atoms: CollateralAtoms,
    candidate_system_composite_debt_atoms: ZUSDAtoms,
    price_e18: PriceE18,
    *,
    expected_at_or_above: bool,
) -> None:
    _validate_risk_inputs(
        source_context,
        candidate_system_collateral_atoms,
        candidate_system_composite_debt_atoms,
        price_e18,
    )
    actual = _candidate_is_at_or_above_ccr(
        candidate_system_collateral_atoms,
        candidate_system_composite_debt_atoms,
        price_e18,
    )
    if actual is not expected_at_or_above:
        relation = "at or above" if expected_at_or_above else "below"
        raise ValueError(f"candidate TCR inputs must be {relation} the Liquity V1 CCR")


@dataclass(frozen=True, slots=True)
class CandidateTCRAtOrAboveCCR:
    source_context: OwnerCloseContext
    candidate_system_collateral_atoms: CollateralAtoms
    candidate_system_composite_debt_atoms: ZUSDAtoms
    price_e18: PriceE18

    def __post_init__(self) -> None:
        _validate_candidate_tcr_inputs(
            self.source_context,
            self.candidate_system_collateral_atoms,
            self.candidate_system_composite_debt_atoms,
            self.price_e18,
            expected_at_or_above=True,
        )


@dataclass(frozen=True, slots=True)
class CandidateTCRBelowCCR:
    source_context: OwnerCloseContext
    candidate_system_collateral_atoms: CollateralAtoms
    candidate_system_composite_debt_atoms: ZUSDAtoms
    price_e18: PriceE18

    def __post_init__(self) -> None:
        _validate_candidate_tcr_inputs(
            self.source_context,
            self.candidate_system_collateral_atoms,
            self.candidate_system_composite_debt_atoms,
            self.price_e18,
            expected_at_or_above=False,
        )


CandidateTCRDecision: TypeAlias = CandidateTCRAtOrAboveCCR | CandidateTCRBelowCCR


@dataclass(frozen=True, slots=True)
class CloseVaultRequest:
    target_vault_identity: VaultIdentity
    authority: AuthenticatedOwnerCapability
    risk_mode: RiskModeDecision
    candidate_tcr: CandidateTCRDecision
    route_context: OwnerCloseContext
    actual_context: OwnerCloseContext

    def __post_init__(self) -> None:
        _require_exact_type(
            self.target_vault_identity,
            VaultIdentity,
            name="target_vault_identity",
        )
        _require_exact_type(
            self.authority,
            AuthenticatedOwnerCapability,
            name="authority",
        )
        if type(self.risk_mode) not in (NormalModeDecision, RecoveryModeDecision):
            raise TypeError("risk_mode must be an exact Normal or Recovery decision")
        if type(self.candidate_tcr) not in (
            CandidateTCRAtOrAboveCCR,
            CandidateTCRBelowCCR,
        ):
            raise TypeError("candidate_tcr must be an exact candidate TCR decision")
        _require_exact_type(self.route_context, OwnerCloseContext, name="route_context")
        _require_exact_type(self.actual_context, OwnerCloseContext, name="actual_context")


class OwnerCloseReject(Enum):
    TARGET_VAULT_INACTIVE = "target_vault_inactive"
    WRONG_VAULT_OWNER = "wrong_vault_owner"
    OWNER_WALLET_BINDING_MISMATCH = "owner_wallet_binding_mismatch"
    RECOVERY_MODE = "recovery_mode"
    INSUFFICIENT_OWNER_NET_DEBT_BALANCE = "insufficient_owner_net_debt_balance"
    FINAL_ACTIVE_VAULT = "final_active_vault"
    CANDIDATE_AGGREGATE_UNDERFLOW = "candidate_aggregate_underflow"
    CANDIDATE_ACCOUNTING_OVERFLOW = "candidate_accounting_overflow"
    CANDIDATE_AGGREGATE_INCONSISTENT = "candidate_aggregate_inconsistent"
    POST_CLOSE_TCR_BELOW_CCR = "post_close_tcr_below_ccr"
    RESERVE_CUSTODY_MISMATCH = "reserve_custody_mismatch"
    RESERVE_CUSTODY_INSUFFICIENT = "reserve_custody_insufficient"
    OWNER_CLOSE_SEQUENCE_EXHAUSTED = "owner_close_sequence_exhausted"
    STALE_OWNER_CLOSE_CONTEXT = "stale_owner_close_context"


_REJECT_ORDER = tuple(OwnerCloseReject)


@dataclass(frozen=True, slots=True)
class GuardPassed:
    ordinal: int

    def __post_init__(self) -> None:
        _require_u256(self.ordinal, name="ordinal")


@dataclass(frozen=True, slots=True)
class GuardFailed:
    ordinal: int
    code: OwnerCloseReject

    def __post_init__(self) -> None:
        _require_u256(self.ordinal, name="ordinal")
        _require_exact_type(self.code, OwnerCloseReject, name="code")


@dataclass(frozen=True, slots=True)
class GuardBlocked:
    ordinal: int
    prerequisite_ordinal: int

    def __post_init__(self) -> None:
        _require_u256(self.ordinal, name="ordinal")
        _require_u256(self.prerequisite_ordinal, name="prerequisite_ordinal")
        if self.prerequisite_ordinal >= self.ordinal:
            raise ValueError("blocked guard prerequisite must have a lower ordinal")


GuardOutcome: TypeAlias = GuardPassed | GuardFailed | GuardBlocked


def _append_guard(
    outcomes: list[GuardOutcome],
    predicate: Callable[[], bool],
    code: OwnerCloseReject,
    *,
    prerequisites: tuple[int, ...] = (),
) -> None:
    ordinal = len(outcomes)
    if _REJECT_ORDER[ordinal] is not code:
        raise RuntimeError("owner-close guard order diverged from its reject ABI")
    for prerequisite in prerequisites:
        if type(outcomes[prerequisite]) is not GuardPassed:
            outcomes.append(GuardBlocked(ordinal, prerequisite))
            return
    outcomes.append(GuardPassed(ordinal) if predicate() else GuardFailed(ordinal, code))


def _failure_projection(outcomes: tuple[GuardOutcome, ...]) -> tuple[OwnerCloseReject, ...]:
    return tuple(outcome.code for outcome in outcomes if type(outcome) is GuardFailed)


def _validate_guard_outcomes(
    outcomes: tuple[GuardOutcome, ...],
    *,
    expect_accept: bool,
) -> None:
    if type(outcomes) is not tuple or len(outcomes) != len(_REJECT_ORDER):
        raise ValueError("guard_outcomes must totalize the owner-close reject partition")
    for ordinal, outcome in enumerate(outcomes):
        if type(outcome) not in (GuardPassed, GuardFailed, GuardBlocked):
            raise TypeError("guard outcome must be Passed, Failed, or Blocked")
        if outcome.ordinal != ordinal:
            raise ValueError("guard outcome ordinal must equal its partition position")
        if type(outcome) is GuardFailed and outcome.code is not _REJECT_ORDER[ordinal]:
            raise ValueError("failed guard code must match its declared ordinal")
    failures = _failure_projection(outcomes)
    if expect_accept and any(type(outcome) is not GuardPassed for outcome in outcomes):
        raise ValueError("accepted owner close requires every guard to pass")
    if not expect_accept and not failures:
        raise ValueError("rejected owner close requires at least one failed guard")


@dataclass(frozen=True, slots=True)
class OwnerCloseEffects:
    """Data-only exact plan for the future F15/F17/F21/F16 composition shell."""

    vault_identity: VaultIdentity
    owner_identity: AccountIdentity
    close_occurrence: SequenceNumber
    owner_net_debt_burn_atoms: ZUSDAtoms
    gas_reserve_burn_atoms: ZUSDAtoms
    total_zusd_burn_atoms: ZUSDAtoms
    system_composite_debt_decrease_atoms: ZUSDAtoms
    collateral_return_atoms: CollateralAtoms
    system_collateral_decrease_atoms: CollateralAtoms
    stake_removal_atoms: StakeAtoms
    sorted_index_removal_vault_identity: VaultIdentity
    active_vault_and_index_count_decrease: ActiveVaultCount

    def __post_init__(self) -> None:
        _require_exact_type(self.vault_identity, VaultIdentity, name="vault_identity")
        _require_exact_type(self.owner_identity, AccountIdentity, name="owner_identity")
        _require_exact_type(self.close_occurrence, SequenceNumber, name="close_occurrence")
        for name in (
            "owner_net_debt_burn_atoms",
            "gas_reserve_burn_atoms",
            "total_zusd_burn_atoms",
            "system_composite_debt_decrease_atoms",
        ):
            _require_exact_type(getattr(self, name), ZUSDAtoms, name=name)
        _require_exact_type(
            self.collateral_return_atoms,
            CollateralAtoms,
            name="collateral_return_atoms",
        )
        _require_exact_type(
            self.system_collateral_decrease_atoms,
            CollateralAtoms,
            name="system_collateral_decrease_atoms",
        )
        _require_exact_type(self.stake_removal_atoms, StakeAtoms, name="stake_removal_atoms")
        _require_exact_type(
            self.sorted_index_removal_vault_identity,
            VaultIdentity,
            name="sorted_index_removal_vault_identity",
        )
        _require_exact_type(
            self.active_vault_and_index_count_decrease,
            ActiveVaultCount,
            name="active_vault_and_index_count_decrease",
        )
        exact_burn = self.owner_net_debt_burn_atoms.value + self.gas_reserve_burn_atoms.value
        if exact_burn >= U256_MODULUS or self.total_zusd_burn_atoms.value != exact_burn:
            raise ValueError("total zUSD burn must equal owner net debt plus reserve")
        if self.system_composite_debt_decrease_atoms != self.total_zusd_burn_atoms:
            raise ValueError("system debt decrease must equal the exact supply burn")
        if self.gas_reserve_burn_atoms.value != LIQUITY_V1_GAS_RESERVE_ATOMS:
            raise ValueError("owner close must burn exactly the Liquity V1 reserve")
        if self.collateral_return_atoms != self.system_collateral_decrease_atoms:
            raise ValueError("collateral return must equal system collateral decrease")
        if self.sorted_index_removal_vault_identity != self.vault_identity:
            raise ValueError("sorted-index removal must target the closed vault")
        if self.active_vault_and_index_count_decrease.value != 1:
            raise ValueError("owner close must remove exactly one active index member")


@dataclass(frozen=True, slots=True)
class OwnerCloseAccepted:
    pre_state: OwnerCloseState
    request: CloseVaultRequest
    post_state: OwnerCloseState
    effects: OwnerCloseEffects
    guard_outcomes: tuple[GuardOutcome, ...]
    _: KW_ONLY
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _RESULT_CONSTRUCTION_TOKEN:
            raise TypeError("owner-close results may only be constructed by the runner")
        _require_exact_type(self.pre_state, OwnerCloseState, name="pre_state")
        _require_exact_type(self.request, CloseVaultRequest, name="request")
        _require_exact_type(self.post_state, OwnerCloseState, name="post_state")
        _require_exact_type(self.effects, OwnerCloseEffects, name="effects")
        _validate_guard_outcomes(self.guard_outcomes, expect_accept=True)
        if self.pre_state.transition_sequence.value == U256_MAX:
            raise ValueError("accepted owner close cannot start at sequence exhaustion")
        if self.post_state.transition_sequence.value != self.pre_state.transition_sequence.value + 1:
            raise ValueError("accepted owner close must advance its sequence once")
        if type(self.post_state.lifecycle) is not ClosedByOwner:
            raise TypeError("accepted owner close must construct ClosedByOwner")
        if self.post_state.lifecycle.close_occurrence != self.post_state.transition_sequence:
            raise ValueError("closed lifecycle must bind the post-transition occurrence")
        if self.effects.close_occurrence != self.post_state.transition_sequence:
            raise ValueError("effects must bind the post-transition occurrence")
        _validate_accepted_result_binding(self)


@dataclass(frozen=True, slots=True)
class OwnerCloseRejected:
    pre_state: OwnerCloseState
    request: CloseVaultRequest
    guard_outcomes: tuple[GuardOutcome, ...]
    _: KW_ONLY
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _RESULT_CONSTRUCTION_TOKEN:
            raise TypeError("owner-close results may only be constructed by the runner")
        _require_exact_type(self.pre_state, OwnerCloseState, name="pre_state")
        _require_exact_type(self.request, CloseVaultRequest, name="request")
        _validate_guard_outcomes(self.guard_outcomes, expect_accept=False)
        _validate_rejected_result_binding(self)

    @property
    def violations(self) -> tuple[OwnerCloseReject, ...]:
        return _failure_projection(self.guard_outcomes)

    @property
    def primary_reason(self) -> OwnerCloseReject:
        return self.violations[0]


OwnerCloseResult: TypeAlias = OwnerCloseAccepted | OwnerCloseRejected


def _active_target(
    state: OwnerCloseState,
    request: CloseVaultRequest,
) -> ActiveWithCompositeDebt | None:
    lifecycle = state.lifecycle
    if type(lifecycle) is not ActiveWithCompositeDebt:
        return None
    if lifecycle.vault_identity != request.target_vault_identity:
        return None
    return lifecycle


def _has_aggregate_underflow(state: OwnerCloseState, active: ActiveWithCompositeDebt) -> bool:
    return any(
        (
            state.system.collateral_atoms.value < active.collateral_atoms.value,
            state.system.composite_debt_atoms.value < active.composite_debt_atoms.value,
            state.system.total_active_stake_atoms.value < active.stake_atoms.value,
            state.supply.total_zusd_supply_atoms.value < active.composite_debt_atoms.value,
        )
    )


def _has_accounting_overflow(state: OwnerCloseState, active: ActiveWithCompositeDebt) -> bool:
    return any(
        (
            state.owner_wallet.collateral_balance_atoms.value
            > U256_MAX - active.collateral_atoms.value,
            state.system.active_vault_and_index_count.value
            > U256_MAX // LIQUITY_V1_GAS_RESERVE_ATOMS,
        )
    )


def _candidate_aggregate_is_exact(
    state: OwnerCloseState,
    request: CloseVaultRequest,
    active: ActiveWithCompositeDebt,
) -> bool:
    candidate = request.candidate_tcr
    expected_collateral = state.system.collateral_atoms.value - active.collateral_atoms.value
    expected_debt = state.system.composite_debt_atoms.value - active.composite_debt_atoms.value
    supply = state.supply.total_zusd_supply_atoms.value
    wallet = state.owner_wallet.zusd_balance_atoms.value
    gas_pool = state.gas_reserve.gas_pool_custody_atoms.value
    active_count = state.system.active_vault_and_index_count.value
    if active_count == 0:
        return False
    minimum_remaining_collateral = active_count - 1
    minimum_remaining_debt = (
        active_count - 1
    ) * LIQUITY_V1_MIN_COMPOSITE_DEBT_ATOMS
    return all(
        (
            candidate.candidate_system_collateral_atoms.value == expected_collateral,
            candidate.candidate_system_composite_debt_atoms.value == expected_debt,
            expected_collateral >= minimum_remaining_collateral,
            expected_debt >= minimum_remaining_debt,
            supply == state.system.composite_debt_atoms.value,
            wallet <= supply,
            gas_pool <= supply,
            wallet + gas_pool <= supply,
        )
    )


def _reserve_projection_matches(
    state: OwnerCloseState,
    active: ActiveWithCompositeDebt,
) -> bool:
    reserve = state.gas_reserve
    if reserve.target_vault_identity != active.vault_identity:
        return False
    if reserve.target_reserve_atoms != active.reserve_debt_atoms:
        return False
    if reserve.gas_pool_custody_atoms.value < active.reserve_debt_atoms.value:
        # The next guard owns this mutually exclusive failure so an exact
        # shortfall reports insufficiency instead of the broader mismatch.
        return True
    expected_pool = (
        state.system.active_vault_and_index_count.value * LIQUITY_V1_GAS_RESERVE_ATOMS
    )
    # LUSDToken permits ordinary transfers to the Gas Pool. A donation must not
    # make owner close unavailable, so cardinality is a custody floor rather
    # than an exact balance. The transition still burns exactly the target's
    # source-fixed 200e18 reserve.
    return (
        expected_pool < U256_MODULUS
        and reserve.gas_pool_custody_atoms.value >= expected_pool
    )


def _context_is_current(state: OwnerCloseState, request: CloseVaultRequest) -> bool:
    actual = request.actual_context
    mode = request.risk_mode
    candidate = request.candidate_tcr
    return all(
        (
            request.route_context == actual,
            actual.owner_close_sequence == state.transition_sequence,
            request.authority.expected_context == actual,
            request.authority.expected_owner_close_sequence == state.transition_sequence,
            mode.source_context == actual,
            mode.system_collateral_atoms == state.system.collateral_atoms,
            mode.system_composite_debt_atoms == state.system.composite_debt_atoms,
            candidate.source_context == actual,
            candidate.price_e18 == mode.price_e18,
        )
    )


def _guard_outcomes(
    state: OwnerCloseState,
    request: CloseVaultRequest,
) -> tuple[GuardOutcome, ...]:
    """Evaluate the complete reject ABI as one reviewable ordinal table.

    This intentionally stays flat even though it exceeds the usual core
    function line target. Splitting the table would separate prerequisite
    ordinals from their predicates and make reject precedence harder to audit.
    Every arithmetic predicate remains a small pure helper.
    """

    active = _active_target(state, request)
    # Every active-dependent thunk is blocked by guard zero before evaluation.
    required_active = cast(ActiveWithCompositeDebt, active)
    outcomes: list[GuardOutcome] = []
    _append_guard(
        outcomes,
        lambda: active is not None,
        OwnerCloseReject.TARGET_VAULT_INACTIVE,
    )
    _append_guard(
        outcomes,
        lambda: request.authority.actor_identity == required_active.owner_identity
        and request.authority.target_vault_identity == request.target_vault_identity,
        OwnerCloseReject.WRONG_VAULT_OWNER,
        prerequisites=(0,),
    )
    _append_guard(
        outcomes,
        lambda: state.owner_wallet.owner_identity == required_active.owner_identity,
        OwnerCloseReject.OWNER_WALLET_BINDING_MISMATCH,
        prerequisites=(0,),
    )
    _append_guard(
        outcomes,
        lambda: type(request.risk_mode) is NormalModeDecision,
        OwnerCloseReject.RECOVERY_MODE,
    )
    _append_guard(
        outcomes,
        lambda: state.owner_wallet.zusd_balance_atoms.value
        >= required_active.net_debt_atoms.value,
        OwnerCloseReject.INSUFFICIENT_OWNER_NET_DEBT_BALANCE,
        prerequisites=(0, 2),
    )
    _append_guard(
        outcomes,
        lambda: state.system.active_vault_and_index_count.value > 1,
        OwnerCloseReject.FINAL_ACTIVE_VAULT,
        prerequisites=(0,),
    )
    _append_guard(
        outcomes,
        lambda: not _has_aggregate_underflow(state, required_active),
        OwnerCloseReject.CANDIDATE_AGGREGATE_UNDERFLOW,
        prerequisites=(0,),
    )
    _append_guard(
        outcomes,
        lambda: not _has_accounting_overflow(state, required_active),
        OwnerCloseReject.CANDIDATE_ACCOUNTING_OVERFLOW,
        prerequisites=(0,),
    )
    _append_guard(
        outcomes,
        lambda: _candidate_aggregate_is_exact(state, request, required_active),
        OwnerCloseReject.CANDIDATE_AGGREGATE_INCONSISTENT,
        prerequisites=(0, 6, 7),
    )
    _append_guard(
        outcomes,
        lambda: type(request.candidate_tcr) is CandidateTCRAtOrAboveCCR,
        OwnerCloseReject.POST_CLOSE_TCR_BELOW_CCR,
        prerequisites=(0, 6, 7, 8),
    )
    _append_guard(
        outcomes,
        lambda: _reserve_projection_matches(state, required_active),
        OwnerCloseReject.RESERVE_CUSTODY_MISMATCH,
        prerequisites=(0,),
    )
    _append_guard(
        outcomes,
        lambda: state.gas_reserve.gas_pool_custody_atoms.value
        >= required_active.reserve_debt_atoms.value,
        OwnerCloseReject.RESERVE_CUSTODY_INSUFFICIENT,
        prerequisites=(0,),
    )
    _append_guard(
        outcomes,
        lambda: state.transition_sequence.value < U256_MAX,
        OwnerCloseReject.OWNER_CLOSE_SEQUENCE_EXHAUSTED,
    )
    _append_guard(
        outcomes,
        lambda: _context_is_current(state, request),
        OwnerCloseReject.STALE_OWNER_CLOSE_CONTEXT,
    )
    return tuple(outcomes)


def _build_effects(
    active: ActiveWithCompositeDebt,
    close_occurrence: SequenceNumber,
) -> OwnerCloseEffects:
    return OwnerCloseEffects(
        vault_identity=active.vault_identity,
        owner_identity=active.owner_identity,
        close_occurrence=close_occurrence,
        owner_net_debt_burn_atoms=active.net_debt_atoms,
        gas_reserve_burn_atoms=active.reserve_debt_atoms,
        total_zusd_burn_atoms=active.composite_debt_atoms,
        system_composite_debt_decrease_atoms=active.composite_debt_atoms,
        collateral_return_atoms=active.collateral_atoms,
        system_collateral_decrease_atoms=active.collateral_atoms,
        stake_removal_atoms=active.stake_atoms,
        sorted_index_removal_vault_identity=active.vault_identity,
        active_vault_and_index_count_decrease=ActiveVaultCount(1),
    )


def _build_post_state(
    state: OwnerCloseState,
    active: ActiveWithCompositeDebt,
    close_occurrence: SequenceNumber,
) -> OwnerCloseState:
    return OwnerCloseState(
        lifecycle=ClosedByOwner(
            active.vault_identity,
            active.owner_identity,
            close_occurrence,
        ),
        system=SystemAggregateProjection(
            collateral_atoms=CollateralAtoms(
                state.system.collateral_atoms.value - active.collateral_atoms.value
            ),
            composite_debt_atoms=ZUSDAtoms(
                state.system.composite_debt_atoms.value - active.composite_debt_atoms.value
            ),
            total_active_stake_atoms=StakeAtoms(
                state.system.total_active_stake_atoms.value - active.stake_atoms.value
            ),
            active_vault_and_index_count=ActiveVaultCount(
                state.system.active_vault_and_index_count.value - 1
            ),
        ),
        owner_wallet=OwnerWalletProjection(
            owner_identity=active.owner_identity,
            zusd_balance_atoms=ZUSDAtoms(
                state.owner_wallet.zusd_balance_atoms.value - active.net_debt_atoms.value
            ),
            collateral_balance_atoms=CollateralAtoms(
                state.owner_wallet.collateral_balance_atoms.value
                + active.collateral_atoms.value
            ),
        ),
        gas_reserve=GasReserveProjection(
            target_vault_identity=active.vault_identity,
            target_reserve_atoms=ZUSDAtoms(0),
            gas_pool_custody_atoms=ZUSDAtoms(
                state.gas_reserve.gas_pool_custody_atoms.value
                - active.reserve_debt_atoms.value
            ),
        ),
        supply=SupplyProjection(
            total_zusd_supply_atoms=ZUSDAtoms(
                state.supply.total_zusd_supply_atoms.value
                - active.composite_debt_atoms.value
            ),
        ),
        transition_sequence=close_occurrence,
    )


def _validate_accepted_result_binding(result: OwnerCloseAccepted) -> None:
    expected_outcomes = _guard_outcomes(result.pre_state, result.request)
    if result.guard_outcomes != expected_outcomes:
        raise ValueError(
            "accepted result guards must equal deterministic guard evaluation"
        )
    if _failure_projection(expected_outcomes):
        raise ValueError("accepted result request must satisfy every owner-close guard")
    active = _active_target(result.pre_state, result.request)
    if active is None:
        raise ValueError("accepted result must bind an active target")
    close_occurrence = SequenceNumber(result.pre_state.transition_sequence.value + 1)
    expected_effects = _build_effects(active, close_occurrence)
    expected_post_state = _build_post_state(
        result.pre_state,
        active,
        close_occurrence,
    )
    if result.effects != expected_effects or result.post_state != expected_post_state:
        raise ValueError(
            "accepted result fields must equal deterministic transition construction"
        )


def _validate_rejected_result_binding(result: OwnerCloseRejected) -> None:
    expected_outcomes = _guard_outcomes(result.pre_state, result.request)
    if result.guard_outcomes != expected_outcomes:
        raise ValueError(
            "rejected result guards must equal deterministic guard evaluation"
        )


def run_owner_close(
    pre_state: OwnerCloseState,
    request: CloseVaultRequest,
) -> OwnerCloseResult:
    """Evaluate one exact Liquity V1 owner close without external effects.

    Inputs are unsigned source units and exact typed decision projections.
    Reject precedence is the declaration order in :class:`OwnerCloseReject`;
    every rejected result commits ``pre_state``. Acceptance removes one active
    lifecycle/index member and preserves:

    ``supply decrease = system debt decrease = owner burn + reserve burn``

    and

    ``system collateral decrease = owner collateral credit``.
    """

    _require_exact_type(pre_state, OwnerCloseState, name="pre_state")
    _require_exact_type(request, CloseVaultRequest, name="request")
    outcomes = _guard_outcomes(pre_state, request)
    if _failure_projection(outcomes):
        return OwnerCloseRejected(
            pre_state=pre_state,
            request=request,
            guard_outcomes=outcomes,
            _construction_token=_RESULT_CONSTRUCTION_TOKEN,
        )
    active = _active_target(pre_state, request)
    if active is None:
        raise RuntimeError("accepted owner close lost its active target")
    close_occurrence = SequenceNumber(pre_state.transition_sequence.value + 1)
    post_state = _build_post_state(pre_state, active, close_occurrence)
    return OwnerCloseAccepted(
        pre_state=pre_state,
        request=request,
        post_state=post_state,
        effects=_build_effects(active, close_occurrence),
        guard_outcomes=outcomes,
        _construction_token=_RESULT_CONSTRUCTION_TOKEN,
    )


def _replay_result(result: OwnerCloseResult) -> OwnerCloseResult:
    return run_owner_close(result.pre_state, result.request)


def committed_state(result: OwnerCloseResult) -> OwnerCloseState:
    """Project state only after exact deterministic replay of every result field."""

    if type(result) not in (OwnerCloseAccepted, OwnerCloseRejected):
        raise TypeError("result must be OwnerCloseAccepted or OwnerCloseRejected")
    replayed = _replay_result(result)
    if replayed != result:
        raise ValueError("owner-close result does not equal deterministic transition replay")
    if type(result) is OwnerCloseAccepted:
        return result.post_state
    return result.pre_state

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, IntEnum

MAX_TOKEN_UNITS = (1 << 32) - 1


class GenericTokenAction(str, Enum):
    """Operations exposed by the generic token writer."""

    TRANSFER = "transfer"
    MINT = "mint"
    BURN = "burn"


class TokenAssetClass(str, Enum):
    """Asset classification already bound by the calling runtime."""

    CANONICAL_ZUSD = "canonical_zusd"
    OTHER = "other"


class TokenWriterRole(str, Enum):
    """Authority role already authenticated by the calling runtime."""

    GENERIC_TOKEN_WRITER = "generic_token_writer"
    ZUSD_MONETARY_AUTHORITY = "zusd_monetary_authority"


class CanonicalZUSDRecipientClass(str, Enum):
    """Destination classes that could carry protocol-accounted zUSD units.

    Stability Pool escrow is the only currently addressable live class. The
    other internal-ledger classes make future balance locations explicit and
    fail closed before any address is added to the authoritative registry.
    """

    ORDINARY_ACCOUNT = "ordinary_account"
    STABILITY_POOL_ESCROW = "stability_pool_escrow"
    GAS_RESERVE_LEDGER = "gas_reserve_ledger"
    PROTOCOL_FEE_RESERVE_LEDGER = "protocol_fee_reserve_ledger"
    STAKING_FEE_POOL_LEDGER = "staking_fee_pool_ledger"
    HOST_FEE_POOL_LEDGER = "host_fee_pool_ledger"
    PERPS_QUOTE_LIABILITY_LEDGER = "perps_quote_liability_ledger"
    DEX_POOL_RESERVE = "dex_pool_reserve"
    BRIDGE_ESCROW = "bridge_escrow"

    @property
    def is_reserved_protocol_location(self) -> bool:
        return self is not CanonicalZUSDRecipientClass.ORDINARY_ACCOUNT


class GenericTokenAdmissionCode(IntEnum):
    """Stable, exhaustive result codes for the canonical-zUSD authority policy."""

    ADMITTED = 0
    CANONICAL_ZUSD_MINT_REQUIRES_MONETARY_AUTHORITY = 1
    CANONICAL_ZUSD_BURN_REQUIRES_MONETARY_AUTHORITY = 2
    CANONICAL_ZUSD_RESERVED_PROTOCOL_ADDRESS_REQUIRES_MONETARY_AUTHORITY = 3
    ROUTE_TO_ZUSD_MONETARY_KERNEL = 4


@dataclass(frozen=True, slots=True)
class ReservedCanonicalZUSDPrincipal:
    """One exact canonical pubkey and its reserved recipient classification."""

    recipient_pubkey: str
    recipient_class: CanonicalZUSDRecipientClass

    def __post_init__(self) -> None:
        if type(self.recipient_pubkey) is not str or not self.recipient_pubkey:
            raise TypeError("recipient_pubkey must be a non-empty str")
        if not isinstance(self.recipient_class, CanonicalZUSDRecipientClass):
            raise TypeError(
                "recipient_class must be a CanonicalZUSDRecipientClass"
            )
        if not self.recipient_class.is_reserved_protocol_location:
            raise ValueError("ordinary accounts must not appear in the reserved registry")


@dataclass(frozen=True, slots=True)
class CanonicalZUSDProtocolAddressRegistry:
    """Immutable, canonical registry for exact recipient-role classification."""

    principals: tuple[ReservedCanonicalZUSDPrincipal, ...]

    def __post_init__(self) -> None:
        if type(self.principals) is not tuple:
            raise TypeError("principals must be a tuple")
        previous_pubkey: str | None = None
        for principal in self.principals:
            if type(principal) is not ReservedCanonicalZUSDPrincipal:
                raise TypeError(
                    "principals must contain ReservedCanonicalZUSDPrincipal values"
                )
            if previous_pubkey is not None and principal.recipient_pubkey <= previous_pubkey:
                raise ValueError(
                    "reserved protocol principals must have unique, strictly sorted pubkeys"
                )
            previous_pubkey = principal.recipient_pubkey

    def classify(self, recipient_pubkey: str) -> CanonicalZUSDRecipientClass:
        """Classify one canonical pubkey by exact equality."""

        if type(recipient_pubkey) is not str or not recipient_pubkey:
            raise TypeError("recipient_pubkey must be a non-empty str")
        for principal in self.principals:
            if principal.recipient_pubkey == recipient_pubkey:
                return principal.recipient_class
        return CanonicalZUSDRecipientClass.ORDINARY_ACCOUNT


@dataclass(frozen=True, slots=True)
class GenericTokenAdmissionCommand:
    """Typed facts needed to decide the generic-writer authority boundary.

    The four enums form a closed decision space. Recipient classification is
    relevant only to transfers, which makes its irrelevance explicit and
    exhaustively testable for mint and burn.
    """

    action: GenericTokenAction
    asset_class: TokenAssetClass
    writer_role: TokenWriterRole
    recipient_class: CanonicalZUSDRecipientClass

    def __post_init__(self) -> None:
        if not isinstance(self.action, GenericTokenAction):
            raise TypeError("action must be a GenericTokenAction")
        if not isinstance(self.asset_class, TokenAssetClass):
            raise TypeError("asset_class must be a TokenAssetClass")
        if not isinstance(self.writer_role, TokenWriterRole):
            raise TypeError("writer_role must be a TokenWriterRole")
        if not isinstance(
            self.recipient_class, CanonicalZUSDRecipientClass
        ):
            raise TypeError(
                "recipient_class must be a CanonicalZUSDRecipientClass"
            )


@dataclass(frozen=True, slots=True)
class CanonicalZUSDSupplyState:
    """The canonical supply projection owned by this admission kernel."""

    total_supply_units: int

    def __post_init__(self) -> None:
        if not isinstance(self.total_supply_units, int) or isinstance(
            self.total_supply_units, bool
        ):
            raise TypeError("total_supply_units must be an int")
        if not 0 <= self.total_supply_units <= MAX_TOKEN_UNITS:
            raise ValueError(f"total_supply_units must be in [0, {MAX_TOKEN_UNITS}]")


@dataclass(frozen=True, slots=True)
class GenericTokenAdmissionDecision:
    """Canonical-zUSD authority decision with no internally inconsistent flags."""

    code: GenericTokenAdmissionCode

    @property
    def admitted(self) -> bool:
        return self.code is GenericTokenAdmissionCode.ADMITTED

    @property
    def requires_zusd_monetary_kernel(self) -> bool:
        return self.code is GenericTokenAdmissionCode.ROUTE_TO_ZUSD_MONETARY_KERNEL

    @property
    def canonical_zusd_supply_delta(self) -> int:
        # This is the admission-stage delta. Routed monetary operations are
        # applied only by their separate supply-changing kernel.
        return 0


@dataclass(frozen=True, slots=True)
class GenericTokenAdmissionTransition:
    """Pure admission result over the supply projection.

    This kernel decides authority only. It never applies account-balance or
    balance effects. The imperative shell may execute an admitted operation
    after its independent balance, amount, signature, and atomic-commit checks.
    """

    pre_state: CanonicalZUSDSupplyState
    post_state: CanonicalZUSDSupplyState
    decision: GenericTokenAdmissionDecision

    @property
    def state_unchanged(self) -> bool:
        return self.post_state == self.pre_state


def evaluate_generic_token_admission(
    command: GenericTokenAdmissionCommand,
) -> GenericTokenAdmissionDecision:
    """Return the complete generic-writer policy decision for one operation."""

    if not isinstance(command, GenericTokenAdmissionCommand):
        raise TypeError("command must be a GenericTokenAdmissionCommand")

    if command.writer_role is TokenWriterRole.ZUSD_MONETARY_AUTHORITY:
        return GenericTokenAdmissionDecision(
            GenericTokenAdmissionCode.ROUTE_TO_ZUSD_MONETARY_KERNEL
        )

    if command.asset_class is TokenAssetClass.OTHER:
        return GenericTokenAdmissionDecision(GenericTokenAdmissionCode.ADMITTED)

    if command.action is GenericTokenAction.MINT:
        return GenericTokenAdmissionDecision(
            GenericTokenAdmissionCode.CANONICAL_ZUSD_MINT_REQUIRES_MONETARY_AUTHORITY
        )
    if command.action is GenericTokenAction.BURN:
        return GenericTokenAdmissionDecision(
            GenericTokenAdmissionCode.CANONICAL_ZUSD_BURN_REQUIRES_MONETARY_AUTHORITY
        )
    if command.recipient_class.is_reserved_protocol_location:
        return GenericTokenAdmissionDecision(
            GenericTokenAdmissionCode.CANONICAL_ZUSD_RESERVED_PROTOCOL_ADDRESS_REQUIRES_MONETARY_AUTHORITY
        )
    return GenericTokenAdmissionDecision(GenericTokenAdmissionCode.ADMITTED)


def evaluate_generic_token_admission_transition(
    state: CanonicalZUSDSupplyState,
    command: GenericTokenAdmissionCommand,
) -> GenericTokenAdmissionTransition:
    """Evaluate the policy without mutating or replacing its immutable prestate."""

    if not isinstance(state, CanonicalZUSDSupplyState):
        raise TypeError("state must be a CanonicalZUSDSupplyState")
    decision = evaluate_generic_token_admission(command)
    return GenericTokenAdmissionTransition(
        pre_state=state,
        post_state=state,
        decision=decision,
    )

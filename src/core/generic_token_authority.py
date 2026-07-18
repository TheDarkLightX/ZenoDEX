"""Pure registered-authority and supply transition for generic tokens."""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum

from ..state.balances import NATIVE_ASSET
from ..state.canonical import canonical_hex_fixed_allow_0x

U32_MAX = 0xFFFFFFFF


def canonical_generic_asset_id(asset_id: str) -> str:
    """Return one canonical non-native token identifier."""

    if not isinstance(asset_id, str):
        raise TypeError("asset_id must be a string")
    canonical_asset = canonical_hex_fixed_allow_0x(
        asset_id,
        nbytes=32,
        name="asset_id",
    )
    if canonical_asset == NATIVE_ASSET:
        raise ValueError("generic token authority cannot register the native asset")
    return canonical_asset


def canonical_token_actor_pubkey(pubkey: str) -> str:
    """Return one canonical 48-byte transaction actor public key."""

    if not isinstance(pubkey, str):
        raise TypeError("actor_pubkey must be a string")
    return canonical_hex_fixed_allow_0x(
        pubkey,
        nbytes=48,
        name="actor_pubkey",
    )


@dataclass(frozen=True, slots=True)
class GenericTokenAssetAuthority:
    """Committed registration, supply, and mint authority for one asset."""

    asset_id: str
    total_supply_units: int
    mint_authority_pubkey: str | None

    def __post_init__(self) -> None:
        canonical_asset = canonical_generic_asset_id(self.asset_id)
        if type(self.total_supply_units) is not int:
            raise TypeError("total_supply_units must be an int")
        if not 0 <= self.total_supply_units <= U32_MAX:
            raise ValueError("total_supply_units must fit in u32")
        authority = (
            None
            if self.mint_authority_pubkey is None
            else canonical_token_actor_pubkey(self.mint_authority_pubkey)
        )
        object.__setattr__(self, "asset_id", canonical_asset)
        object.__setattr__(self, "mint_authority_pubkey", authority)


@dataclass(frozen=True, slots=True)
class GenericTokenAuthorityState:
    """Immutable canonical registry of generic-token supply authorities."""

    assets: tuple[GenericTokenAssetAuthority, ...] = ()

    def __post_init__(self) -> None:
        if type(self.assets) is not tuple:
            raise TypeError("assets must be a tuple")
        previous_asset: str | None = None
        for asset in self.assets:
            if type(asset) is not GenericTokenAssetAuthority:
                raise TypeError(
                    "assets must contain GenericTokenAssetAuthority values"
                )
            if previous_asset is not None and asset.asset_id <= previous_asset:
                raise ValueError("assets must be unique and strictly sorted")
            previous_asset = asset.asset_id

    def get_asset(self, asset_id: str) -> GenericTokenAssetAuthority | None:
        canonical_asset = canonical_generic_asset_id(asset_id)
        for registered in self.assets:
            if registered.asset_id == canonical_asset:
                return registered
            if registered.asset_id > canonical_asset:
                break
        return None


class GenericTokenSupplyAction(str, Enum):
    TRANSFER = "transfer"
    MINT = "mint"
    BURN = "burn"


@dataclass(frozen=True, slots=True)
class GenericTokenSupplyCommand:
    """One authenticated supply-changing command."""

    action: GenericTokenSupplyAction
    asset_id: str
    actor_pubkey: str
    amount_units: int
    recipient_pubkey: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.action, GenericTokenSupplyAction):
            raise TypeError("action must be a GenericTokenSupplyAction")
        object.__setattr__(
            self,
            "asset_id",
            canonical_generic_asset_id(self.asset_id),
        )
        object.__setattr__(
            self,
            "actor_pubkey",
            canonical_token_actor_pubkey(self.actor_pubkey),
        )
        recipient = (
            None
            if self.recipient_pubkey is None
            else canonical_token_actor_pubkey(self.recipient_pubkey)
        )
        object.__setattr__(self, "recipient_pubkey", recipient)


class GenericTokenSupplyRejectCode(str, Enum):
    INVALID_AMOUNT = "invalid_amount"
    UNREGISTERED_ASSET = "unregistered_asset"
    RECIPIENT_REQUIRED = "recipient_required"
    SELF_TRANSFER = "self_transfer"
    MINT_DISABLED = "mint_disabled"
    UNAUTHORIZED_MINT = "unauthorized_mint"
    SUPPLY_OVERFLOW = "supply_overflow"
    SUPPLY_UNDERFLOW = "supply_underflow"


@dataclass(frozen=True, slots=True)
class GenericTokenSupplyDecision:
    accepted: bool
    next_state: GenericTokenAuthorityState | None = None
    reject_code: GenericTokenSupplyRejectCode | None = None

    def __post_init__(self) -> None:
        if type(self.accepted) is not bool:
            raise TypeError("accepted must be a bool")
        if self.accepted:
            if not isinstance(self.next_state, GenericTokenAuthorityState):
                raise ValueError("accepted decision requires next_state")
            if self.reject_code is not None:
                raise ValueError("accepted decision cannot carry reject_code")
            return
        if self.next_state is not None or not isinstance(
            self.reject_code,
            GenericTokenSupplyRejectCode,
        ):
            raise ValueError("rejected decision requires exactly one reject_code")


def _reject(code: GenericTokenSupplyRejectCode) -> GenericTokenSupplyDecision:
    return GenericTokenSupplyDecision(accepted=False, reject_code=code)


def apply_generic_token_supply_command(
    state: GenericTokenAuthorityState,
    command: GenericTokenSupplyCommand,
) -> GenericTokenSupplyDecision:
    """Apply one supply command with no mutation or hidden authority.

    Amounts and committed supplies are whole token units. Expected protocol
    rejection carries no candidate state. Registration and mint authority are
    preserved across both mint and burn, including a burn to zero supply.
    """

    if not isinstance(state, GenericTokenAuthorityState):
        raise TypeError("state must be a GenericTokenAuthorityState")
    if not isinstance(command, GenericTokenSupplyCommand):
        raise TypeError("command must be a GenericTokenSupplyCommand")
    if (
        type(command.amount_units) is not int
        or command.amount_units <= 0
        or command.amount_units > U32_MAX
    ):
        return _reject(GenericTokenSupplyRejectCode.INVALID_AMOUNT)

    registered = state.get_asset(command.asset_id)
    if registered is None:
        return _reject(GenericTokenSupplyRejectCode.UNREGISTERED_ASSET)

    supply_before = registered.total_supply_units
    if command.action is GenericTokenSupplyAction.TRANSFER:
        if command.recipient_pubkey is None:
            return _reject(GenericTokenSupplyRejectCode.RECIPIENT_REQUIRED)
        if command.actor_pubkey == command.recipient_pubkey:
            return _reject(GenericTokenSupplyRejectCode.SELF_TRANSFER)
        return GenericTokenSupplyDecision(accepted=True, next_state=state)

    if command.action is GenericTokenSupplyAction.MINT:
        if registered.mint_authority_pubkey is None:
            return _reject(GenericTokenSupplyRejectCode.MINT_DISABLED)
        if command.actor_pubkey != registered.mint_authority_pubkey:
            return _reject(GenericTokenSupplyRejectCode.UNAUTHORIZED_MINT)
        if supply_before > U32_MAX - command.amount_units:
            return _reject(GenericTokenSupplyRejectCode.SUPPLY_OVERFLOW)
        supply_after = supply_before + command.amount_units
    else:
        if command.amount_units > supply_before:
            return _reject(GenericTokenSupplyRejectCode.SUPPLY_UNDERFLOW)
        supply_after = supply_before - command.amount_units

    updated = replace(registered, total_supply_units=supply_after)
    next_assets = tuple(
        updated if item.asset_id == registered.asset_id else item
        for item in state.assets
    )
    return GenericTokenSupplyDecision(
        accepted=True,
        next_state=GenericTokenAuthorityState(assets=next_assets),
    )

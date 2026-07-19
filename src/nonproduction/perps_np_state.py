"""Research-only persistent state for the N-party perps clearinghouse.

The model remains available for proofs and differential research without
becoming a production state variant.  Production ``PerpsState`` deliberately
does not import, export, or admit any of these types, and production artifacts
remove the entire :mod:`src.nonproduction` package.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Literal, TypeVar

from src.state.canonical import canonical_hex_fixed_allow_0x
from src.state.immutable import FrozenDict, SealedValue, seal_dataclass_init

from . import perps_np_validation as _validation
from .perps_np_validation import (
    NpMarketValidationRequest,
    validate_np_account_record,
    validate_np_market_state,
    validate_np_pending_intent_record,
)

_OwnedValue = TypeVar("_OwnedValue")

PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1: Literal["clearinghouse_np_v1"] = (
    "clearinghouse_np_v1"
)
PERP_CLEARINGHOUSE_NP_ACCOUNT_KEYS = _validation.PERP_CLEARINGHOUSE_NP_ACCOUNT_KEYS
PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS = _validation.PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS
PERP_CLEARINGHOUSE_NP_PENDING_INTENT_KEYS = (
    _validation.PERP_CLEARINGHOUSE_NP_PENDING_INTENT_KEYS
)


def _pubkey_bytes48(pubkey: str, *, name: str) -> bytes:
    canon = canonical_hex_fixed_allow_0x(pubkey, nbytes=48, name=name)
    return bytes.fromhex(canon[2:])


def _pubkey_bytes48_or_none(pubkey: str) -> bytes | None:
    try:
        return _pubkey_bytes48(pubkey, name="pubkey")
    except (TypeError, ValueError):
        return None


def _owned_str_key_mapping(
    value: Mapping[str, _OwnedValue],
    *,
    name: str,
) -> dict[str, _OwnedValue]:
    owned: dict[str, _OwnedValue] = {}
    for key, inner in value.items():
        if type(key) is not str:
            raise TypeError(f"{name} keys must be exact strings")
        if key in owned:
            raise ValueError(f"{name} contains duplicate key {key!r}")
        owned[key] = inner
    return owned


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class PerpClearinghouseNpAccount(SealedValue):
    """One participant in a research-only N-party clearinghouse market."""

    pubkey: str
    position_base: int = 0
    entry_price_e8: int = 0
    collateral_e8: int = 0
    funding_paid_cum_e8: int = 0
    nonce: int = 0

    def __post_init__(self) -> None:
        validate_np_account_record(account=self, pubkey_bytes48=_pubkey_bytes48)


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class PerpClearinghouseNpPendingIntent(SealedValue):
    """A single-signed position intent queued for a research batch match."""

    pubkey: str
    target_base: int
    nonce: int
    limit_price_e8: int = 0
    min_fill_base: int = 0
    expiry_epoch: int = 1 << 62

    def __post_init__(self) -> None:
        validate_np_pending_intent_record(intent=self, pubkey_bytes48=_pubkey_bytes48)


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class PerpClearinghouseNpMarketState(SealedValue):
    """Open N-party net-zero clearinghouse state for nonproduction research."""

    quote_asset: str
    global_state: Mapping[str, int]
    accounts: tuple[PerpClearinghouseNpAccount, ...] = ()
    pending_intents: tuple[PerpClearinghouseNpPendingIntent, ...] = ()
    kind: Literal["clearinghouse_np_v1"] = PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1

    def __post_init__(self) -> None:
        if not isinstance(self.global_state, Mapping):
            raise TypeError("global_state must be a mapping")
        if type(self.accounts) is not tuple:
            raise TypeError("accounts must be a tuple")
        if type(self.pending_intents) is not tuple:
            raise TypeError("pending_intents must be a tuple")
        owned_global_state = _owned_str_key_mapping(
            self.global_state,
            name="global_state",
        )
        owned_accounts = tuple(self.accounts)
        owned_pending_intents = tuple(self.pending_intents)
        if any(type(account) is not PerpClearinghouseNpAccount for account in owned_accounts):
            raise TypeError("accounts must contain exact PerpClearinghouseNpAccount instances")
        if any(
            type(intent) is not PerpClearinghouseNpPendingIntent
            for intent in owned_pending_intents
        ):
            raise TypeError(
                "pending_intents must contain exact "
                "PerpClearinghouseNpPendingIntent instances"
            )
        validate_np_market_state(
            NpMarketValidationRequest(
                kind=self.kind,
                expected_kind=PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
                quote_asset=self.quote_asset,
                global_state=owned_global_state,
                accounts=owned_accounts,
                pending_intents=owned_pending_intents,
                account_type=PerpClearinghouseNpAccount,
                pending_intent_type=PerpClearinghouseNpPendingIntent,
                pubkey_bytes48=_pubkey_bytes48,
            )
        )
        object.__setattr__(self, "global_state", FrozenDict(owned_global_state))
        object.__setattr__(self, "accounts", owned_accounts)
        object.__setattr__(self, "pending_intents", owned_pending_intents)

    def by_pubkey(self) -> dict[str, PerpClearinghouseNpAccount]:
        return {account.pubkey: account for account in self.accounts}

    def role_for_pubkey(self, pubkey: str) -> str | None:
        """Return the participant's own pubkey when it is a market member."""

        candidate = _pubkey_bytes48_or_none(pubkey)
        if candidate is None:
            return None
        for account in self.accounts:
            if candidate == _pubkey_bytes48_or_none(account.pubkey):
                return account.pubkey
        return None

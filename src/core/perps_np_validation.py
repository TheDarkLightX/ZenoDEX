"""N-party clearinghouse market snapshot validation."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any, Protocol

from .perp_liquidation_envelope import require_perp_liquidation_envelope_bps


class PubkeyBytes48(Protocol):
    def __call__(self, pubkey: str, *, name: str) -> bytes: ...


@dataclass(frozen=True)
class NpMarketValidationRequest:
    kind: str
    expected_kind: str
    quote_asset: str
    global_state: dict[str, int]
    accounts: tuple[Any, ...]
    pending_intents: tuple[Any, ...]
    account_type: type[Any]
    pending_intent_type: type[Any]
    pubkey_bytes48: PubkeyBytes48


PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS: set[str] = {
    "now_epoch",
    "index_price_e8",
    "clearing_price_seen",
    "clearing_price_epoch",
    "clearing_price_e8",
    "fee_pool_e8",
    "insurance_e8",
    "insurance_ext_e8",
    "claims_paid_e8",
    "net_deposited_e8",
    "initial_margin_bps",
    "maintenance_margin_bps",
    "depeg_buffer_bps",
    "liquidation_penalty_bps",
    "max_oracle_move_bps",
    "funding_cap_bps",
    "max_position_abs",
    "min_notional_for_bounty_e8",
}

PERP_CLEARINGHOUSE_NP_ACCOUNT_KEYS: set[str] = {
    "pubkey",
    "position_base",
    "entry_price_e8",
    "collateral_e8",
    "funding_paid_cum_e8",
    "nonce",
}

PERP_CLEARINGHOUSE_NP_PENDING_INTENT_KEYS: set[str] = {
    "pubkey",
    "target_base",
    "limit_price_e8",
    "min_fill_base",
    "expiry_epoch",
    "nonce",
}

_PERP_CLEARINGHOUSE_NP_GLOBAL_DEFAULTS: dict[str, int] = {
    "clearing_price_seen": 0,
    "clearing_price_epoch": 0,
    "clearing_price_e8": 0,
}

_PERP_CLEARINGHOUSE_NP_NONNEGATIVE_GLOBAL_KEYS: set[str] = {
    "now_epoch",
    "clearing_price_epoch",
    "clearing_price_e8",
    "fee_pool_e8",
    "insurance_e8",
    "insurance_ext_e8",
    "claims_paid_e8",
    "initial_margin_bps",
    "maintenance_margin_bps",
    "depeg_buffer_bps",
    "liquidation_penalty_bps",
    "max_oracle_move_bps",
    "funding_cap_bps",
    "max_position_abs",
    "min_notional_for_bounty_e8",
}

_PERP_CLEARINGHOUSE_NP_PARAM_BOUNDS: dict[str, tuple[int, int]] = {
    "initial_margin_bps": (0, 10_000),
    "maintenance_margin_bps": (0, 10_000),
    "depeg_buffer_bps": (0, 5_000),
    "liquidation_penalty_bps": (0, 10_000),
    "max_oracle_move_bps": (0, 10_000),
    "funding_cap_bps": (1, 10_000),
    "max_position_abs": (1, 1_000_000),
    "min_notional_for_bounty_e8": (0, 1_000_000_000_000 * 100_000_000),
}


def validate_np_account_record(*, account: Any, pubkey_bytes48: PubkeyBytes48) -> None:
    """Validate one N-party clearinghouse account record."""
    if not isinstance(account.pubkey, str) or not account.pubkey:
        raise TypeError("account pubkey must be a non-empty string")
    pubkey_bytes48(account.pubkey, name="account pubkey")
    for field_name in (
        "position_base",
        "entry_price_e8",
        "collateral_e8",
        "funding_paid_cum_e8",
        "nonce",
    ):
        value = getattr(account, field_name)
        if not isinstance(value, int) or isinstance(value, bool):
            raise TypeError(f"account {field_name} must be an int")
    if account.entry_price_e8 < 0:
        raise ValueError("account entry_price_e8 must be non-negative")
    if account.collateral_e8 < 0:
        raise ValueError("account collateral_e8 must be non-negative")
    if account.nonce < 0:
        raise ValueError("account nonce must be non-negative")


def validate_np_pending_intent_record(*, intent: Any, pubkey_bytes48: PubkeyBytes48) -> None:
    """Validate one N-party clearinghouse pending-intent record."""
    if not isinstance(intent.pubkey, str) or not intent.pubkey:
        raise TypeError("pending intent pubkey must be a non-empty string")
    pubkey_bytes48(intent.pubkey, name="pending intent pubkey")
    for field_name in ("target_base", "nonce", "limit_price_e8", "min_fill_base", "expiry_epoch"):
        value = getattr(intent, field_name)
        if not isinstance(value, int) or isinstance(value, bool):
            raise TypeError(f"pending intent {field_name} must be an int")
    if intent.nonce <= 0:
        raise ValueError("pending intent nonce must be positive")
    if intent.limit_price_e8 < 0:
        raise ValueError("pending intent limit_price_e8 must be non-negative")
    if intent.min_fill_base < 0:
        raise ValueError("pending intent min_fill_base must be non-negative")
    if intent.expiry_epoch < 0:
        raise ValueError("pending intent expiry_epoch must be non-negative")


def _validate_market_identity(*, kind: str, expected_kind: str, quote_asset: str) -> None:
    if kind != expected_kind:
        raise ValueError(f"unsupported perps market kind: {kind}")
    if not isinstance(quote_asset, str) or not quote_asset:
        raise TypeError("quote_asset must be a non-empty string")


def _fill_global_defaults(global_state: dict[str, int]) -> None:
    for key, value in _PERP_CLEARINGHOUSE_NP_GLOBAL_DEFAULTS.items():
        global_state.setdefault(key, value)


def _validate_global_keyset(global_state: Mapping[str, int]) -> None:
    keys = set(global_state.keys())
    extra = keys - PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS
    missing = PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS - keys
    if extra:
        raise ValueError(f"global_state has unknown keys: {sorted(extra)[:8]}")
    if missing:
        raise ValueError(f"global_state missing required keys: {sorted(missing)[:8]}")


def _validate_global_types(global_state: Mapping[str, int]) -> None:
    for key, value in global_state.items():
        if not isinstance(value, int) or isinstance(value, bool):
            raise TypeError(f"global_state[{key!r}] must be an int")


def _validate_global_nonnegative(global_state: Mapping[str, int]) -> None:
    for key in _PERP_CLEARINGHOUSE_NP_NONNEGATIVE_GLOBAL_KEYS:
        if int(global_state[key]) < 0:
            raise ValueError(f"global_state[{key!r}] must be non-negative")


def _validate_global_bounds(global_state: Mapping[str, int]) -> None:
    for key, (lo, hi) in _PERP_CLEARINGHOUSE_NP_PARAM_BOUNDS.items():
        value = int(global_state[key])
        if value < lo or value > hi:
            raise ValueError(f"global_state[{key!r}] out of range: {value} not in [{lo}, {hi}]")


def _validate_global_liquidation_envelope(global_state: Mapping[str, int]) -> None:
    require_perp_liquidation_envelope_bps(
        initial_margin_bps=global_state["initial_margin_bps"],
        maintenance_margin_bps=global_state["maintenance_margin_bps"],
        depeg_buffer_bps=global_state["depeg_buffer_bps"],
        max_oracle_move_bps=global_state["max_oracle_move_bps"],
        liquidation_penalty_bps=global_state["liquidation_penalty_bps"],
    )


def _validate_global_state(global_state: dict[str, int]) -> None:
    if not isinstance(global_state, dict):
        raise TypeError("global_state must be a dict")
    _fill_global_defaults(global_state)
    _validate_global_keyset(global_state)
    _validate_global_types(global_state)
    _validate_global_nonnegative(global_state)
    _validate_global_bounds(global_state)
    _validate_global_liquidation_envelope(global_state)


def _validate_account_collection(
    *,
    accounts: tuple[Any, ...],
    account_type: type[Any],
    pubkey_bytes48: PubkeyBytes48,
) -> list[bytes]:
    if not isinstance(accounts, tuple):
        raise TypeError("accounts must be a tuple")
    for account in accounts:
        if not isinstance(account, account_type):
            raise TypeError("accounts must be PerpClearinghouseNpAccount instances")
    pubkey_bytes = [pubkey_bytes48(account.pubkey, name="account pubkey") for account in accounts]
    if len(set(pubkey_bytes)) != len(pubkey_bytes):
        raise ValueError("clearinghouse_np accounts must be distinct")
    return pubkey_bytes


def _validate_pending_intents(
    *,
    pending_intents: tuple[Any, ...],
    pending_intent_type: type[Any],
    member_bytes: set[bytes],
    pubkey_bytes48: PubkeyBytes48,
) -> None:
    if not isinstance(pending_intents, tuple):
        raise TypeError("pending_intents must be a tuple")
    intent_bytes: list[bytes] = []
    for intent in pending_intents:
        if not isinstance(intent, pending_intent_type):
            raise TypeError("pending_intents must be PerpClearinghouseNpPendingIntent instances")
        intent_pubkey = pubkey_bytes48(intent.pubkey, name="pending intent pubkey")
        if intent_pubkey not in member_bytes:
            raise ValueError("pending intent pubkey is not a market member")
        intent_bytes.append(intent_pubkey)
    if len(set(intent_bytes)) != len(intent_bytes):
        raise ValueError("clearinghouse_np pending intents must be one-per-account")


def _validate_index_price(global_state: Mapping[str, int]) -> None:
    if int(global_state["index_price_e8"]) <= 0:
        raise ValueError("index_price_e8 must be positive")


def _validate_unseen_clearing_price(*, clearing_price_epoch: int, clearing_price_e8: int) -> None:
    if clearing_price_epoch != 0 or clearing_price_e8 != 0:
        raise ValueError("clearinghouse_np clearing_price fields must be 0 when not seen")


def _validate_seen_clearing_price(
    *,
    clearing_price_epoch: int,
    clearing_price_e8: int,
    now_epoch: int,
) -> None:
    if clearing_price_e8 <= 0:
        raise ValueError("clearinghouse_np clearing_price_e8 must be positive when seen")
    if clearing_price_epoch != now_epoch:
        raise ValueError("clearinghouse_np clearing_price_epoch must equal now_epoch when seen")


def _validate_clearing_price(global_state: Mapping[str, int]) -> None:
    clearing_price_seen = int(global_state["clearing_price_seen"])
    clearing_price_epoch = int(global_state["clearing_price_epoch"])
    clearing_price_e8 = int(global_state["clearing_price_e8"])
    now_epoch = int(global_state["now_epoch"])
    if clearing_price_seen not in (0, 1):
        raise ValueError("clearinghouse_np clearing_price_seen must be 0 or 1")
    if clearing_price_seen == 0:
        _validate_unseen_clearing_price(
            clearing_price_epoch=clearing_price_epoch,
            clearing_price_e8=clearing_price_e8,
        )
        return
    _validate_seen_clearing_price(
        clearing_price_epoch=clearing_price_epoch,
        clearing_price_e8=clearing_price_e8,
        now_epoch=now_epoch,
    )


def _validate_net_zero(accounts: tuple[Any, ...]) -> None:
    if sum(account.position_base for account in accounts) != 0:
        raise ValueError("clearinghouse_np state must satisfy sum(position_base) == 0")


def _validate_quote_conservation(*, global_state: Mapping[str, int], accounts: tuple[Any, ...]) -> None:
    total_collateral = sum(account.collateral_e8 for account in accounts)
    lhs = int(global_state["net_deposited_e8"]) + int(global_state["insurance_ext_e8"])
    rhs = total_collateral + int(global_state["fee_pool_e8"]) + int(global_state["insurance_e8"])
    if lhs != rhs:
        raise ValueError(
            "clearinghouse_np state must satisfy net_deposited_e8 + insurance_ext_e8 "
            "== sum(collateral_e8) + fee_pool_e8 + insurance_e8"
        )


def _validate_insurance_accounting(global_state: Mapping[str, int]) -> None:
    if int(global_state["insurance_e8"]) != int(global_state["insurance_ext_e8"]) - int(global_state["claims_paid_e8"]):
        raise ValueError("clearinghouse_np state must satisfy insurance_e8 == insurance_ext_e8 - claims_paid_e8")
    if int(global_state["insurance_e8"]) < 0:
        raise ValueError("clearinghouse_np insurance_e8 must be non-negative")
    if int(global_state["fee_pool_e8"]) < 0:
        raise ValueError("clearinghouse_np fee_pool_e8 must be non-negative")


def validate_np_market_state(request: NpMarketValidationRequest) -> None:
    """Validate fail-closed N-party clearinghouse snapshot invariants."""
    _validate_market_identity(
        kind=request.kind,
        expected_kind=request.expected_kind,
        quote_asset=request.quote_asset,
    )
    _validate_global_state(request.global_state)
    account_bytes = _validate_account_collection(
        accounts=request.accounts,
        account_type=request.account_type,
        pubkey_bytes48=request.pubkey_bytes48,
    )
    _validate_pending_intents(
        pending_intents=request.pending_intents,
        pending_intent_type=request.pending_intent_type,
        member_bytes=set(account_bytes),
        pubkey_bytes48=request.pubkey_bytes48,
    )
    _validate_index_price(request.global_state)
    _validate_clearing_price(request.global_state)
    _validate_net_zero(request.accounts)
    _validate_quote_conservation(global_state=request.global_state, accounts=request.accounts)
    _validate_insurance_accounting(request.global_state)

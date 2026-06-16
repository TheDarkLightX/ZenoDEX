"""Fixed-participant clearinghouse market snapshot validation."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Protocol

Value = bool | int | str


PERP_CLEARINGHOUSE_2P_STATE_KEYS: set[str] = {
    "now_epoch",
    "breaker_active",
    "breaker_last_trigger_epoch",
    "clearing_price_seen",
    "clearing_price_epoch",
    "clearing_price_e8",
    "oracle_seen",
    "oracle_last_update_epoch",
    "index_price_e8",
    "max_oracle_staleness_epochs",
    "max_oracle_move_bps",
    "initial_margin_bps",
    "maintenance_margin_bps",
    "liquidation_penalty_bps",
    "max_position_abs",
    "fee_pool_e8",
    "liquidated_this_step",
    "net_deposited_e8",
    "position_base_a",
    "entry_price_e8_a",
    "collateral_e8_a",
    "position_base_b",
    "entry_price_e8_b",
    "collateral_e8_b",
}

PERP_CLEARINGHOUSE_2P_BOOL_KEYS: set[str] = {
    "breaker_active",
    "clearing_price_seen",
    "oracle_seen",
    "liquidated_this_step",
}

PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS: set[str] = {
    "now_epoch",
    "breaker_active",
    "breaker_last_trigger_epoch",
    "clearing_price_seen",
    "clearing_price_epoch",
    "clearing_price_e8",
    "oracle_seen",
    "oracle_last_update_epoch",
    "index_price_e8",
    "max_oracle_staleness_epochs",
    "max_oracle_move_bps",
    "initial_margin_bps",
    "maintenance_margin_bps",
    "liquidation_penalty_bps",
    "max_position_abs",
    "fee_pool_e8",
    "liquidated_this_step",
    "net_deposited_e8",
    "position_base_a",
    "entry_price_e8_a",
    "collateral_e8_a",
    "position_base_b",
    "entry_price_e8_b",
    "collateral_e8_b",
    "position_base_c",
    "entry_price_e8_c",
    "collateral_e8_c",
}

PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS: set[str] = {
    "breaker_active",
    "clearing_price_seen",
    "oracle_seen",
    "liquidated_this_step",
}


class PubkeyBytes48(Protocol):
    def __call__(self, pubkey: str, *, name: str) -> bytes: ...


@dataclass(frozen=True)
class FixedClearinghouseValidationRequest:
    kind: str
    expected_kind: str
    quote_asset: str
    account_pubkeys: tuple[tuple[str, str], ...]
    state: dict[str, Value]
    state_keys: set[str]
    bool_keys: set[str]
    pubkey_bytes48: PubkeyBytes48


def _validate_market_identity(request: FixedClearinghouseValidationRequest) -> None:
    if request.kind != request.expected_kind:
        raise ValueError(f"unsupported perps market kind: {request.kind}")
    if not isinstance(request.quote_asset, str) or not request.quote_asset:
        raise TypeError("quote_asset must be a non-empty string")


def _validate_account_pubkeys(request: FixedClearinghouseValidationRequest) -> None:
    pubkey_bytes: list[bytes] = []
    for name, pubkey in request.account_pubkeys:
        if not isinstance(pubkey, str) or not pubkey:
            raise TypeError(f"{name} must be a non-empty string")
        pubkey_bytes.append(request.pubkey_bytes48(pubkey, name=name))
    if len(set(pubkey_bytes)) != len(pubkey_bytes):
        raise ValueError("clearinghouse accounts must be distinct")


def _validate_state_keyset(*, state: Mapping[str, Value], state_keys: set[str]) -> None:
    keys = set(state.keys())
    extra = keys - state_keys
    missing = state_keys - keys
    if extra:
        raise ValueError(f"state has unknown keys: {sorted(extra)[:8]}")
    if missing:
        raise ValueError(f"state missing required keys: {sorted(missing)[:8]}")


def _validate_state_values(*, state: Mapping[str, Value], bool_keys: set[str]) -> None:
    for key, value in state.items():
        if key in bool_keys:
            if not isinstance(value, bool):
                raise TypeError(f"state[{key!r}] must be a bool")
            continue
        if isinstance(value, int) and not isinstance(value, bool):
            continue
        raise TypeError(f"state[{key!r}] must be an int")


def validate_fixed_clearinghouse_shape(request: FixedClearinghouseValidationRequest) -> None:
    """Validate shared fixed-participant clearinghouse constructor shape."""
    _validate_market_identity(request)
    _validate_account_pubkeys(request)
    if not isinstance(request.state, dict):
        raise TypeError("state must be a dict")
    _validate_state_keyset(state=request.state, state_keys=request.state_keys)
    _validate_state_values(state=request.state, bool_keys=request.bool_keys)


def validate_two_party_clearinghouse_invariants(state: Mapping[str, Value]) -> None:
    """Validate 2-party net-zero exposure and quote-e8 conservation."""
    pos_a = int(state["position_base_a"])
    pos_b = int(state["position_base_b"])
    if pos_a + pos_b != 0:
        raise ValueError("clearinghouse state must satisfy position_base_a + position_base_b == 0")

    coll_a = int(state["collateral_e8_a"])
    coll_b = int(state["collateral_e8_b"])
    fee_pool = int(state["fee_pool_e8"])
    net_deposited = int(state["net_deposited_e8"])
    if net_deposited != coll_a + coll_b + fee_pool:
        raise ValueError(
            "clearinghouse state must satisfy "
            "net_deposited_e8 == collateral_e8_a + collateral_e8_b + fee_pool_e8"
        )


def validate_three_party_transfer_clearinghouse_invariants(state: Mapping[str, Value]) -> None:
    """Validate 3-party transfer netting, flat-slot, and quote-e8 conservation."""
    pos_a = int(state["position_base_a"])
    pos_b = int(state["position_base_b"])
    pos_c = int(state["position_base_c"])
    if pos_a + pos_b + pos_c != 0:
        raise ValueError("clearinghouse state must satisfy position_base_a + position_base_b + position_base_c == 0")
    if not (pos_a == 0 or pos_b == 0 or pos_c == 0):
        raise ValueError("clearinghouse state must satisfy at least one flat position")

    coll_a = int(state["collateral_e8_a"])
    coll_b = int(state["collateral_e8_b"])
    coll_c = int(state["collateral_e8_c"])
    fee_pool = int(state["fee_pool_e8"])
    net_deposited = int(state["net_deposited_e8"])
    if net_deposited != coll_a + coll_b + coll_c + fee_pool:
        raise ValueError(
            "clearinghouse state must satisfy "
            "net_deposited_e8 == collateral_e8_a + collateral_e8_b + collateral_e8_c + fee_pool_e8"
        )

"""Pure committed-policy binding for the zUSD monetary state machine.

The runtime configuration is an input proposal.  Once a monetary state exists,
its full policy binding is authoritative until an explicit governed migration
creates a new state under a new binding.
"""

from __future__ import annotations

import unicodedata
from dataclasses import dataclass
from enum import IntEnum

ZUSD_MONETARY_POLICY_SCHEMA = "zenodex/zusd-monetary-policy/v2"
_BPS_SCALE = 10_000
_CHAIN_ID_MAX_UTF8_BYTES = 128
_MAX_AMOUNT_E8 = 10**30
_NATIVE_ASSET_ID = "0x" + "00" * 32

ZUSD_MONETARY_POLICY_FIELDS = (
    "chain_id",
    "canonical_zusd_asset",
    "clock_policy_hash",
    "oracle_pubkey",
    "protocol_fee_recipient_pubkey",
    "liquidation_gas_comp_fixed_collateral_e8",
    "liquidation_gas_comp_bps",
    "borrow_fee_floor_bps",
    "borrow_fee_max_bps",
    "host_protocol_fee_share_bps",
    "fee_stake_asset_id",
    "staking_activation_delay_epochs",
)


def _require_int(
    value: object,
    *,
    name: str,
    minimum: int = 0,
    maximum: int | None = None,
) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < minimum or (maximum is not None and value > maximum):
        upper = "" if maximum is None else f", {maximum}"
        raise ValueError(f"{name} must be in [{minimum}{upper}]")
    return value


def _require_canonical_hex(value: object, *, name: str, nbytes: int) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a str")
    expected_length = 2 + 2 * nbytes
    if len(value) != expected_length or not value.startswith("0x") or value != value.lower():
        raise ValueError(f"{name} must be canonical 0x-prefixed lowercase hex")
    try:
        bytes.fromhex(value[2:])
    except ValueError as exc:
        raise ValueError(f"{name} must be canonical 0x-prefixed lowercase hex") from exc
    return value


@dataclass(frozen=True, slots=True)
class ZUSDMonetaryPolicyBinding:
    """All runtime policy facts that may change zUSD authority or economics."""

    chain_id: str
    canonical_zusd_asset: str
    clock_policy_hash: str
    oracle_pubkey: str | None
    protocol_fee_recipient_pubkey: str | None
    liquidation_gas_comp_fixed_collateral_e8: int
    liquidation_gas_comp_bps: int
    borrow_fee_floor_bps: int
    borrow_fee_max_bps: int
    host_protocol_fee_share_bps: int
    fee_stake_asset_id: str | None
    staking_activation_delay_epochs: int

    def __post_init__(self) -> None:
        if type(self.chain_id) is not str or not self.chain_id:
            raise TypeError("chain_id must be a non-empty str")
        if self.chain_id != self.chain_id.strip():
            raise ValueError("chain_id must not have surrounding whitespace")
        if unicodedata.normalize("NFC", self.chain_id) != self.chain_id:
            raise ValueError("chain_id must be NFC-normalized")
        if len(self.chain_id.encode("utf-8")) > _CHAIN_ID_MAX_UTF8_BYTES:
            raise ValueError(f"chain_id must be at most {_CHAIN_ID_MAX_UTF8_BYTES} UTF-8 bytes")
        if any(unicodedata.category(char).startswith("C") for char in self.chain_id):
            raise ValueError("chain_id must not contain control or format characters")
        _require_canonical_hex(
            self.canonical_zusd_asset,
            name="canonical_zusd_asset",
            nbytes=32,
        )
        if self.canonical_zusd_asset == _NATIVE_ASSET_ID:
            raise ValueError("canonical_zusd_asset must be non-native")
        _require_canonical_hex(
            self.clock_policy_hash,
            name="clock_policy_hash",
            nbytes=32,
        )
        if self.clock_policy_hash == _NATIVE_ASSET_ID:
            raise ValueError("clock_policy_hash must be non-zero")
        if self.oracle_pubkey is not None:
            _require_canonical_hex(self.oracle_pubkey, name="oracle_pubkey", nbytes=48)
        if self.protocol_fee_recipient_pubkey is not None:
            _require_canonical_hex(
                self.protocol_fee_recipient_pubkey,
                name="protocol_fee_recipient_pubkey",
                nbytes=48,
            )
        if self.fee_stake_asset_id is not None:
            _require_canonical_hex(
                self.fee_stake_asset_id,
                name="fee_stake_asset_id",
                nbytes=32,
            )
            if self.fee_stake_asset_id == _NATIVE_ASSET_ID:
                raise ValueError("fee_stake_asset_id must be non-native")
            if self.fee_stake_asset_id == self.canonical_zusd_asset:
                raise ValueError("fee_stake_asset_id must differ from canonical_zusd_asset")
        _require_int(
            self.liquidation_gas_comp_fixed_collateral_e8,
            name="liquidation_gas_comp_fixed_collateral_e8",
            maximum=_MAX_AMOUNT_E8,
        )
        _require_int(
            self.liquidation_gas_comp_bps,
            name="liquidation_gas_comp_bps",
            maximum=_BPS_SCALE,
        )
        _require_int(
            self.borrow_fee_floor_bps,
            name="borrow_fee_floor_bps",
            maximum=_BPS_SCALE,
        )
        _require_int(
            self.borrow_fee_max_bps,
            name="borrow_fee_max_bps",
            maximum=_BPS_SCALE,
        )
        if self.borrow_fee_floor_bps > self.borrow_fee_max_bps:
            raise ValueError("borrow fee bounds are inverted")
        _require_int(
            self.host_protocol_fee_share_bps,
            name="host_protocol_fee_share_bps",
            maximum=_BPS_SCALE,
        )
        _require_int(
            self.staking_activation_delay_epochs,
            name="staking_activation_delay_epochs",
            minimum=1,
            maximum=_MAX_AMOUNT_E8,
        )


class ZUSDPolicyBindingCode(IntEnum):
    MATCHED = 0
    MISMATCH = 1


@dataclass(frozen=True, slots=True)
class ZUSDPolicyBindingDecision:
    code: ZUSDPolicyBindingCode
    mismatch_fields: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not ZUSDPolicyBindingCode:
            raise TypeError("code must be a ZUSDPolicyBindingCode")
        if type(self.mismatch_fields) is not tuple:
            raise TypeError("mismatch_fields must be a tuple")
        canonical_mismatches = tuple(
            field_name
            for field_name in ZUSD_MONETARY_POLICY_FIELDS
            if field_name in self.mismatch_fields
        )
        if (
            any(type(field_name) is not str for field_name in self.mismatch_fields)
            or len(set(self.mismatch_fields)) != len(self.mismatch_fields)
            or canonical_mismatches != self.mismatch_fields
        ):
            raise ValueError("mismatch_fields must be unique known fields in canonical order")
        if (self.code is ZUSDPolicyBindingCode.MATCHED) != (self.mismatch_fields == ()):
            raise ValueError("MATCHED requires no mismatches and MISMATCH requires some")

    @property
    def matched(self) -> bool:
        return self.code is ZUSDPolicyBindingCode.MATCHED


def evaluate_zusd_policy_binding(
    *,
    committed: ZUSDMonetaryPolicyBinding,
    configured: ZUSDMonetaryPolicyBinding,
) -> ZUSDPolicyBindingDecision:
    """Compare full typed bindings in a stable, audit-visible field order."""

    if not isinstance(committed, ZUSDMonetaryPolicyBinding):
        raise TypeError("committed must be a ZUSDMonetaryPolicyBinding")
    if not isinstance(configured, ZUSDMonetaryPolicyBinding):
        raise TypeError("configured must be a ZUSDMonetaryPolicyBinding")
    mismatches = tuple(
        field_name
        for field_name in ZUSD_MONETARY_POLICY_FIELDS
        if getattr(committed, field_name) != getattr(configured, field_name)
    )
    return ZUSDPolicyBindingDecision(
        code=(ZUSDPolicyBindingCode.MATCHED if not mismatches else ZUSDPolicyBindingCode.MISMATCH),
        mismatch_fields=mismatches,
    )

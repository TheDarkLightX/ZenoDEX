"""Closed canonical V2 wire values for the perps margin successor.

This module is an untrusted decode boundary.  It converts exact canonical JSON
into the existing immutable V1 economic values and the V2 claim-bound state;
it creates no accepted result, proof, receipt, or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Final, TypeVar

from .global_economic_proof_v2 import EconomicCommandOccurrenceV2
from .global_settlement_abi_v2_codec import (
    GlobalSettlementCodecErrorV2,
    _construct_v2,
    _expect_fields_v2,
    _expect_nonnegative_integer_v2,
    _expect_object_v2,
    _expect_text_v2,
    _load_canonical_object_v2,
)
from .global_settlement_resource_limits_v2 import (
    MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2,
)
from .global_settlement_types_v2 import GLOBAL_SETTLEMENT_ABI_V2, canonical_global_bytes_v2
from .perps_margin_global_v2 import PerpsMarginOracleV2
from .perps_margin_state_v2 import (
    MAX_PERPS_MARGIN_ACCOUNTS_V2,
    PERPS_MARGIN_MODULE_SCHEMA_V2,
    PerpsMarginClaimBindingV2,
    PerpsMarginStateV2,
)
from .perps_margin_types_v1 import (
    PerpsMarginAccountStatusV1,
    PerpsMarginAccountV1,
    PerpsMarginCommandV1,
    PerpsMarginMarketStatusV1,
    PerpsMarginStateV1,
)

PERPS_MARGIN_REQUEST_SCHEMA_V2: Final = "zenodex/perps-margin-request/v2"


class PerpsMarginWireCodecErrorV2(GlobalSettlementCodecErrorV2):
    """One malformed, noncanonical, or semantically invalid perps V2 value."""


_EnumT = TypeVar("_EnumT", bound=Enum)

_REQUEST_FIELDS_V2 = frozenset({"schema", "command", "occurrence", "oracle"})
_COMMAND_FIELDS_V1 = frozenset(
    {"command_kind", "account_id", "market_id", "owner", "asset", "amount_atoms", "nonce"}
)
_OCCURRENCE_FIELDS_V2 = frozenset(
    {
        "schema",
        "chain_id",
        "deployment_root",
        "height",
        "tx_index",
        "op_index",
        "command_kind",
        "command_body_hash",
        "route_release_id",
        "subject_id",
        "grant_root",
        "nonce",
        "profile_root",
        "pre_state_root",
        "consumed_object_ids",
    }
)
_ORACLE_FIELDS_V2 = frozenset({"authority_root", "occurrence_root", "price_e8"})
_STATE_FIELDS_V2 = frozenset(
    {
        "schema",
        "module_release_id",
        "market_id",
        "collateral_asset",
        "index_price_e8",
        "maintenance_margin_bps",
        "depeg_buffer_bps",
        "max_position_abs",
        "market_status",
        "accounts",
        "active_claims",
    }
)
_ACCOUNT_FIELDS_V1 = frozenset(
    {
        "account_id",
        "owner",
        "position_base",
        "entry_price_e8",
        "collateral_atoms",
        "nonce",
        "status",
    }
)
_CLAIM_FIELDS_V2 = frozenset({"account_id", "obligation_id"})


def _load_perps_object_v2(raw: bytes) -> dict[str, object]:
    """Normalize parser and host recursion failures to one wire error type."""

    try:
        return _load_canonical_object_v2(raw)
    except PerpsMarginWireCodecErrorV2:
        raise
    except GlobalSettlementCodecErrorV2 as exc:
        raise PerpsMarginWireCodecErrorV2(str(exc)) from exc
    except (RecursionError, TypeError, ValueError) as exc:
        raise PerpsMarginWireCodecErrorV2("encoded perps value is invalid JSON") from exc


def _construct_perps_v2(builder):
    try:
        return _construct_v2(builder)
    except GlobalSettlementCodecErrorV2 as exc:
        raise PerpsMarginWireCodecErrorV2(str(exc)) from exc


def _expect_integer_v2(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise PerpsMarginWireCodecErrorV2(f"{name} must be an integer")
    return value


def _expect_bounded_objects_v2(
    value: object,
    *,
    name: str,
    limit: int,
) -> tuple[dict[str, object], ...]:
    if type(value) is not list:
        raise PerpsMarginWireCodecErrorV2(f"{name} must be an array")
    if len(value) > limit:
        raise PerpsMarginWireCodecErrorV2(f"{name} exceeds its {limit}-item ceiling")
    return tuple(
        _expect_object_v2(item, name=f"{name}[{index}]")
        for index, item in enumerate(value)
    )


def _expect_bounded_texts_v2(
    value: object,
    *,
    name: str,
    limit: int,
) -> tuple[str, ...]:
    if type(value) is not list:
        raise PerpsMarginWireCodecErrorV2(f"{name} must be an array")
    if len(value) > limit:
        raise PerpsMarginWireCodecErrorV2(f"{name} exceeds its {limit}-item ceiling")
    return tuple(
        _expect_text_v2(item, name=f"{name}[{index}]")
        for index, item in enumerate(value)
    )


def _decode_enum_v2(
    value: object,
    enum_type: type[_EnumT],
    *,
    name: str,
) -> _EnumT:
    text = _expect_text_v2(value, name=name)
    try:
        return enum_type(text)
    except ValueError as exc:
        raise PerpsMarginWireCodecErrorV2(f"{name} is unknown") from exc


def _decode_command_object_v2(value: dict[str, object]) -> PerpsMarginCommandV1:
    _expect_fields_v2(value, _COMMAND_FIELDS_V1, name="perps margin command")
    return _construct_perps_v2(
        lambda: PerpsMarginCommandV1(
            command_kind=_expect_text_v2(value["command_kind"], name="command kind"),
            account_id=_expect_text_v2(value["account_id"], name="command account id"),
            market_id=_expect_text_v2(value["market_id"], name="command market id"),
            owner=_expect_text_v2(value["owner"], name="command owner"),
            asset=_expect_text_v2(value["asset"], name="command asset"),
            amount_atoms=_expect_nonnegative_integer_v2(
                value["amount_atoms"], name="command amount"
            ),
            nonce=_expect_nonnegative_integer_v2(value["nonce"], name="command nonce"),
        )
    )


def _decode_occurrence_object_v2(value: dict[str, object]) -> EconomicCommandOccurrenceV2:
    _expect_fields_v2(value, _OCCURRENCE_FIELDS_V2, name="perps margin occurrence")
    if value["schema"] != GLOBAL_SETTLEMENT_ABI_V2:
        raise PerpsMarginWireCodecErrorV2("perps margin occurrence schema is not V2")
    consumed = _expect_bounded_texts_v2(
        value["consumed_object_ids"],
        name="occurrence consumed object ids",
        limit=MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2,
    )
    return _construct_perps_v2(
        lambda: EconomicCommandOccurrenceV2(
            chain_id=_expect_text_v2(value["chain_id"], name="occurrence chain id"),
            deployment_root=_expect_text_v2(
                value["deployment_root"], name="occurrence deployment root"
            ),
            height=_expect_nonnegative_integer_v2(value["height"], name="occurrence height"),
            tx_index=_expect_nonnegative_integer_v2(
                value["tx_index"], name="occurrence tx index"
            ),
            op_index=_expect_nonnegative_integer_v2(value["op_index"], name="occurrence op index"),
            command_kind=_expect_text_v2(value["command_kind"], name="occurrence command kind"),
            command_body_hash=_expect_text_v2(
                value["command_body_hash"], name="occurrence command body hash"
            ),
            route_release_id=_expect_text_v2(
                value["route_release_id"], name="occurrence route release"
            ),
            subject_id=_expect_text_v2(value["subject_id"], name="occurrence subject"),
            grant_root=_expect_text_v2(value["grant_root"], name="occurrence grant"),
            nonce=_expect_nonnegative_integer_v2(value["nonce"], name="occurrence nonce"),
            profile_root=_expect_text_v2(value["profile_root"], name="occurrence profile root"),
            pre_state_root=_expect_text_v2(
                value["pre_state_root"], name="occurrence pre-state root"
            ),
            consumed_object_ids=consumed,
        )
    )


def _decode_oracle_object_v2(value: object) -> PerpsMarginOracleV2 | None:
    if value is None:
        return None
    oracle = _expect_object_v2(value, name="perps margin oracle")
    _expect_fields_v2(oracle, _ORACLE_FIELDS_V2, name="perps margin oracle")
    return _construct_perps_v2(
        lambda: PerpsMarginOracleV2(
            authority_root=_expect_text_v2(oracle["authority_root"], name="oracle authority root"),
            occurrence_root=_expect_text_v2(
                oracle["occurrence_root"], name="oracle occurrence root"
            ),
            price_e8=_expect_nonnegative_integer_v2(oracle["price_e8"], name="oracle price"),
        )
    )


@dataclass(frozen=True, slots=True)
class PerpsMarginRequestV2:
    """One owned typed command, occurrence, and optional explicit oracle value."""

    command: PerpsMarginCommandV1
    occurrence: EconomicCommandOccurrenceV2
    oracle: PerpsMarginOracleV2 | None = None

    def __post_init__(self) -> None:
        if type(self.command) is not PerpsMarginCommandV1:
            raise TypeError("perps margin request command must be exact V1")
        if type(self.occurrence) is not EconomicCommandOccurrenceV2:
            raise TypeError("perps margin request occurrence must be exact V2")
        if self.oracle is not None and type(self.oracle) is not PerpsMarginOracleV2:
            raise TypeError("perps margin request oracle must be exact V2 or absent")
        object.__setattr__(self, "command", replace(self.command))
        object.__setattr__(self, "occurrence", replace(self.occurrence))
        object.__setattr__(
            self,
            "oracle",
            None if self.oracle is None else replace(self.oracle),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": PERPS_MARGIN_REQUEST_SCHEMA_V2,
            "command": self.command,
            "occurrence": self.occurrence,
            "oracle": self.oracle,
        }


def _decode_account_object_v2(value: dict[str, object]) -> PerpsMarginAccountV1:
    _expect_fields_v2(value, _ACCOUNT_FIELDS_V1, name="perps margin account")
    return _construct_perps_v2(
        lambda: PerpsMarginAccountV1(
            account_id=_expect_text_v2(value["account_id"], name="account id"),
            owner=_expect_text_v2(value["owner"], name="account owner"),
            position_base=_expect_integer_v2(value["position_base"], name="account position"),
            entry_price_e8=_expect_nonnegative_integer_v2(
                value["entry_price_e8"], name="account entry price"
            ),
            collateral_atoms=_expect_nonnegative_integer_v2(
                value["collateral_atoms"], name="account collateral"
            ),
            nonce=_expect_nonnegative_integer_v2(value["nonce"], name="account nonce"),
            status=_decode_enum_v2(
                value["status"], PerpsMarginAccountStatusV1, name="account status"
            ),
        )
    )


def _decode_claim_object_v2(value: dict[str, object]) -> PerpsMarginClaimBindingV2:
    _expect_fields_v2(value, _CLAIM_FIELDS_V2, name="perps margin active claim")
    return _construct_perps_v2(
        lambda: PerpsMarginClaimBindingV2(
            account_id=_expect_text_v2(value["account_id"], name="claim account id"),
            obligation_id=_expect_text_v2(value["obligation_id"], name="claim obligation id"),
        )
    )


def decode_perps_margin_state_v2(raw: bytes) -> PerpsMarginStateV2:
    """Decode exact canonical flat V2 margin state bytes into owned values."""

    value = _load_perps_object_v2(raw)
    _expect_fields_v2(value, _STATE_FIELDS_V2, name="perps margin state")
    if value["schema"] != PERPS_MARGIN_MODULE_SCHEMA_V2:
        raise PerpsMarginWireCodecErrorV2("perps margin state schema is not V2")
    accounts = tuple(
        _decode_account_object_v2(item)
        for item in _expect_bounded_objects_v2(
            value["accounts"],
            name="perps margin accounts",
            limit=MAX_PERPS_MARGIN_ACCOUNTS_V2,
        )
    )
    claims = tuple(
        _decode_claim_object_v2(item)
        for item in _expect_bounded_objects_v2(
            value["active_claims"],
            name="perps margin active claims",
            limit=MAX_PERPS_MARGIN_ACCOUNTS_V2,
        )
    )
    economic = _construct_perps_v2(
        lambda: PerpsMarginStateV1(
            module_release_id=_expect_text_v2(value["module_release_id"], name="module release"),
            market_id=_expect_text_v2(value["market_id"], name="market id"),
            collateral_asset=_expect_text_v2(
                value["collateral_asset"], name="collateral asset"
            ),
            index_price_e8=_expect_nonnegative_integer_v2(
                value["index_price_e8"], name="index price"
            ),
            maintenance_margin_bps=_expect_nonnegative_integer_v2(
                value["maintenance_margin_bps"], name="maintenance margin"
            ),
            depeg_buffer_bps=_expect_nonnegative_integer_v2(
                value["depeg_buffer_bps"], name="depeg buffer"
            ),
            max_position_abs=_expect_nonnegative_integer_v2(
                value["max_position_abs"], name="max position"
            ),
            market_status=_decode_enum_v2(
                value["market_status"], PerpsMarginMarketStatusV1, name="market status"
            ),
            accounts=accounts,
        )
    )
    state = _construct_perps_v2(lambda: PerpsMarginStateV2(economic, claims))
    if canonical_global_bytes_v2(state.to_canonical()) != raw:
        raise PerpsMarginWireCodecErrorV2("perps margin state is not canonical V2")
    return state


def decode_perps_margin_request_v2(raw: bytes) -> PerpsMarginRequestV2:
    """Decode exact canonical V2 request bytes into owned typed inputs."""

    value = _load_perps_object_v2(raw)
    _expect_fields_v2(value, _REQUEST_FIELDS_V2, name="perps margin request")
    if value["schema"] != PERPS_MARGIN_REQUEST_SCHEMA_V2:
        raise PerpsMarginWireCodecErrorV2("perps margin request schema is not V2")
    command = _decode_command_object_v2(
        _expect_object_v2(value["command"], name="perps margin command")
    )
    occurrence = _decode_occurrence_object_v2(
        _expect_object_v2(value["occurrence"], name="perps margin occurrence")
    )
    oracle = _decode_oracle_object_v2(value["oracle"])
    request = _construct_perps_v2(lambda: PerpsMarginRequestV2(command, occurrence, oracle))
    if canonical_global_bytes_v2(request.to_canonical()) != raw:
        raise PerpsMarginWireCodecErrorV2("perps margin request is not canonical V2")
    return request


__all__ = [
    "PERPS_MARGIN_REQUEST_SCHEMA_V2",
    "PerpsMarginWireCodecErrorV2",
    "PerpsMarginRequestV2",
    "decode_perps_margin_state_v2",
    "decode_perps_margin_request_v2",
]

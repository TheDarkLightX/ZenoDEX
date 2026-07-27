"""Exact owned route-binding values for the FCIS M5-P4B3 exact route path.

Every authority-bearing value in this module is final, frozen, slotted, and
constructible only through the closed derivation/replay module
``fcis_route_binding.py``: the private construction token never leaves that
pair of modules.  Decoded or projected claims remain non-authoritative.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import TypeAlias, final

from ..state.owned_collections import OwnedMapV1

_ROUTE_BINDING_CONSTRUCTION_TOKEN_V1 = object()


class RouteKindV1(Enum):
    """Closed route direction; serialized values match the mounted protocol."""

    EXACT_IN = "exact_in"
    EXACT_OUT = "exact_out"


class RouteBindingRejectCodeV1(Enum):
    """Closed cross-field derivation rejections in frozen check order.

    STRUCTURAL_INVALID precedes the eight ordered cross-field checks: it covers
    missing fields and corrupted owned graphs whose shapes no longer match the
    admitted schema, so the cross-field checks always read exact typed values.
    """

    STRUCTURAL_INVALID = "route_binding_structural_invalid"
    KIND_MISMATCH = "route_binding_kind_mismatch"
    ENDPOINT_ASSETS_INVALID = "route_binding_endpoint_assets_invalid"
    LEG_COVERAGE_MISMATCH = "route_binding_leg_coverage_mismatch"
    LEG_ENDPOINT_MISMATCH = "route_binding_leg_endpoint_mismatch"
    FINGERPRINT_POOL_MISMATCH = "route_binding_fingerprint_pool_mismatch"
    AMOUNT_SUM_INVALID = "route_binding_amount_sum_invalid"
    EXACT_IN_TOTALS_MISMATCH = "route_binding_exact_in_totals_mismatch"
    EXACT_OUT_TOTALS_MISMATCH = "route_binding_exact_out_totals_mismatch"


class RouteReplayRejectCodeV1(Enum):
    """Closed exact-replay rejections.

    Serialized values are the existing stable public route rejection strings;
    BINDING_INVALID reuses ROUTE_BINDING_MISSING for a binding that fails
    recursive revalidation before any pool read.
    """

    BINDING_INVALID = "ROUTE_BINDING_MISSING"
    POOL_NOT_FOUND = "POOL_NOT_FOUND"
    POOL_NOT_ACTIVE = "POOL_NOT_ACTIVE"
    POOL_STATE_DRIFT = "ROUTE_POOL_STATE_DRIFT"
    INVALID_PARAMS = "INVALID_PARAMS"
    LEG_QUOTE_MISMATCH = "ROUTE_LEG_QUOTE_MISMATCH"


def _require_exact_text_field(name: str, value: str) -> None:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be an exact nonempty string")


def _require_exact_amount_field(name: str, value: int) -> None:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")


@final
@dataclass(frozen=True, slots=True)
class RouteLegBindingV1:
    """One single-hop leg of an exactly derived route binding."""

    pool_id: str
    asset_in: str
    asset_out: str
    amount_in: int
    amount_out: int
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1:
            raise TypeError("RouteLegBindingV1 requires controlled derivation")
        _require_exact_text_field("route leg pool_id", self.pool_id)
        _require_exact_text_field("route leg asset_in", self.asset_in)
        _require_exact_text_field("route leg asset_out", self.asset_out)
        _require_exact_amount_field("route leg amount_in", self.amount_in)
        _require_exact_amount_field("route leg amount_out", self.amount_out)


@final
@dataclass(frozen=True, slots=True)
class RouteBindingV1:
    """Verified exact route plan derived from one admitted route intent."""

    kind: RouteKindV1
    asset_in: str
    asset_out: str
    total_amount_in: int
    total_amount_out: int
    legs: tuple[RouteLegBindingV1, ...]
    pool_fingerprints: OwnedMapV1[str, str]
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1:
            raise TypeError("RouteBindingV1 requires controlled derivation")
        if type(self.kind) is not RouteKindV1:
            raise TypeError("route binding kind must be an exact RouteKindV1")
        _require_exact_text_field("route binding asset_in", self.asset_in)
        _require_exact_text_field("route binding asset_out", self.asset_out)
        _require_exact_amount_field("route binding total_amount_in", self.total_amount_in)
        _require_exact_amount_field("route binding total_amount_out", self.total_amount_out)
        if type(self.legs) is not tuple or any(
            type(leg) is not RouteLegBindingV1 for leg in self.legs
        ):
            raise TypeError("route binding legs must be an exact RouteLegBindingV1 tuple")
        if type(self.pool_fingerprints) is not OwnedMapV1:
            raise TypeError("route binding fingerprints must be an exact OwnedMapV1")


@final
@dataclass(frozen=True, slots=True)
class RouteBindingOkV1:
    """Successful exact route-binding derivation."""

    binding: RouteBindingV1
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1:
            raise TypeError("RouteBindingOkV1 requires controlled derivation")
        if type(self.binding) is not RouteBindingV1:
            raise TypeError("route binding result must carry an exact RouteBindingV1")


@final
@dataclass(frozen=True, slots=True)
class RouteBindingRejectV1:
    """Stable exact route-binding rejection bound to a closed code and path."""

    code: RouteBindingRejectCodeV1
    path: tuple[str | int, ...]
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1:
            raise TypeError("RouteBindingRejectV1 requires controlled derivation")
        if type(self.code) is not RouteBindingRejectCodeV1:
            raise TypeError("route binding rejection requires an exact closed code")
        if type(self.path) is not tuple or any(type(part) not in (str, int) for part in self.path):
            raise TypeError("route binding rejection path must contain exact strings or ints")


RouteBindingResultV1: TypeAlias = RouteBindingOkV1 | RouteBindingRejectV1


@final
@dataclass(frozen=True, slots=True)
class RouteReplayLegV1:
    """One exactly replayed leg against threaded committed reserves."""

    pool_id: str
    asset_in: str
    asset_out: str
    amount_in: int
    amount_out: int
    fee_paid: int
    new_reserve0: int
    new_reserve1: int
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1:
            raise TypeError("RouteReplayLegV1 requires controlled derivation")
        _require_exact_text_field("replay leg pool_id", self.pool_id)
        _require_exact_text_field("replay leg asset_in", self.asset_in)
        _require_exact_text_field("replay leg asset_out", self.asset_out)
        for name, value in (
            ("amount_in", self.amount_in),
            ("amount_out", self.amount_out),
            ("fee_paid", self.fee_paid),
            ("new_reserve0", self.new_reserve0),
            ("new_reserve1", self.new_reserve1),
        ):
            _require_exact_amount_field(f"replay leg {name}", value)


@final
@dataclass(frozen=True, slots=True)
class RouteReplayOkV1:
    """Successful exact route replay with threaded post-reserves."""

    legs: tuple[RouteReplayLegV1, ...]
    total_amount_in: int
    total_amount_out: int
    total_fee_paid: int
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1:
            raise TypeError("RouteReplayOkV1 requires controlled derivation")
        if type(self.legs) is not tuple or any(
            type(leg) is not RouteReplayLegV1 for leg in self.legs
        ):
            raise TypeError("route replay legs must be an exact RouteReplayLegV1 tuple")
        _require_exact_amount_field("route replay total_amount_in", self.total_amount_in)
        _require_exact_amount_field("route replay total_amount_out", self.total_amount_out)
        _require_exact_amount_field("route replay total_fee_paid", self.total_fee_paid)


@final
@dataclass(frozen=True, slots=True)
class RouteReplayRejectV1:
    """Stable exact route-replay rejection bound to a closed public code."""

    code: RouteReplayRejectCodeV1
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1:
            raise TypeError("RouteReplayRejectV1 requires controlled derivation")
        if type(self.code) is not RouteReplayRejectCodeV1:
            raise TypeError("route replay rejection requires an exact closed code")


RouteReplayResultV1: TypeAlias = RouteReplayOkV1 | RouteReplayRejectV1

__all__ = (
    "RouteBindingOkV1",
    "RouteBindingRejectCodeV1",
    "RouteBindingRejectV1",
    "RouteBindingResultV1",
    "RouteBindingV1",
    "RouteKindV1",
    "RouteLegBindingV1",
    "RouteReplayLegV1",
    "RouteReplayOkV1",
    "RouteReplayRejectCodeV1",
    "RouteReplayRejectV1",
    "RouteReplayResultV1",
)

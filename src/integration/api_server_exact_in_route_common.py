from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class ExactInRouteRequest:
    asset_in: str
    asset_out: str
    amount_in: int
    split_search_profile: str
    enable_mixed_direct_twohop_split: bool
    binding_ok: int


@dataclass(frozen=True)
class ExactInRouteNoBindingRequest:
    asset_in: str
    asset_out: str
    amount_in: int
    split_search_profile: str
    enable_mixed_direct_twohop_split: bool


class BadRequest(Exception):
    def __init__(self, error: str) -> None:
        super().__init__(error)
        self.error = error


def parse_exact_in_route_request(obj: dict[str, object]) -> ExactInRouteRequest:
    asset_in, asset_out = _assets(obj)
    return ExactInRouteRequest(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=_amount_in(obj),
        split_search_profile=_split_search_profile(obj),
        enable_mixed_direct_twohop_split=_enable_mixed_direct_twohop_split(obj),
        binding_ok=_binding_ok(obj),
    )


def parse_exact_in_route_no_binding_request(obj: dict[str, object]) -> ExactInRouteNoBindingRequest:
    asset_in, asset_out = _assets(obj)
    return ExactInRouteNoBindingRequest(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=_amount_in(obj),
        split_search_profile=_split_search_profile(obj),
        enable_mixed_direct_twohop_split=_enable_mixed_direct_twohop_split(obj),
    )


def _assets(obj: dict[str, object]) -> tuple[str, str]:
    asset_in = str(obj.get("asset_in", "")).strip()
    asset_out = str(obj.get("asset_out", "")).strip()
    if not asset_in or not asset_out or asset_in == asset_out:
        raise BadRequest("bad_assets")
    return asset_in, asset_out


def _amount_in(obj: dict[str, object]) -> int:
    amount_in = obj.get("amount_in")
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        raise BadRequest("bad_amount_in")
    return int(amount_in)


def _split_search_profile(obj: dict[str, object]) -> str:
    split_search_profile = str(obj.get("split_search_profile", "adaptive_v6")).strip()
    if not split_search_profile:
        raise BadRequest("bad_split_search_profile")
    return split_search_profile


def _enable_mixed_direct_twohop_split(obj: dict[str, object]) -> bool:
    enable = obj.get("enable_mixed_direct_twohop_split", False)
    if not isinstance(enable, bool):
        raise BadRequest("bad_enable_mixed_direct_twohop_split")
    return bool(enable)


def _binding_ok(obj: dict[str, object]) -> int:
    binding_ok = obj.get("binding_ok", 1)
    if not isinstance(binding_ok, int) or isinstance(binding_ok, bool) or binding_ok not in {0, 1}:
        raise BadRequest("bad_binding_ok")
    return int(binding_ok)

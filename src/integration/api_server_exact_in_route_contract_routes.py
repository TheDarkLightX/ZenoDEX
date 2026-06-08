from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable


WriteJson = Callable[[int, object], None]
ParsePools = Callable[[], dict[str, Any]]

_BUILD_ORACLE_CONTRACT_ENDPOINT = "/api/dex/build_exact_in_route_oracle_contract"
_VERIFY_ORACLE_CONTRACT_ENDPOINT = "/api/dex/verify_exact_in_route_oracle_contract"
_ORACLE_CONTRACT_SCHEMA = "zenodex/exact-in-route-oracle-contract/v1"


@dataclass(frozen=True)
class _BuildOracleContractRequest:
    asset_in: str
    asset_out: str
    amount_in: int
    split_search_profile: str
    enable_mixed_direct_twohop_split: bool
    binding_ok: int


class _BadRequest(Exception):
    def __init__(self, error: str) -> None:
        super().__init__(error)
        self.error = error


def _parse_build_request(obj: dict[str, object]) -> _BuildOracleContractRequest:
    return _BuildOracleContractRequest(
        asset_in=_asset_in(obj),
        asset_out=_asset_out(obj),
        amount_in=_amount_in(obj),
        split_search_profile=_split_search_profile(obj),
        enable_mixed_direct_twohop_split=_enable_mixed_direct_twohop_split(obj),
        binding_ok=_binding_ok(obj),
    )


def _asset_in(obj: dict[str, object]) -> str:
    return str(obj.get("asset_in", "")).strip()


def _asset_out(obj: dict[str, object]) -> str:
    asset_in = _asset_in(obj)
    asset_out = str(obj.get("asset_out", "")).strip()
    if not asset_in or not asset_out or asset_in == asset_out:
        raise _BadRequest("bad_assets")
    return asset_out


def _amount_in(obj: dict[str, object]) -> int:
    amount_in = obj.get("amount_in")
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        raise _BadRequest("bad_amount_in")
    return int(amount_in)


def _split_search_profile(obj: dict[str, object]) -> str:
    split_search_profile = str(obj.get("split_search_profile", "adaptive_v6")).strip()
    if not split_search_profile:
        raise _BadRequest("bad_split_search_profile")
    return split_search_profile


def _enable_mixed_direct_twohop_split(obj: dict[str, object]) -> bool:
    enable = obj.get("enable_mixed_direct_twohop_split", False)
    if not isinstance(enable, bool):
        raise _BadRequest("bad_enable_mixed_direct_twohop_split")
    return bool(enable)


def _binding_ok(obj: dict[str, object]) -> int:
    binding_ok = obj.get("binding_ok", 1)
    if not isinstance(binding_ok, int) or isinstance(binding_ok, bool) or binding_ok not in {0, 1}:
        raise _BadRequest("bad_binding_ok")
    return int(binding_ok)


def _write_build_success(write_json: WriteJson, contract: object) -> None:
    write_json(
        200,
        {
            "ok": True,
            "contract_schema": _ORACLE_CONTRACT_SCHEMA,
            "verify_contract_endpoint": _VERIFY_ORACLE_CONTRACT_ENDPOINT,
            "contract": contract.to_dict(),
        },
    )


def _handle_build_oracle_contract(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        pools_by_id = parse_pools()
        req = _parse_build_request(obj)
        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_oracle_contract,
        )

        contract = build_exact_in_route_oracle_contract(
            pools_by_id=pools_by_id,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_in=req.amount_in,
            split_search_profile=req.split_search_profile,
            enable_mixed_direct_twohop_split=req.enable_mixed_direct_twohop_split,
            binding_ok=req.binding_ok,
        )
        _write_build_success(write_json, contract)
    except _BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "build_exact_in_route_oracle_contract_error", "details": "request failed"},
        )


def _handle_verify_oracle_contract(obj: dict[str, object], write_json: WriteJson) -> None:
    contract = obj.get("contract")
    if not isinstance(contract, dict):
        write_json(400, {"ok": False, "error": "bad_contract"})
        return
    try:
        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            verify_exact_in_route_oracle_contract_payload,
        )

        ok, err = verify_exact_in_route_oracle_contract_payload(contract)
        write_json(200, {"ok": bool(ok), "error": err})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "verify_exact_in_route_oracle_contract_error", "details": "request failed"},
        )


def maybe_handle_exact_in_route_contract_route(
    *,
    path: str,
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> bool:
    if path == _BUILD_ORACLE_CONTRACT_ENDPOINT:
        _handle_build_oracle_contract(obj, parse_pools, write_json)
        return True
    if path == _VERIFY_ORACLE_CONTRACT_ENDPOINT:
        _handle_verify_oracle_contract(obj, write_json)
        return True
    return False

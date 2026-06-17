"""Exact-out many-pool contract-builder handlers for the DEX dispatch registry."""

from __future__ import annotations

import importlib
from dataclasses import dataclass
from typing import Any, Mapping, Optional, Sequence

from src.integration._dex_api_helpers import (
    EndpointSchema,
    IntFieldSpec,
    parse_int_kwargs,
    parse_pools,
)
from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register


def _int_field_specs_from_tuples(
    tuples: Sequence[tuple[str, Any, int]],
) -> tuple[IntFieldSpec, ...]:
    """Convert the legacy ``(name, default, minimum)`` tuple form into specs."""
    return tuple(IntFieldSpec(name=n, default=d, minimum=m) for n, d, m in tuples)


@dataclass(frozen=True)
class _ExactOutContractResponseSpec:
    schema: str
    verify_endpoint: str
    include_contract_ok: bool
    quote_endpoint: Optional[str]


@dataclass(frozen=True)
class _ExactOutContractBuilderSpec:
    field_specs: Sequence[IntFieldSpec]
    module_function_name: str
    module_schema_name: str
    verify_endpoint: str
    error_code: str
    include_contract_ok: bool = False
    quote_endpoint: Optional[str] = None


def _exact_out_contract_response(
    *,
    contract_dict: Mapping[str, Any],
    spec: _ExactOutContractResponseSpec,
) -> dict[str, Any]:
    if spec.quote_endpoint is not None:
        return {
            "ok": True,
            "contract": contract_dict,
            "contract_schema": spec.schema,
            "quote_endpoint": spec.quote_endpoint,
            "verify_contract_endpoint": spec.verify_endpoint,
        }
    if spec.include_contract_ok:
        return {
            "ok": True,
            "contract": contract_dict,
            "contract_ok": bool(contract_dict["contract_ok"]),
            "contract_schema": spec.schema,
            "verify_contract_endpoint": spec.verify_endpoint,
        }
    return {
        "ok": True,
        "contract": contract_dict,
        "contract_schema": spec.schema,
        "verify_contract_endpoint": spec.verify_endpoint,
    }


def _make_exact_out_many_pool_contract_builder(spec: _ExactOutContractBuilderSpec) -> Any:
    """Factory for the build_exact_out_many_pool_*_contract endpoints."""

    def _handler(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
        pools_by_id = parse_pools(obj)
        asset_in = str(obj.get("asset_in", "")).strip()
        asset_out = str(obj.get("asset_out", "")).strip()
        if not asset_in or not asset_out or asset_in == asset_out:
            return 400, {"ok": False, "error": "bad_assets"}

        int_kwargs = parse_int_kwargs(obj, spec.field_specs)

        module = importlib.import_module("src.integration.exact_out_route_certificate")
        builder = getattr(module, spec.module_function_name)
        schema = getattr(module, spec.module_schema_name)

        contract = builder(
            list(pools_by_id.values()),
            asset_in=asset_in,
            asset_out=asset_out,
            **int_kwargs,
        )
        return 200, _exact_out_contract_response(
            contract_dict=contract.to_dict(),
            spec=_ExactOutContractResponseSpec(
                schema=schema,
                verify_endpoint=spec.verify_endpoint,
                include_contract_ok=spec.include_contract_ok,
                quote_endpoint=spec.quote_endpoint,
            ),
        )

    return _handler


_BUILD_EXACT_OUT_CONTRACT_SPECS: tuple[tuple[str, dict[str, Any]], ...] = (
    (
        "/api/dex/build_exact_out_many_pool_candidate_domain_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_candidate_domain_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_candidate_domain_contract",
            "error_code": "build_exact_out_many_pool_candidate_domain_contract_error",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_prefilter_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_prefilter_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_prefilter_contract",
            "error_code": "build_exact_out_many_pool_prefilter_contract_error",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_prefilter_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_full_domain_pools", 8, 1),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_repaired_prefilter_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_prefilter_contract",
            "error_code": "build_exact_out_many_pool_repaired_prefilter_contract_error",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_selected_domain_oracle_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_candidates", 12, 1),
                ("max_iters", 4096, 1),
                ("window", 64, 0),
                ("brute_force_max", 512, 0),
                ("max_full_domain_pools", 8, 1),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_repaired_selected_domain_oracle_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_selected_domain_oracle_contract",
            "error_code": "build_exact_out_many_pool_repaired_selected_domain_oracle_contract_error",
            "quote_endpoint": "/api/dex/quote_exact_out_many_pool_repaired_selected_domain",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_oracle_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_candidates", 12, 1),
                ("max_iters", 4096, 1),
                ("window", 64, 0),
                ("brute_force_max", 512, 0),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_oracle_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_oracle_contract",
            "error_code": "build_exact_out_many_pool_oracle_contract_error",
            "include_contract_ok": True,
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_audited_bounds_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_candidates", 12, 1),
                ("max_iters", 4096, 1),
                ("window", 64, 0),
                ("brute_force_max", 512, 0),
                ("max_full_domain_pools", 8, 1),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_audited_bounds_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_AUDITED_BOUNDS_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_audited_bounds_contract",
            "error_code": "build_exact_out_many_pool_audited_bounds_contract_error",
        },
    ),
)

for _path, _spec in _BUILD_EXACT_OUT_CONTRACT_SPECS:
    # Convert the legacy tuple form to IntFieldSpec for the factory and the
    # registered EndpointSchema. The schema gives OpenAPI coverage for every
    # contract builder without changing handler behavior.
    _field_specs = _int_field_specs_from_tuples(_spec["field_defaults"])
    _contract_builder_spec = _ExactOutContractBuilderSpec(
        field_specs=_field_specs,
        module_function_name=_spec["module_function_name"],
        module_schema_name=_spec["module_schema_name"],
        verify_endpoint=_spec["verify_endpoint"],
        error_code=_spec["error_code"],
        include_contract_ok=_spec.get("include_contract_ok", False),
        quote_endpoint=_spec.get("quote_endpoint"),
    )
    _handler_fn = _make_exact_out_many_pool_contract_builder(_contract_builder_spec)
    _register(
        _path,
        _handler_fn,
        default_error_code=_contract_builder_spec.error_code,
        schema=EndpointSchema(requires_pools=True, requires_assets=True, int_fields=_field_specs),
    )

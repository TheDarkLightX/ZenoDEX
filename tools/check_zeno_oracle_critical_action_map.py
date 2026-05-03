#!/usr/bin/env python3
"""Check critical ZenoOracle consumer-profile runtime wiring.

The consumer-profile catalog is the design-level map. This checker compares
that catalog against the runtime modules that currently consume Oracle adapter
bridges, and reports any catalog/runtime drift.
"""

from __future__ import annotations

import ast
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "tools"))

from tools import zenodex_oracle_consumer_profiles as catalog_mod  # noqa: E402
from tools.zenodex_oracle_adapter import profile_content_hash  # noqa: E402


RESULT_SCHEMA = "zenodex.oracle.critical_action_map_check.v1"


def _source(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def _module_ast(path: str) -> ast.Module:
    return ast.parse(_source(path), filename=path)


def _string_set_from_assignment(tree: ast.AST, name: str) -> set[str]:
    for node in ast.walk(tree):
        if not isinstance(node, ast.Assign):
            continue
        if not any(isinstance(target, ast.Name) and target.id == name for target in node.targets):
            continue
        if isinstance(node.value, (ast.Set, ast.List, ast.Tuple)):
            values: set[str] = set()
            for elt in node.value.elts:
                if isinstance(elt, ast.Constant) and isinstance(elt.value, str):
                    values.add(elt.value)
            return values
    return set()


def _profile_key(profile: Mapping[str, Any]) -> tuple[str, str]:
    return str(profile["consumer_module"]), str(profile["action_kind"])


def _expected_profiles() -> dict[tuple[str, str], dict[str, Any]]:
    catalog = catalog_mod.sample_catalog()
    result = catalog_mod.verify_consumer_profile_catalog(catalog)
    if result.status != "accepted":
        raise RuntimeError(f"sample consumer profile catalog rejected: {result.errors}")
    return {_profile_key(profile): dict(profile) for profile in catalog["profiles"]}


def _expect(condition: bool, errors: list[str], code: str) -> None:
    if not condition:
        errors.append(code)


def _profile_id_for(*, consumer_module: str, action_kind: str) -> str:
    profile = _expected_profiles()[(consumer_module, action_kind)]
    return str(profile["profile_id"])


def _query_id_for(*, consumer_module: str, action_kind: str) -> str:
    profile = _expected_profiles()[(consumer_module, action_kind)]
    return str(profile["query_id"])


def _runtime_surface(
    *,
    consumer_module: str,
    action_kind: str,
    path: str,
    details: Mapping[str, Any],
    errors: list[str],
) -> dict[str, Any]:
    key = f"{consumer_module}:{action_kind}"
    return {
        "key": key,
        "consumer_module": consumer_module,
        "action_kind": action_kind,
        "path": path,
        "status": "accepted" if not errors else "rejected",
        "ok": not errors,
        "errors": list(errors),
        "details": dict(details),
    }


def _check_perps_settle_epoch(profiles: Mapping[tuple[str, str], Mapping[str, Any]]) -> dict[str, Any]:
    errors: list[str] = []
    key = ("zenodex.perps", "settle_epoch")
    profile = profiles[key]
    source = _source("src/integration/perp_engine.py")

    from src.integration import perp_engine  # pylint: disable=import-outside-toplevel

    _expect(
        str(profile["query_id"]) == perp_engine._ORACLE_PERPS_INDEX_QUERY_ID,  # noqa: SLF001
        errors,
        "perps_settle_query_id_drift",
    )
    _expect(
        str(profile["profile_id"]) == perp_engine._ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,  # noqa: SLF001
        errors,
        "perps_settle_profile_id_drift",
    )
    for needle in (
        "_require_oracle_adapter_bridge(",
        'consumer_module="zenodex.perps"',
        'action_kind="settle_epoch"',
        "expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID",
        "expected_profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID",
        "expected_action_id=_perps_runtime_oracle_action_id(",
        "expected_action_id=_perps_clearinghouse_runtime_oracle_action_id(",
        "required=ctx.config.require_oracle_adapter_for_isolated_settle_epoch",
        "required=config.require_oracle_adapter_for_clearinghouse_settle_epoch",
    ):
        _expect(needle in source, errors, f"perps_settle_missing_static_wiring:{needle}")
    return _runtime_surface(
        consumer_module=key[0],
        action_kind=key[1],
        path="src/integration/perp_engine.py",
        details={
            "query_id": profile["query_id"],
            "profile_id": profile["profile_id"],
            "required_controls": [
                "require_oracle_adapter_for_isolated_settle_epoch",
                "require_oracle_adapter_for_clearinghouse_settle_epoch",
            ],
            "covered_runtime_actions": [
                "isolated_settle_epoch",
                "clearinghouse_2p_settle_epoch",
                "clearinghouse_3p_transfer_settle_epoch",
            ],
        },
        errors=errors,
    )


def _check_zusd_action(
    profiles: Mapping[tuple[str, str], Mapping[str, Any]],
    *,
    action_kind: str,
    expected_tag: str,
) -> dict[str, Any]:
    errors: list[str] = []
    key = ("zenodex.zusd", action_kind)
    profile = profiles[key]
    source = _source("src/integration/zusd_api.py")

    from src.integration import zusd_api  # pylint: disable=import-outside-toplevel

    _expect(
        str(profile["query_id"]) == zusd_api._ORACLE_ZUSD_COLLATERAL_QUERY_ID,  # noqa: SLF001
        errors,
        f"zusd_{action_kind}_query_id_drift",
    )
    _expect(
        str(profile["profile_id"]) == zusd_api._ZUSD_ORACLE_CONSUMER_PROFILE_IDS[action_kind],  # noqa: SLF001
        errors,
        f"zusd_{action_kind}_profile_id_drift",
    )
    _expect(
        zusd_api._ZUSD_ORACLE_ADAPTER_ACTIONS.get(expected_tag) == action_kind,  # noqa: SLF001
        errors,
        f"zusd_{action_kind}_tag_mapping_missing",
    )
    for needle in (
        "_check_zusd_oracle_adapter_bridge(",
        "ZUSD_ORACLE_ADAPTER_REQUIRED",
        'consumer_module": "zenodex.zusd"',
        'if _adapter_result_get(result, "profile_id") != _ZUSD_ORACLE_CONSUMER_PROFILE_IDS[action_kind]',
        'if _adapter_result_get(result, "action_id") != expected_action_id',
    ):
        _expect(needle in source, errors, f"zusd_{action_kind}_missing_static_wiring:{needle}")
    return _runtime_surface(
        consumer_module=key[0],
        action_kind=key[1],
        path="src/integration/zusd_api.py",
        details={
            "query_id": profile["query_id"],
            "profile_id": profile["profile_id"],
            "required_control": "ZUSD_ORACLE_ADAPTER_REQUIRED",
            "runtime_tag": expected_tag,
        },
        errors=errors,
    )


def _check_routing_guarded_quote(profiles: Mapping[tuple[str, str], Mapping[str, Any]]) -> dict[str, Any]:
    errors: list[str] = []
    key = ("zenodex.routing", "guarded_quote")
    profile = profiles[key]
    source = _source("src/integration/api_server.py")
    tree = _module_ast("src/integration/api_server.py")

    from src.integration import api_server  # pylint: disable=import-outside-toplevel

    _expect(
        str(profile["query_id"]) == api_server.DEX_ROUTING_REFERENCE_QUERY_ID,
        errors,
        "routing_guarded_quote_query_id_drift",
    )
    _expect(
        str(profile["profile_id"]) == api_server.DEX_ROUTING_GUARDED_QUOTE_PROFILE_ID,
        errors,
        "routing_guarded_quote_profile_id_drift",
    )
    guarded_paths = _string_set_from_assignment(tree, "DEX_API_EXACT_IN_ROUTE_SEARCH_PATHS")
    for path in (
        "/api/dex/quote_exact_in_route_guarded",
        "/api/dex/build_exact_in_route_guarded_quote_packet",
    ):
        _expect(path in guarded_paths, errors, f"routing_guarded_path_missing:{path}")
    for needle in (
        "_check_routing_oracle_adapter_bridge(",
        "_check_routing_exact_out_oracle_adapter_bridge(",
        "DEX_ROUTING_ORACLE_ADAPTER_REQUIRED",
        "expected_action_id = _routing_guarded_quote_oracle_action_id(",
        "expected_action_id = _routing_guarded_exact_out_quote_oracle_action_id(",
        'if _adapter_result_get(result, "profile_id") != DEX_ROUTING_GUARDED_QUOTE_PROFILE_ID',
        'if _adapter_result_get(result, "action_id") != expected_action_id',
    ):
        _expect(needle in source, errors, f"routing_guarded_quote_missing_static_wiring:{needle}")
    return _runtime_surface(
        consumer_module=key[0],
        action_kind=key[1],
        path="src/integration/api_server.py",
        details={
            "query_id": profile["query_id"],
            "profile_id": profile["profile_id"],
            "required_control": "DEX_ROUTING_ORACLE_ADAPTER_REQUIRED",
            "covered_runtime_actions": [
                "exact_in_guarded_quote",
                "exact_out_many_pool_guarded_quote",
            ],
        },
        errors=errors,
    )


def check_critical_action_map() -> dict[str, Any]:
    profiles = _expected_profiles()
    errors: list[str] = []
    for key in catalog_mod.REQUIRED_PROFILE_SPECS:
        if key not in profiles:
            errors.append(f"catalog_missing_required_profile:{key[0]}:{key[1]}")

    runtime_surfaces = [
        _check_perps_settle_epoch(profiles),
        _check_zusd_action(profiles, action_kind="mint", expected_tag="mint_zusd"),
        _check_zusd_action(profiles, action_kind="liquidate_vault", expected_tag="liquidate"),
        _check_routing_guarded_quote(profiles),
    ]
    errors.extend(
        f"runtime_surface_rejected:{surface['key']}:{error}"
        for surface in runtime_surfaces
        for error in surface["errors"]
    )

    design_only_backlog = [
        {
            "key": "zenodex.perps:liquidate_account",
            "status": "design_only_backlog",
            "reason": "profile is reserved for a future standalone liquidation adapter; current perps liquidation occurs inside settle_epoch",
            "query_id": _query_id_for(consumer_module="zenodex.perps", action_kind="liquidate_account"),
            "profile_id": _profile_id_for(consumer_module="zenodex.perps", action_kind="liquidate_account"),
        },
        {
            "key": "zenodex.trigger:execute_trigger",
            "status": "design_only_backlog",
            "reason": "profile exists in the first-shell catalog, but no trigger runtime module is wired in this checkout",
            "query_id": _query_id_for(consumer_module="zenodex.trigger", action_kind="execute_trigger"),
            "profile_id": _profile_id_for(consumer_module="zenodex.trigger", action_kind="execute_trigger"),
        },
    ]

    ok = not errors
    return {
        "schema": RESULT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "catalog_profile_count": len(profiles),
        "runtime_wired_count": len(runtime_surfaces),
        "design_only_backlog_count": len(design_only_backlog),
        "runtime_surfaces": runtime_surfaces,
        "design_only_backlog": design_only_backlog,
        "errors": errors,
        "not_claimed": [
            "does_not_claim_design_only_backlog_profiles_are_runtime_wired",
            "does_not_force_optional_runtime_adapter_flags_on_by_default",
            "does_not_claim_production_oracle_network_live",
        ],
    }


def main() -> int:
    receipt = check_critical_action_map()
    sys.stdout.write(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())

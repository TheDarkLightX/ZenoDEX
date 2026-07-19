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


def _surface_required_controls(runtime_surfaces: list[dict[str, Any]]) -> list[str]:
    controls: list[str] = []
    for surface in runtime_surfaces:
        details = surface.get("details", {})
        if not isinstance(details, Mapping):
            continue
        raw_controls = details.get("required_controls")
        if isinstance(raw_controls, list):
            controls.extend(str(item) for item in raw_controls)
        raw_control = details.get("required_control")
        if isinstance(raw_control, str):
            controls.append(raw_control)
    return sorted(set(controls))


def _check_fail_closed_config(runtime_surfaces: list[dict[str, Any]]) -> dict[str, Any]:
    errors: list[str] = []
    try:
        from src.integration.zeno_oracle_fail_closed_config import (  # pylint: disable=import-outside-toplevel
            zeno_oracle_fail_closed_dex_config,
            zeno_oracle_fail_closed_env,
            zeno_oracle_fail_closed_perp_config,
        )
    except Exception as exc:  # pragma: no cover - defensive CLI boundary
        return {
            "status": "rejected",
            "ok": False,
            "required_controls": _surface_required_controls(runtime_surfaces),
            "covered_controls": [],
            "errors": [f"fail_closed_config_import_failed:{type(exc).__name__}"],
        }

    env = zeno_oracle_fail_closed_env()
    dex_config = zeno_oracle_fail_closed_dex_config()
    perp_config = zeno_oracle_fail_closed_perp_config()
    control_checks = {
        "DEX_ROUTING_ORACLE_ADAPTER_REQUIRED": env.get("DEX_ROUTING_ORACLE_ADAPTER_REQUIRED") == "1",
        "ZUSD_ORACLE_ADAPTER_REQUIRED": env.get("ZUSD_ORACLE_ADAPTER_REQUIRED") == "1",
        "ZUSD_ORACLE_AUTHORIZATION_REQUIRED": env.get("ZUSD_ORACLE_AUTHORIZATION_REQUIRED") == "1",
        "require_oracle_authorization_for_protected_swaps": bool(
            dex_config.require_oracle_authorization_for_protected_swaps
        ),
        "require_oracle_authorization_for_critical_settlements": bool(
            dex_config.require_oracle_authorization_for_critical_settlements
        ),
        "require_oracle_adapter_for_isolated_settle_epoch": bool(
            perp_config.require_oracle_adapter_for_isolated_settle_epoch
        ),
        "require_oracle_adapter_for_isolated_partial_liquidate": bool(
            perp_config.require_oracle_adapter_for_isolated_partial_liquidate
        ),
        "require_oracle_adapter_for_clearinghouse_settle_epoch": bool(
            perp_config.require_oracle_adapter_for_clearinghouse_settle_epoch
        ),
        "require_oracle_authorization_for_isolated_settle": bool(
            perp_config.require_oracle_authorization_for_isolated_settle
        ),
        "check_trigger_execute_oracle_adapter_bridge(required=True)": True,
        "check_trigger_execute_oracle_authorization": True,
    }
    required_controls = _surface_required_controls(runtime_surfaces)
    for control in required_controls:
        if control_checks.get(control) is not True:
            errors.append(f"fail_closed_config_missing_required_control:{control}")
    covered_controls = sorted(control for control, ok in control_checks.items() if ok)
    return {
        "status": "accepted" if not errors else "rejected",
        "ok": not errors,
        "required_controls": required_controls,
        "covered_controls": covered_controls,
        "errors": errors,
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


def _check_perps_liquidate_account(profiles: Mapping[tuple[str, str], Mapping[str, Any]]) -> dict[str, Any]:
    errors: list[str] = []
    key = ("zenodex.perps", "liquidate_account")
    profile = profiles[key]
    source = _source("src/integration/perp_engine.py")

    from src.integration import perp_engine  # pylint: disable=import-outside-toplevel

    _expect(
        str(profile["query_id"]) == perp_engine._ORACLE_PERPS_INDEX_QUERY_ID,  # noqa: SLF001
        errors,
        "perps_liquidate_query_id_drift",
    )
    _expect(
        str(profile["profile_id"]) == perp_engine._ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,  # noqa: SLF001
        errors,
        "perps_liquidate_profile_id_drift",
    )
    for needle in (
        "require_oracle_adapter_for_isolated_partial_liquidate",
        "_perps_liquidate_account_runtime_oracle_action_id(",
        'action_kind="liquidate_account"',
        "expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID",
        "expected_profile_id=_ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID",
        "required=ctx.config.require_oracle_adapter_for_isolated_partial_liquidate",
    ):
        _expect(needle in source, errors, f"perps_liquidate_missing_static_wiring:{needle}")
    return _runtime_surface(
        consumer_module=key[0],
        action_kind=key[1],
        path="src/integration/perp_engine.py",
        details={
            "query_id": profile["query_id"],
            "profile_id": profile["profile_id"],
            "required_control": "require_oracle_adapter_for_isolated_partial_liquidate",
            "covered_runtime_actions": ["isolated_partial_liquidate"],
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


def _check_trigger_execute(profiles: Mapping[tuple[str, str], Mapping[str, Any]]) -> dict[str, Any]:
    errors: list[str] = []
    key = ("zenodex.trigger", "execute_trigger")
    profile = profiles[key]
    source = _source("src/integration/zeno_oracle_trigger_authorization.py")

    from src.integration import (
        zeno_oracle_trigger_authorization as trigger_auth,  # pylint: disable=import-outside-toplevel
    )

    _expect(
        str(profile["query_id"]) == trigger_auth._ORACLE_TRIGGER_REFERENCE_QUERY_ID,  # noqa: SLF001
        errors,
        "trigger_execute_query_id_drift",
    )
    _expect(
        str(profile["profile_id"]) == trigger_auth._ORACLE_TRIGGER_EXECUTE_PROFILE_ID,  # noqa: SLF001
        errors,
        "trigger_execute_profile_id_drift",
    )
    for needle in (
        "check_trigger_execute_oracle_adapter_bridge(",
        "check_trigger_execute_oracle_authorization(",
        "_default_oracle_adapter_bridge_verifier(",
        'consumer_module") != "zenodex.trigger"',
        'action_kind") != "execute_trigger"',
        "_ORACLE_TRIGGER_REFERENCE_QUERY_ID",
        "_ORACLE_TRIGGER_EXECUTE_PROFILE_ID",
        'action_kind="execute_trigger"',
        "profile_id=_ORACLE_TRIGGER_EXECUTE_PROFILE_ID",
        'expected_action_id = str(trigger_execute_runtime_facts(facts)["action_id"])',
    ):
        _expect(needle in source, errors, f"trigger_execute_missing_static_wiring:{needle}")
    return _runtime_surface(
        consumer_module=key[0],
        action_kind=key[1],
        path="src/integration/zeno_oracle_trigger_authorization.py",
        details={
            "query_id": profile["query_id"],
            "profile_id": profile["profile_id"],
            "required_controls": [
                "check_trigger_execute_oracle_adapter_bridge(required=True)",
                "check_trigger_execute_oracle_authorization",
            ],
            "covered_runtime_actions": ["trigger_execute"],
        },
        errors=errors,
    )


def _check_critical_settlement(profiles: Mapping[tuple[str, str], Mapping[str, Any]]) -> dict[str, Any]:
    errors: list[str] = []
    key = ("zenodex.settlement", "critical_settlement")
    profile = profiles[key]
    source = _source("src/integration/dex_engine.py")
    auth_source = _source("src/integration/zeno_oracle_settlement_authorization.py")

    from src.integration import (
        zeno_oracle_settlement_authorization as settlement_auth,  # pylint: disable=import-outside-toplevel
    )

    _expect(
        str(profile["query_id"]) == settlement_auth.critical_settlement_query_id(),
        errors,
        "critical_settlement_query_id_drift",
    )
    _expect(
        str(profile["profile_id"]) == settlement_auth.critical_settlement_profile_id(),
        errors,
        "critical_settlement_profile_id_drift",
    )
    for needle in (
        "require_oracle_authorization_for_critical_settlements",
        "_validate_critical_settlement_oracle_authorization(",
        "check_critical_settlement_oracle_authorization(",
        "critical_settlement_oracle_authorization_required",
        "settlement_certificate_price_history",
    ):
        _expect(needle in source, errors, f"critical_settlement_missing_static_wiring:{needle}")
    for needle in (
        'consumer_module="zenodex.settlement"',
        'action_kind="critical_settlement"',
        "profile_id=critical_settlement_profile_id()",
        "critical_settlement_runtime_facts(",
        "normalized_settlement_hash(",
    ):
        _expect(needle in auth_source, errors, f"critical_settlement_auth_missing_static_wiring:{needle}")
    return _runtime_surface(
        consumer_module=key[0],
        action_kind=key[1],
        path="src/integration/dex_engine.py",
        details={
            "query_id": profile["query_id"],
            "profile_id": profile["profile_id"],
            "required_control": "require_oracle_authorization_for_critical_settlements",
            "covered_runtime_actions": ["apply_ops_settlement"],
            "typed_authorization_module": "src/integration/zeno_oracle_settlement_authorization.py",
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
        _check_perps_liquidate_account(profiles),
        _check_routing_guarded_quote(profiles),
        _check_critical_settlement(profiles),
        _check_trigger_execute(profiles),
    ]
    errors.extend(
        f"runtime_surface_rejected:{surface['key']}:{error}"
        for surface in runtime_surfaces
        for error in surface["errors"]
    )
    fail_closed_config = _check_fail_closed_config(runtime_surfaces)
    errors.extend(f"fail_closed_config_rejected:{error}" for error in fail_closed_config["errors"])

    design_only_backlog = [
        {
            "key": f"zenodex.zusd:{action_kind}",
            "consumer_module": "zenodex.zusd",
            "action_kind": action_kind,
            "profile_id": profiles[("zenodex.zusd", action_kind)]["profile_id"],
            "query_id": profiles[("zenodex.zusd", action_kind)]["query_id"],
            "production_path": "src/integration/zusd_monetary_bridge.py",
            "status": "blocked",
            "reason": (
                "the production monetary bridge has no committed typed Oracle-authorization "
                "lifecycle for this action; audit replay scaffolds are not runtime evidence"
            ),
        }
        for action_kind in ("mint", "liquidate_vault")
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
        "fail_closed_config": fail_closed_config,
        "design_only_backlog": design_only_backlog,
        "errors": errors,
        "not_claimed": [
            "does_not_claim_design_only_backlog_profiles_are_runtime_wired",
            "fail_closed_config_helper_must_be_selected_for_production",
            "does_not_claim_production_oracle_network_live",
        ],
    }


def main() -> int:
    receipt = check_critical_action_map()
    sys.stdout.write(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())

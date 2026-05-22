#!/usr/bin/env python3
"""Audit production-boundary closure for value-moving ZenoDEX paths."""

from __future__ import annotations

import argparse
import ast
import json
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

UNSAFE_CONFIG_PATTERNS: tuple[tuple[str, re.Pattern[str], str], ...] = (
    (
        "require_settlement_match_false",
        re.compile(r"(?:\brequire_settlement_match\s*=|['\"]require_settlement_match['\"]\s*:)\s*False\b"),
        "Production code must not disable settlement matching.",
    ),
    (
        "allow_missing_settlement_true",
        re.compile(r"(?:\ballow_missing_settlement\s*=|['\"]allow_missing_settlement['\"]\s*:)\s*True\b"),
        "Production code must not accept nonce-bearing DEX intent batches without an explicit settlement.",
    ),
)

PRODUCTION_SCAN_ROOTS: tuple[str, ...] = ("src", "tools")
APPLY_OPERATIONS_EXPOSURE_EXEMPT: frozenset[str] = frozenset(
    {
        "src/integration/validation.py",
    }
)

API_SERVER_FORBIDDEN_TOKENS: tuple[str, ...] = (
    "apply_ops",
    "DexEngineConfig",
    "apply_settlement(",
    "apply_settlement_pure",
    "from src.core.dex",
    "from ..core.dex",
)

PRODUCTION_BOUNDARY_REQUIREMENTS: tuple[dict[str, Any], ...] = (
    {
        "requirement_id": "value_moving_paths_use_safe_profile",
        "objective": "Value-moving production paths go through fail-closed safe profiles.",
        "check_ids": (
            "dex_engine_defaults_fail_closed",
            "core_dex_defaults_use_strong_settlement_profile",
            "named_safe_profiles_force_production_closure",
            "tau_testnet_dex_plugin_enters_through_dex_engine",
            "public_operator_node_preflight_blocks_unsigned_testnet_mutation",
        ),
    },
    {
        "requirement_id": "no_production_nonce_free_path",
        "objective": "Production posture does not expose nonce-free value-moving admission.",
        "check_ids": (
            "dex_engine_defaults_fail_closed",
            "named_safe_profiles_force_production_closure",
            "nonce_free_value_moving_batch_rejected",
            "public_operator_node_preflight_blocks_unsigned_testnet_mutation",
        ),
    },
    {
        "requirement_id": "no_legacy_settlement_validation_in_production",
        "objective": "Production posture does not use legacy settlement validation.",
        "check_ids": (
            "core_dex_defaults_use_strong_settlement_profile",
            "integration_validation_uses_strong_settlement_validator",
            "production_src_has_no_legacy_settlement_profile_literals",
        ),
    },
    {
        "requirement_id": "no_require_settlement_match_false_in_production",
        "objective": "Production posture does not disable settlement matching.",
        "check_ids": (
            "dex_engine_defaults_fail_closed",
            "named_safe_profiles_force_production_closure",
            "production_src_has_no_unsafe_dex_config_literals",
        ),
    },
    {
        "requirement_id": "no_direct_pure_core_ingress_exposed",
        "objective": "External-facing production ingress does not call direct pure-core settlement helpers.",
        "check_ids": (
            "direct_settlement_apply_helper_unexposed",
            "api_server_does_not_expose_direct_value_moving_core_ingress",
            "tau_testnet_dex_plugin_enters_through_dex_engine",
        ),
    },
)


@dataclass(frozen=True)
class BoundaryCheck:
    check_id: str
    ok: bool
    evidence: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "check_id": self.check_id,
            "ok": self.ok,
            "evidence": self.evidence,
        }


def scan_unsafe_config_literals(paths: Iterable[Path], *, root: Path = REPO_ROOT) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for path in paths:
        if not path.is_file():
            continue
        try:
            rel = path.relative_to(root)
        except ValueError:
            rel = path
        text = path.read_text(encoding="utf-8")
        for line_no, line in enumerate(text.splitlines(), start=1):
            for rule_id, pattern, message in UNSAFE_CONFIG_PATTERNS:
                if pattern.search(line):
                    findings.append(
                        {
                            "path": str(rel),
                            "line": line_no,
                            "rule_id": rule_id,
                            "message": message,
                            "text": line.strip(),
                        }
                    )
    return findings


def scan_legacy_settlement_profile_literals(
    paths: Iterable[Path],
    *,
    root: Path = REPO_ROOT,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for path in paths:
        if not path.is_file():
            continue
        try:
            rel = path.relative_to(root).as_posix()
        except ValueError:
            rel = path.as_posix()
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        except SyntaxError as exc:
            findings.append(
                {
                    "path": rel,
                    "line": exc.lineno or 0,
                    "rule_id": "python_parse_error",
                    "message": "production-boundary scanner could not parse Python source",
                    "text": exc.msg,
                }
            )
            continue
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and _call_name(node.func) == "DexConfig":
                for keyword in node.keywords:
                    if keyword.arg == "settlement_validation" and _literal_str(keyword.value) == "legacy":
                        findings.append(
                            {
                                "path": rel,
                                "line": int(getattr(node, "lineno", 0)),
                                "rule_id": "legacy_settlement_validation_profile",
                                "message": "Production source must not construct DexConfig with legacy settlement validation.",
                                "text": "DexConfig(settlement_validation='legacy')",
                            }
                        )
            if isinstance(node, ast.Dict):
                for key, value in zip(node.keys, node.values):
                    if _literal_str(key) == "settlement_validation" and _literal_str(value) == "legacy":
                        findings.append(
                            {
                                "path": rel,
                                "line": int(getattr(node, "lineno", 0)),
                                "rule_id": "legacy_settlement_validation_profile",
                                "message": "Production source must not declare legacy settlement validation.",
                                "text": "{'settlement_validation': 'legacy'}",
                            }
                        )
    return findings


def scan_apply_operations_exposure(
    paths: Iterable[Path],
    *,
    root: Path = REPO_ROOT,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for path in paths:
        if not path.is_file():
            continue
        try:
            rel = path.relative_to(root).as_posix()
        except ValueError:
            rel = path.as_posix()
        if rel in APPLY_OPERATIONS_EXPOSURE_EXEMPT:
            continue
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        except SyntaxError as exc:
            findings.append(
                {
                    "path": rel,
                    "line": exc.lineno or 0,
                    "rule_id": "python_parse_error",
                    "message": "production-boundary scanner could not parse Python source",
                    "text": exc.msg,
                }
            )
            continue
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom):
                imported = {alias.name for alias in node.names}
                if "apply_operations" in imported:
                    findings.append(
                        {
                            "path": rel,
                            "line": int(getattr(node, "lineno", 0)),
                            "rule_id": "legacy_apply_operations_import",
                            "message": "Production source must not import the direct settlement apply helper.",
                            "text": "apply_operations",
                        }
                    )
            if isinstance(node, ast.Call) and _call_name(node.func) == "apply_operations":
                findings.append(
                    {
                        "path": rel,
                        "line": int(getattr(node, "lineno", 0)),
                        "rule_id": "legacy_apply_operations_call",
                        "message": "Production source must not call the direct settlement apply helper.",
                        "text": "apply_operations(...)",
                    }
                )
    return findings


def _src_python_files(root: Path) -> list[Path]:
    return sorted((root / "src").rglob("*.py"))


def _production_python_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for rel in PRODUCTION_SCAN_ROOTS:
        base = root / rel
        if base.exists():
            files.extend(sorted(base.rglob("*.py")))
    return files


def _call_name(func: ast.AST) -> str:
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        return func.attr
    return ""


def _literal_str(value: ast.AST | None) -> str | None:
    if isinstance(value, ast.Constant) and isinstance(value.value, str):
        return value.value
    return None


def _check_dex_config_defaults() -> BoundaryCheck:
    from src.integration.dex_engine import DexEngineConfig

    cfg = DexEngineConfig()
    facts = {
        "allow_missing_settlement": cfg.allow_missing_settlement,
        "require_settlement_match": cfg.require_settlement_match,
        "require_intent_signatures": cfg.require_intent_signatures,
        "consensus_mode": cfg.consensus_mode,
        "allow_external_tools": cfg.allow_external_tools,
    }
    ok = (
        facts["allow_missing_settlement"] is False
        and facts["require_settlement_match"] is True
        and facts["require_intent_signatures"] is True
        and facts["consensus_mode"] is True
        and facts["allow_external_tools"] is False
    )
    return BoundaryCheck(
        check_id="dex_engine_defaults_fail_closed",
        ok=ok,
        evidence=json.dumps(facts, sort_keys=True),
    )


def _check_core_dex_config_defaults() -> BoundaryCheck:
    from src.core.dex import DexConfig

    cfg = DexConfig()
    facts = {
        "settlement_validation": cfg.settlement_validation,
        "allow_snapshot_bound_quote_bindings": cfg.allow_snapshot_bound_quote_bindings,
        "swap_ordering": cfg.swap_ordering,
    }
    ok = (
        facts["settlement_validation"] == "strong_proof_carrying"
        and facts["allow_snapshot_bound_quote_bindings"] is False
        and facts["swap_ordering"] in ("greedy_ab_refined", "optimal_ab_bounded")
    )
    return BoundaryCheck(
        check_id="core_dex_defaults_use_strong_settlement_profile",
        ok=ok,
        evidence=json.dumps(facts, sort_keys=True),
    )


def _check_named_safe_profile_helpers() -> BoundaryCheck:
    from src.core.dex import DexConfig
    from src.integration.dex_engine import (
        make_strict_upba_engine_config,
        strict_upba_engine_config_facts_v0,
    )
    from src.integration.zeno_oracle_fail_closed_config import zeno_oracle_fail_closed_dex_config

    unsafe_dex_config = DexConfig(
        settlement_validation="legacy",
        allow_snapshot_bound_quote_bindings=True,
    )
    strict_upba = make_strict_upba_engine_config(
        allow_missing_settlement=True,
        require_settlement_match=False,
        require_intent_signatures=False,
        allow_external_tools=True,
        consensus_mode=False,
        dex_config=unsafe_dex_config,
        allow_uniform_batch_certificate=False,
        require_uniform_batch_certificate_for_supported_swaps=False,
        require_uniform_batch_optimality_certificate=False,
        require_uniform_batch_v2_bounded_grid_optimality=False,
        require_uniform_batch_v3_exact_out_grid_optimality=False,
    )
    oracle_closed = zeno_oracle_fail_closed_dex_config(
        allow_missing_settlement=True,
        require_settlement_match=False,
        require_intent_signatures=False,
        allow_external_tools=True,
        consensus_mode=False,
        dex_config=unsafe_dex_config,
        require_oracle_authorization_for_protected_swaps=False,
        require_oracle_authorization_for_critical_settlements=False,
    )
    upba_facts = strict_upba_engine_config_facts_v0(strict_upba)
    oracle_facts = {
        "allow_missing_settlement": oracle_closed.allow_missing_settlement,
        "require_settlement_match": oracle_closed.require_settlement_match,
        "require_intent_signatures": oracle_closed.require_intent_signatures,
        "allow_external_tools": oracle_closed.allow_external_tools,
        "consensus_mode": oracle_closed.consensus_mode,
        "settlement_validation": oracle_closed.dex_config.settlement_validation,
        "allow_snapshot_bound_quote_bindings": oracle_closed.dex_config.allow_snapshot_bound_quote_bindings,
        "require_oracle_authorization_for_protected_swaps": (
            oracle_closed.require_oracle_authorization_for_protected_swaps
        ),
        "require_oracle_authorization_for_critical_settlements": (
            oracle_closed.require_oracle_authorization_for_critical_settlements
        ),
    }
    expected_common = {
        "allow_missing_settlement": False,
        "require_settlement_match": True,
        "require_intent_signatures": True,
        "allow_external_tools": False,
        "consensus_mode": True,
        "settlement_validation": "strong_proof_carrying",
        "allow_snapshot_bound_quote_bindings": False,
    }
    ok = all(upba_facts.get(key) == value for key, value in expected_common.items())
    ok = ok and all(oracle_facts.get(key) == value for key, value in expected_common.items())
    ok = ok and upba_facts["allow_uniform_batch_certificate"] is True
    ok = ok and upba_facts["require_uniform_batch_certificate_for_supported_swaps"] is True
    ok = ok and upba_facts["require_uniform_batch_optimality_certificate"] is True
    ok = ok and upba_facts["require_uniform_batch_v2_bounded_grid_optimality"] is True
    ok = ok and upba_facts["require_uniform_batch_v3_exact_out_grid_optimality"] is True
    ok = ok and oracle_facts["require_oracle_authorization_for_protected_swaps"] is True
    ok = ok and oracle_facts["require_oracle_authorization_for_critical_settlements"] is True
    return BoundaryCheck(
        check_id="named_safe_profiles_force_production_closure",
        ok=ok,
        evidence=json.dumps({"strict_upba": upba_facts, "zeno_oracle": oracle_facts}, sort_keys=True),
    )


def _check_nonce_free_batch_rejected() -> BoundaryCheck:
    from src.core.dex import DexState
    from src.core.liquidity import create_pool
    from src.integration.dex_engine import DexEngineConfig, apply_ops
    from src.state import BalanceTable, LPTable

    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    pool_id, pool, _lp = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=10_000,
        amount1=10_000,
        fee_bps=30,
        creator_pubkey=sender,
    )
    balances = BalanceTable()
    balances.set(sender, asset0, 10_000)
    state = DexState(balances=balances, pools={pool_id: pool}, lp_balances=LPTable())
    operations = {
        "2": [
            {
                "module": "TauSwap",
                "version": "0.1",
                "kind": "SWAP_EXACT_IN",
                "intent_id": "0x" + "01" * 32,
                "sender_pubkey": sender,
                "deadline": 9_999_999_999,
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 1,
            }
        ]
    }
    result = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=operations,
        block_timestamp=42,
        tx_sender_pubkey=sender,
    )
    ok = result.ok is False and result.error == "Missing/invalid nonce"
    return BoundaryCheck(
        check_id="nonce_free_value_moving_batch_rejected",
        ok=ok,
        evidence=f"ok={result.ok!r}, error={result.error!r}",
    )


def _check_strong_settlement_validator(root: Path) -> BoundaryCheck:
    text = (root / "src/integration/validation.py").read_text(encoding="utf-8")
    ok = "validate_settlement_strong(" in text and "from ..core.settlement import validate_settlement" not in text
    return BoundaryCheck(
        check_id="integration_validation_uses_strong_settlement_validator",
        ok=ok,
        evidence="src/integration/validation.py imports and calls validate_settlement_strong",
    )


def _check_no_unsafe_config_literals(root: Path) -> BoundaryCheck:
    findings = scan_unsafe_config_literals(_src_python_files(root), root=root)
    return BoundaryCheck(
        check_id="production_src_has_no_unsafe_dex_config_literals",
        ok=not findings,
        evidence=json.dumps(findings, sort_keys=True),
    )


def _check_no_legacy_settlement_profile_literals(root: Path) -> BoundaryCheck:
    findings = scan_legacy_settlement_profile_literals(_src_python_files(root), root=root)
    return BoundaryCheck(
        check_id="production_src_has_no_legacy_settlement_profile_literals",
        ok=not findings,
        evidence=json.dumps(findings, sort_keys=True),
    )


def _check_direct_apply_operations_unexposed(root: Path) -> BoundaryCheck:
    findings = scan_apply_operations_exposure(_production_python_files(root), root=root)
    return BoundaryCheck(
        check_id="direct_settlement_apply_helper_unexposed",
        ok=not findings,
        evidence=json.dumps(findings, sort_keys=True),
    )


def _check_api_server_read_only_boundary(root: Path) -> BoundaryCheck:
    path = root / "src/integration/api_server.py"
    text = path.read_text(encoding="utf-8")
    found = [token for token in API_SERVER_FORBIDDEN_TOKENS if token in text]
    return BoundaryCheck(
        check_id="api_server_does_not_expose_direct_value_moving_core_ingress",
        ok=not found,
        evidence=json.dumps({"forbidden_tokens_found": found}, sort_keys=True),
    )


def _check_tau_testnet_uses_dex_engine_boundary(root: Path) -> BoundaryCheck:
    path = root / "src/integration/tau_testnet_dex_plugin.py"
    text = path.read_text(encoding="utf-8")
    required = ("DexEngineConfig", "apply_ops")
    forbidden = ("apply_settlement_pure", "apply_settlement(")
    found_forbidden = [token for token in forbidden if token in text]
    missing_required = [token for token in required if token not in text]
    return BoundaryCheck(
        check_id="tau_testnet_dex_plugin_enters_through_dex_engine",
        ok=not found_forbidden and not missing_required,
        evidence=json.dumps(
            {
                "missing_required": missing_required,
                "forbidden_tokens_found": found_forbidden,
            },
            sort_keys=True,
        ),
    )


def _check_supported_runtime_doc_scope(root: Path) -> BoundaryCheck:
    text = (root / "docs/RC1_SUPPORTED_RUNTIME_PATH.md").read_text(encoding="utf-8")
    anchors = (
        "RuntimePathOK := ReadOnlyHTTPBounded",
        "Spot intent admission and signing path",
        "does not promote the entire integration shell",
    )
    missing = [anchor for anchor in anchors if anchor not in text]
    return BoundaryCheck(
        check_id="supported_runtime_doc_scopes_public_boundary",
        ok=not missing,
        evidence=json.dumps({"missing_anchors": missing}, sort_keys=True),
    )


def _check_public_operator_node_preflight_blocks_unsigned_testnet_mutation() -> BoundaryCheck:
    from tools.zeno_ledger_node import NODE_JOIN_CONFIG_SCHEMA, preflight_node_join_config_v0

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        config_path = tmp_path / "node-config.json"
        bundle_root = tmp_path / "bundle"
        data_dir = tmp_path / "data"
        bundle_root.mkdir()
        config = {
            "schema": NODE_JOIN_CONFIG_SCHEMA,
            "node_id": "production-boundary-public-operator",
            "base_url": "http://127.0.0.1:1",
            "bundle_root": str(bundle_root),
            "data_dir": str(data_dir),
            "serve": True,
            "host": "0.0.0.0",
            "port": 8787,
            "enable_testnet_intake": True,
        }
        config_path.write_text(json.dumps(config, sort_keys=True), encoding="utf-8")
        report = preflight_node_join_config_v0(
            config_path=config_path,
            check_port=False,
            strict_exposure=True,
            public_operator=True,
        )
    errors = list(report.get("errors", []))
    required_errors = (
        "public_operator: public binds must not expose testnet faucet or intake endpoints",
        "strict_exposure: testnet transaction intake is enabled; this endpoint accepts unsigned fixture traffic",
    )
    ok = report.get("ok") is False and all(item in errors for item in required_errors)
    return BoundaryCheck(
        check_id="public_operator_node_preflight_blocks_unsigned_testnet_mutation",
        ok=ok,
        evidence=json.dumps(
            {
                "preflight_ok": report.get("ok"),
                "errors": errors,
                "required_errors": list(required_errors),
            },
            sort_keys=True,
        ),
    )


def _requirement_reports(checks: Iterable[BoundaryCheck]) -> list[dict[str, Any]]:
    by_id = {check.check_id: check for check in checks}
    reports: list[dict[str, Any]] = []
    for requirement in PRODUCTION_BOUNDARY_REQUIREMENTS:
        check_ids = tuple(str(check_id) for check_id in requirement["check_ids"])
        missing = [check_id for check_id in check_ids if check_id not in by_id]
        failing = [check_id for check_id in check_ids if check_id in by_id and not by_id[check_id].ok]
        reports.append(
            {
                "requirement_id": requirement["requirement_id"],
                "objective": requirement["objective"],
                "ok": not missing and not failing,
                "check_ids": list(check_ids),
                "missing_check_ids": missing,
                "failing_check_ids": failing,
            }
        )
    return reports


def audit_production_boundary(root: Path = REPO_ROOT) -> dict[str, Any]:
    checks = [
        _check_dex_config_defaults(),
        _check_core_dex_config_defaults(),
        _check_named_safe_profile_helpers(),
        _check_nonce_free_batch_rejected(),
        _check_strong_settlement_validator(root),
        _check_no_unsafe_config_literals(root),
        _check_no_legacy_settlement_profile_literals(root),
        _check_direct_apply_operations_unexposed(root),
        _check_api_server_read_only_boundary(root),
        _check_tau_testnet_uses_dex_engine_boundary(root),
        _check_supported_runtime_doc_scope(root),
        _check_public_operator_node_preflight_blocks_unsigned_testnet_mutation(),
    ]
    requirements = _requirement_reports(checks)
    return {
        "schema": "zenodex/production_boundary_audit/v0",
        "ok": all(check.ok for check in checks) and all(item["ok"] for item in requirements),
        "checks": [check.to_dict() for check in checks],
        "requirements": requirements,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    payload = audit_production_boundary(args.root)
    if args.json or not payload["ok"]:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print("production boundary ok")
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

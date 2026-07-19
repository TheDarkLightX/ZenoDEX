from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"


def test_unsigned_in_memory_demo_apis_are_not_shipped() -> None:
    assert not (SRC / "integration" / "perps_api.py").exists()
    assert not (SRC / "integration" / "zusd_api.py").exists()
    api_server = (SRC / "integration" / "api_server.py").read_text(encoding="utf-8")
    assert "from src.integration.perps_api" not in api_server
    assert "PERPS_DEMO_API_UNSAFE_ENABLED" in api_server  # retired-setting refusal only
    assert "retired unsafe runtime settings" in api_server


def test_test_only_provider_and_fire_signer_material_are_not_shipped() -> None:
    forbidden = {
        "DEMO_SIGNER_PRIVKEY",
        "StaticAutoTraderLanguageProvider",
    }
    violations: list[str] = []
    for path in SRC.rglob("*.py"):
        source = path.read_text(encoding="utf-8")
        for token in forbidden:
            if token in source:
                violations.append(f"{path.relative_to(ROOT)}:{token}")
    assert violations == []


def test_local_harnesses_do_not_reanimate_retired_unsigned_apis() -> None:
    compose = (ROOT / "docker-compose.local-testnet.yml").read_text(encoding="utf-8")
    chaos = (ROOT / "tools" / "chaos" / "run_chaos_experiments.py").read_text(
        encoding="utf-8"
    )
    assert "ZUSD_API_ENABLED" not in compose
    assert "server.demo_api_token" not in chaos
    assert "server.perps_api_enabled" not in chaos
    assert "server.zusd_api_enabled" not in chaos


def test_incomplete_multi_vault_model_is_absent_from_shipped_src() -> None:
    forbidden_names = {
        "ZUSDMultiState",
        "ZUSDMultiCommand",
        "ZUSDMultiStepResult",
        "init_multi_state",
        "step_multi",
        "step_multi_with_tau",
        "validate_zusd_multi_transition",
        "in_multi_recovery_mode",
    }
    assert not [
        path
        for path in SRC.rglob("*")
        if path.is_file()
        and "__pycache__" not in path.parts
        and "zusd_multi" in path.name
    ]

    violations: list[str] = []
    for path in SRC.rglob("*.py"):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            name: str | None = None
            if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef, ast.Name)):
                name = node.name if hasattr(node, "name") else node.id
            elif isinstance(node, ast.Attribute):
                name = node.attr
            elif isinstance(node, ast.alias):
                name = node.name.rsplit(".", 1)[-1]
            if name in forbidden_names or (name is not None and name.startswith("ZUSDMulti")):
                violations.append(f"{path.relative_to(ROOT)}:{getattr(node, 'lineno', 0)}:{name}")
    assert violations == []


def test_checked_in_ui_runtime_config_is_production_safe() -> None:
    path = ROOT / "tools" / "dex-ui" / "public" / "zenodex-config.json"
    config = json.loads(path.read_text(encoding="utf-8"))
    contract = json.loads(
        (ROOT / "tools" / "dex-ui" / "audit" / "production-surface-contract.json").read_text(
            encoding="utf-8"
        )
    )
    canonical = json.dumps(contract, sort_keys=True, separators=(",", ":")).encode()
    assert config["deployment"] == "production"
    assert "demoMode" not in config
    assert "allowDemoMode" not in config
    assert "allowBrowserKeyGeneration" not in config
    assert config["allowDefaultExternalSigner"] is False
    assert "temporaryBrowserKeygenForTesting" not in config
    assert config["uiSurfaceContractSchema"] == contract["schema"]
    assert config["uiSurfaceContractVersion"] == contract["version"]
    assert config["uiSurfaceContractHash"] == (
        "sha256:" + hashlib.sha256(canonical).hexdigest()
    )


def test_production_dex_registry_has_no_in_process_attestation_signing_route() -> None:
    from src.integration.api_server_dex_dispatch import DEX_ENDPOINT_REGISTRY

    assert "/api/dex/build_settlement_spot_price_attestation" not in DEX_ENDPOINT_REGISTRY


def test_local_proof_mining_payout_template_is_not_shipped() -> None:
    integration = SRC / "integration"
    retired_modules = (
        "dex_dispatch_proof_mining_reward.py",
        "dex_dispatch_proof_mining_snapshots.py",
        "dex_dispatch_proof_mining_templates.py",
    )
    assert not [name for name in retired_modules if (integration / name).exists()]

    from src.integration.api_server_dex_dispatch import DEX_ENDPOINT_REGISTRY

    assert "/api/dex/proof_mining_payout_template" not in DEX_ENDPOINT_REGISTRY

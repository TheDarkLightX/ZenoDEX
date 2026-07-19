from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / ".docker" / "check_production_python_artifact.py"
UI_CONFIG_VALIDATOR = ROOT / ".docker" / "validate_production_ui_config.py"
UI_SURFACE_CONTRACT = (
    ROOT / "tools" / "dex-ui" / "audit" / "production-surface-contract.json"
)
PRODUCTION_DOCKERFILES = (
    ROOT / "Dockerfile",
    ROOT / "Dockerfile.hashlocked",
    ROOT / "Dockerfile.production-hashlocked",
)
EXCLUDED_RUNTIME_MODULES = (
    "autotrader_live.py",
    "autotrader_live_api.py",
    "confidential_attestation_api.py",
    "tau_testnet_dex_plugin.py",
    "tau_net_client.py",
    "zeno_ledger_tokenomics.py",
    "zenodex_local_signer.py",
)
EXCLUDED_RUNTIME_DIRECTORIES = ("src/nonproduction",)


def _ui_contract_binding() -> dict[str, str]:
    contract = json.loads(UI_SURFACE_CONTRACT.read_text(encoding="utf-8"))
    canonical = json.dumps(contract, sort_keys=True, separators=(",", ":")).encode()
    return {
        "uiSurfaceContractSchema": str(contract["schema"]),
        "uiSurfaceContractVersion": str(contract["version"]),
        "uiSurfaceContractHash": "sha256:" + hashlib.sha256(canonical).hexdigest(),
    }


def _run_checker(root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(CHECKER), str(root)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )


def test_every_production_dockerfile_enforces_the_same_python_exclusion_gate() -> None:
    for path in PRODUCTION_DOCKERFILES:
        content = path.read_text(encoding="utf-8")
        assert "ENV ZENODEX_ENV=production" in content, path.name
        assert "check_production_python_artifact.py /app/src" in content, path.name
        assert "COPY .docker/validate_production_ui_config.py /validate_production_ui_config.py" in content
        proof_client_copy = content.index(
            "COPY packages/zeno-proof-client/package.json "
            "./packages/zeno-proof-client/package.json"
        )
        npm_install = content.index("RUN npm ci --silent")
        assert proof_client_copy < npm_install, (
            f"{path.name} resolves the local UI package before it enters the build context"
        )
        assert "COPY packages/zeno-proof-client/src/ ./packages/zeno-proof-client/src/" in content
        assert "WORKDIR /app/tools/dex-ui" in content
        assert "RUN npm run test:contract && npm run build" in content
        assert "COPY --from=ui-builder /app/tools/dex-ui/dist /var/www/zenodex" in content
        final_source_copy = content.index("COPY --from=python-base /app/src ./src")
        assert content.index("check_production_python_artifact.py /app/src") < final_source_copy, (
            f"{path.name} scans source only after it entered the final image"
        )
        for module in EXCLUDED_RUNTIME_MODULES:
            assert module in content, f"{path.name} does not exclude {module}"
            assert content.index(module) < final_source_copy, (
                f"{path.name} deletes {module} only after it entered a final OCI layer"
            )
            assert module not in content[final_source_copy:], (
                f"{path.name} leaves recoverable {module} bytes in a lower final-image layer"
            )
        for directory in EXCLUDED_RUNTIME_DIRECTORIES:
            removal = f"rm -rf ./{directory}"
            assert removal in content, f"{path.name} does not exclude {directory}"
            assert content.index(removal) < final_source_copy, (
                f"{path.name} deletes {directory} only after it entered a final OCI layer"
            )
            assert directory not in content[final_source_copy:], (
                f"{path.name} leaves recoverable {directory} bytes in a lower final-image layer"
            )


def test_docker_context_includes_only_the_proof_client_surface_needed_by_ui() -> None:
    content = (ROOT / ".dockerignore").read_text(encoding="utf-8")
    assert "!packages/zeno-proof-client/package.json" in content
    assert "!packages/zeno-proof-client/src/**" in content
    assert "!packages/**" not in content


def test_production_python_checker_accepts_a_minimal_runtime_tree(tmp_path: Path) -> None:
    integration = tmp_path / "integration"
    integration.mkdir()
    (integration / "api.py").write_text("def health() -> bool:\n    return True\n", encoding="utf-8")
    result = _run_checker(tmp_path)
    assert result.returncode == 0, result.stdout + result.stderr


def test_production_python_checker_rejects_demo_and_local_fixture_surfaces(tmp_path: Path) -> None:
    integration = tmp_path / "integration"
    integration.mkdir()
    (integration / "perps_api.py").write_text("VALUE = 1\n", encoding="utf-8")
    (integration / "safe_name.py").write_text(
        "class StaticAutoTraderLanguageProvider:\n    pass\n",
        encoding="utf-8",
    )
    result = _run_checker(tmp_path)
    assert result.returncode == 1
    assert "forbidden production module: integration/perps_api.py" in result.stdout
    assert "StaticAutoTraderLanguageProvider" in result.stdout


def test_production_python_checker_rejects_oracle_tooling_imports(
    tmp_path: Path,
) -> None:
    integration = tmp_path / "integration"
    integration.mkdir()
    (integration / "unsafe_oracle.py").write_text(
        "from tools.zenodex_oracle_aggregate_adapter import "
        "verify_aggregate_adapter_bridge\n",
        encoding="utf-8",
    )
    (integration / "unsafe_oracle_alias.py").write_text(
        "from tools import zenodex_oracle_aggregate_adapter\n",
        encoding="utf-8",
    )

    result = _run_checker(tmp_path)

    assert result.returncode == 1
    assert (
        "forbidden production import: "
        "integration/unsafe_oracle.py:1:tools.zenodex_oracle_aggregate_adapter"
    ) in result.stdout
    assert (
        "forbidden production import: "
        "integration/unsafe_oracle_alias.py:1:tools.zenodex_oracle_aggregate_adapter"
    ) in result.stdout


def test_production_python_checker_rejects_tau_signing_and_block_production(
    tmp_path: Path,
) -> None:
    integration = tmp_path / "integration"
    integration.mkdir()
    (integration / "unsafe_tau.py").write_text(
        "def build_signed_tau_transaction() -> None:\n"
        "    return None\n"
        "def createblock() -> None:\n"
        "    return None\n",
        encoding="utf-8",
    )

    result = _run_checker(tmp_path)

    assert result.returncode == 1
    assert "build_signed_tau_transaction" in result.stdout
    assert "createblock" in result.stdout


def test_production_tau_rpc_surface_cannot_sign_or_produce_blocks() -> None:
    from src.integration import tau_net_rpc

    forbidden_exports = {
        "bls_pubkey_hex_from_privkey",
        "build_signed_tau_transaction",
        "sign_dex_intent_for_engine",
        "sign_perp_op_for_engine",
        "sign_tau_transaction_payload",
    }
    assert forbidden_exports.isdisjoint(vars(tau_net_rpc))
    client = tau_net_rpc.TauNetTcpClient()
    assert not hasattr(client, "createblock")
    assert not hasattr(client, "send_signed_tx")
    with pytest.raises(ValueError, match="not available in production"):
        client.rpc("createblock")
    with pytest.raises(ValueError, match="exactly one Tau RPC command"):
        client.rpc("getbalance account\r\ncreateblock")


def test_production_wallets_import_only_the_safe_tau_rpc_boundary() -> None:
    production_consumers = (
        ROOT / "src" / "integration" / "perps_wallet_api.py",
        ROOT / "src" / "integration" / "zusd_monetary_wallet_api.py",
        ROOT / "src" / "integration" / "zusd_tau_wallet_api.py",
        ROOT / "src" / "kernels" / "python" / "strategy_submit_bundle_guard_v1_adapter.py",
    )
    for path in production_consumers:
        source = path.read_text(encoding="utf-8")
        assert "tau_net_rpc" in source, path
        assert "tau_net_client" not in source, path


def test_production_sss_boundary_has_no_fixture_construction_capability() -> None:
    from src.integration import perps_wallet_encrypted_sss_backup

    forbidden_exports = {
        "SssBackupRecipient",
        "_delivery_receipt_for_envelope",
        "_derive_coefficient",
        "_encrypt_share_envelope",
        "_eval_poly_gf256",
        "_local_fixture_delivery_receipt",
        "build_perps_wallet_encrypted_sss_backup_v1",
        "split_secret_shamir_gf256",
    }
    assert forbidden_exports.isdisjoint(vars(perps_wallet_encrypted_sss_backup))


def test_production_python_checker_rejects_sss_fixture_builders(tmp_path: Path) -> None:
    integration = tmp_path / "integration"
    integration.mkdir()
    (integration / "unsafe_sss.py").write_text(
        "class SssBackupRecipient:\n"
        "    pass\n"
        "def split_secret_shamir_gf256() -> None:\n"
        "    return None\n"
        "def build_perps_wallet_encrypted_sss_backup_v1() -> None:\n"
        "    return None\n"
        "def _encrypt_share_envelope() -> None:\n"
        "    return None\n",
        encoding="utf-8",
    )

    result = _run_checker(tmp_path)

    assert result.returncode == 1
    for name in (
        "SssBackupRecipient",
        "split_secret_shamir_gf256",
        "build_perps_wallet_encrypted_sss_backup_v1",
        "_encrypt_share_envelope",
    ):
        assert name in result.stdout


def test_production_python_checker_rejects_nonproduction_perps_implementations(
    tmp_path: Path,
) -> None:
    nonproduction = tmp_path / "nonproduction"
    nonproduction.mkdir()
    (nonproduction / "perp_np_matching.py").write_text(
        "def match_fake_value() -> None:\n    return None\n",
        encoding="utf-8",
    )
    core = tmp_path / "core"
    core.mkdir()
    (core / "perp_np_clearinghouse.py").write_text("VALUE = 1\n", encoding="utf-8")
    (core / "perps_np_validation.py").write_text("VALUE = 1\n", encoding="utf-8")

    result = _run_checker(tmp_path)

    assert result.returncode == 1
    assert "forbidden production path: nonproduction" in result.stdout
    assert "forbidden production module: core/perp_np_clearinghouse.py" in result.stdout
    assert "forbidden production module: core/perps_np_validation.py" in result.stdout


def test_production_python_checker_rejects_retired_perps_adapter_surface(
    tmp_path: Path,
) -> None:
    integration = tmp_path / "integration"
    integration.mkdir()
    (integration / "perp_engine.py").write_text(
        "PERP_OP_VERSION_CHNP_V1_2 = '1.2'\n"
        "PERP_CHNP_MARKET_PREFIX = 'perp:chnp:'\n"
        "def _apply_init_market_np() -> None:\n"
        "    return None\n",
        encoding="utf-8",
    )

    result = _run_checker(tmp_path)

    assert result.returncode == 1
    assert "PERP_OP_VERSION_CHNP_V1_2" in result.stdout
    assert "PERP_CHNP_MARKET_PREFIX" in result.stdout
    assert "_apply_init_market_np" in result.stdout
    assert "retired fake-value perps action" in result.stdout
    assert "retired fake-value perps market namespace" in result.stdout


def test_curated_production_source_imports_without_nonproduction_package(tmp_path: Path) -> None:
    runtime_root = tmp_path / "runtime"
    shutil.copytree(
        ROOT / "src",
        runtime_root / "src",
        ignore=shutil.ignore_patterns("nonproduction", "__pycache__", "*.pyc", "*.pyo"),
    )
    env = os.environ.copy()
    env["PYTHONPATH"] = str(runtime_root)
    env["ZENODEX_ENV"] = "production"
    result = subprocess.run(
        [
            sys.executable,
            "-c",
            "import src.integration.perp_engine; import src.integration.api_server",
        ],
        cwd=runtime_root,
        env=env,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stdout + result.stderr


def test_production_python_checker_rejects_stale_bytecode(tmp_path: Path) -> None:
    cache = tmp_path / "integration" / "__pycache__"
    cache.mkdir(parents=True)
    (cache / "removed_demo.cpython-311.pyc").write_bytes(b"stale")
    result = _run_checker(tmp_path)
    assert result.returncode == 1
    assert "generated Python artifact" in result.stdout


def test_production_python_checker_rejects_in_process_attestation_signing_route(
    tmp_path: Path,
) -> None:
    integration = tmp_path / "integration"
    integration.mkdir()
    (integration / "unsafe_route.py").write_text(
        'PATH = "/api/dex/build_settlement_spot_price_attestation"\n',
        encoding="utf-8",
    )
    result = _run_checker(tmp_path)
    assert result.returncode == 1
    assert "in-process settlement-attestation signing route" in result.stdout


def test_production_python_checker_rejects_local_proof_mining_template_surface(
    tmp_path: Path,
) -> None:
    integration = tmp_path / "integration"
    integration.mkdir()
    (integration / "dex_dispatch_proof_mining_templates.py").write_text(
        "def assemble_local_template() -> dict[str, object]:\n    return {}\n",
        encoding="utf-8",
    )
    (integration / "unsafe_route.py").write_text(
        'PATH = "/api/dex/proof_mining_payout_template"\n',
        encoding="utf-8",
    )
    result = _run_checker(tmp_path)
    assert result.returncode == 1
    assert (
        "forbidden production module: integration/dex_dispatch_proof_mining_templates.py"
        in result.stdout
    )
    assert "local proof-mining payout-template route" in result.stdout


@pytest.mark.parametrize(
    ("setting", "expected_label"),
    (
        ("PERPS_WALLET_AUTO_MINE", "wallet API block-production switch"),
        ("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "retired in-process wallet-signing switch"),
        (
            "PERPS_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD",
            "retired signed-payload disclosure switch",
        ),
        ("ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING", "retired in-process wallet-signing switch"),
        (
            "ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING",
            "retired in-process wallet-signing switch",
        ),
    ),
)
def test_production_python_checker_rejects_retired_wallet_capability_switches(
    tmp_path: Path,
    setting: str,
    expected_label: str,
) -> None:
    integration = tmp_path / "integration"
    integration.mkdir()
    (integration / "unsafe_mining.py").write_text(
        f'UNSAFE_ENV = "{setting}"\n',
        encoding="utf-8",
    )
    result = _run_checker(tmp_path)
    assert result.returncode == 1
    assert expected_label in result.stdout


def _run_ui_config_validator(
    tmp_path: Path,
    config: object,
) -> subprocess.CompletedProcess[str]:
    path = tmp_path / "zenodex-config.json"
    path.write_text(json.dumps(config), encoding="utf-8")
    return subprocess.run(
        [
            sys.executable,
            str(UI_CONFIG_VALIDATOR),
            str(path),
            "--expected-chain-id",
            "zenodex-mainnet-v1",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )


def test_production_ui_config_validator_accepts_exact_chain_without_demo_capability(
    tmp_path: Path,
) -> None:
    result = _run_ui_config_validator(
        tmp_path,
        {
            "deployment": "production",
            "chainId": "zenodex-mainnet-v1",
            "apiBase": "",
            "zenoOracleApiBase": "",
            "allowDefaultExternalSigner": False,
            **_ui_contract_binding(),
        },
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_production_ui_config_validator_rejects_retired_capability_knobs(tmp_path: Path) -> None:
    for key in ("demoMode", "allowDemoMode", "allowBrowserKeyGeneration"):
        result = _run_ui_config_validator(
            tmp_path,
            {
                "deployment": "production",
                "chainId": "zenodex-mainnet-v1",
                "apiBase": "",
                "zenoOracleApiBase": "",
                "allowDefaultExternalSigner": False,
                **_ui_contract_binding(),
                key: False,
            },
        )
        assert result.returncode == 1
        assert f"forbidden_capability_key:{key}" in result.stdout


def test_production_ui_config_validator_requires_explicit_api_authorities(
    tmp_path: Path,
) -> None:
    base = {
        "deployment": "production",
        "chainId": "zenodex-mainnet-v1",
        "allowDefaultExternalSigner": False,
        **_ui_contract_binding(),
    }
    for missing_key, retained in (("apiBase", "zenoOracleApiBase"), ("zenoOracleApiBase", "apiBase")):
        result = _run_ui_config_validator(tmp_path, {**base, retained: ""})
        assert result.returncode == 1
        assert f"{missing_key}_must_be_explicit" in result.stdout


@pytest.mark.parametrize(
    "key",
    ("uiSurfaceContractSchema", "uiSurfaceContractVersion", "uiSurfaceContractHash"),
)
def test_production_ui_config_validator_rejects_stale_ui_contract_binding(
    tmp_path: Path,
    key: str,
) -> None:
    config = {
        "deployment": "production",
        "chainId": "zenodex-mainnet-v1",
        "apiBase": "",
        "zenoOracleApiBase": "",
        "allowDefaultExternalSigner": False,
        **_ui_contract_binding(),
    }
    config[key] = "stale"
    result = _run_ui_config_validator(tmp_path, config)
    assert result.returncode == 1
    assert f"{key}_mismatch" in result.stdout

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from src.integration.production_promotion_evidence import (
    ORACLE_AUTHORITY_EVIDENCE_SCHEMA_V1,
    _oracle_authority_attestation_message,
    attach_production_oracle_authority_hash_v1,
)

ROOT = Path(__file__).resolve().parents[1]
NOW = 1747878000
_ORACLE_AUTHORITY_PRIVATE_KEY = Ed25519PrivateKey.from_private_bytes(bytes.fromhex("44" * 32))


def _bounded_oracle_exercise() -> dict[str, object]:
    return {
        "authority_exercised": True,
        "public_testnet_exercised": True,
        "exercise_hash": "exhash",
        "authority_hash": "authhash",
        "chain_id": "tau-test-prod",
        "public_broadcast_height": 100,
        "public_settlement_height": 105,
    }


def _oracle_evidence() -> dict[str, object]:
    issued_at = NOW - 60
    pubkey = _ORACLE_AUTHORITY_PRIVATE_KEY.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )
    signature = _ORACLE_AUTHORITY_PRIVATE_KEY.sign(
        _oracle_authority_attestation_message(
            authority_id="zeno-oracle-prod",
            chain_id="tau-test-prod",
            target_network="public_testnet",
            exercise_hash="exhash",
            profile_authority_hash="authhash",
            public_broadcast_height=100,
            public_settlement_height=105,
            public_broadcast_block_hash="11" * 32,
            public_settlement_block_hash="22" * 32,
            public_broadcast_explorer_url="https://explorer.public-testnet/block/100",
            public_settlement_explorer_url="https://explorer.public-testnet/block/105",
            issued_at=issued_at,
        )
    )
    return attach_production_oracle_authority_hash_v1(
        {
            "schema": ORACLE_AUTHORITY_EVIDENCE_SCHEMA_V1,
            "authority_id": "zeno-oracle-prod",
            "chain_id": "tau-test-prod",
            "target_network": "public_testnet",
            "exercise_hash": "exhash",
            "profile_authority_hash": "authhash",
            "public_broadcast_height": 100,
            "public_settlement_height": 105,
            "public_broadcast_block_hash": "11" * 32,
            "public_settlement_block_hash": "22" * 32,
            "public_broadcast_explorer_url": "https://explorer.public-testnet/block/100",
            "public_settlement_explorer_url": "https://explorer.public-testnet/block/105",
            "authority_attestation_signature": signature.hex(),
            "authority_attestation_signer_pubkey": pubkey.hex(),
            "issued_at": issued_at,
        }
    )


def _run_gate(*args: str, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["bash", "tools/run_production_promotion_evidence_gate.sh", *args],
        cwd=ROOT,
        env=os.environ if env is None else env,
        check=False,
        capture_output=True,
        text=True,
    )


def test_production_promotion_gate_auto_fills_app_root_jmt_replay_evidence() -> None:
    proc = _run_gate("--explain-missing")

    assert proc.returncode == 1
    out = json.loads(proc.stdout)
    assert out["lanes"]["app_root_jmt"]["production_ready"] is True
    assert "app_root_jmt" not in out["blocked_lanes"]
    assert not any(gap.startswith("app_root_jmt:") for gap in out["gaps"])


def test_production_promotion_gate_can_include_collection_runbook() -> None:
    proc = _run_gate("--explain-missing", "--include-runbook")

    assert proc.returncode == 1
    out = json.loads(proc.stdout)
    runbook = out["collection_runbook"]
    assert runbook["schema"] == "zenodex/production-promotion-evidence-collection-runbook/v1"
    assert "oracle_authority" in runbook["lanes"]
    assert "app_root_jmt" in runbook["lanes"]
    assert "--include-runbook" in runbook["final_gate_command_template"]
    assert out["lanes"]["app_root_jmt"]["production_ready"] is True


def test_production_promotion_gate_include_runbook_respects_selected_lane() -> None:
    proc = _run_gate("--lane", "autotrader", "--include-runbook")

    assert proc.returncode == 1
    out = json.loads(proc.stdout)
    assert out["selected_lane"] == "autotrader"
    assert list(out["collection_runbook"]["lanes"]) == ["autotrader"]
    assert (
        out["collection_runbook"]["lanes"]["autotrader"]["producer_tool"]
        == "tools/build_autotrader_evidence.py"
    )
    assert "--include-runbook" in out["collection_runbook"]["final_gate_command_template"]


def test_production_promotion_gate_can_disable_app_root_jmt_auto_fill() -> None:
    env = {
        **os.environ,
        "ZENODEX_AUTO_APP_ROOT_JMT_EVIDENCE": "0",
    }
    proc = _run_gate("--explain-missing", env=env)

    assert proc.returncode == 1
    out = json.loads(proc.stdout)
    assert out["lanes"]["app_root_jmt"]["production_ready"] is False
    assert "app_root_jmt" in out["blocked_lanes"]
    assert "app_root_jmt: app-root/JMT live-root evidence is missing" in out["gaps"]


def test_production_promotion_gate_uses_env_manifest_override(tmp_path: Path) -> None:
    manifest = tmp_path / "bad-schema.json"
    manifest.write_text(json.dumps({"schema": "wrong"}), encoding="utf-8")
    env = {
        **os.environ,
        "PRODUCTION_PROMOTION_EVIDENCE_MANIFEST": str(manifest),
    }

    proc = _run_gate(env=env)

    assert proc.returncode == 2
    assert json.loads(proc.stdout)["error"] == "manifest_schema_mismatch"


def test_production_promotion_gate_positional_manifest_wins_over_env(tmp_path: Path) -> None:
    env_manifest = tmp_path / "env-bad-schema.json"
    env_manifest.write_text(json.dumps({"schema": "wrong"}), encoding="utf-8")
    positional = tmp_path / "positional.json"
    positional.write_text(
        json.dumps(
            {
                "schema": "zenodex/production-promotion-evidence-manifest/v1",
                "config": {},
                "bundle": {},
            }
        ),
        encoding="utf-8",
    )
    env = {
        **os.environ,
        "PRODUCTION_PROMOTION_EVIDENCE_MANIFEST": str(env_manifest),
    }

    proc = _run_gate(str(positional), "--lane", "autotrader", env=env)

    assert proc.returncode == 1
    out = json.loads(proc.stdout)
    assert out["selected_lane"] == "autotrader"
    assert "autotrader: autotrader evidence is missing" in out["gaps"]
    assert any("config.supervisor_profile_hash is required" in gap for gap in out["gaps"])


def test_production_promotion_gate_full_scope_preserves_relative_sidecars_during_auto_fill(
    tmp_path: Path,
) -> None:
    manifest_dir = tmp_path / "promotion"
    manifest_dir.mkdir()
    (manifest_dir / "bounded.json").write_text(
        json.dumps(_bounded_oracle_exercise(), sort_keys=True),
        encoding="utf-8",
    )
    manifest = manifest_dir / "manifest.json"
    manifest.write_text(
        json.dumps(
            {
                "schema": "zenodex/production-promotion-evidence-manifest/v1",
                "config": {
                    "bounded_oracle_exercise_status_path": "bounded.json",
                    "expected_chain_id": "tau-test-prod",
                },
                "bundle": {"oracle_authority": _oracle_evidence(), "app_root_jmt": None},
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    proc = _run_gate(str(manifest), "--now", str(NOW))

    assert proc.returncode == 1
    out = json.loads(proc.stdout)
    assert out["lanes"]["oracle_authority"]["production_ready"] is True
    assert out["lanes"]["app_root_jmt"]["production_ready"] is True
    assert "oracle_authority" not in out["blocked_lanes"]
    assert "app_root_jmt" not in out["blocked_lanes"]


def test_production_promotion_gate_selected_external_lane_skips_app_root_auto_fill(
    tmp_path: Path,
) -> None:
    log_path = tmp_path / "python-wrapper.log"
    wrapper = tmp_path / "python-wrapper.sh"
    wrapper.write_text(
        "#!/usr/bin/env bash\n"
        f"printf '%s\\n' \"$@\" >> {str(log_path)!r}\n"
        f"exec {sys.executable!r} \"$@\"\n",
        encoding="utf-8",
    )
    wrapper.chmod(0o755)

    manifest = tmp_path / "manifest.json"
    manifest.write_text(
        json.dumps(
            {
                "schema": "zenodex/production-promotion-evidence-manifest/v1",
                "config": {},
                "bundle": {"app_root_jmt": None},
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    proc = _run_gate(
        str(manifest),
        "--lane",
        "autotrader",
        env={**os.environ, "PYTHON": str(wrapper)},
    )

    assert proc.returncode == 1
    out = json.loads(proc.stdout)
    assert out["selected_lane"] == "autotrader"
    log = log_path.read_text(encoding="utf-8")
    assert "tools/check_production_promotion_evidence_manifest.py" in log
    assert "tools/build_app_root_jmt_evidence.py" not in log


def test_production_promotion_gate_uses_python_env_override(tmp_path: Path) -> None:
    log_path = tmp_path / "python-wrapper.log"
    wrapper = tmp_path / "python-wrapper.sh"
    wrapper.write_text(
        "#!/usr/bin/env bash\n"
        f"printf '%s\\n' \"$@\" >> {str(log_path)!r}\n"
        f"exec {sys.executable!r} \"$@\"\n",
        encoding="utf-8",
    )
    wrapper.chmod(0o755)

    proc = _run_gate("--lane", "app_root_jmt", env={**os.environ, "PYTHON": str(wrapper)})

    assert proc.returncode == 0
    log = log_path.read_text(encoding="utf-8")
    assert "tools/build_app_root_jmt_evidence.py" in log
    assert "tools/check_production_promotion_evidence_manifest.py" in log

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.check_zeno_oracle_production_network_config import check_config, sample_config


ROOT = Path(__file__).resolve().parents[1]


def test_production_network_config_accepts_sample_candidate() -> None:
    config = sample_config()
    result = check_config(config)

    assert result["schema"] == "zenodex.oracle.production_network_config_check.v1"
    assert result["status"] == "accepted"
    assert result["error_count"] == 0
    assert config["runtime_controls"]["require_oracle_authorization_for_isolated_settle_epoch"] is True
    assert "live_token_settlement_disabled" in result["go_live_blockers"]
    assert "does_not_claim_live_token_settlement" in result["not_claimed"]


def test_production_network_config_rejects_devnet_chain_id() -> None:
    config = sample_config()
    config["chain_id"] = "zenodex.oracle.local"

    result = check_config(config)

    assert result["status"] == "rejected"
    assert "chain_id_must_be_production_candidate" in result["errors"]
    assert "config_id_mismatch" in result["errors"]


def test_production_network_config_rejects_weak_reporter_quorum_and_operator_concentration() -> None:
    config = sample_config()
    registry = config["reporter_registry"]
    registry["quorum"] = 4
    registry["registered_reporters"] = registry["registered_reporters"][:3]
    for reporter in registry["registered_reporters"]:
        reporter["operator_id"] = "operator.cartel"

    result = check_config(config)

    assert result["status"] == "rejected"
    assert "registered_reporter_count_below_min" in result["errors"]
    assert "active_reporter_count_below_quorum" in result["errors"]
    assert "distinct_operator_count_below_quorum" in result["errors"]
    assert "operator_share_exceeds_policy:operator.cartel" in result["errors"]


def test_production_network_config_rejects_missing_signing_and_runtime_controls() -> None:
    config = sample_config()
    config["code_signing"]["required"] = False
    config["signing"]["receipt_signature_required"] = False
    del config["runtime_controls"]["DEX_ROUTING_ORACLE_ADAPTER_REQUIRED"]
    del config["runtime_controls"]["require_oracle_authorization_for_isolated_settle_epoch"]
    config["runtime_controls"]["ZUSD_ORACLE_ADAPTER_REQUIRED"] = False

    result = check_config(config)

    assert result["status"] == "rejected"
    assert "required_must_be_true" in result["errors"]
    assert "receipt_signature_required_must_be_true" in result["errors"]
    assert "missing_runtime_control:DEX_ROUTING_ORACLE_ADAPTER_REQUIRED" in result["errors"]
    assert "missing_runtime_control:require_oracle_authorization_for_isolated_settle_epoch" in result["errors"]
    assert "runtime_control_not_enabled:ZUSD_ORACLE_ADAPTER_REQUIRED" in result["errors"]


def test_production_network_config_rejects_missing_explicit_non_claims() -> None:
    config = sample_config()
    config["not_claimed"] = ["does_not_claim_network_deployed"]

    result = check_config(config)

    assert result["status"] == "rejected"
    assert "missing_not_claim:does_not_claim_live_token_settlement" in result["errors"]
    assert "missing_not_claim:does_not_claim_reporter_honesty" in result["errors"]


def test_production_network_config_cli_sample_and_require_live(tmp_path: Path) -> None:
    sample = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_production_network_config.py",
            "--sample",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0
    config_path = tmp_path / "production-network-config.json"
    config_path.write_text(sample.stdout, encoding="utf-8")

    accepted = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_production_network_config.py",
            "--input",
            str(config_path),
            "--format",
            "text",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert accepted.returncode == 0, accepted.stdout + accepted.stderr
    assert "status = accepted" in accepted.stdout

    require_live = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_production_network_config.py",
            "--input",
            str(config_path),
            "--require-live",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert require_live.returncode == 1
    receipt = json.loads(require_live.stdout)
    assert receipt["status"] == "rejected"
    assert "go_live_blockers_present" in receipt["errors"]

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.agents.krr_bundle_artifacts import (
    KRRReviewRecord,
    build_autotrader_krr_bundle,
    sign_autotrader_krr_bundle,
)
from src.agents.strategy_ir import AUTOTRADER_TAU_POLICY_SPECS
from src.integration.tau_witness import AUTOTRADER_COMPILE_CONTRACT_V1

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "autotrader_policy_compile.py"


def _write_minimal_krr_bundle(tmp_path: Path) -> Path:
    bundle = build_autotrader_krr_bundle(
        bundle_name="bundle.compile.cli",
        built_at="2026-03-12T00:15:00Z",
        compiler_version="bundle_builder_v1",
        policy_version="policy_v1",
        runtime_krr_kb={
            "operator_priors": {},
            "semantic_rules": [],
            "check_priors": {"policy::budget_guard": {"base_weight": 1.25}},
            "check_family_priors": {},
        },
        runtime_history={"history_check_stats": {"policy::budget_guard": {"seen": 3}}},
        review_records=(
            KRRReviewRecord(
                review_id="bundle.compile.cli.review",
                target_kind="bundle",
                target_id="bundle.compile.cli",
                decision="approve",
                reviewer="security.review",
                reviewed_at="2026-03-12T00:10:00Z",
                rationale="compile bundle approved",
                approved_for_runtime=True,
                provenance_ok=True,
            ),
        ),
    )
    signed = sign_autotrader_krr_bundle(bundle, privkey=21)
    bundle_path = tmp_path / "krr_bundle.json"
    bundle_path.write_text(json.dumps(signed.to_dict(), indent=2, sort_keys=True), encoding="utf-8")
    return bundle_path


def test_autotrader_policy_compile_cli_sentence_roundtrip(tmp_path: Path) -> None:
    telemetry_path = tmp_path / "compile_report.json"
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--text",
            "dca 100 zUSD into BTC every 4 epochs until epoch 20 max slippage 25 bps "
            "per window max 300 lifetime max 900 backend tau max live orders 2",
            "--owner-pubkey",
            "owner.pubkey.1",
            "--krr-backend",
            "off",
            "--telemetry-out",
            str(telemetry_path),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["source_form"] == "sentence"
    assert report["strategy"]["template"] == "dca"
    assert report["strategy"]["policy_backend"] == "tau"
    assert report["strategy"]["tau_policy_specs"] == list(AUTOTRADER_TAU_POLICY_SPECS)
    assert report["local_policy"]["schema"] == "zenodex/local-policy/v1"
    assert report["compile_contract_tau_receipt"]["spec_id"] == AUTOTRADER_COMPILE_CONTRACT_V1.spec_id
    assert report["compile_contract_tau_receipt"]["expected_ok"] is True
    assert report["source_artifact"]["schema"] == "zenodex/strategy-source-artifact/v1"
    assert report["source_artifact"]["source_form"] == "sentence"
    assert report["source_artifact_hash"] == report["source_artifact"]["source_artifact_hash"]
    assert report["strategy_hash"] == report["policy_artifact"]["strategy_hash"]
    assert report["decision_model_version"] == "autotrader-binary-v1"
    assert report["tau_policy_bundle_hash"] == report["tau_policy_bundle"]["tau_policy_bundle_hash"]
    assert report["policy_artifact_hash"] == report["policy_artifact"]["policy_artifact_hash"]
    assert report["tau_policy_bundle"]["schema"] == "zenodex/strategy-policy-bundle/v1"
    assert report["policy_artifact"]["schema"] == "zenodex/strategy-policy-artifact/v1"
    assert report["tau_policy_bundle"]["source_artifact_hash"] == report["source_artifact"]["source_artifact_hash"]
    assert report["tau_policy_bundle"]["compilation_witness_tau_receipt"]["spec_id"] == "autotrader_compilation_witness_v1"
    assert report["policy_artifact"]["tau_policy_bundle_hash"] == report["tau_policy_bundle"]["tau_policy_bundle_hash"]
    assert report["policy_artifact"]["source_artifact_hash"] == report["source_artifact"]["source_artifact_hash"]
    assert report["krr_advice"] is None
    persisted = json.loads(telemetry_path.read_text(encoding="utf-8"))
    assert persisted == report


def test_autotrader_policy_compile_cli_kv_file_with_krr(tmp_path: Path) -> None:
    policy_text = """
template: dca
strategy_id: dca.kv.cli
backend: local
asset_in: zUSD
asset_out: BTC
fixed_order_size: 100
cadence_epochs: 4
per_order_max: 100
per_window_max: 500
lifetime_max: 1000
valid_from_epoch: 1
valid_until_epoch: 100
""".strip()
    text_path = tmp_path / "policy.txt"
    text_path.write_text(policy_text, encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--text-file",
            str(text_path),
            "--owner-pubkey",
            "owner.pubkey.1",
            "--krr-backend",
            "python",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["source_form"] == "kv"
    assert report["strategy"]["strategy_id"] == "dca.kv.cli"
    assert report["strategy"]["owner_pubkey"] == "owner.pubkey.1"
    assert report["compile_contract_tau_receipt"]["spec_id"] == AUTOTRADER_COMPILE_CONTRACT_V1.spec_id
    assert report["tau_policy_bundle"]["compile_contract_tau_receipt"]["spec_id"] == AUTOTRADER_COMPILE_CONTRACT_V1.spec_id
    assert report["tau_policy_bundle"]["compilation_witness_tau_receipt"]["spec_id"] == "autotrader_compilation_witness_v1"
    assert report["policy_artifact"]["signature"] is None
    assert report["policy_artifact_hash"] == report["policy_artifact"]["policy_artifact_hash"]
    assert report["source_artifact"]["source_form"] == "kv"
    assert report["source_artifact_hash"] == report["policy_artifact"]["source_artifact_hash"]
    assert report["krr_advice"] is not None
    assert report["krr_advice"]["backend_used"] == "python"
    assert "policy::budget_guard" in report["krr_advice"]["preferred_checks"]


def test_autotrader_policy_compile_cli_invalid_text_fails(tmp_path: Path) -> None:
    telemetry_path = tmp_path / "compile_error.json"
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--text",
            "ape into BTC whenever vibes look strong",
            "--owner-pubkey",
            "owner.pubkey.1",
            "--telemetry-out",
            str(telemetry_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "unsupported policy text" in report["error"]
    persisted = json.loads(telemetry_path.read_text(encoding="utf-8"))
    assert persisted == report


def test_autotrader_policy_compile_cli_accepts_krr_bundle(tmp_path: Path) -> None:
    bundle_path = _write_minimal_krr_bundle(tmp_path)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--text",
            "dca 100 zUSD into BTC every 4 epochs until epoch 20 max slippage 25 bps "
            "per window max 300 lifetime max 900 backend local",
            "--owner-pubkey",
            "owner.pubkey.1",
            "--krr-backend",
            "python",
            "--krr-bundle-file",
            str(bundle_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["krr_bundle"]["schema"] == "zenodex/autotrader-krr-bundle/v1"
    assert report["krr_advice"] is not None
    assert report["krr_advice"]["backend_used"] == "python"


def test_autotrader_policy_compile_cli_rejects_mixed_krr_bundle_and_kb(tmp_path: Path) -> None:
    bundle_path = _write_minimal_krr_bundle(tmp_path)
    kb_path = tmp_path / "krr_kb.json"
    kb_path.write_text(
        json.dumps({"operator_priors": {}, "semantic_rules": [], "check_priors": {}, "check_family_priors": {}}),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--text",
            "dca 100 zUSD into BTC every 4 epochs until epoch 20 max slippage 25 bps "
            "per window max 300 lifetime max 900 backend local",
            "--owner-pubkey",
            "owner.pubkey.1",
            "--krr-backend",
            "python",
            "--krr-bundle-file",
            str(bundle_path),
            "--krr-kb",
            str(kb_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "--krr-bundle-file cannot be combined with --krr-kb" in report["error"]

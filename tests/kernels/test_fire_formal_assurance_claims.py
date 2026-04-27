from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import yaml

from src.fire.pathing_v1 import fire_formal_assurance_claims_path
from src.fire.verifier.formal_assurance_claims_v1 import (
    FIRE_FORMAL_ASSURANCE_CLAIMS_CHECK_REPORT_SCHEMA,
    verify_fire_formal_assurance_claims_file,
)


REPO_ROOT = Path(__file__).resolve().parents[2]


def _load_manifest() -> dict[str, Any]:
    payload = yaml.safe_load(fire_formal_assurance_claims_path().read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _write_manifest(tmp_path: Path, payload: dict[str, Any]) -> Path:
    manifest_path = tmp_path / "formal-assurance-claims.yaml"
    manifest_path.write_text(yaml.safe_dump(payload, sort_keys=False), encoding="utf-8")
    return manifest_path


def _component(payload: dict[str, Any], component_id: str) -> dict[str, Any]:
    for component in payload["components"]:
        if component["id"] == component_id:
            return component
    raise AssertionError(f"missing component {component_id}")


def test_fire_formal_assurance_claims_accept_current_manifest() -> None:
    ok, err, verification = verify_fire_formal_assurance_claims_file()

    assert ok is True, err
    assert verification is not None
    report = verification.to_report_dict()
    assert report["schema"] == FIRE_FORMAL_ASSURANCE_CLAIMS_CHECK_REPORT_SCHEMA
    assert report["component_count"] == 8
    assert report["formally_verified_components"] == ["fire_zpl_language_lean_v1"]
    assert report["settlement_authority_components"] == [
        "fire_settlement_receipt_v1",
        "fire_verifier_v1",
    ]
    assert report["non_authoritative_components"] == [
        "fire_compiler_v1",
        "fire_refiner_ore_v1",
        "fire_registry_ui_docs_v1",
        "fire_zpl_language_lean_v1",
    ]
    assert report["weakest_assurance_level"] == "hypothesis"


def test_fire_formal_assurance_claims_cli_accepts_current_manifest() -> None:
    result = subprocess.run(
        [sys.executable, "tools/check_fire_formal_assurance_claims.py"],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report["ok"] is True
    assert report["schema"] == FIRE_FORMAL_ASSURANCE_CLAIMS_CHECK_REPORT_SCHEMA


def test_fire_formal_assurance_claims_rejects_bug_free_claim(tmp_path: Path) -> None:
    payload = _load_manifest()
    _component(payload, "fire_compiler_v1")["claims_bug_free"] = True
    manifest_path = _write_manifest(tmp_path, payload)

    ok, err, verification = verify_fire_formal_assurance_claims_file(manifest_path, repo_root=REPO_ROOT)

    assert ok is False
    assert err is not None
    assert "bug-free claims are forbidden" in err
    assert verification is None


def test_fire_formal_assurance_claims_rejects_formal_claim_without_receipt(tmp_path: Path) -> None:
    payload = _load_manifest()
    formal = _component(payload, "fire_verifier_v1")["formal_verification"]
    formal["claimed"] = True
    formal["status"] = "formally_verified"
    formal["proof_receipts"] = []
    manifest_path = _write_manifest(tmp_path, payload)

    ok, err, verification = verify_fire_formal_assurance_claims_file(manifest_path, repo_root=REPO_ROOT)

    assert ok is False
    assert err is not None
    assert "formal verification claim requires at least one proof receipt" in err
    assert verification is None


def test_fire_formal_assurance_claims_rejects_non_authoritative_settlement_authority(tmp_path: Path) -> None:
    payload = _load_manifest()
    _component(payload, "fire_compiler_v1")["can_authorize_settlement"] = True
    manifest_path = _write_manifest(tmp_path, payload)

    ok, err, verification = verify_fire_formal_assurance_claims_file(manifest_path, repo_root=REPO_ROOT)

    assert ok is False
    assert err is not None
    assert "non-authoritative surface cannot authorize settlement" in err
    assert verification is None


def test_fire_formal_assurance_claims_rejects_missing_witness_binding(tmp_path: Path) -> None:
    payload = _load_manifest()
    payload["settlement_authority"]["required_bindings"] = [
        "object_hash",
        "instance_hash",
        "cert_sha256",
        "delta_hash",
        "delta_hash",
    ]
    manifest_path = _write_manifest(tmp_path, payload)

    ok, err, verification = verify_fire_formal_assurance_claims_file(manifest_path, repo_root=REPO_ROOT)

    assert ok is False
    assert err is not None
    assert "settlement authority receipt binding mismatch" in err
    assert verification is None


def test_fire_formal_assurance_claims_rejects_acceptance_receipt_authority(tmp_path: Path) -> None:
    payload = _load_manifest()
    receipt = _component(payload, "fire_acceptance_receipt_v1")
    receipt["can_authorize_settlement"] = True
    receipt["authorizes_settlement"] = True
    receipt["requires_firev_receipt_ok"] = True
    receipt["required_receipt_bindings"] = [
        "object_hash",
        "instance_hash",
        "cert_sha256",
        "witness_hash",
        "delta_hash",
    ]
    receipt["fails_closed_on_missing_receipt"] = True
    manifest_path = _write_manifest(tmp_path, payload)

    ok, err, verification = verify_fire_formal_assurance_claims_file(manifest_path, repo_root=REPO_ROOT)

    assert ok is False
    assert err is not None
    assert "package acceptance cannot authorize settlement" in err
    assert verification is None

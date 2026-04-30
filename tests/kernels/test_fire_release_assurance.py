from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import yaml

from src.fire.pathing_v1 import (
    fire_acceptance_receipt_schema_path,
    fire_formal_assurance_claims_path,
    fire_verifier_rules_path,
)
from src.fire.verifier.release_assurance_v1 import (
    FIRE_RELEASE_ASSURANCE_CHECK_REPORT_SCHEMA,
    MONEY_MOVING_SOURCE_RULES,
    verify_fire_release_assurance,
)


REPO_ROOT = Path(__file__).resolve().parents[2]


def _write_json(tmp_path: Path, filename: str, payload: dict[str, Any]) -> Path:
    path = tmp_path / filename
    path.write_text(json.dumps(payload, sort_keys=True, indent=2), encoding="utf-8")
    return path


def _write_yaml(tmp_path: Path, filename: str, payload: dict[str, Any]) -> Path:
    path = tmp_path / filename
    path.write_text(yaml.safe_dump(payload, sort_keys=False), encoding="utf-8")
    return path


def _copy_money_moving_sources(tmp_path: Path) -> Path:
    source_root = tmp_path / "source_root"
    for rel in MONEY_MOVING_SOURCE_RULES:
        dst = source_root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text((REPO_ROOT / rel).read_text(encoding="utf-8"), encoding="utf-8")
    return source_root


def test_fire_release_assurance_accepts_repo_gate() -> None:
    ok, err, verification = verify_fire_release_assurance()

    assert ok is True, err
    assert verification is not None
    report = verification.to_report_dict()
    assert report["schema"] == FIRE_RELEASE_ASSURANCE_CHECK_REPORT_SCHEMA
    assert report["acceptance_receipt_authorizes_settlement"] is False
    assert report["settlement_authority_predicate"] == "FIREVReceiptOK"
    assert report["settlement_authority_missing_or_mismatch_behavior"] == "reject"


def test_fire_release_assurance_cli_accepts_repo_gate() -> None:
    result = subprocess.run(
        [sys.executable, "tools/check_fire_release_assurance.py"],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report["ok"] is True
    assert report["schema"] == FIRE_RELEASE_ASSURANCE_CHECK_REPORT_SCHEMA


def test_fire_release_assurance_rejects_acceptance_receipt_settlement_authority(tmp_path: Path) -> None:
    schema = json.loads(fire_acceptance_receipt_schema_path().read_text(encoding="utf-8"))
    schema["properties"]["package_acceptance"]["properties"]["authorizes_settlement"]["const"] = True
    schema_path = _write_json(tmp_path, "fire-acceptance-receipt.schema.json", schema)

    ok, err, verification = verify_fire_release_assurance(
        acceptance_receipt_schema=schema_path,
        repo_root=REPO_ROOT,
    )

    assert ok is False
    assert err is not None
    assert "authorizes_settlement to false" in err
    assert verification is None


def test_fire_release_assurance_rejects_missing_witness_reject_rule(tmp_path: Path) -> None:
    rules = yaml.safe_load(fire_verifier_rules_path().read_text(encoding="utf-8"))
    assert isinstance(rules, dict)
    for entry in rules["rule_catalog"]["settlement"]:
        if entry["id"] == "settlement_authority_receipt_binding":
            entry["reject_if"] = [value for value in entry["reject_if"] if value != "witness_hash_mismatch"]
    rules_path = _write_yaml(tmp_path, "verifier-rules.yaml", rules)

    ok, err, verification = verify_fire_release_assurance(
        verifier_rules=rules_path,
        repo_root=REPO_ROOT,
    )

    assert ok is False
    assert err is not None
    assert "witness_hash_mismatch" in err
    assert verification is None


def test_fire_release_assurance_rejects_non_string_rule_predicate(tmp_path: Path) -> None:
    rules = yaml.safe_load(fire_verifier_rules_path().read_text(encoding="utf-8"))
    assert isinstance(rules, dict)
    for entry in rules["rule_catalog"]["settlement"]:
        if entry["id"] == "settlement_authority_receipt_binding":
            entry["establishes"].append({"predicate": 123})
    rules_path = _write_yaml(tmp_path, "verifier-rules.yaml", rules)

    ok, err, verification = verify_fire_release_assurance(
        verifier_rules=rules_path,
        repo_root=REPO_ROOT,
    )

    assert ok is False
    assert err is not None
    assert "settlement_authority_receipt_binding.establishes" in err
    assert "predicate" in err
    assert verification is None


def test_fire_release_assurance_rejects_non_string_surface(tmp_path: Path) -> None:
    rules = yaml.safe_load(fire_verifier_rules_path().read_text(encoding="utf-8"))
    assert isinstance(rules, dict)
    rules["non_authoritative_surfaces"].append(123)
    rules_path = _write_yaml(tmp_path, "verifier-rules.yaml", rules)

    ok, err, verification = verify_fire_release_assurance(
        verifier_rules=rules_path,
        repo_root=REPO_ROOT,
    )

    assert ok is False
    assert err is not None
    assert "non_authoritative_surfaces" in err
    assert verification is None


def test_fire_release_assurance_rejects_formal_claim_gate_failure(tmp_path: Path) -> None:
    manifest = yaml.safe_load(fire_formal_assurance_claims_path().read_text(encoding="utf-8"))
    assert isinstance(manifest, dict)
    manifest["claim_gate"]["bug_free_claim_allowed"] = True
    manifest_path = _write_yaml(tmp_path, "formal-assurance-claims.yaml", manifest)

    ok, err, verification = verify_fire_release_assurance(
        formal_claims_manifest=manifest_path,
        repo_root=REPO_ROOT,
    )

    assert ok is False
    assert err is not None
    assert "formal assurance claims failed" in err
    assert verification is None


def test_fire_release_assurance_rejects_money_moving_source_generic_verifier(tmp_path: Path) -> None:
    source_root = _copy_money_moving_sources(tmp_path)
    ledger_path = source_root / "src/fire/kernel/ledger_adapter_v1.py"
    text = ledger_path.read_text(encoding="utf-8")
    text = text.replace("verify_fire_settlement_authority_packet", "verify_fire_settlement_packet")
    ledger_path.write_text(text, encoding="utf-8")

    ok, err, verification = verify_fire_release_assurance(
        repo_root=REPO_ROOT,
        source_root=source_root,
    )

    assert ok is False
    assert err is not None
    assert "verify_fire_settlement_authority_packet" in err
    assert verification is None

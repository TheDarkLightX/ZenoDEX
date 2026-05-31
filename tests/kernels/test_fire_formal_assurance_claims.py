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


def _sha256_text(text: str) -> str:
    import hashlib

    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


def _materialize_declared_paths(root: Path, payload: dict[str, Any]) -> None:
    toolchain_path = root / "lean-mathlib/lean-toolchain"
    toolchain_path.parent.mkdir(parents=True, exist_ok=True)
    toolchain_path.write_text("leanprover/lean4:v4.27.0\n", encoding="utf-8")
    for component in payload["components"]:
        for rel in component["paths"]:
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            if path.suffix:
                path.write_text("placeholder\n", encoding="utf-8")
            else:
                path.mkdir(parents=True, exist_ok=True)


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


def test_fire_formal_assurance_claims_rejects_stale_proof_receipt_module_hash(tmp_path: Path) -> None:
    payload = _load_manifest()
    _materialize_declared_paths(tmp_path, payload)

    module_path = tmp_path / "lean-mathlib/Proofs/StaleReceiptProbe.lean"
    module_path.parent.mkdir(parents=True, exist_ok=True)
    module_path.write_text("def staleReceiptProbe : Nat := 1\n", encoding="utf-8")

    receipt_payload = {
        "schema": "zenodex/lean-proof-receipt/v1",
        "receipt_id": "stale_receipt_probe_v1",
        "checker": "lean",
        "lean_toolchain": "leanprover/lean4:v4.27.0",
        "commands": [{"cwd": "lean-mathlib", "cmd": "lake env lean Proofs/StaleReceiptProbe.lean"}],
        "modules": [
            {
                "module": "Proofs.StaleReceiptProbe",
                "path": "lean-mathlib/Proofs/StaleReceiptProbe.lean",
                "sha256": "sha256:" + ("0" * 64),
                "theorems": ["staleReceiptProbe"],
            }
        ],
        "claim": "negative test receipt with stale module hash",
        "result": "proved",
    }
    receipt_path = tmp_path / "proof_receipts/stale_receipt_probe_v1.json"
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_text = json.dumps(receipt_payload, sort_keys=True, separators=(",", ":"))
    receipt_path.write_text(receipt_text, encoding="utf-8")

    formal = _component(payload, "fire_zpl_language_lean_v1")["formal_verification"]
    formal["proof_receipts"] = [
        {
            "path": "proof_receipts/stale_receipt_probe_v1.json",
            "checker": "lean",
            "result": "proved",
            "sha256": _sha256_text(receipt_text),
            "scope": "negative stale module hash test",
        }
    ]
    manifest_path = _write_manifest(tmp_path, payload)

    ok, err, verification = verify_fire_formal_assurance_claims_file(manifest_path, repo_root=tmp_path)

    assert ok is False
    assert err is not None
    assert "proof receipt module hash mismatch" in err
    assert verification is None


def test_fire_formal_assurance_claims_rejects_receipt_without_named_theorems(tmp_path: Path) -> None:
    payload = _load_manifest()
    _materialize_declared_paths(tmp_path, payload)

    module_path = tmp_path / "lean-mathlib/Proofs/NoTheoremProbe.lean"
    module_path.parent.mkdir(parents=True, exist_ok=True)
    module_text = "def noTheoremProbe : Nat := 1\n"
    module_path.write_text(module_text, encoding="utf-8")

    receipt_payload = {
        "schema": "zenodex/lean-proof-receipt/v1",
        "receipt_id": "no_theorem_probe_v1",
        "checker": "lean",
        "lean_toolchain": "leanprover/lean4:v4.27.0",
        "commands": [{"cwd": "lean-mathlib", "cmd": "lake env lean Proofs/NoTheoremProbe.lean"}],
        "modules": [
            {
                "module": "Proofs.NoTheoremProbe",
                "path": "lean-mathlib/Proofs/NoTheoremProbe.lean",
                "sha256": _sha256_text(module_text),
                "theorems": [],
            }
        ],
        "claim": "negative test receipt without named theorem surface",
        "result": "proved",
    }
    receipt_path = tmp_path / "proof_receipts/no_theorem_probe_v1.json"
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_text = json.dumps(receipt_payload, sort_keys=True, separators=(",", ":"))
    receipt_path.write_text(receipt_text, encoding="utf-8")

    formal = _component(payload, "fire_zpl_language_lean_v1")["formal_verification"]
    formal["proof_receipts"] = [
        {
            "path": "proof_receipts/no_theorem_probe_v1.json",
            "checker": "lean",
            "result": "proved",
            "sha256": _sha256_text(receipt_text),
            "scope": "negative missing theorem list test",
        }
    ]
    manifest_path = _write_manifest(tmp_path, payload)

    ok, err, verification = verify_fire_formal_assurance_claims_file(manifest_path, repo_root=tmp_path)

    assert ok is False
    assert err is not None
    assert "theorems must be non-empty" in err
    assert verification is None


def test_fire_formal_assurance_claims_rejects_receipt_without_module_checker_command(tmp_path: Path) -> None:
    payload = _load_manifest()
    _materialize_declared_paths(tmp_path, payload)

    module_path = tmp_path / "lean-mathlib/Proofs/UncheckedModuleProbe.lean"
    module_path.parent.mkdir(parents=True, exist_ok=True)
    module_text = "def uncheckedModuleProbe : Nat := 1\n"
    module_path.write_text(module_text, encoding="utf-8")

    receipt_payload = {
        "schema": "zenodex/lean-proof-receipt/v1",
        "receipt_id": "unchecked_module_probe_v1",
        "checker": "lean",
        "lean_toolchain": "leanprover/lean4:v4.27.0",
        "commands": [{"cwd": "lean-mathlib", "cmd": "lake env lean Proofs/SomeOtherModule.lean"}],
        "modules": [
            {
                "module": "Proofs.UncheckedModuleProbe",
                "path": "lean-mathlib/Proofs/UncheckedModuleProbe.lean",
                "sha256": _sha256_text(module_text),
                "theorems": ["uncheckedModuleProbe"],
            }
        ],
        "claim": "negative test receipt whose checker command targets another module",
        "result": "proved",
    }
    receipt_path = tmp_path / "proof_receipts/unchecked_module_probe_v1.json"
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_text = json.dumps(receipt_payload, sort_keys=True, separators=(",", ":"))
    receipt_path.write_text(receipt_text, encoding="utf-8")

    formal = _component(payload, "fire_zpl_language_lean_v1")["formal_verification"]
    formal["proof_receipts"] = [
        {
            "path": "proof_receipts/unchecked_module_probe_v1.json",
            "checker": "lean",
            "result": "proved",
            "sha256": _sha256_text(receipt_text),
            "scope": "negative missing module checker command test",
        }
    ]
    manifest_path = _write_manifest(tmp_path, payload)

    ok, err, verification = verify_fire_formal_assurance_claims_file(manifest_path, repo_root=tmp_path)

    assert ok is False
    assert err is not None
    assert "missing Lean checker command" in err
    assert "Proofs.UncheckedModuleProbe" in err
    assert verification is None


def test_fire_formal_assurance_claims_rejects_lean_trust_escape_even_with_current_hash(tmp_path: Path) -> None:
    payload = _load_manifest()
    _materialize_declared_paths(tmp_path, payload)

    module_path = tmp_path / "lean-mathlib/Proofs/TrustEscapeProbe.lean"
    module_path.parent.mkdir(parents=True, exist_ok=True)
    module_text = """
/- This comment may mention sorry, axiom, admit, or unsafe without authorizing it. -/
axiom trustEscapeProbe : Nat
"""
    module_path.write_text(module_text, encoding="utf-8")

    receipt_payload = {
        "schema": "zenodex/lean-proof-receipt/v1",
        "receipt_id": "trust_escape_probe_v1",
        "checker": "lean",
        "lean_toolchain": "leanprover/lean4:v4.27.0",
        "commands": [{"cwd": "lean-mathlib", "cmd": "lake env lean Proofs/TrustEscapeProbe.lean"}],
        "modules": [
            {
                "module": "Proofs.TrustEscapeProbe",
                "path": "lean-mathlib/Proofs/TrustEscapeProbe.lean",
                "sha256": _sha256_text(module_text),
                "theorems": ["trustEscapeProbe"],
            }
        ],
        "claim": "negative test receipt with an in-source Lean trust escape",
        "result": "proved",
    }
    receipt_path = tmp_path / "proof_receipts/trust_escape_probe_v1.json"
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_text = json.dumps(receipt_payload, sort_keys=True, separators=(",", ":"))
    receipt_path.write_text(receipt_text, encoding="utf-8")

    formal = _component(payload, "fire_zpl_language_lean_v1")["formal_verification"]
    formal["proof_receipts"] = [
        {
            "path": "proof_receipts/trust_escape_probe_v1.json",
            "checker": "lean",
            "result": "proved",
            "sha256": _sha256_text(receipt_text),
            "scope": "negative Lean trust escape test",
        }
    ]
    manifest_path = _write_manifest(tmp_path, payload)

    ok, err, verification = verify_fire_formal_assurance_claims_file(manifest_path, repo_root=tmp_path)

    assert ok is False
    assert err is not None
    assert "proof receipt module contains Lean trust escape" in err
    assert "'axiom'" in err
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

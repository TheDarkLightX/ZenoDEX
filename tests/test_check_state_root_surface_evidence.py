from __future__ import annotations

import json
from pathlib import Path

import tools.check_state_root_surface_evidence as sre

ROOT = Path(__file__).resolve().parents[1]
RECEIPT = ROOT / "docs" / "assurance" / "state_root_surface_evidence_receipt.json"
SPEC = ROOT / "src" / "kernels" / "dex" / "state_root_v5_scope_contract.json"


def _load_receipt() -> dict:
    return json.loads(RECEIPT.read_text(encoding="utf-8"))


def _reseal(receipt: dict) -> None:
    receipt["receipt_sha256"] = sre._sha256_bytes(sre._canonical_json_bytes(sre._receipt_hash_body(receipt)))


def test_committed_state_root_surface_receipt_verifies() -> None:
    report = sre.check_receipt_file(receipt_path=RECEIPT, spec_path=SPEC)
    assert report["ok"] is True, report["errors"]
    assert report["schema"] == sre.CHECK_SCHEMA


def test_committed_receipt_covers_all_six_evidence_columns() -> None:
    receipt = _load_receipt()
    assert receipt["schema"] == sre.RECEIPT_SCHEMA
    assert receipt["private_toolchain_source_included"] is False
    assert set(receipt["evidence_columns"]) == {
        "running_impl",
        "formal_spec",
        "proof_artifact",
        "differential_tests",
        "runtime_invariants",
        "authority_mode",
    }
    assert receipt["evidence_columns"]["proof_artifact"]["kani"]["verdict"] == "VERIFIED"
    assert receipt["evidence_columns"]["proof_artifact"]["preimage_injectivity"]["ok"] is True


def test_resealed_source_hash_tamper_fails() -> None:
    receipt = _load_receipt()
    receipt["source_files"][0]["sha256"] = "0" * 64
    _reseal(receipt)
    errors = sre.verify_receipt(receipt, spec_path=SPEC)
    assert any("source hash drift" in err for err in errors), errors


def test_resealed_kani_harness_drop_fails() -> None:
    receipt = _load_receipt()
    receipt["evidence_columns"]["proof_artifact"]["kani"]["harnesses"] = receipt["evidence_columns"][
        "proof_artifact"
    ]["kani"]["harnesses"][:-1]
    _reseal(receipt)
    errors = sre.verify_receipt(receipt, spec_path=SPEC)
    assert any("harness" in err for err in errors), errors


def test_resealed_proof_verdict_downgrade_fails() -> None:
    receipt = _load_receipt()
    receipt["evidence_columns"]["proof_artifact"]["verdict"] = "CLAIMED"
    _reseal(receipt)
    errors = sre.verify_receipt(receipt, spec_path=SPEC)
    assert any("proof_artifact verdict" in err for err in errors), errors


def test_weakened_formal_spec_fails(tmp_path: Path) -> None:
    weakened = json.loads(SPEC.read_text(encoding="utf-8"))
    weakened["root_formula"]["section_order"] = ["BAL", "POL", "LPB", "LPA", "NNC"]
    spec_path = tmp_path / "state_root_v5_scope_contract.json"
    spec_path.write_text(json.dumps(weakened, indent=2, sort_keys=True), encoding="utf-8")

    report = sre.check_receipt_file(receipt_path=RECEIPT, spec_path=spec_path)
    assert report["ok"] is False
    assert any("section_order" in err or "included_sections" in err for err in report["errors"])

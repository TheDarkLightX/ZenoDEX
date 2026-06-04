"""The committed spot-proof public receipt must verify, and tampering must fail.

Pure-Python (no ESSO/Lean/Kani toolchains), so it runs anywhere CI runs pytest —
mirroring tests/test_check_kernel_assurance_public_receipt.py. Verifies the shipped
receipt is valid against its manifest and that drift / tampering is detected.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

import tools.spot_proof_public_receipt as spr

ROOT = Path(__file__).resolve().parents[2]
RECEIPT = ROOT / "docs" / "assurance" / "spot_proof_public_receipt.json"
MANIFEST = ROOT / "tools" / "spot_proof_public_manifest.json"


def test_committed_receipt_verifies() -> None:
    report = spr.check_receipt_file(receipt_path=RECEIPT, manifest_path=MANIFEST)
    assert report["ok"] is True, report["errors"]
    assert report["schema"] == "zenodex.spot_proof.public_receipt_check.v1"


def test_committed_receipt_shape_is_honest() -> None:
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    assert receipt["schema"] == spr.RECEIPT_SCHEMA
    assert receipt["private_toolchain_source_included"] is False
    ids = {p["id"] for p in receipt["proofs"]}
    # every proof carries a verdict + at least one pinned source hash
    for p in receipt["proofs"]:
        assert p["result"]["verdict"] in ("VERIFIED", "BUILT_NO_SORRY")
        assert p["source_files"] and all(h["sha256"] for h in p["source_files"])
    # the manifest and receipt cover the same proof ids
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert ids == {p["id"] for p in manifest["proofs"]}


def _load() -> tuple[dict, dict, str]:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    return receipt, manifest, spr._sha256_file(MANIFEST)


def test_tampered_receipt_hash_fails() -> None:
    receipt, manifest, msha = _load()
    receipt["proofs"][0]["result"]["verdict"] = "VERIFIED"  # body changed but hash not recomputed
    receipt["proofs"][0]["source_files"][0]["sha256"] = "0" * 64
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert errs, "tampered source hash must be rejected"


def test_wrong_manifest_hash_fails() -> None:
    receipt, manifest, _ = _load()
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256="deadbeef")
    assert any("manifest_sha256" in e for e in errs)


def test_downgraded_verdict_fails() -> None:
    receipt, manifest, msha = _load()
    receipt["proofs"][0]["result"]["verdict"] = "UNKNOWN"
    receipt["receipt_sha256"] = spr._sha256_bytes(spr._canonical_json_bytes(spr._receipt_hash_body(receipt)))
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("verdict" in e for e in errs), errs


def test_missing_proof_fails() -> None:
    receipt, manifest, msha = _load()
    receipt["proofs"] = receipt["proofs"][:-1]
    receipt["receipt_sha256"] = spr._sha256_bytes(spr._canonical_json_bytes(spr._receipt_hash_body(receipt)))
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("missing proofs" in e for e in errs), errs


def test_check_fails_closed_on_missing_files(tmp_path) -> None:
    assert spr.check_receipt_file(receipt_path=tmp_path / "nope.json", manifest_path=MANIFEST)["ok"] is False
    assert spr.check_receipt_file(receipt_path=RECEIPT, manifest_path=tmp_path / "nope.json")["ok"] is False


# --- Codex pass-2 regressions (forge defenses, each re-seals the receipt hash so
#     it is the source-pin / dedup / tool check under test, not the hash check) ---


def test_forged_lean_module_fails() -> None:
    """Pass-2 #2: retargeting a Lean receipt's `module` to a different (e.g.
    weaker) module must be rejected — the module is part of the source pin."""
    receipt, manifest, msha = _load()
    target = next(p for p in receipt["proofs"] if p["id"] == "cpmm_invariants_lean")
    target["result"]["module"] = "Proofs.ForgedOtherModule"
    receipt["receipt_sha256"] = spr._sha256_bytes(spr._canonical_json_bytes(spr._receipt_hash_body(receipt)))
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("module" in e for e in errs), errs


def test_duplicate_receipt_proof_id_fails() -> None:
    """Pass-2 #3: a duplicated receipt proof id must be rejected (the checker
    builds a by-id dict, so a dup could otherwise shadow-replace a real entry)."""
    receipt, manifest, msha = _load()
    receipt["proofs"].append(json.loads(json.dumps(receipt["proofs"][0])))
    receipt["receipt_sha256"] = spr._sha256_bytes(spr._canonical_json_bytes(spr._receipt_hash_body(receipt)))
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("duplicate" in e for e in errs), errs


def test_forged_receipt_tool_fails() -> None:
    """Pass-2 #3: a receipt `tool` that disagrees with the source pin must be
    rejected, not silently accepted because the manifest tool still matches."""
    receipt, manifest, msha = _load()
    target = next(p for p in receipt["proofs"] if p["id"] == "nonce_batch_sequencing_v1")
    target["tool"] = "lean-lake-build"
    receipt["receipt_sha256"] = spr._sha256_bytes(spr._canonical_json_bytes(spr._receipt_hash_body(receipt)))
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("tool" in e for e in errs), errs


def test_placeholder_proof_is_not_pinned() -> None:
    """Pass-2 #1: cpmm_output_amount_v2.yaml is a placeholder (only invariant is
    `dummy == 0`, amount_out is a `const: 0` HOLE). It must never appear in the
    source pin OR the manifest — it is not genuine proof evidence."""
    assert "cpmm_output_amount_v2" not in spr.EXPECTED_PROOFS
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert "cpmm_output_amount_v2" not in {p["id"] for p in manifest["proofs"]}

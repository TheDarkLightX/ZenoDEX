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
    assert manifest["schema"] == spr.MANIFEST_SCHEMA
    assert ids == {p["id"] for p in manifest["proofs"]}


def _load() -> tuple[dict, dict, str]:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    return receipt, manifest, spr._sha256_file(MANIFEST)


def _proof(receipt: dict, proof_id: str) -> dict:
    return next(p for p in receipt["proofs"] if p["id"] == proof_id)


def _reseal(receipt: dict) -> None:
    receipt["receipt_sha256"] = spr._sha256_bytes(spr._canonical_json_bytes(spr._receipt_hash_body(receipt)))


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
    _reseal(receipt)
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("verdict" in e for e in errs), errs


def test_missing_proof_fails() -> None:
    receipt, manifest, msha = _load()
    receipt["proofs"] = receipt["proofs"][:-1]
    _reseal(receipt)
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("missing proofs" in e for e in errs), errs


def test_malformed_receipt_proof_row_fails() -> None:
    """A re-sealed receipt cannot carry ignored malformed proof rows."""
    receipt, manifest, msha = _load()
    receipt["proofs"].append("not-a-proof-object")
    _reseal(receipt)
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("receipt.proofs" in e for e in errs), errs


def test_check_fails_closed_on_missing_files(tmp_path) -> None:
    assert spr.check_receipt_file(receipt_path=tmp_path / "nope.json", manifest_path=MANIFEST)["ok"] is False
    assert spr.check_receipt_file(receipt_path=RECEIPT, manifest_path=tmp_path / "nope.json")["ok"] is False


def test_build_rejects_weakened_manifest_before_toolchain() -> None:
    """Pass-3: build and check must enforce the same source-pinned proof set."""
    _, manifest, msha = _load()
    manifest["proofs"] = [p for p in manifest["proofs"] if p["id"] != "zenodex_nonces_lean"]
    with pytest.raises(spr.ReceiptError, match="source-pinned"):
        spr.build_receipt(manifest, manifest_sha256=msha, manifest_relpath="tools/spot_proof_public_manifest.json")


def test_build_rejects_unknown_required_verdict_before_toolchain() -> None:
    """Pass-3: verdicts are a closed enum, not free-form receipt labels."""
    _, manifest, msha = _load()
    manifest["proofs"][0]["required_verdict"] = "VERIFIED_WITH_WARNINGS"
    with pytest.raises(spr.ReceiptError, match="unsupported"):
        spr.build_receipt(manifest, manifest_sha256=msha, manifest_relpath="tools/spot_proof_public_manifest.json")


def test_build_rejects_wrong_manifest_schema_before_toolchain() -> None:
    """Review regression: the proof manifest envelope is part of the contract."""
    _, manifest, msha = _load()
    manifest["schema"] = "zenodex.spot_proof.public_manifest.v0"
    with pytest.raises(spr.ReceiptError, match="manifest.schema"):
        spr.build_receipt(manifest, manifest_sha256=msha, manifest_relpath="tools/spot_proof_public_manifest.json")


def test_build_rejects_stale_lean_toolchain_result(monkeypatch) -> None:
    """Build mode must reject Lean metadata that check mode would reject."""
    _, manifest, msha = _load()

    def fake_lean(module: str, source_rels: list[str]) -> dict:
        return {
            "verdict": "BUILT_NO_SORRY",
            "lean_toolchain": "leanprover/lean4:v4.1.0",
            "module": module,
        }

    monkeypatch.setattr(spr, "_run_lean", fake_lean)
    with pytest.raises(spr.ReceiptError, match="lean_toolchain"):
        spr.build_receipt(manifest, manifest_sha256=msha, manifest_relpath="tools/spot_proof_public_manifest.json")


def test_build_rejects_stale_esso_result_metadata(monkeypatch) -> None:
    """Build mode must source-pin ESSO report metadata before writing a receipt."""
    _, manifest, msha = _load()
    lean_toolchain = spr.EXPECTED_PROOFS["cpmm_invariants_lean"]["expected_lean_toolchain"]

    def fake_lean(module: str, source_rels: list[str]) -> dict:
        return {"verdict": "BUILT_NO_SORRY", "lean_toolchain": lean_toolchain, "module": module}

    def fake_esso(model_rel: str) -> dict:
        expected = dict(spr.EXPECTED_PROOFS["nonce_batch_sequencing_v1"]["expected_result"])
        expected["passed_queries"] = 0
        return {"verdict": "VERIFIED", **expected}

    monkeypatch.setattr(spr, "_run_lean", fake_lean)
    monkeypatch.setattr(spr, "_run_esso", fake_esso)
    with pytest.raises(spr.ReceiptError, match="passed_queries"):
        spr.build_receipt(manifest, manifest_sha256=msha, manifest_relpath="tools/spot_proof_public_manifest.json")


def test_lean_build_rejects_unsafe_source_after_lake_success(monkeypatch, tmp_path) -> None:
    """Review regression: `unsafe` must not earn a public Lean proof receipt.

    Why this failed review: `lake build` can succeed for source that extends the
    trusted surface, and the old build-side lexical scan did not reject `unsafe`.
    The public receipt is now fail-closed for this token before it records
    `BUILT_NO_SORRY`.
    """
    (tmp_path / "lean-mathlib").mkdir()
    (tmp_path / "lean-mathlib" / "lean-toolchain").write_text(
        "leanprover/lean4:v4.27.0\n", encoding="utf-8"
    )
    (tmp_path / "UnsafeReceipt.lean").write_text("unsafe def bad : Nat := 0\n", encoding="utf-8")

    class FakeLakeProc:
        returncode = 0
        stderr = ""

    monkeypatch.setattr(spr, "ROOT", tmp_path)
    monkeypatch.setattr(spr.subprocess, "run", lambda *args, **kwargs: FakeLakeProc())
    with pytest.raises(spr.ReceiptError, match="unsafe"):
        spr._run_lean("Proofs.UnsafeReceipt", ["UnsafeReceipt.lean"])


# Codex pass-2/pass-3 regression set. Each forged receipt is re-sealed first, so
# the test exercises source pins and result-body validation rather than the hash
# mismatch check.


def test_forged_lean_module_fails() -> None:
    """Pass-2 #2: a Lean proof cannot be retargeted to a weaker module."""
    receipt, manifest, msha = _load()
    target = _proof(receipt, "cpmm_invariants_lean")
    target["result"]["module"] = "Proofs.ForgedOtherModule"
    _reseal(receipt)
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("module" in e for e in errs), errs


def test_forged_lean_toolchain_fails() -> None:
    """Pass-3: a re-sealed receipt cannot claim a different Lean toolchain."""
    receipt, manifest, msha = _load()
    target = _proof(receipt, "zenodex_nonces_lean")
    target["result"]["lean_toolchain"] = "leanprover/lean4:v4.1.0"
    _reseal(receipt)
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("lean_toolchain" in e for e in errs), errs


def test_lean_toolchain_disk_downgrade_fails(monkeypatch) -> None:
    """Gemini Phase-5: the FULL toolchain-downgrade attack must fail. An attacker
    downgrades the on-disk lean-toolchain file AND rewrites the receipt's
    lean_toolchain to match, then re-seals — so there is no source-hash drift and
    receipt==on-disk. The expected toolchain is a source-pinned CONSTANT, so both
    the receipt value and the (simulated) on-disk value mismatch the pin and the
    check fails closed."""
    receipt, manifest, msha = _load()
    fake = "leanprover/lean4:v4.1.0"
    # Simulate the on-disk lean-toolchain file having been downgraded too.
    monkeypatch.setattr(spr, "_lean_toolchain_from_source_pin", lambda pid, exp: (fake, []))
    for pid in ("cpmm_invariants_lean", "zenodex_nonces_lean"):
        _proof(receipt, pid)["result"]["lean_toolchain"] = fake
    _reseal(receipt)
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("lean_toolchain" in e or "toolchain" in e for e in errs), errs


def test_missing_expected_lean_toolchain_pin_fails(monkeypatch) -> None:
    """The source pin itself must be present: if EXPECTED_PROOFS lacks
    expected_lean_toolchain, validation fails closed rather than trusting the receipt."""
    receipt, manifest, msha = _load()
    patched = {
        k: ({kk: vv for kk, vv in v.items() if kk != "expected_lean_toolchain"}
            if v.get("tool") == "lean-lake-build" else v)
        for k, v in spr.EXPECTED_PROOFS.items()
    }
    monkeypatch.setattr(spr, "EXPECTED_PROOFS", patched)
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("expected_lean_toolchain source pin missing" in e for e in errs), errs


def test_forged_esso_result_metadata_fails() -> None:
    """Pass-3: a re-sealed ESSO receipt cannot weaken solver metadata."""
    receipt, manifest, msha = _load()
    target = _proof(receipt, "nonce_batch_sequencing_v1")
    target["result"]["solvers_agreed"] = False
    target["result"]["passed_queries"] = 0
    target["result"]["ir_hash"] = "forged"
    target["result"]["solvers"] = {"z3": "4.15.4"}
    _reseal(receipt)
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("solvers_agreed" in e for e in errs), errs
    assert any("passed_queries" in e for e in errs), errs
    assert any("ir_hash" in e for e in errs), errs
    assert any("solvers" in e for e in errs), errs


def test_duplicate_receipt_proof_id_fails() -> None:
    """Pass-2 #3: duplicate ids cannot shadow-replace a real proof entry."""
    receipt, manifest, msha = _load()
    receipt["proofs"].append(json.loads(json.dumps(receipt["proofs"][0])))
    _reseal(receipt)
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("duplicate" in e for e in errs), errs


def test_forged_receipt_tool_fails() -> None:
    """Pass-2 #3: the receipt tool must match the source pin."""
    receipt, manifest, msha = _load()
    target = _proof(receipt, "nonce_batch_sequencing_v1")
    target["tool"] = "lean-lake-build"
    _reseal(receipt)
    errs = spr.verify_receipt(receipt, manifest=manifest, manifest_sha256=msha)
    assert any("tool" in e for e in errs), errs


def test_placeholder_proof_is_not_pinned() -> None:
    """Pass-2 #1: cpmm_output_amount_v2.yaml is a placeholder (only invariant is
    `dummy == 0`, amount_out is a `const: 0` HOLE). It is excluded from evidence."""
    assert "cpmm_output_amount_v2" not in spr.EXPECTED_PROOFS
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert "cpmm_output_amount_v2" not in {p["id"] for p in manifest["proofs"]}

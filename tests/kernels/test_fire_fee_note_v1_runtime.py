from __future__ import annotations

from dataclasses import replace

import pytest

from src.fire.registry.bundle_v1 import write_fire_registry_bundle
from src.fire.registry.object_manifest_v1 import fire_manifest_file_sha256, verify_fire_object_manifest
from src.fire.runtime.fee_note_v1 import (
    FeeNoteTerms,
    build_manifest,
    compile_terms,
    holder_collateral_required,
    render_object_card,
    verify_and_settle,
    writer_collateral_required,
)
from src.fire.verifier.cert_v1 import fire_cert_sha256
from src.fire.verifier.settlement_v1 import verify_fire_verifier_receipt


def _manual_payoff(*, n: int, cap: int, witness_final: int) -> int:
    return n * min(witness_final, cap)


def test_compile_terms_emits_expected_artifact_when_cap_binds() -> None:
    terms = FeeNoteTerms(n_notional=10, cap_index=3, source_upper=9)
    artifact = compile_terms(terms)

    assert artifact.terms == terms
    assert artifact.artifact_lower == 0
    assert artifact.artifact_upper == 30
    assert holder_collateral_required(artifact) == 0
    assert writer_collateral_required(artifact) == 30
    assert artifact.cert_sha256 == fire_cert_sha256(artifact.certificate)
    assert artifact.manifest_sha256 == build_manifest(artifact).manifest_hash
    assert artifact.manifest_file_sha256 == fire_manifest_file_sha256(build_manifest(artifact))


def test_compile_terms_emits_expected_artifact_when_source_binds() -> None:
    terms = FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2)
    artifact = compile_terms(terms)

    assert artifact.artifact_lower == 0
    assert artifact.artifact_upper == 20
    assert writer_collateral_required(artifact) == 20


def test_build_manifest_and_render_object_card() -> None:
    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    manifest = build_manifest(artifact)
    card = render_object_card(artifact)

    assert verify_fire_object_manifest(manifest) == (True, None)
    assert manifest.object_name == "FeeNote"
    assert manifest.writer_collateral_required == 20
    assert manifest.witnesses[0].name == "FeeIndexPacket"
    assert "FeeNote v1" in card
    assert "FeeIndex_T" in card
    assert "Instance gate claim evidence:" in card
    assert "ParamOK: implemented" in card
    assert "WindowOK: implemented" in card


def test_verify_and_settle_matches_manual_formula() -> None:
    terms = FeeNoteTerms(n_notional=10, cap_index=3, source_upper=9)
    artifact = compile_terms(terms)
    result = verify_and_settle(
        artifact=artifact,
        witness_final=7,
        holder_posted=0,
        writer_posted=30,
    )

    assert result.ok is True
    assert result.settlement is not None
    expected = _manual_payoff(n=10, cap=3, witness_final=7)
    assert result.settlement.holder_delta == expected
    assert result.settlement.writer_delta == -expected
    assert verify_fire_verifier_receipt(
        result.settlement.verifier_receipt,
        expected_object_hash=artifact.manifest_sha256,
        expected_cert_sha256=artifact.cert_sha256,
        expected_holder_delta=expected,
        expected_writer_delta=-expected,
        expected_command_tag="firev_accept_and_settle",
    ) == (True, None)


def test_verify_and_settle_rejects_artifact_mismatch() -> None:
    artifact = replace(
        compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2)),
        artifact_upper=19,
    )
    result = verify_and_settle(
        artifact=artifact,
        witness_final=2,
        holder_posted=0,
        writer_posted=20,
    )
    assert result.ok is False
    assert result.error == "artifact_mismatch"


def test_verify_and_settle_rejects_ir_hash_mismatch() -> None:
    artifact = replace(
        compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2)),
        ir_hash="bad",
    )
    result = verify_and_settle(
        artifact=artifact,
        witness_final=2,
        holder_posted=0,
        writer_posted=20,
    )
    assert result.ok is False
    assert result.error == "ir_hash_mismatch"


def test_verify_and_settle_rejects_certificate_hash_mismatch() -> None:
    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    result = verify_and_settle(
        artifact=replace(artifact, cert_sha256="sha256:" + "0" * 64),
        witness_final=2,
        holder_posted=0,
        writer_posted=20,
    )
    assert result.ok is False
    assert result.error == "cert_sha_mismatch"


def test_verify_and_settle_rejects_manifest_hash_mismatch() -> None:
    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    result = verify_and_settle(
        artifact=replace(artifact, manifest_sha256="sha256:" + "0" * 64),
        witness_final=2,
        holder_posted=0,
        writer_posted=20,
    )
    assert result.ok is False
    assert result.error == "manifest_sha_mismatch"


def test_verify_and_settle_accepts_persisted_bundle(tmp_path) -> None:
    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    bundle_dir = tmp_path / "fee_bundle"
    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    result = verify_and_settle(
        artifact=artifact,
        witness_final=2,
        holder_posted=0,
        writer_posted=20,
        persisted_bundle_dir=bundle_dir,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_bundle_file_sha256=bundle_file_sha256,
    )

    assert result.ok is True


def test_verify_and_settle_rejects_persisted_bundle_file_hash_mismatch(tmp_path) -> None:
    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    bundle_dir = tmp_path / "fee_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    result = verify_and_settle(
        artifact=artifact,
        witness_final=2,
        holder_posted=0,
        writer_posted=20,
        persisted_bundle_dir=bundle_dir,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_bundle_file_sha256="sha256:" + "0" * 64,
    )

    assert result.ok is False
    assert result.error == "persisted_bundle_invalid:expected_bundle_file_sha_mismatch"


def test_verify_and_settle_rejects_invalid_certificate_tree() -> None:
    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    bad_root = replace(artifact.certificate.root, upper=21)
    bad_cert = replace(artifact.certificate, root=bad_root)
    result = verify_and_settle(
        artifact=replace(artifact, certificate=bad_cert, cert_sha256=fire_cert_sha256(bad_cert)),
        witness_final=2,
        holder_posted=0,
        writer_posted=20,
    )
    assert result.ok is False
    assert result.error is not None
    assert result.error.startswith("certificate_invalid:")


def test_verify_and_settle_rejects_kernel_guard_failure() -> None:
    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    result = verify_and_settle(
        artifact=artifact,
        witness_final=2,
        holder_posted=0,
        writer_posted=19,
    )
    assert result.ok is False
    assert result.error is not None
    assert "guard failed" in result.error


def test_runtime_rejects_bad_types_and_ranges() -> None:
    with pytest.raises(TypeError, match="n_notional must be an int"):
        FeeNoteTerms(n_notional=True, cap_index=0, source_upper=0)
    with pytest.raises(ValueError, match="cap_index out of range"):
        FeeNoteTerms(n_notional=0, cap_index=1001, source_upper=0)
    with pytest.raises(TypeError, match="artifact must be a FeeNoteArtifact"):
        verify_and_settle(artifact="bad", witness_final=0, holder_posted=0, writer_posted=0)  # type: ignore[arg-type]

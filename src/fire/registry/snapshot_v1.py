from __future__ import annotations

from pathlib import Path

from src.fire.registry.bundle_v1 import write_fire_registry_bundle
from src.fire.registry.index_v1 import write_fire_registry_index
from src.fire.registry.release_v1 import write_fire_registry_release_metadata
from src.fire.runtime.burn_boost_call_v1 import (
    BurnBoostCallTerms,
)
from src.fire.runtime.burn_boost_call_v1 import (
    build_manifest as build_burn_manifest,
)
from src.fire.runtime.burn_boost_call_v1 import (
    compile_terms as compile_burn_terms,
)
from src.fire.runtime.burn_boost_call_v1 import (
    render_object_card as render_burn_object_card,
)
from src.fire.runtime.fee_note_v1 import (
    FeeNoteTerms,
)
from src.fire.runtime.fee_note_v1 import (
    build_manifest as build_fee_manifest,
)
from src.fire.runtime.fee_note_v1 import (
    compile_terms as compile_fee_terms,
)
from src.fire.runtime.fee_note_v1 import (
    render_object_card as render_fee_object_card,
)
from src.fire.runtime.lp_loss_cover_v1 import (
    LPLossCoverTerms,
)
from src.fire.runtime.lp_loss_cover_v1 import (
    build_manifest as build_lp_manifest,
)
from src.fire.runtime.lp_loss_cover_v1 import (
    compile_terms as compile_lp_terms,
)
from src.fire.runtime.lp_loss_cover_v1 import (
    render_object_card as render_lp_object_card,
)

SNAPSHOT_REPORT_SCHEMA = "zenodex/fire-registry-snapshot-build-report/v1"


def build_fire_registry_snapshot(
    *,
    output_dir: Path,
    snapshot_name: str,
    signer_privkey: str,
    emit_proof_tree_cert: bool = False,
) -> dict[str, object]:
    out_dir = output_dir.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    burn_dir = out_dir / "burn_boost_call_v1"
    burn_artifact = compile_burn_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    burn_bundle, burn_bundle_file_sha256 = write_fire_registry_bundle(
        burn_dir,
        artifact=burn_artifact,
        build_manifest=build_burn_manifest,
        render_object_card=render_burn_object_card,
        emit_proof_tree_certificate=emit_proof_tree_cert,
    )

    fee_dir = out_dir / "fee_note_v1"
    fee_artifact = compile_fee_terms(FeeNoteTerms(n_notional=11, cap_index=7, source_upper=12))
    fee_bundle, fee_bundle_file_sha256 = write_fire_registry_bundle(
        fee_dir,
        artifact=fee_artifact,
        build_manifest=build_fee_manifest,
        render_object_card=render_fee_object_card,
        emit_proof_tree_certificate=emit_proof_tree_cert,
    )

    lp_dir = out_dir / "lp_loss_cover_v1"
    lp_artifact = compile_lp_terms(
        LPLossCoverTerms(
            n_notional=2,
            deductible=5,
            cap_amount=40,
            hodl_lower=30,
            hodl_upper=80,
            lpv_lower=10,
            lpv_upper=60,
        )
    )
    lp_bundle, lp_bundle_file_sha256 = write_fire_registry_bundle(
        lp_dir,
        artifact=lp_artifact,
        build_manifest=build_lp_manifest,
        render_object_card=render_lp_object_card,
        emit_proof_tree_certificate=emit_proof_tree_cert,
    )

    index_path = out_dir / "fire_registry_index.json"
    index, index_file_sha256 = write_fire_registry_index(
        index_path,
        [burn_dir, fee_dir, lp_dir],
        signer_privkey=signer_privkey,
    )
    release_metadata_path = out_dir / "release_metadata.json"
    release_metadata, release_metadata_file_sha256 = write_fire_registry_release_metadata(
        release_metadata_path,
        snapshot_name=snapshot_name,
        index_path=index_path.name,
        index_hash=index.index_hash,
        index_file_sha256=index_file_sha256,
        require_signature=index.signature is not None,
        instance_gate_summary=index.instance_gate_summary,
        certificate_instance_gate_summary=index.certificate_instance_gate_summary,
        contract_receipts=index.contract_receipts,
        signer_pubkey=index.signer_pubkey,
    )

    return {
        "schema": SNAPSHOT_REPORT_SCHEMA,
        "ok": True,
        "output_dir": str(out_dir),
        "index_path": str(index_path),
        "index_hash": index.index_hash,
        "index_file_sha256": index_file_sha256,
        "release_metadata_path": str(release_metadata_path),
        "release_metadata_file_sha256": release_metadata_file_sha256,
        "snapshot_name": release_metadata.snapshot_name,
        "contract_count": len(index.contract_receipts),
        "instance_gate_summary": index.instance_gate_summary.to_dict(),
        "certificate_instance_gate_summary": index.certificate_instance_gate_summary.to_dict(),
        "compile_receipt_emitted": True,
        "kernel_receipt_emitted": True,
        "kernel_eval_receipt_emitted": True,
        "kernel_replay_receipt_emitted": True,
        "kernel_settlement_receipt_emitted": True,
        "proof_tree_cert_emitted": emit_proof_tree_cert,
        "contracts": [receipt.to_dict() for receipt in index.contract_receipts],
        "signer_pubkey": index.signer_pubkey,
        "signature_present": index.signature is not None,
        "bundles": {
            "burn_boost_call_v1": {
                "dir": str(burn_dir),
                "bundle_hash": burn_bundle.bundle_hash,
                "bundle_file_sha256": burn_bundle_file_sha256,
                "object_hash": burn_artifact.manifest_sha256,
                "compile_receipt_present": burn_bundle.compile_receipt_path is not None,
                "kernel_receipt_present": burn_bundle.kernel_receipt_path is not None,
                "kernel_eval_receipt_present": burn_bundle.kernel_eval_receipt_path is not None,
                "kernel_replay_receipt_present": burn_bundle.kernel_replay_receipt_path is not None,
                "kernel_settlement_receipt_present": burn_bundle.kernel_settlement_receipt_path is not None,
                "proof_tree_cert_present": burn_bundle.proof_tree_certificate_path is not None,
            },
            "fee_note_v1": {
                "dir": str(fee_dir),
                "bundle_hash": fee_bundle.bundle_hash,
                "bundle_file_sha256": fee_bundle_file_sha256,
                "object_hash": fee_artifact.manifest_sha256,
                "compile_receipt_present": fee_bundle.compile_receipt_path is not None,
                "kernel_receipt_present": fee_bundle.kernel_receipt_path is not None,
                "kernel_eval_receipt_present": fee_bundle.kernel_eval_receipt_path is not None,
                "kernel_replay_receipt_present": fee_bundle.kernel_replay_receipt_path is not None,
                "kernel_settlement_receipt_present": fee_bundle.kernel_settlement_receipt_path is not None,
                "proof_tree_cert_present": fee_bundle.proof_tree_certificate_path is not None,
            },
            "lp_loss_cover_v1": {
                "dir": str(lp_dir),
                "bundle_hash": lp_bundle.bundle_hash,
                "bundle_file_sha256": lp_bundle_file_sha256,
                "object_hash": lp_artifact.manifest_sha256,
                "compile_receipt_present": lp_bundle.compile_receipt_path is not None,
                "kernel_receipt_present": lp_bundle.kernel_receipt_path is not None,
                "kernel_eval_receipt_present": lp_bundle.kernel_eval_receipt_path is not None,
                "kernel_replay_receipt_present": lp_bundle.kernel_replay_receipt_path is not None,
                "kernel_settlement_receipt_present": lp_bundle.kernel_settlement_receipt_path is not None,
                "proof_tree_cert_present": lp_bundle.proof_tree_certificate_path is not None,
            },
        },
    }

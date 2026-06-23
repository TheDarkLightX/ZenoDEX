from __future__ import annotations

import json
from pathlib import Path

from src.fire.registry.bundle_v1 import write_fire_registry_bundle
from src.fire.registry.instance_v1 import FireObjectInstanceManifest
from src.fire.registry.object_manifest_v1 import FireObjectManifest
from src.fire.runtime.adapter_manifest_gate_v1 import (
    validate_persisted_bundle_command_args,
    validate_persisted_bundle_settlement_receipt,
)
from src.fire.runtime.burn_boost_call_v1 import BurnBoostCallTerms, build_manifest, compile_terms, render_object_card
from src.fire.runtime.burn_boost_call_v1_native_adapter import IR_HASH
from src.fire.verifier.settlement_v1 import FireVerifierReceipt


def _burn_bundle(tmp_path: Path) -> tuple[Path, str, str, FireObjectManifest, FireObjectInstanceManifest]:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    object_manifest = FireObjectManifest.from_dict(
        json.loads((bundle_dir / "object_manifest.json").read_text(encoding="utf-8"))
    )
    object_instance = FireObjectInstanceManifest.from_dict(
        json.loads((bundle_dir / "instance_manifest.json").read_text(encoding="utf-8"))
    )
    return bundle_dir, bundle_manifest.bundle_hash, bundle_file_sha256, object_manifest, object_instance


def test_validate_persisted_bundle_command_args_rejects_string_artifact_bound(tmp_path: Path) -> None:
    bundle_dir, bundle_hash, bundle_file_sha256, object_manifest, _object_instance = _burn_bundle(tmp_path)

    err = validate_persisted_bundle_command_args(
        state={"artifact_lower": "0", "artifact_upper": object_manifest.artifact_upper},
        args={
            "persisted_bundle_dir": str(bundle_dir),
            "expected_bundle_hash": bundle_hash,
            "expected_bundle_file_sha256": bundle_file_sha256,
            "expected_cert_sha256": object_manifest.cert_sha256,
        },
        expected_ir_hash=IR_HASH,
    )

    assert err == "state artifact bounds invalid: state.artifact_lower must be an int"


def test_validate_persisted_bundle_settlement_receipt_rejects_bool_delta(tmp_path: Path) -> None:
    bundle_dir, bundle_hash, bundle_file_sha256, object_manifest, object_instance = _burn_bundle(tmp_path)
    receipt = FireVerifierReceipt.build(
        object_hash=object_manifest.manifest_hash,
        instance_hash=object_instance.instance_hash,
        cert_sha256=object_manifest.cert_sha256,
        holder_delta=0,
        writer_delta=0,
        command_tag="firev_accept_and_settle",
        object_name=object_manifest.object_name,
        object_version=object_manifest.object_version,
        bundle_hash=bundle_hash,
    )

    err = validate_persisted_bundle_settlement_receipt(
        state_after={"holder_delta": False, "writer_delta": 0},
        args={
            "persisted_bundle_dir": str(bundle_dir),
            "expected_bundle_hash": bundle_hash,
            "expected_bundle_file_sha256": bundle_file_sha256,
            "verifier_receipt": receipt.to_dict(),
        },
        expected_ir_hash=IR_HASH,
    )

    assert err == "state delta invalid: state_after.holder_delta must be an int"

#!/usr/bin/env python3
"""Replay-check the ZenoCover lp_loss_cover_v1 FIRE bundle."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.fire.registry.bundle_v1 import (  # noqa: E402
    load_fire_registry_bundle,
    verify_fire_registry_bundle,
)
from src.fire.registry.replay_input_v1 import load_fire_replay_input  # noqa: E402
from src.fire.runtime.lp_loss_cover_v1 import (  # noqa: E402
    LPLossCoverTerms,
    compile_terms,
    verify_and_settle,
    writer_collateral_required,
)
from src.fire.verifier.proof_tree_cert_v1 import (  # noqa: E402
    verify_fire_proof_tree_certificate_file,
)

REPORT_SCHEMA = "zenodex.zenocover.lp_loss_cover_replay_report.v0"
DEFAULT_BUNDLE_DIR = ROOT / "docs" / "fire_registry" / "devnet_v1" / "lp_loss_cover_v1"


def validate_zenocover_lp_loss_cover_bundle(
    bundle_dir: str | Path,
    *,
    expected_bundle_hash: str | None = None,
    expected_bundle_file_sha256: str | None = None,
) -> dict[str, Any]:
    root = Path(bundle_dir)
    errors: list[str] = []
    ok, err, bundle_manifest, object_manifest, object_instance, _object_lock = verify_fire_registry_bundle(
        root,
        expected_bundle_hash=expected_bundle_hash,
        expected_bundle_file_sha256=expected_bundle_file_sha256,
    )
    if not ok or bundle_manifest is None or object_manifest is None or object_instance is None:
        return _report(root, errors=[err or "bundle verification failed"])

    if object_manifest.object_name != "LPLossCover":
        errors.append("object_name must be LPLossCover")
    if object_manifest.object_version != "v1":
        errors.append("object_version must be v1")
    if object_manifest.object_family != "capped_lp_loss_cover":
        errors.append("object_family must be capped_lp_loss_cover")

    try:
        bundle_manifest_loaded, bundle_file_sha256, _manifest, _instance, _lock = load_fire_registry_bundle(root)
        if bundle_manifest_loaded.bundle_hash != bundle_manifest.bundle_hash:
            errors.append("loaded bundle hash mismatch")
    except (FileNotFoundError, OSError, TypeError, ValueError, KeyError, json.JSONDecodeError) as exc:
        return _report(root, errors=[*errors, f"bundle reload failed: {exc}"])

    if bundle_manifest.proof_tree_certificate_path is None:
        errors.append("proof_tree_certificate_path is required")
        proof_tree_report = None
    else:
        proof_ok, proof_err, proof_verification = verify_fire_proof_tree_certificate_file(
            root / bundle_manifest.proof_tree_certificate_path,
            expected_object_hash=object_manifest.manifest_hash,
            expected_instance_hash=object_instance.instance_hash,
            expected_certificate_sha256=object_manifest.cert_sha256,
        )
        if not proof_ok or proof_verification is None:
            errors.append(f"proof tree certificate rejected: {proof_err or 'unknown'}")
            proof_tree_report = None
        else:
            proof_tree_report = proof_verification.to_report_dict()

    if bundle_manifest.replay_input_path is None:
        return _report(root, errors=[*errors, "replay_input_path is required"])

    try:
        replay_input, replay_input_file_sha256 = load_fire_replay_input(root / bundle_manifest.replay_input_path)
        params_by_name = {item.name: item.value for item in object_instance.parameters}
        terms = _terms_from_instance_parameters(params_by_name)
        artifact = compile_terms(terms)
        replay_result = verify_and_settle(
            artifact=artifact,
            witness_hodl_final=_int_witness(replay_input.witness_inputs, "witness_hodl_final"),
            witness_lpv_final=_int_witness(replay_input.witness_inputs, "witness_lpv_final"),
            holder_posted=replay_input.holder_posted,
            writer_posted=replay_input.writer_posted,
            persisted_bundle_dir=root,
            expected_bundle_hash=bundle_manifest.bundle_hash,
            expected_bundle_file_sha256=bundle_file_sha256,
        )
    except (FileNotFoundError, OSError, TypeError, ValueError, KeyError, json.JSONDecodeError) as exc:
        return _report(root, errors=[*errors, f"replay failed: {exc}"])

    if not replay_result.ok or replay_result.settlement is None:
        errors.append(f"settlement rejected: {replay_result.error or 'unknown'}")
        settlement_facts: dict[str, Any] = {}
    else:
        settlement = replay_result.settlement
        settlement_facts = {
            "holder_delta": settlement.holder_delta,
            "writer_delta": settlement.writer_delta,
            "delta_conservation": settlement.holder_delta + settlement.writer_delta == 0,
            "writer_collateral_required": writer_collateral_required(artifact),
            "writer_posted": replay_input.writer_posted,
        }
        if settlement.holder_delta + settlement.writer_delta != 0:
            errors.append("settlement deltas do not conserve value")

    return _report(
        root,
        errors=errors,
        bundle_hash=bundle_manifest.bundle_hash,
        bundle_file_sha256=bundle_file_sha256,
        object_hash=object_manifest.manifest_hash,
        instance_hash=object_instance.instance_hash,
        cert_sha256=object_manifest.cert_sha256,
        artifact_upper=object_manifest.artifact_upper,
        proof_tree_evidence_floor=None if proof_tree_report is None else proof_tree_report.get("evidence_floor"),
        replay_input_file_sha256=replay_input_file_sha256,
        settlement=settlement_facts,
    )


def _terms_from_instance_parameters(params: Mapping[str, int]) -> LPLossCoverTerms:
    return LPLossCoverTerms(
        n_notional=int(params["n_notional"]),
        deductible=int(params["deductible"]),
        cap_amount=int(params["cap_amount"]),
        hodl_lower=int(params["hodl_lower"]),
        hodl_upper=int(params["hodl_upper"]),
        lpv_lower=int(params["lpv_lower"]),
        lpv_upper=int(params["lpv_upper"]),
    )


def _int_witness(witness_inputs: Mapping[str, int], name: str) -> int:
    value = witness_inputs[name]
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _report(bundle_dir: Path, *, errors: list[str], **facts: Any) -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "bundle_dir": str(bundle_dir.resolve()),
        **facts,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle-dir", type=Path, default=DEFAULT_BUNDLE_DIR)
    parser.add_argument("--expected-bundle-hash")
    parser.add_argument("--expected-bundle-file-sha256")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = validate_zenocover_lp_loss_cover_bundle(
        args.bundle_dir,
        expected_bundle_hash=args.expected_bundle_hash,
        expected_bundle_file_sha256=args.expected_bundle_file_sha256,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

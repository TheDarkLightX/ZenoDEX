#!/usr/bin/env python3
"""Verify a ZenoLedger v0 header/body sequence."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_app_hash_history import (  # noqa: E402
    app_hash_history_merkle_root_v0,
    checked_range_hash_v0,
    checked_range_summary_v0,
)
from src.integration.zeno_ledger_profile import (  # noqa: E402
    validate_checkpoint_admission_v0,
    validate_zeno_ledger_profile_v0,
)
from src.integration.zeno_ledger_signature import (  # noqa: E402
    PROOF_VERIFICATION_REPORT_PAYLOAD_KIND_V0,
    infer_artifact_hash_v0,
)
from src.integration.zeno_ledger_signer_registry import verify_signature_quorum_v0  # noqa: E402
from src.integration.zeno_ledger_v0 import (  # noqa: E402
    canonical_header_hash_v0,
    validate_checkpoint_header_binding_v0,
    validate_header_body_roots_v0,
    validate_header_v0,
    validate_proof_metadata_header_binding_v0,
    validate_proof_metadata_v0,
)
from tools.check_recursive_lifecycle_admission import (  # noqa: E402
    PROOF_PROFILE_RECURSIVE,
    PROOF_TYPE_RECURSIVE,
    validate_recursive_lifecycle_admission_packet_v1,
)

ZERO_ROOT = "0x" + "00" * 32
REPORT_SCHEMA = "zenodex.zeno_ledger.verify_report.v0"
RISC0_PROOF_METADATA_REPORT_SCHEMA = "zenodex.zeno_ledger.risc0_proof_metadata_report.v0"
TEE_PROOF_METADATA_REPORT_SCHEMA = "zenodex.zeno_ledger.tee_proof_metadata_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def verify_zeno_ledger_v0(
    *,
    headers_dir: Path,
    bodies_dir: Path,
    checkpoints_dir: Path | None,
    profile_path: Path | None,
    from_height: int,
    to_height: int,
    trusted_prev_header_hash: str = ZERO_ROOT,
    proof_metadata_dir: Path | None = None,
    proof_verification_report_dir: Path | None = None,
    require_proof_verification_report: bool = False,
    require_proof_verification_report_signature: bool = False,
    proof_verification_report_registry_path: Path | None = None,
    proof_verification_report_envelope_dir: Path | None = None,
    recursive_lifecycle_admission_dir: Path | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    checked_heights: list[int] = []
    app_hashes_by_height: list[dict[str, Any]] = []
    proof_metadata_checked_heights: list[int] = []
    proof_verification_checked_heights: list[int] = []
    proof_verification_signature_checked_heights: list[int] = []
    proof_verification_signature_quorum_reports: list[dict[str, Any]] = []
    recursive_lifecycle_admission_checked_heights: list[int] = []
    last_header_hash: str | None = None
    last_post_state_root: str | None = None
    last_app_hash: str | None = None
    expected_prev_hash = trusted_prev_header_hash

    if from_height < 0:
        errors.append("from_height_must_be_nonnegative")
    if to_height < from_height:
        errors.append("to_height_before_from_height")
    if not headers_dir.is_dir():
        errors.append("headers_dir_missing")
    if not bodies_dir.is_dir():
        errors.append("bodies_dir_missing")
    if proof_metadata_dir is not None and not proof_metadata_dir.is_dir():
        errors.append("proof_metadata_dir_missing")
    if proof_verification_report_dir is not None and not proof_verification_report_dir.is_dir():
        errors.append("proof_verification_report_dir_missing")
    if proof_verification_report_registry_path is not None and not proof_verification_report_registry_path.is_file():
        errors.append("proof_verification_report_registry_missing")
    if proof_verification_report_envelope_dir is not None and not proof_verification_report_envelope_dir.is_dir():
        errors.append("proof_verification_report_envelope_dir_missing")
    if recursive_lifecycle_admission_dir is not None and not recursive_lifecycle_admission_dir.is_dir():
        errors.append("recursive_lifecycle_admission_dir_missing")
    if require_proof_verification_report and proof_verification_report_dir is None:
        errors.append("require_proof_verification_report_requires_dir")
    if require_proof_verification_report_signature and (
        proof_verification_report_registry_path is None or proof_verification_report_envelope_dir is None
    ):
        errors.append("require_proof_verification_report_signature_requires_registry_and_envelope_dir")
    if proof_verification_report_dir is not None and proof_metadata_dir is None:
        errors.append("proof_verification_report_requires_proof_metadata_dir")
    if (proof_verification_report_registry_path is None) != (proof_verification_report_envelope_dir is None):
        errors.append("proof_verification_report_signature_requires_registry_and_envelope_dir")
    if proof_verification_report_registry_path is not None and proof_verification_report_dir is None:
        errors.append("proof_verification_report_signature_requires_report_dir")
    proof_verification_report_registry: dict[str, Any] | None = None
    if proof_verification_report_registry_path is not None and proof_verification_report_registry_path.is_file():
        try:
            proof_verification_report_registry = dict(_load_json_object(proof_verification_report_registry_path))
        except Exception as exc:
            errors.append(f"proof_verification_report_registry_invalid:{exc}")
    profile: dict[str, Any] | None = None
    if profile_path is not None:
        if checkpoints_dir is None:
            errors.append("profile_requires_checkpoints_dir")
        elif not profile_path.is_file():
            errors.append("profile_missing")
        else:
            try:
                profile = dict(_load_json_object(profile_path))
                validate_zeno_ledger_profile_v0(profile)
                bridge_policy = profile.get("bridge_policy")
                bridge_requires_proof = (
                    isinstance(bridge_policy, Mapping)
                    and bool(bridge_policy.get("requires_proof_journal"))
                )
                profile_requires_proof = bool(profile.get("proof_required")) or bridge_requires_proof
                if profile_requires_proof and proof_metadata_dir is None:
                    errors.append("profile_requires_proof_metadata_dir")
                if profile_requires_proof and proof_verification_report_dir is None:
                    errors.append("profile_requires_proof_verification_report_dir")
            except Exception as exc:
                errors.append(f"profile_invalid:{exc}")
    if errors:
        return _report(
            errors=errors,
            checked_heights=checked_heights,
            app_hashes_by_height=app_hashes_by_height,
            proof_metadata_checked_heights=proof_metadata_checked_heights,
            proof_verification_checked_heights=proof_verification_checked_heights,
            proof_verification_signature_checked_heights=proof_verification_signature_checked_heights,
            proof_verification_signature_quorum_reports=proof_verification_signature_quorum_reports,
            recursive_lifecycle_admission_checked_heights=recursive_lifecycle_admission_checked_heights,
            last_header_hash=last_header_hash,
            last_post_state_root=last_post_state_root,
            last_app_hash=last_app_hash,
        )

    for height in range(from_height, to_height + 1):
        header_path = headers_dir / f"{height}.json"
        body_path = bodies_dir / f"{height}.json"
        if not header_path.is_file():
            errors.append(f"header_missing:{height}")
            break
        if not body_path.is_file():
            errors.append(f"body_missing:{height}")
            break

        try:
            header = dict(_load_json_object(header_path))
            body = dict(_load_json_object(body_path))
            validate_header_v0(header)
            if header["height"] != height:
                raise ValueError(f"header height mismatch for file {height}")
            if header["prev_header_hash"] != expected_prev_hash:
                raise ValueError(f"prev_header_hash mismatch at height {height}")
            validate_header_body_roots_v0(header, body)
            if proof_metadata_dir is not None:
                proof_metadata_path = proof_metadata_dir / f"{height}.json"
                if not proof_metadata_path.is_file():
                    raise ValueError(f"proof metadata missing at height {height}")
                proof_metadata = dict(_load_json_object(proof_metadata_path))
                validate_proof_metadata_header_binding_v0(proof_metadata, header)
                proof_metadata_checked_heights.append(height)
                proof_verification_report: dict[str, Any] | None = None
                if proof_verification_report_dir is not None:
                    report_path = proof_verification_report_dir / f"{height}.json"
                    if not report_path.is_file():
                        raise ValueError(f"proof verification report missing at height {height}")
                    proof_verification_report = dict(_load_json_object(report_path))
                    validate_proof_verification_report_v0(
                        report=proof_verification_report,
                        proof_metadata=proof_metadata,
                        header=header,
                    )
                    proof_verification_checked_heights.append(height)
                    if proof_verification_report_registry is not None:
                        if proof_verification_report_envelope_dir is None:
                            raise ValueError("proof verification report envelope dir missing")
                        envelope_path = proof_verification_report_envelope_dir / f"{height}.json"
                        envelopes = _load_proof_verification_report_envelopes_v0(envelope_path)
                        payload_hash = infer_artifact_hash_v0(
                            artifact=proof_verification_report,
                            payload_kind=PROOF_VERIFICATION_REPORT_PAYLOAD_KIND_V0,
                        )
                        quorum_report = verify_signature_quorum_v0(
                            registry=proof_verification_report_registry,
                            payload_kind=PROOF_VERIFICATION_REPORT_PAYLOAD_KIND_V0,
                            payload_hash=payload_hash,
                            envelopes=envelopes,
                        )
                        proof_verification_signature_checked_heights.append(height)
                        proof_verification_signature_quorum_reports.append(
                            {
                                "height": height,
                                "registry_hash": quorum_report["registry_hash"],
                                "quorum_report_hash": quorum_report["quorum_report_hash"],
                                "accepted_weight": quorum_report["accepted_weight"],
                                "threshold": quorum_report["threshold"],
                            }
                        )
                elif proof_metadata.get("proof_kind") == "recursive_epoch_v0":
                    raise ValueError("recursive proof verification report required")
                if proof_metadata.get("proof_kind") == "recursive_epoch_v0":
                    if proof_verification_report is None:
                        raise ValueError("recursive proof verification report required")
                    _validate_recursive_lifecycle_admission_for_height_v0(
                        height=height,
                        recursive_lifecycle_admission_dir=recursive_lifecycle_admission_dir,
                        proof_metadata=proof_metadata,
                        proof_verification_report=proof_verification_report,
                        header=header,
                    )
                    recursive_lifecycle_admission_checked_heights.append(height)
            if checkpoints_dir is not None:
                checkpoint_path = checkpoints_dir / f"{height}.json"
                if not checkpoint_path.is_file():
                    raise ValueError(f"checkpoint missing at height {height}")
                checkpoint = dict(_load_json_object(checkpoint_path))
                validate_checkpoint_header_binding_v0(checkpoint, header)
                if profile is not None:
                    validate_checkpoint_admission_v0(checkpoint=checkpoint, profile=profile)
            last_header_hash = canonical_header_hash_v0(header)
            last_post_state_root = str(header["post_state_root"])
            last_app_hash = str(header["app_hash"])
            expected_prev_hash = last_header_hash
            checked_heights.append(height)
            app_hashes_by_height.append({"height": height, "app_hash": last_app_hash})
        except Exception as exc:
            errors.append(f"height_{height}_invalid:{exc}")
            break

    return _report(
        errors=errors,
        checked_heights=checked_heights,
        app_hashes_by_height=app_hashes_by_height,
        proof_metadata_checked_heights=proof_metadata_checked_heights,
        proof_verification_checked_heights=proof_verification_checked_heights,
        proof_verification_signature_checked_heights=proof_verification_signature_checked_heights,
        proof_verification_signature_quorum_reports=proof_verification_signature_quorum_reports,
        recursive_lifecycle_admission_checked_heights=recursive_lifecycle_admission_checked_heights,
        last_header_hash=last_header_hash,
        last_post_state_root=last_post_state_root,
        last_app_hash=last_app_hash,
    )


def _report(
    *,
    errors: list[str],
    checked_heights: list[int],
    app_hashes_by_height: list[dict[str, Any]],
    proof_metadata_checked_heights: list[int],
    proof_verification_checked_heights: list[int],
    proof_verification_signature_checked_heights: list[int],
    proof_verification_signature_quorum_reports: list[dict[str, Any]],
    recursive_lifecycle_admission_checked_heights: list[int],
    last_header_hash: str | None,
    last_post_state_root: str | None,
    last_app_hash: str | None,
) -> dict[str, Any]:
    ok = not errors
    checked_range = checked_range_summary_v0(checked_heights) if checked_heights else None
    return {
        "schema": REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "checked_heights": checked_heights,
        "checked_range": checked_range,
        "checked_range_hash": checked_range_hash_v0(checked_range) if checked_range is not None else None,
        "app_hashes_by_height": app_hashes_by_height,
        "app_hash_history_root": (
            app_hash_history_merkle_root_v0(app_hashes_by_height) if app_hashes_by_height else None
        ),
        "proof_metadata_checked_heights": proof_metadata_checked_heights,
        "proof_verification_checked_heights": proof_verification_checked_heights,
        "proof_verification_signature_checked_heights": proof_verification_signature_checked_heights,
        "proof_verification_signature_quorum_reports": proof_verification_signature_quorum_reports,
        "recursive_lifecycle_admission_checked_heights": recursive_lifecycle_admission_checked_heights,
        "last_header_hash": last_header_hash,
        "last_post_state_root": last_post_state_root,
        "last_app_hash": last_app_hash,
        "errors": errors,
    }


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty str")
    return value


def _load_proof_verification_report_envelopes_v0(path: Path) -> list[Mapping[str, Any]]:
    if not path.is_file():
        raise ValueError(f"proof verification report signature envelopes missing at height {path.stem}")
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("proof verification report signature envelope bundle must be a JSON object")
    if obj.get("schema") != "zenodex.zeno_ledger.proof_verification_report_envelopes.v0":
        raise ValueError("proof verification report signature envelope bundle schema mismatch")
    raw_envelopes = obj.get("envelopes")
    if not isinstance(raw_envelopes, list) or not raw_envelopes:
        raise ValueError("proof verification report signature envelope bundle requires envelopes")
    envelopes: list[Mapping[str, Any]] = []
    for index, raw_envelope in enumerate(raw_envelopes):
        if not isinstance(raw_envelope, Mapping):
            raise ValueError(f"proof verification report signature envelopes[{index}] must be an object")
        envelopes.append(raw_envelope)
    return envelopes


def _validate_recursive_lifecycle_admission_for_height_v0(
    *,
    height: int,
    recursive_lifecycle_admission_dir: Path | None,
    proof_metadata: Mapping[str, Any],
    proof_verification_report: Mapping[str, Any],
    header: Mapping[str, Any],
) -> None:
    if recursive_lifecycle_admission_dir is None:
        raise ValueError("recursive lifecycle admission packet dir required")
    packet_path = recursive_lifecycle_admission_dir / f"{height}.json"
    if not packet_path.is_file():
        raise ValueError(f"recursive lifecycle admission packet missing at height {height}")

    packet = dict(_load_json_object(packet_path))
    admission_report = validate_recursive_lifecycle_admission_packet_v1(packet)
    if admission_report.get("ok") is not True:
        errors = admission_report.get("errors")
        if not isinstance(errors, list):
            errors = ["invalid recursive lifecycle admission report"]
        raise ValueError("recursive lifecycle admission rejected: " + "; ".join(str(error) for error in errors))

    packet_header = _load_mapping(packet.get("header"), name="recursive_lifecycle_admission.header")
    packet_meta = _load_mapping(packet.get("proof_meta"), name="recursive_lifecycle_admission.proof_meta")
    for key in (
        "post_state_root",
        "tx_root",
        "evidence_root",
        "data_availability_root",
    ):
        _require_same_hex32_no_prefix(
            actual=packet_header.get(key),
            expected=header.get(key),
            name=f"recursive lifecycle admission/header {key}",
        )
    _require_same_hex32_no_prefix(
        actual=packet_header.get("feature_suite_hash"),
        expected=proof_metadata.get("feature_suite_hash"),
        name="recursive lifecycle admission/proof_metadata feature_suite_hash",
    )
    _require_same_hex32_no_prefix(
        actual=packet_meta.get("aggregate_asset_delta_root"),
        expected=admission_report.get("computed_aggregate_asset_delta_root"),
        name="recursive lifecycle admission/aggregate_asset_delta_root",
    )
    _validate_recursive_report_packet_binding_v0(
        report=proof_verification_report,
        packet=packet,
        packet_meta=packet_meta,
    )


def _require_same_hex32_no_prefix(*, actual: object, expected: object, name: str) -> None:
    actual_hex = _hex32_no_prefix(actual, name=f"{name}.actual")
    expected_hex = _hex32_no_prefix(expected, name=f"{name}.expected")
    if actual_hex != expected_hex:
        raise ValueError(f"{name} mismatch")


def _validate_recursive_report_packet_binding_v0(
    *,
    report: Mapping[str, Any],
    packet: Mapping[str, Any],
    packet_meta: Mapping[str, Any],
) -> None:
    if _require_bool(report.get("risc0_verified"), name="recursive proof report.risc0_verified") is not True:
        raise ValueError("recursive proof report must be verifier-backed")
    if _require_str(report.get("proof_type"), name="recursive proof report.proof_type") != PROOF_TYPE_RECURSIVE:
        raise ValueError("recursive proof report proof_type mismatch")
    if _require_str(report.get("proof_profile"), name="recursive proof report.proof_profile") != PROOF_PROFILE_RECURSIVE:
        raise ValueError("recursive proof report proof_profile mismatch")
    if packet.get("proof_type") != report.get("proof_type"):
        raise ValueError("recursive lifecycle admission/proof report proof_type mismatch")
    if packet.get("proof_profile") != report.get("proof_profile"):
        raise ValueError("recursive lifecycle admission/proof report proof_profile mismatch")
    _require_same_int(
        actual=packet_meta.get("child_count"),
        expected=report.get("child_count"),
        name="recursive lifecycle admission/proof report child_count",
    )
    for key in (
        "post_state_root",
        "tx_root",
        "evidence_root",
        "receipt_root",
        "aggregate_asset_delta_root",
        "data_availability_root",
        "public_policy_hash",
        "feature_suite_hash",
    ):
        _require_same_hex32_no_prefix(
            actual=packet_meta.get(key),
            expected=report.get(key),
            name=f"recursive lifecycle admission/proof report {key}",
        )


def _require_same_int(*, actual: object, expected: object, name: str) -> None:
    actual_int = _require_nonnegative_int(actual, name=f"{name}.actual")
    expected_int = _require_nonnegative_int(expected, name=f"{name}.expected")
    if actual_int != expected_int:
        raise ValueError(f"{name} mismatch")


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be a nonnegative int")
    if value < 0:
        raise ValueError(f"{name} must be a nonnegative int")
    return int(value)


def _require_positive_int(value: object, *, name: str) -> int:
    out = _require_nonnegative_int(value, name=name)
    if out <= 0:
        raise ValueError(f"{name} must be a positive int")
    return out


def _hex32_no_prefix(value: object, *, name: str) -> str:
    raw = _require_str(value, name=name)
    raw = raw[2:] if raw.startswith("0x") else raw
    if len(raw) != 64:
        raise ValueError(f"{name} must be a hex32 string")
    try:
        bytes.fromhex(raw)
    except ValueError as exc:
        raise ValueError(f"{name} must be a hex32 string") from exc
    return raw.lower()


def validate_proof_verification_report_v0(
    *,
    report: Mapping[str, Any],
    proof_metadata: Mapping[str, Any],
    header: Mapping[str, Any],
) -> None:
    validate_header_v0(dict(header))
    metadata = dict(proof_metadata)
    validate_proof_metadata_v0(metadata)
    obj = dict(_load_mapping(report, name="proof_verification_report"))
    schema = _require_str(obj.get("schema"), name="proof_verification_report.schema")
    if schema not in {RISC0_PROOF_METADATA_REPORT_SCHEMA, TEE_PROOF_METADATA_REPORT_SCHEMA}:
        raise ValueError("proof_verification_report schema is not supported")
    if _require_bool(obj.get("ok"), name="proof_verification_report.ok") is not True:
        raise ValueError("proof_verification_report must be accepted")
    if _require_bool(obj.get("header_bound"), name="proof_verification_report.header_bound") is not True:
        raise ValueError("proof_verification_report must be header-bound")
    for key in ("proof_kind", "program_id", "verifier_id", "toolchain_lock_hash"):
        if obj.get(key) != metadata.get(key):
            raise ValueError(f"proof_verification_report/metadata {key} mismatch")
    if obj["proof_journal_hash"] != header["proof_journal_hash"]:
        raise ValueError("proof_verification_report/header proof_journal_hash mismatch")
    proof_kind = metadata["proof_kind"]
    if proof_kind == "risc0_zkvm_v0":
        if schema != RISC0_PROOF_METADATA_REPORT_SCHEMA:
            raise ValueError("risc0 proof metadata requires risc0 verification report")
        if _require_bool(obj.get("body_checked"), name="proof_verification_report.body_checked") is not True:
            raise ValueError("risc0 proof verification report must be body-checked")
        post_app_checked = _require_bool(
            obj.get("post_app_hash_checked"),
            name="proof_verification_report.post_app_hash_checked",
        )
        post_state_checked = _require_bool(
            obj.get("post_state_root_checked"),
            name="proof_verification_report.post_state_root_checked",
        )
        if post_app_checked is not True and post_state_checked is not True:
            raise ValueError("risc0 proof verification report must bind post_app_hash to header")
        if _require_bool(obj.get("risc0_verified"), name="proof_verification_report.risc0_verified") is not True:
            raise ValueError("risc0 proof verification report must be verifier-backed")
    elif proof_kind == "recursive_epoch_v0":
        if schema != RISC0_PROOF_METADATA_REPORT_SCHEMA:
            raise ValueError("recursive proof metadata requires risc0 verification report")
        if _require_bool(obj.get("body_checked"), name="proof_verification_report.body_checked") is not True:
            raise ValueError("recursive proof verification report must be body-checked")
        if _require_bool(
            obj.get("post_state_root_checked"),
            name="proof_verification_report.post_state_root_checked",
        ) is not True:
            raise ValueError("recursive proof verification report must bind post_state_root to header")
        if _require_bool(obj.get("risc0_verified"), name="proof_verification_report.risc0_verified") is not True:
            raise ValueError("recursive proof verification report must be verifier-backed")
        if _require_str(obj.get("proof_type"), name="proof_verification_report.proof_type") != PROOF_TYPE_RECURSIVE:
            raise ValueError("recursive proof verification report proof_type mismatch")
        if (
            _require_str(obj.get("proof_profile"), name="proof_verification_report.proof_profile")
            != PROOF_PROFILE_RECURSIVE
        ):
            raise ValueError("recursive proof verification report proof_profile mismatch")
        _require_positive_int(obj.get("child_count"), name="proof_verification_report.child_count")
        if obj.get("chain_id") != metadata.get("chain_id"):
            raise ValueError("proof_verification_report/metadata chain_id mismatch")
        _require_same_hex32_no_prefix(
            actual=obj.get("pre_state_root"),
            expected=metadata.get("pre_state_root"),
            name="proof_verification_report/metadata pre_state_root",
        )
        for key in (
            "post_state_root",
            "tx_root",
            "evidence_root",
            "data_availability_root",
        ):
            _require_same_hex32_no_prefix(
                actual=obj.get(key),
                expected=header.get(key),
                name=f"proof_verification_report/header {key}",
            )
        for key in (
            "feature_suite_hash",
            "dependency_lock_hash",
            "toolchain_lock_hash",
        ):
            _require_same_hex32_no_prefix(
                actual=obj.get(key),
                expected=metadata.get(key),
                name=f"proof_verification_report/metadata {key}",
            )
        for key in (
            "statement_hash",
            "verifier_set_root",
            "allowed_authority_roots_root",
            "child_verification_claims_root",
            "child_journals_root",
            "child_effect_summaries_root",
            "receipt_root",
            "accepted_receipts_root",
            "rejected_receipts_root",
            "aggregate_asset_delta_root",
            "cross_shard_outbox_root",
            "cross_shard_inbox_root",
            "carry_queue_pre_root",
            "carry_queue_post_root",
            "conflict_schedule_hash",
            "public_policy_hash",
        ):
            _hex32_no_prefix(obj.get(key), name=f"proof_verification_report.{key}")
    elif proof_kind == "tee_attestation_v0":
        if schema != TEE_PROOF_METADATA_REPORT_SCHEMA:
            raise ValueError("TEE proof metadata requires TEE verification report")
        if _require_bool(obj.get("tee_verified"), name="proof_verification_report.tee_verified") is not True:
            raise ValueError("TEE proof verification report must be verifier-backed")
        if obj.get("tee_measurement_hash") != metadata.get("tee_measurement_hash"):
            raise ValueError("proof_verification_report/metadata tee_measurement_hash mismatch")
    else:
        raise ValueError("proof verification report is only defined for Risc0 and TEE metadata")


def _load_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{name} must be a JSON object")
    return value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify a ZenoLedger v0 header/body sequence")
    parser.add_argument("--headers-dir", required=True, type=Path)
    parser.add_argument("--bodies-dir", required=True, type=Path)
    parser.add_argument("--checkpoints-dir", type=Path)
    parser.add_argument("--proof-metadata-dir", type=Path)
    parser.add_argument("--proof-verification-report-dir", type=Path)
    parser.add_argument("--require-proof-verification-report", action="store_true")
    parser.add_argument("--require-proof-verification-report-signature", action="store_true")
    parser.add_argument("--proof-verification-report-registry", type=Path)
    parser.add_argument("--proof-verification-report-envelope-dir", type=Path)
    parser.add_argument("--recursive-lifecycle-admission-dir", type=Path)
    parser.add_argument("--profile", type=Path)
    parser.add_argument("--from-height", required=True, type=int)
    parser.add_argument("--to-height", required=True, type=int)
    parser.add_argument("--trusted-prev-header-hash", default=ZERO_ROOT)
    args = parser.parse_args(argv)

    result = verify_zeno_ledger_v0(
        headers_dir=args.headers_dir,
        bodies_dir=args.bodies_dir,
        checkpoints_dir=args.checkpoints_dir,
        profile_path=args.profile,
        from_height=args.from_height,
        to_height=args.to_height,
        trusted_prev_header_hash=args.trusted_prev_header_hash,
        proof_metadata_dir=args.proof_metadata_dir,
        proof_verification_report_dir=args.proof_verification_report_dir,
        require_proof_verification_report=bool(args.require_proof_verification_report),
        require_proof_verification_report_signature=bool(args.require_proof_verification_report_signature),
        proof_verification_report_registry_path=args.proof_verification_report_registry,
        proof_verification_report_envelope_dir=args.proof_verification_report_envelope_dir,
        recursive_lifecycle_admission_dir=args.recursive_lifecycle_admission_dir,
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Check the path-redacted temporary ZRPF V1 Spot adapter evidence.

Final RISC0 receipt cryptography must be verified by the Rust harness. This
checker validates the evidence schema, pinned bytes, and local source closures.
It does not parse or cryptographically verify a RISC0 receipt seal.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

if __package__:
    from tools import zrpf_v1_spot_adapter_evidence_support as support
else:
    import zrpf_v1_spot_adapter_evidence_support as support  # type: ignore[no-redef]

REPO_ROOT = support.REPO_ROOT
DEFAULT_MANIFEST = support.DEFAULT_MANIFEST
REPORT_SCHEMA = support.REPORT_SCHEMA
EXPECTED_SCHEMA = support.EXPECTED_SCHEMA
MAX_MANIFEST_BYTES = support.MAX_MANIFEST_BYTES
EXPECTED_FIELDS = support.EXPECTED_FIELDS
EXPECTED_CONTROL_FIELDS = support.EXPECTED_CONTROL_FIELDS
EXPECTED_SOURCE_FIELDS = support.EXPECTED_SOURCE_FIELDS
EXPECTED_NON_CLAIMS = support.EXPECTED_NON_CLAIMS
EXPECTED_ARTIFACTS = support.EXPECTED_ARTIFACTS
_validate_redaction = support.validate_redaction
_validate_source_closure = support.validate_source_closure
verify_optional_artifact = support.verify_optional_artifact
_canonical_sha256 = support.canonical_sha256
_is_digest = support.is_digest


class EvidenceInputError(ValueError):
    """The manifest JSON is ambiguous or outside the accepted grammar."""


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise EvidenceInputError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise EvidenceInputError(f"non-finite JSON number: {value}")


def load_manifest(path: Path = DEFAULT_MANIFEST) -> tuple[Any | None, list[str]]:
    try:
        raw = path.read_bytes()
    except OSError:
        return None, ["manifest read failed"]
    if not raw or len(raw) > MAX_MANIFEST_BYTES:
        return None, ["manifest byte length is empty or exceeds the cap"]
    try:
        document = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_unique_object,
            parse_constant=_reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, EvidenceInputError) as exc:
        return None, [f"manifest JSON rejected: {exc}"]
    return document, []


def validate_manifest(
    document: Any,
    *,
    repo_root: Path = REPO_ROOT,
) -> dict[str, Any]:
    errors: list[str] = []
    if not isinstance(document, dict):
        return _report(["manifest root must be an object"], 0, "")

    _validate_object_shapes(document, errors)
    canonical_sha256 = _canonical_sha256(document)
    is_final = document.get("status") == "temporary_local_receipt_evidence"
    if not is_final:
        errors.append("evidence record is pending final rebuild")
    elif not support.EXPECTED_FINAL_CANONICAL_SHA256:
        errors.append("final reviewed manifest SHA-256 is not configured")
    elif canonical_sha256 != support.EXPECTED_FINAL_CANONICAL_SHA256:
        errors.append("manifest canonical SHA-256 differs from the reviewed record")
    _validate_required_values(document, errors)
    _validate_redaction(document, errors)
    source_count = 0
    source_count += _validate_source_closure(
        document.get("evidence_build_sources"),
        repo_root,
        errors,
        allow_pending=not is_final,
    )
    source_count += _validate_source_closure(
        document.get("verification_sources"),
        repo_root,
        errors,
        allow_pending=not is_final,
    )
    return _report(errors, source_count, canonical_sha256)


def _report(errors: list[str], source_count: int, canonical_sha256: str) -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "facts": {
            "manifest_canonical_sha256": canonical_sha256,
            "source_files_checked": source_count,
            "python_verifies_risc0_seal": False,
            "evidence_ready": not errors,
        },
    }


def _validate_object_shapes(document: dict[str, Any], errors: list[str]) -> None:
    for path, expected in EXPECTED_FIELDS.items():
        value = _get(document, path)
        label = ".".join(path) or "manifest"
        if not isinstance(value, dict):
            errors.append(f"{label} must be an object")
            continue
        _require_exact_fields(value, expected, label, errors)

    controls = document.get("negative_controls")
    if not isinstance(controls, list) or len(controls) != len(EXPECTED_CONTROL_FIELDS):
        errors.append("negative_controls must contain exactly three controls")
    else:
        for index, expected in enumerate(EXPECTED_CONTROL_FIELDS):
            control = controls[index]
            if not isinstance(control, dict):
                errors.append(f"negative_controls[{index}] must be an object")
            else:
                _require_exact_fields(
                    control,
                    expected,
                    f"negative_controls[{index}]",
                    errors,
                )

    for closure_name in ("evidence_build_sources", "verification_sources"):
        closure = document.get(closure_name)
        files = closure.get("files") if isinstance(closure, dict) else None
        if not isinstance(files, list):
            errors.append(f"{closure_name}.files must be a list")
        else:
            for index, row in enumerate(files):
                if not isinstance(row, dict):
                    errors.append(f"{closure_name}.files[{index}] must be an object")
                else:
                    _require_exact_fields(
                        row,
                        EXPECTED_SOURCE_FIELDS,
                        f"{closure_name}.files[{index}]",
                        errors,
                    )


def _get(document: dict[str, Any], path: tuple[str, ...]) -> Any:
    value: Any = document
    for part in path:
        if not isinstance(value, dict):
            return None
        value = value.get(part)
    return value


def _require_exact_fields(
    value: dict[str, Any],
    expected: set[str],
    label: str,
    errors: list[str],
) -> None:
    actual = set(value)
    missing = sorted(expected - actual)
    unknown = sorted(actual - expected)
    if missing:
        errors.append(f"{label} missing fields: {','.join(missing)}")
    if unknown:
        errors.append(f"{label} has unknown fields: {','.join(unknown)}")


def _validate_required_values(document: dict[str, Any], errors: list[str]) -> None:
    status = _validate_header(document, errors)
    is_final = status == "temporary_local_receipt_evidence"
    _validate_adapter_state(document.get("adapter"), is_final, errors)
    _validate_receipt_state(document.get("receipt_verification"), is_final, errors)
    _validate_control_state(document.get("negative_controls"), is_final, errors)
    _validate_claim_state(document, is_final, errors)


def _validate_header(document: dict[str, Any], errors: list[str]) -> Any:
    if document.get("schema") != EXPECTED_SCHEMA:
        errors.append("manifest schema mismatch")
    if type(document.get("version")) is not int or document.get("version") != 1:
        errors.append("manifest version mismatch")
    status: Any = document.get("status")
    if status not in {"pending_final_rebuild", "temporary_local_receipt_evidence"}:
        errors.append("manifest status mismatch")
    if document.get("scope") != "current_v1_spot_receipt_to_zrpf_v3_leaf_adapter":
        errors.append("manifest scope mismatch")

    sanitization = document.get("sanitization")
    if isinstance(sanitization, dict) and sanitization != {
        "absolute_paths_included": False,
        "private_project_names_included": False,
        "public_safe_record": True,
    }:
        errors.append("sanitization assertions mismatch")
    build_scope = document.get("build_scope")
    if isinstance(build_scope, dict) and build_scope != {
        "compiler_visible_path_stable": False,
        "cross_host_reproduced": False,
        "release_authority": False,
    }:
        errors.append("temporary build scope mismatch")
    return status


def _validate_adapter_state(adapter: Any, is_final: bool, errors: list[str]) -> None:
    if is_final and isinstance(adapter, dict):
        _validate_adapter(adapter, errors)
    elif isinstance(adapter, dict):
        pending_adapter_values = (
            adapter.get("image_id"),
            adapter.get("image_id_words"),
            _nested(adapter, "elf", "sha256"),
            _nested(adapter, "elf", "size_bytes"),
            _nested(adapter, "receipt", "sha256"),
            _nested(adapter, "receipt", "size_bytes"),
            _nested(adapter, "journal", "protocol_hash"),
            _nested(adapter, "journal", "sha256"),
        )
        if any(value is not None for value in pending_adapter_values):
            errors.append("pending adapter evidence fields must remain null")


def _validate_receipt_state(
    receipt_verification: Any,
    is_final: bool,
    errors: list[str],
) -> None:
    if isinstance(receipt_verification, dict):
        if is_final:
            if receipt_verification.get("performed_by") != "Rust RISC0 harness":
                errors.append("receipt verifier boundary mismatch")
            if receipt_verification.get("source_receipt_verified") is not True:
                errors.append("source receipt verification fact missing")
            if receipt_verification.get("adapter_receipt_verified") is not True:
                errors.append("adapter receipt verification fact missing")
        elif (
            receipt_verification.get("performed_by") is not None
            or receipt_verification.get("source_receipt_verified") is not False
            or receipt_verification.get("adapter_receipt_verified") is not False
        ):
            errors.append("pending receipt verification facts must remain unset")
        if receipt_verification.get("python_checker_verifies_seal") is not False:
            errors.append("Python checker must deny RISC0 seal verification")


def _validate_control_state(controls: Any, is_final: bool, errors: list[str]) -> None:
    expected_control_ids = [
        "missing_source_assumption_rejected",
        "substituted_source_journal_rejected",
        "proof_bearing_mislabeled_adapter_rejected",
    ]
    if isinstance(controls, list):
        ids = [row.get("id") if isinstance(row, dict) else None for row in controls]
        if ids != expected_control_ids:
            errors.append("negative control IDs or order mismatch")
        expected_passed = is_final
        if any(
            not isinstance(row, dict) or row.get("passed") is not expected_passed
            for row in controls
        ):
            errors.append("negative control completion state mismatch")
        if not is_final and len(controls) == 3 and isinstance(controls[2], dict):
            if (
                controls[2].get("control_receipt_sha256") is not None
                or controls[2].get("substituted_adapter_image_id") is not None
            ):
                errors.append("pending negative-control artifact fields must remain null")


def _validate_claim_state(
    document: dict[str, Any],
    is_final: bool,
    errors: list[str],
) -> None:
    if not is_final and document.get("non_claims") != EXPECTED_NON_CLAIMS:
        errors.append("required non-claims mismatch")
    if is_final and document.get("non_claims") != EXPECTED_NON_CLAIMS[1:]:
        errors.append("required final non-claims mismatch")
    claims = document.get("claims")
    if isinstance(claims, dict):
        if not is_final and any(value is not False for value in claims.values()):
            errors.append("pending evidence must not enable any claim")
        if is_final and (
            claims.get("rust_harness_verified_receipt_cryptography") is not True
            or claims.get("temporary_local_computational_integrity_evidence") is not True
        ):
            errors.append("required temporary-local evidence claims are missing")
        forbidden_true = (
            "release_backed",
            "public_replay",
            "recursive_aggregate_evidence",
            "full_zenodex_semantic_composition",
            "ledger_or_settlement_admission_authority",
        )
        if any(claims.get(field) is not False for field in forbidden_true):
            errors.append("a prohibited evidence promotion claim is enabled")


def _nested(value: dict[str, Any], section: str, field: str) -> Any:
    child = value.get(section)
    return child.get(field) if isinstance(child, dict) else None


def _validate_adapter(adapter: dict[str, Any], errors: list[str]) -> None:
    image_id = adapter.get("image_id")
    words = adapter.get("image_id_words")
    if not _is_digest(image_id):
        errors.append("adapter image_id must be lowercase SHA-256 hex")
    if (
        not isinstance(words, list)
        or len(words) != 8
        or any(type(word) is not int or word < 0 or word > 0xFFFFFFFF for word in words)
    ):
        errors.append("adapter image_id_words must contain exactly eight u32 values")
    elif image_id != b"".join(word.to_bytes(4, "little") for word in words).hex():
        errors.append("adapter image_id_words do not encode adapter image_id")
    _validate_adapter_artifact_fields(adapter, errors)


def _validate_adapter_artifact_fields(
    adapter: dict[str, Any],
    errors: list[str],
) -> None:
    for label, fields in (
        ("adapter.elf", adapter.get("elf")),
        ("adapter.receipt", adapter.get("receipt")),
        ("adapter.journal", adapter.get("journal")),
    ):
        if not isinstance(fields, dict):
            continue
        _validate_digest_fields(label, fields, errors)


def _validate_digest_fields(
    label: str,
    fields: dict[str, Any],
    errors: list[str],
) -> None:
    for key, value in fields.items():
        is_hash_field = key.endswith("sha256") or key == "protocol_hash"
        if is_hash_field and not _is_digest(value):
            errors.append(f"{label}.{key} must be lowercase SHA-256 hex")
        if key == "size_bytes" and (type(value) is not int or value <= 0):
            errors.append(f"{label}.size_bytes must be a positive integer")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--adapter-receipt", type=Path)
    parser.add_argument("--source-proof", type=Path)
    parser.add_argument("--elf", type=Path)
    args = parser.parse_args()

    document, load_errors = load_manifest(args.manifest)
    if load_errors:
        report = _report(load_errors, 0, "")
    else:
        report = validate_manifest(document)

    optional_paths = {
        "adapter_receipt": args.adapter_receipt,
        "source_proof": args.source_proof,
        "elf": args.elf,
    }
    checked_artifacts: list[str] = []
    for label, path in optional_paths.items():
        if path is not None:
            checked_artifacts.append(label)
            report["errors"].extend(verify_optional_artifact(path, label))
    report["facts"]["optional_artifacts_checked"] = checked_artifacts
    report["ok"] = not report["errors"]
    report["facts"]["evidence_ready"] = report["ok"]
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Build and verify public kernel-assurance receipts.

ESSO, Kani, and Lean are proof toolchains. Public ZenoDEX checkouts should not
need the ESSO source tree, cargo-kani, or a Lean/mathlib checkout to verify that
a release is bound to specific toolchain runs. This checker validates a public
receipt emitted from a private `tools/dex_kernel_assurance.py` report plus
source-pinned Kani/Lean proof results without importing ESSO or running proof
toolchains in ordinary CI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "tools" / "kernel_assurance_manifest.json"
DEFAULT_RECEIPT = ROOT / "docs" / "assurance" / "kernel_assurance_public_receipt.json"
RECEIPT_SCHEMA = "zenodex.kernel_assurance.public_receipt.v1"


VALID_KANI_VERDICTS = frozenset({"VERIFIED"})
VALID_LEAN_VERDICTS = frozenset({"BUILT_NO_SORRY"})

# SOURCE-PINNED Kani proof set. The manifest and receipt must match this exactly,
# so a config-only edit cannot drop a harness, lower the required verdict, or
# repoint the source file without a reviewed edit to this checker.
EXPECTED_KANI_PROOFS: dict[str, dict[str, Any]] = {
    "balance_kernel_kani": {
        "tool": "cargo-kani",
        "required_verdict": "VERIFIED",
        "package": "zenodex-runtime-core",
        "working_directory": "rust-runtime",
        "cargo_kani_version": "cargo-kani 0.60.0",
        "harness_timeout": "10m",
        "source_files": ["rust-runtime/crates/zenodex-runtime-core/src/balance_kernel.rs"],
        "harnesses": {
            "balance_kernel::kani_contracts::covers_are_reachable": {
                "checks_failed": 0,
                "checks_total": 97,
                "cover_properties_satisfied": 3,
                "cover_properties_total": 3,
            },
            "balance_kernel::kani_contracts::credit_covers_are_reachable": {
                "checks_failed": 0,
                "checks_total": 94,
                "cover_properties_satisfied": 2,
                "cover_properties_total": 2,
            },
            "balance_kernel::kani_contracts::settle_credit_is_total": {
                "checks_failed": 0,
                "checks_total": 9,
                "cover_properties_satisfied": 0,
                "cover_properties_total": 0,
            },
            "balance_kernel::kani_contracts::settle_credit_mints_or_overflows": {
                "checks_failed": 0,
                "checks_total": 17,
                "cover_properties_satisfied": 0,
                "cover_properties_total": 0,
            },
            "balance_kernel::kani_contracts::settle_transfer_conserves_and_moves_exact": {
                "checks_failed": 0,
                "checks_total": 21,
                "cover_properties_satisfied": 0,
                "cover_properties_total": 0,
            },
            "balance_kernel::kani_contracts::settle_transfer_is_total": {
                "checks_failed": 0,
                "checks_total": 12,
                "cover_properties_satisfied": 0,
                "cover_properties_total": 0,
            },
            "balance_kernel::kani_contracts::settle_transfer_reject_precedence": {
                "checks_failed": 0,
                "checks_total": 21,
                "cover_properties_satisfied": 0,
                "cover_properties_total": 0,
            },
        },
    }
}

# SOURCE-PINNED Lean proof set for kernel-assurance receipt checks. Keep this
# separate from the SPOT proof receipt so nonce-wrapper work can be gated without
# touching the forbidden SPOT receipt files.
EXPECTED_LEAN_PROOFS: dict[str, dict[str, Any]] = {
    "nonce_batch_wrapper_lean": {
        "tool": "lean-lake-build",
        "required_verdict": "BUILT_NO_SORRY",
        "module": "Proofs.ZenoDEXNonceBatchWrapper",
        "expected_lean_toolchain": "leanprover/lean4:v4.27.0",
        "lean_toolchain_file": "lean-mathlib/lean-toolchain",
        "source_files": ["lean-mathlib/Proofs/ZenoDEXNonceBatchWrapper.lean"],
        "required_theorems": [
            "Proofs.ZenoDEX.NonceBatchWrapper.canonical_batch_accept_decision_implies_safety",
            "Proofs.ZenoDEX.NonceBatchWrapper.canonical_batch_sender_ids_nodup",
            "Proofs.ZenoDEX.NonceBatchWrapper.batch_accept_decision_implies_safety",
            "Proofs.ZenoDEX.NonceBatchWrapper.batch_accept_decision_implies_group_nodup",
            "Proofs.ZenoDEX.NonceBatchWrapper.witness_batch_accepts",
            "Proofs.ZenoDEX.NonceBatchWrapper.witness_canonical_batch_accepts",
            "Proofs.ZenoDEX.NonceBatchWrapper.witness_reject_gap",
            "Proofs.ZenoDEX.NonceBatchWrapper.witness_reject_is_noop_finals",
        ],
    }
}


class ReceiptError(ValueError):
    pass


def _canonical_json_bytes(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _load_json_object(path: Path, *, name: str) -> dict[str, Any]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ReceiptError(f"{name} missing: {path}") from exc
    except Exception as exc:
        raise ReceiptError(f"{name} is not valid JSON: {path}: {exc}") from exc
    if not isinstance(obj, dict):
        raise ReceiptError(f"{name} must be a JSON object: {path}")
    return obj


def _require_mapping(obj: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(obj, Mapping):
        raise ReceiptError(f"{name} must be an object")
    return obj


def _require_string(obj: Any, *, name: str) -> str:
    if not isinstance(obj, str) or not obj:
        raise ReceiptError(f"{name} must be a non-empty string")
    return obj


def _require_bool(obj: Any, *, name: str) -> bool:
    if not isinstance(obj, bool):
        raise ReceiptError(f"{name} must be a boolean")
    return obj


def _manifest_kernels(manifest: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    kernels = manifest.get("kernels")
    if not isinstance(kernels, list) or not kernels:
        raise ReceiptError("manifest.kernels must be a non-empty list")

    out: dict[str, Mapping[str, Any]] = {}
    for index, entry in enumerate(kernels):
        if not isinstance(entry, Mapping):
            raise ReceiptError(f"manifest.kernels[{index}] must be an object")
        model_id = _require_string(entry.get("model_id"), name=f"manifest.kernels[{index}].model_id")
        if model_id in out:
            raise ReceiptError(f"duplicate manifest kernel model_id: {model_id}")
        out[model_id] = entry
    return out


def _manifest_kani_proofs(manifest: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    proofs = manifest.get("kani_proofs")
    if not isinstance(proofs, list) or not proofs:
        raise ReceiptError("manifest.kani_proofs must be a non-empty list")

    out: dict[str, Mapping[str, Any]] = {}
    for index, entry in enumerate(proofs):
        if not isinstance(entry, Mapping):
            raise ReceiptError(f"manifest.kani_proofs[{index}] must be an object")
        pid = _require_string(entry.get("id"), name=f"manifest.kani_proofs[{index}].id")
        tool = _require_string(entry.get("tool"), name=f"{pid}.tool")
        if tool != "cargo-kani":
            raise ReceiptError(f"{pid}.tool unsupported: {tool!r}")
        verdict = _require_string(entry.get("required_verdict"), name=f"{pid}.required_verdict")
        if verdict not in VALID_KANI_VERDICTS:
            raise ReceiptError(f"{pid}.required_verdict unsupported: {verdict!r}")
        source_files = entry.get("source_files")
        if (
            not isinstance(source_files, list)
            or not source_files
            or not all(isinstance(path, str) and path for path in source_files)
        ):
            raise ReceiptError(f"{pid}.source_files must be a non-empty list of paths")
        harnesses = entry.get("harnesses")
        if (
            not isinstance(harnesses, list)
            or not harnesses
            or not all(isinstance(h, str) and h for h in harnesses)
        ):
            raise ReceiptError(f"{pid}.harnesses must be a non-empty list of harness names")
        if len(set(harnesses)) != len(harnesses):
            raise ReceiptError(f"{pid}.harnesses has duplicates")
        if pid in out:
            raise ReceiptError(f"duplicate manifest Kani proof id: {pid}")
        out[pid] = entry
    return out


def _report_kani_proofs(report: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    proofs = report.get("kani_proofs")
    if not isinstance(proofs, list) or not proofs:
        raise ReceiptError("private report kani_proofs must be a non-empty list")

    out: dict[str, Mapping[str, Any]] = {}
    for index, entry in enumerate(proofs):
        if not isinstance(entry, Mapping):
            raise ReceiptError(f"private report kani_proofs[{index}] must be an object")
        pid = _require_string(entry.get("id"), name=f"private report kani_proofs[{index}].id")
        if pid in out:
            raise ReceiptError(f"duplicate private report Kani proof id: {pid}")
        out[pid] = entry
    return out


def _manifest_lean_proofs(manifest: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    proofs = manifest.get("lean_proofs")
    if not isinstance(proofs, list) or not proofs:
        raise ReceiptError("manifest.lean_proofs must be a non-empty list")

    out: dict[str, Mapping[str, Any]] = {}
    for index, entry in enumerate(proofs):
        if not isinstance(entry, Mapping):
            raise ReceiptError(f"manifest.lean_proofs[{index}] must be an object")
        pid = _require_string(entry.get("id"), name=f"manifest.lean_proofs[{index}].id")
        tool = _require_string(entry.get("tool"), name=f"{pid}.tool")
        if tool != "lean-lake-build":
            raise ReceiptError(f"{pid}.tool unsupported: {tool!r}")
        verdict = _require_string(entry.get("required_verdict"), name=f"{pid}.required_verdict")
        if verdict not in VALID_LEAN_VERDICTS:
            raise ReceiptError(f"{pid}.required_verdict unsupported: {verdict!r}")
        _require_string(entry.get("module"), name=f"{pid}.module")
        source_files = entry.get("source_files")
        if (
            not isinstance(source_files, list)
            or not source_files
            or not all(isinstance(path, str) and path for path in source_files)
        ):
            raise ReceiptError(f"{pid}.source_files must be a non-empty list of paths")
        theorems = entry.get("required_theorems")
        if (
            not isinstance(theorems, list)
            or not theorems
            or not all(isinstance(name, str) and name for name in theorems)
        ):
            raise ReceiptError(f"{pid}.required_theorems must be a non-empty list of theorem names")
        if pid in out:
            raise ReceiptError(f"duplicate manifest Lean proof id: {pid}")
        out[pid] = entry
    return out


def _report_lean_proofs(report: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    proofs = report.get("lean_proofs")
    if not isinstance(proofs, list) or not proofs:
        raise ReceiptError("private report lean_proofs must be a non-empty list")

    out: dict[str, Mapping[str, Any]] = {}
    for index, entry in enumerate(proofs):
        if not isinstance(entry, Mapping):
            raise ReceiptError(f"private report lean_proofs[{index}] must be an object")
        pid = _require_string(entry.get("id"), name=f"private report lean_proofs[{index}].id")
        if pid in out:
            raise ReceiptError(f"duplicate private report Lean proof id: {pid}")
        out[pid] = entry
    return out


def _source_hashes(entry: Mapping[str, Any], *, pid: str) -> list[dict[str, str]]:
    source_files = entry.get("source_files")
    if not isinstance(source_files, list):
        raise ReceiptError(f"{pid}.source_files must be a list")
    out: list[dict[str, str]] = []
    for rel in source_files:
        if not isinstance(rel, str) or not rel:
            raise ReceiptError(f"{pid}.source_files entries must be non-empty strings")
        path = ROOT / rel
        if not path.is_file():
            raise ReceiptError(f"{pid}: source file missing: {rel}")
        out.append({"path": rel, "sha256": _sha256_file(path)})
    return out


def _check_kani_source_pin(manifest_by_id: Mapping[str, Mapping[str, Any]]) -> list[str]:
    errors: list[str] = []
    if set(manifest_by_id) != set(EXPECTED_KANI_PROOFS):
        errors.append(
            f"manifest Kani proof ids {sorted(manifest_by_id)} != source-pinned "
            f"EXPECTED_KANI_PROOFS {sorted(EXPECTED_KANI_PROOFS)} "
            f"(add/drop a proof only by editing EXPECTED_KANI_PROOFS)"
        )
    for pid in sorted(set(manifest_by_id) & set(EXPECTED_KANI_PROOFS)):
        exp = EXPECTED_KANI_PROOFS[pid]
        manifest_entry = manifest_by_id[pid]
        for key in (
            "tool",
            "required_verdict",
            "package",
            "working_directory",
            "cargo_kani_version",
            "harness_timeout",
        ):
            if manifest_entry.get(key) != exp[key]:
                errors.append(
                    f"{pid}: {key} {manifest_entry.get(key)!r} != source-pinned {exp[key]!r}"
                )
        if list(manifest_entry.get("source_files") or []) != exp["source_files"]:
            errors.append(
                f"{pid}: source_files {list(manifest_entry.get('source_files') or [])} "
                f"!= source-pinned {exp['source_files']}"
            )
        expected_harnesses = list(exp["harnesses"])
        if list(manifest_entry.get("harnesses") or []) != expected_harnesses:
            errors.append(
                f"{pid}: harnesses {list(manifest_entry.get('harnesses') or [])} "
                f"!= source-pinned {expected_harnesses}"
            )
    return errors


def _check_lean_source_pin(manifest_by_id: Mapping[str, Mapping[str, Any]]) -> list[str]:
    errors: list[str] = []
    if set(manifest_by_id) != set(EXPECTED_LEAN_PROOFS):
        errors.append(
            f"manifest Lean proof ids {sorted(manifest_by_id)} != source-pinned "
            f"EXPECTED_LEAN_PROOFS {sorted(EXPECTED_LEAN_PROOFS)} "
            f"(add/drop a proof only by editing EXPECTED_LEAN_PROOFS)"
        )
    for pid in sorted(set(manifest_by_id) & set(EXPECTED_LEAN_PROOFS)):
        exp = EXPECTED_LEAN_PROOFS[pid]
        manifest_entry = manifest_by_id[pid]
        for key in ("tool", "required_verdict", "module"):
            if manifest_entry.get(key) != exp[key]:
                errors.append(
                    f"{pid}: {key} {manifest_entry.get(key)!r} != source-pinned {exp[key]!r}"
                )
        if list(manifest_entry.get("source_files") or []) != exp["source_files"]:
            errors.append(
                f"{pid}: source_files {list(manifest_entry.get('source_files') or [])} "
                f"!= source-pinned {exp['source_files']}"
            )
        if list(manifest_entry.get("required_theorems") or []) != exp["required_theorems"]:
            errors.append(
                f"{pid}: required_theorems {list(manifest_entry.get('required_theorems') or [])} "
                f"!= source-pinned {exp['required_theorems']}"
            )
    return errors


def _report_kernels(report: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    kernels = report.get("kernels")
    if not isinstance(kernels, list) or not kernels:
        raise ReceiptError("private report kernels must be a non-empty list")

    out: dict[str, Mapping[str, Any]] = {}
    for index, entry in enumerate(kernels):
        if not isinstance(entry, Mapping):
            raise ReceiptError(f"private report kernels[{index}] must be an object")
        model_id = _require_string(entry.get("model_id"), name=f"private report kernels[{index}].model_id")
        if model_id in out:
            raise ReceiptError(f"duplicate private report kernel model_id: {model_id}")
        out[model_id] = entry
    return out


def _expected_solvers(manifest: Mapping[str, Any], kernel: Mapping[str, Any]) -> list[str]:
    raw = kernel.get("solvers", manifest.get("solvers"))
    if not isinstance(raw, list) or not raw or not all(isinstance(x, str) and x for x in raw):
        raise ReceiptError("manifest solvers must be a non-empty list of strings")
    return list(raw)


def _validate_toolchain_pin(manifest: Mapping[str, Any], report: Mapping[str, Any]) -> dict[str, Any]:
    expected = _require_mapping(manifest.get("toolchain"), name="manifest.toolchain")
    actual = _require_mapping(report.get("toolchain"), name="private report toolchain")

    out: dict[str, Any] = {}
    for key in ("esso_code_hash", "esso_tree_sha256"):
        expected_value = _require_string(expected.get(key), name=f"manifest.toolchain.{key}")
        actual_value = _require_string(actual.get(key), name=f"private report toolchain.{key}")
        if actual_value != expected_value:
            raise ReceiptError(f"{key} mismatch: expected {expected_value}, got {actual_value}")
        out[key] = actual_value

    out["esso_dirty"] = bool(actual.get("esso_dirty"))
    return out


def _kernel_receipt(
    *,
    manifest: Mapping[str, Any],
    manifest_kernel: Mapping[str, Any],
    report_kernel: Mapping[str, Any],
) -> dict[str, Any]:
    model_id = _require_string(manifest_kernel.get("model_id"), name="manifest kernel model_id")

    expected_pairs = (
        ("kernel_path", "kernel_path"),
        ("expected_ir_hash", "ir_hash"),
        ("ce_corpus_path", "ce_corpus_path"),
        ("expected_ce_corpus_sha256", "ce_corpus_sha256"),
    )
    out: dict[str, Any] = {"model_id": model_id}
    for manifest_key, report_key in expected_pairs:
        expected = _require_string(manifest_kernel.get(manifest_key), name=f"{model_id}.{manifest_key}")
        actual = _require_string(report_kernel.get(report_key), name=f"{model_id}.{report_key}")
        if actual != expected:
            raise ReceiptError(f"{model_id}.{report_key} mismatch: expected {expected}, got {actual}")
        public_key = "ir_hash" if report_key == "ir_hash" else report_key
        out[public_key] = actual

    stats = _require_mapping(report_kernel.get("corpus_stats"), name=f"{model_id}.corpus_stats")
    out["corpus_stats"] = {
        "total": stats.get("total"),
        "per_action": stats.get("per_action"),
        "boundary_per_action": stats.get("boundary_per_action"),
        "unique_ids": stats.get("unique_ids"),
        "unique_signatures": stats.get("unique_signatures"),
        "unique_signature_ratio": stats.get("unique_signature_ratio"),
    }

    verification = _require_mapping(report_kernel.get("verification"), name=f"{model_id}.verification")
    fingerprint = _require_string(verification.get("fingerprint"), name=f"{model_id}.verification.fingerprint")
    tool_versions = _require_mapping(verification.get("tool_versions"), name=f"{model_id}.verification.tool_versions")
    solver_versions = _require_mapping(tool_versions.get("solvers"), name=f"{model_id}.verification.tool_versions.solvers")

    expected_toolchain = _require_mapping(manifest.get("toolchain"), name="manifest.toolchain")
    expected_solver_versions = _require_mapping(expected_toolchain.get("solvers"), name="manifest.toolchain.solvers")
    solvers = _expected_solvers(manifest, manifest_kernel)
    public_solver_versions: dict[str, str] = {}
    for solver in solvers:
        expected_version = _require_string(expected_solver_versions.get(solver), name=f"manifest.toolchain.solvers.{solver}")
        actual_version = _require_string(solver_versions.get(solver), name=f"{model_id}.solver_versions.{solver}")
        if actual_version != expected_version:
            raise ReceiptError(f"{model_id}.{solver} version mismatch: expected {expected_version!r}, got {actual_version!r}")
        public_solver_versions[solver] = actual_version

    out["verification"] = {
        "fingerprint": fingerprint,
        "timeout_ms": verification.get("timeout_ms"),
        "determinism_trials": verification.get("determinism_trials"),
        "seeds": verification.get("seeds"),
        "tool_versions": {"solvers": public_solver_versions},
    }
    return out


def _kani_command(exp: Mapping[str, Any]) -> list[str]:
    command = [
        "cargo",
        "kani",
        "-p",
        str(exp["package"]),
        "--lib",
    ]
    for harness in exp["harnesses"]:
        command.extend(["--harness", str(harness)])
    command.extend(
        [
            "--exact",
            "--output-format",
            "terse",
            "--harness-timeout",
            str(exp["harness_timeout"]),
            "-Z",
            "unstable-options",
        ]
    )
    return command


def _validate_kani_result(
    pid: str,
    result: Any,
    *,
    required_verdict: Any,
    exp: Mapping[str, Any],
) -> list[str]:
    if not isinstance(result, Mapping):
        return [f"{pid}: Kani result must be an object"]
    errors: list[str] = []
    if result.get("verdict") != required_verdict:
        errors.append(
            f"{pid}: result verdict {result.get('verdict')!r} != required {required_verdict!r}"
        )
    if result.get("cargo_kani_version") != exp["cargo_kani_version"]:
        errors.append(
            f"{pid}: cargo_kani_version {result.get('cargo_kani_version')!r} "
            f"!= source-pinned {exp['cargo_kani_version']!r}"
        )
    if result.get("package") != exp["package"]:
        errors.append(f"{pid}: package {result.get('package')!r} != source-pinned {exp['package']!r}")
    if result.get("working_directory") != exp["working_directory"]:
        errors.append(
            f"{pid}: working_directory {result.get('working_directory')!r} "
            f"!= source-pinned {exp['working_directory']!r}"
        )
    expected_command = _kani_command(exp)
    if result.get("command") != expected_command:
        errors.append(f"{pid}: command {result.get('command')!r} != source-pinned {expected_command!r}")

    harnesses = result.get("harnesses")
    if not isinstance(harnesses, list):
        errors.append(f"{pid}: result.harnesses must be a list")
        return errors

    by_name: dict[str, Mapping[str, Any]] = {}
    names: list[str] = []
    for index, harness in enumerate(harnesses):
        if not isinstance(harness, Mapping):
            errors.append(f"{pid}: result.harnesses[{index}] must be an object")
            continue
        name = harness.get("name")
        if not isinstance(name, str) or not name:
            errors.append(f"{pid}: result.harnesses[{index}].name must be a non-empty string")
            continue
        names.append(name)
        by_name.setdefault(name, harness)
    duplicates = sorted({name for name in names if names.count(name) > 1})
    if duplicates:
        errors.append(f"{pid}: duplicate Kani harness results: {duplicates}")

    expected_harnesses = exp["harnesses"]
    if names != list(expected_harnesses):
        errors.append(
            f"{pid}: result harnesses {names} != source-pinned {list(expected_harnesses)}"
        )
    for name, expected in expected_harnesses.items():
        actual = by_name.get(name)
        if actual is None:
            continue
        if actual.get("verdict") != "VERIFIED":
            errors.append(f"{pid}: {name} verdict {actual.get('verdict')!r} != 'VERIFIED'")
        for key in (
            "checks_failed",
            "checks_total",
            "cover_properties_satisfied",
            "cover_properties_total",
        ):
            if actual.get(key) != expected[key]:
                errors.append(
                    f"{pid}: {name} {key} {actual.get(key)!r} "
                    f"!= source-pinned {expected[key]!r}"
                )

    summary = result.get("summary")
    if not isinstance(summary, Mapping):
        errors.append(f"{pid}: result.summary must be an object")
    else:
        expected_total = len(expected_harnesses)
        if summary.get("successfully_verified") != expected_total:
            errors.append(
                f"{pid}: summary.successfully_verified {summary.get('successfully_verified')!r} "
                f"!= {expected_total}"
            )
        if summary.get("failures") != 0:
            errors.append(f"{pid}: summary.failures {summary.get('failures')!r} != 0")
        if summary.get("total") != expected_total:
            errors.append(f"{pid}: summary.total {summary.get('total')!r} != {expected_total}")
    return errors


def _kani_receipt(
    *,
    manifest_entry: Mapping[str, Any],
    report_entry: Mapping[str, Any],
) -> dict[str, Any]:
    pid = _require_string(manifest_entry.get("id"), name="manifest Kani proof id")
    exp = EXPECTED_KANI_PROOFS.get(pid)
    if not isinstance(exp, Mapping):
        raise ReceiptError(f"{pid}: missing source-pinned Kani proof entry")

    out: dict[str, Any] = {"id": pid}
    for key in ("tool", "package", "working_directory"):
        expected = _require_string(manifest_entry.get(key), name=f"{pid}.{key}")
        actual = _require_string(report_entry.get(key), name=f"{pid}.{key}")
        if actual != expected:
            raise ReceiptError(f"{pid}.{key} mismatch: expected {expected}, got {actual}")
        out[key] = actual

    current_sources = _source_hashes(manifest_entry, pid=pid)
    report_sources = report_entry.get("source_files")
    if report_sources != current_sources:
        raise ReceiptError(
            f"{pid}: source hashes drifted from the Kani report "
            f"(re-run build): pinned={report_sources} current={current_sources}"
        )
    out["source_files"] = current_sources

    result = report_entry.get("result")
    result_errors = _validate_kani_result(
        pid,
        result,
        required_verdict=manifest_entry.get("required_verdict"),
        exp=exp,
    )
    if result_errors:
        raise ReceiptError("; ".join(result_errors))
    out["result"] = result
    return out


def _parse_kani_terse_output(stdout: str, *, pid: str, exp: Mapping[str, Any]) -> list[dict[str, Any]]:
    chunks = stdout.split("Checking harness ")[1:]
    harnesses: dict[str, dict[str, Any]] = {}
    for chunk in chunks:
        first_line, _, body = chunk.partition("\n")
        name = first_line.strip().rstrip(".")
        result_block = body.split("Checking harness ", 1)[0]
        checks = re.search(r"\*\* (\d+) of (\d+) failed", result_block)
        status = re.search(r"VERIFICATION:-\s+(\w+)", result_block)
        cover = re.search(r"\*\* (\d+) of (\d+) cover properties satisfied", result_block)
        if checks is None or status is None:
            raise ReceiptError(f"{pid}: could not parse Kani result for {name!r}")
        harnesses[name] = {
            "name": name,
            "verdict": "VERIFIED" if status.group(1) == "SUCCESSFUL" else status.group(1),
            "checks_failed": int(checks.group(1)),
            "checks_total": int(checks.group(2)),
            "cover_properties_satisfied": int(cover.group(1)) if cover else 0,
            "cover_properties_total": int(cover.group(2)) if cover else 0,
        }
    missing = sorted(set(exp["harnesses"]) - set(harnesses))
    extra = sorted(set(harnesses) - set(exp["harnesses"]))
    if missing or extra:
        raise ReceiptError(f"{pid}: parsed Kani harness mismatch: missing={missing}, extra={extra}")
    return [harnesses[name] for name in exp["harnesses"]]


def _run_kani_proof(manifest_entry: Mapping[str, Any]) -> dict[str, Any]:
    pid = _require_string(manifest_entry.get("id"), name="manifest Kani proof id")
    exp = EXPECTED_KANI_PROOFS[pid]
    command = _kani_command(exp)
    cwd = ROOT / str(exp["working_directory"])
    version_proc = subprocess.run(
        ["cargo", "kani", "--version"],
        cwd=str(cwd),
        capture_output=True,
        text=True,
        timeout=30,
    )
    if version_proc.returncode != 0:
        raise ReceiptError(f"{pid}: cargo kani --version failed: {version_proc.stderr[-400:]}")
    cargo_kani_version = version_proc.stdout.strip()
    proc = subprocess.run(command, cwd=str(cwd), capture_output=True, text=True, timeout=1800)
    if proc.returncode != 0:
        raise ReceiptError(
            f"{pid}: cargo kani failed with returncode={proc.returncode}: "
            f"stdout={proc.stdout[-800:]} stderr={proc.stderr[-800:]}"
        )
    harnesses = _parse_kani_terse_output(proc.stdout, pid=pid, exp=exp)
    result = {
        "verdict": "VERIFIED",
        "cargo_kani_version": cargo_kani_version,
        "package": exp["package"],
        "working_directory": exp["working_directory"],
        "command": command,
        "harnesses": harnesses,
        "summary": {
            "successfully_verified": len(harnesses),
            "failures": 0,
            "total": len(harnesses),
        },
    }
    result_errors = _validate_kani_result(
        pid,
        result,
        required_verdict=manifest_entry.get("required_verdict"),
        exp=exp,
    )
    if result_errors:
        raise ReceiptError("; ".join(result_errors))
    return {
        "id": pid,
        "tool": exp["tool"],
        "package": exp["package"],
        "working_directory": exp["working_directory"],
        "source_files": _source_hashes(manifest_entry, pid=pid),
        "result": result,
    }


def _lean_toolchain_from_source_pin(pid: str, exp: Mapping[str, Any]) -> tuple[str | None, list[str]]:
    rel = exp.get("lean_toolchain_file")
    if not isinstance(rel, str) or not rel:
        return None, [f"{pid}: lean_toolchain_file source pin missing"]
    path = ROOT / rel
    try:
        return path.read_text(encoding="utf-8").strip(), []
    except OSError as exc:
        return None, [f"{pid}: lean toolchain source pin unreadable: {rel}: {exc}"]


def _validate_lean_result(
    pid: str,
    result: Any,
    *,
    required_verdict: Any,
    exp: Mapping[str, Any],
) -> list[str]:
    if not isinstance(result, Mapping):
        return [f"{pid}: Lean result must be an object"]
    errors: list[str] = []
    if result.get("verdict") != required_verdict:
        errors.append(
            f"{pid}: result verdict {result.get('verdict')!r} != required {required_verdict!r}"
        )
    if result.get("module") != exp["module"]:
        errors.append(f"{pid}: module {result.get('module')!r} != source-pinned {exp['module']!r}")
    pinned_toolchain = exp.get("expected_lean_toolchain")
    if not isinstance(pinned_toolchain, str) or not pinned_toolchain:
        errors.append(f"{pid}: expected_lean_toolchain source pin missing")
    elif result.get("lean_toolchain") != pinned_toolchain:
        errors.append(
            f"{pid}: lean_toolchain {result.get('lean_toolchain')!r} "
            f"!= source-pinned {pinned_toolchain!r}"
        )
    live_toolchain, live_errors = _lean_toolchain_from_source_pin(pid, exp)
    errors.extend(live_errors)
    if pinned_toolchain and live_toolchain is not None and live_toolchain != pinned_toolchain:
        errors.append(
            f"{pid}: on-disk lean toolchain {live_toolchain!r} "
            f"!= source-pinned {pinned_toolchain!r}"
        )
    if list(result.get("required_theorems") or []) != exp["required_theorems"]:
        errors.append(
            f"{pid}: required_theorems {list(result.get('required_theorems') or [])} "
            f"!= source-pinned {exp['required_theorems']}"
        )
    return errors


def _lean_required_theorem_check_source(module: str, theorem_names: list[str]) -> str:
    lines = [f"import {module}"]
    lines.extend(f"#check {name}" for name in theorem_names)
    return "\n".join(lines) + "\n"


def _check_lean_required_theorems(pid: str, exp: Mapping[str, Any]) -> None:
    module = _require_string(exp.get("module"), name=f"{pid}.module")
    theorem_names = list(exp.get("required_theorems") or [])
    if not theorem_names or not all(isinstance(name, str) and name for name in theorem_names):
        raise ReceiptError(f"{pid}: required_theorems source pin must be a non-empty string list")

    safe_pid = re.sub(r"[^A-Za-z0-9_.-]", "_", pid)
    smoke_path = ROOT / "lean-mathlib" / f".tmp_{safe_pid}_required_theorems.lean"
    smoke_path.write_text(_lean_required_theorem_check_source(module, theorem_names), encoding="utf-8")
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", smoke_path.name],
            cwd=str(ROOT / "lean-mathlib"),
            capture_output=True,
            text=True,
            timeout=120,
        )
    finally:
        smoke_path.unlink(missing_ok=True)
    if proc.returncode != 0:
        raise ReceiptError(
            f"{pid}: required Lean theorem smoke check failed: "
            f"stdout={proc.stdout[-800:]} stderr={proc.stderr[-800:]}"
        )


def _lean_receipt(
    *,
    manifest_entry: Mapping[str, Any],
    report_entry: Mapping[str, Any],
) -> dict[str, Any]:
    pid = _require_string(manifest_entry.get("id"), name="manifest Lean proof id")
    exp = EXPECTED_LEAN_PROOFS.get(pid)
    if not isinstance(exp, Mapping):
        raise ReceiptError(f"{pid}: missing source-pinned Lean proof entry")

    out: dict[str, Any] = {"id": pid}
    for key in ("tool", "module"):
        expected = _require_string(manifest_entry.get(key), name=f"{pid}.{key}")
        actual = _require_string(report_entry.get(key), name=f"{pid}.{key}")
        if actual != expected:
            raise ReceiptError(f"{pid}.{key} mismatch: expected {expected}, got {actual}")
        out[key] = actual

    current_sources = _source_hashes(manifest_entry, pid=pid)
    report_sources = report_entry.get("source_files")
    if report_sources != current_sources:
        raise ReceiptError(
            f"{pid}: source hashes drifted from the Lean report "
            f"(re-run build): pinned={report_sources} current={current_sources}"
        )
    out["source_files"] = current_sources

    result = report_entry.get("result")
    result_errors = _validate_lean_result(
        pid,
        result,
        required_verdict=manifest_entry.get("required_verdict"),
        exp=exp,
    )
    if result_errors:
        raise ReceiptError("; ".join(result_errors))
    out["result"] = result
    return out


def _run_lean_proof(manifest_entry: Mapping[str, Any]) -> dict[str, Any]:
    pid = _require_string(manifest_entry.get("id"), name="manifest Lean proof id")
    exp = EXPECTED_LEAN_PROOFS[pid]
    module = _require_string(exp.get("module"), name=f"{pid}.module")
    proc = subprocess.run(
        ["lake", "build", module],
        cwd=str(ROOT / "lean-mathlib"),
        capture_output=True,
        text=True,
        timeout=600,
    )
    if proc.returncode != 0:
        raise ReceiptError(f"{pid}: lake build failed for {module}: {proc.stderr[-800:]}")

    # REVIEW [B -> A-]: `lake build <module>` proves the source compiles, but a
    # receipt can still overclaim by listing theorem names that no longer exist.
    # The builder now imports the module and #checks every source-pinned theorem
    # before it emits `BUILT_NO_SORRY`.
    _check_lean_required_theorems(pid, exp)

    forbidden = re.compile(r"\b(sorry|admit|sorryAx|unsafe)\b|\baxiom\b")
    for rel in exp["source_files"]:
        if forbidden.search((ROOT / rel).read_text(encoding="utf-8")):
            raise ReceiptError(f"{pid}: forbidden token (sorry/admit/axiom/unsafe) in {rel}")

    lean_toolchain, live_errors = _lean_toolchain_from_source_pin(pid, exp)
    if live_errors:
        raise ReceiptError("; ".join(live_errors))
    result = {
        "verdict": "BUILT_NO_SORRY",
        "lean_toolchain": lean_toolchain,
        "module": module,
        "required_theorems": exp["required_theorems"],
    }
    result_errors = _validate_lean_result(
        pid,
        result,
        required_verdict=manifest_entry.get("required_verdict"),
        exp=exp,
    )
    if result_errors:
        raise ReceiptError("; ".join(result_errors))
    return {
        "id": pid,
        "tool": exp["tool"],
        "module": module,
        "source_files": _source_hashes(manifest_entry, pid=pid),
        "result": result,
    }


def _receipt_hash_body(receipt: Mapping[str, Any]) -> dict[str, Any]:
    return {k: v for k, v in receipt.items() if k != "receipt_sha256"}


def _add_receipt_hash(receipt: dict[str, Any]) -> dict[str, Any]:
    receipt["receipt_sha256"] = _sha256_bytes(_canonical_json_bytes(_receipt_hash_body(receipt)))
    return receipt


def build_public_receipt_from_report(
    report: Mapping[str, Any],
    *,
    manifest: Mapping[str, Any],
    manifest_sha256: str,
    manifest_relpath: str = "tools/kernel_assurance_manifest.json",
    source_report_sha256: str = "",
) -> dict[str, Any]:
    if report.get("ok") is not True:
        raise ReceiptError("private kernel assurance report is not ok=true")

    report_manifest_hash = _require_string(report.get("manifest_sha256"), name="private report manifest_sha256")
    if report_manifest_hash != manifest_sha256:
        raise ReceiptError(f"private report manifest hash mismatch: expected {manifest_sha256}, got {report_manifest_hash}")

    toolchain = _validate_toolchain_pin(manifest, report)
    manifest_by_id = _manifest_kernels(manifest)
    report_by_id = _report_kernels(report)
    manifest_kani_by_id = _manifest_kani_proofs(manifest)
    source_pin_errors = _check_kani_source_pin(manifest_kani_by_id)
    if source_pin_errors:
        raise ReceiptError("; ".join(source_pin_errors))
    report_kani_by_id = _report_kani_proofs(report)
    manifest_lean_by_id = _manifest_lean_proofs(manifest)
    lean_source_pin_errors = _check_lean_source_pin(manifest_lean_by_id)
    if lean_source_pin_errors:
        raise ReceiptError("; ".join(lean_source_pin_errors))
    report_lean_by_id = _report_lean_proofs(report)

    missing = sorted(set(manifest_by_id) - set(report_by_id))
    extra = sorted(set(report_by_id) - set(manifest_by_id))
    if missing:
        raise ReceiptError(f"private report missing kernel receipts: {missing}")
    if extra:
        raise ReceiptError(f"private report has kernels outside manifest: {extra}")
    missing_kani = sorted(set(manifest_kani_by_id) - set(report_kani_by_id))
    extra_kani = sorted(set(report_kani_by_id) - set(manifest_kani_by_id))
    if missing_kani:
        raise ReceiptError(f"private report missing Kani proof receipts: {missing_kani}")
    if extra_kani:
        raise ReceiptError(f"private report has Kani proofs outside manifest: {extra_kani}")
    missing_lean = sorted(set(manifest_lean_by_id) - set(report_lean_by_id))
    extra_lean = sorted(set(report_lean_by_id) - set(manifest_lean_by_id))
    if missing_lean:
        raise ReceiptError(f"private report missing Lean proof receipts: {missing_lean}")
    if extra_lean:
        raise ReceiptError(f"private report has Lean proofs outside manifest: {extra_lean}")

    kernels = [
        _kernel_receipt(manifest=manifest, manifest_kernel=manifest_by_id[model_id], report_kernel=report_by_id[model_id])
        for model_id in sorted(manifest_by_id)
    ]
    kani_proofs = [
        _kani_receipt(manifest_entry=manifest_kani_by_id[pid], report_entry=report_kani_by_id[pid])
        for pid in sorted(manifest_kani_by_id)
    ]
    lean_proofs = [
        _lean_receipt(manifest_entry=manifest_lean_by_id[pid], report_entry=report_lean_by_id[pid])
        for pid in sorted(manifest_lean_by_id)
    ]

    receipt: dict[str, Any] = {
        "schema": RECEIPT_SCHEMA,
        "ok": True,
        "manifest": manifest_relpath,
        "manifest_sha256": manifest_sha256,
        "toolchain": toolchain,
        "source_report_sha256": source_report_sha256,
        "private_toolchain_source_included": False,
        "kernels": kernels,
        "kani_proofs": kani_proofs,
        "lean_proofs": lean_proofs,
    }
    return _add_receipt_hash(receipt)


def verify_public_receipt(
    receipt: Mapping[str, Any],
    *,
    manifest: Mapping[str, Any],
    manifest_sha256: str,
) -> list[str]:
    errors: list[str] = []

    def catch(label: str, fn: Any) -> Any:
        try:
            return fn()
        except ReceiptError as exc:
            errors.append(f"{label}: {exc}")
            return None

    catch("schema", lambda: _require_string(receipt.get("schema"), name="receipt.schema"))
    if receipt.get("schema") != RECEIPT_SCHEMA:
        errors.append(f"schema: expected {RECEIPT_SCHEMA}, got {receipt.get('schema')!r}")

    try:
        if _require_bool(receipt.get("ok"), name="receipt.ok") is not True:
            errors.append("receipt.ok must be true")
    except ReceiptError as exc:
        errors.append(f"ok: {exc}")

    receipt_manifest_sha = receipt.get("manifest_sha256")
    if receipt_manifest_sha != manifest_sha256:
        errors.append(f"manifest_sha256 mismatch: expected {manifest_sha256}, got {receipt_manifest_sha!r}")

    if receipt.get("private_toolchain_source_included") is not False:
        errors.append("private_toolchain_source_included must be false")

    supplied_hash = receipt.get("receipt_sha256")
    if not isinstance(supplied_hash, str) or not supplied_hash:
        errors.append("receipt_sha256 missing")
    else:
        actual_hash = _sha256_bytes(_canonical_json_bytes(_receipt_hash_body(receipt)))
        if supplied_hash != actual_hash:
            errors.append(f"receipt_sha256 mismatch: expected {actual_hash}, got {supplied_hash}")

    rebuilt = catch(
        "body",
        lambda: build_public_receipt_from_report(
            _receipt_to_report_shape(receipt),
            manifest=manifest,
            manifest_sha256=manifest_sha256,
            manifest_relpath=str(receipt.get("manifest") or "tools/kernel_assurance_manifest.json"),
            source_report_sha256=str(receipt.get("source_report_sha256") or ""),
        ),
    )
    if rebuilt is not None:
        rebuilt_hash = rebuilt.get("receipt_sha256")
        if supplied_hash != rebuilt_hash:
            errors.append(f"receipt body is not canonical for current manifest: expected hash {rebuilt_hash}, got {supplied_hash}")

    return errors


def _receipt_to_report_shape(receipt: Mapping[str, Any]) -> dict[str, Any]:
    """Map a public receipt back to the report subset used by the builder."""
    kernels = []
    for entry in receipt.get("kernels", []):
        if not isinstance(entry, Mapping):
            kernels.append(entry)
            continue
        verification = _require_mapping(entry.get("verification"), name="receipt kernel verification")
        kernels.append(
            {
                "model_id": entry.get("model_id"),
                "kernel_path": entry.get("kernel_path"),
                "ir_hash": entry.get("ir_hash"),
                "ce_corpus_path": entry.get("ce_corpus_path"),
                "ce_corpus_sha256": entry.get("ce_corpus_sha256"),
                "corpus_stats": entry.get("corpus_stats"),
                "verification": verification,
            }
        )
    kani_proofs = []
    for entry in receipt.get("kani_proofs", []):
        if not isinstance(entry, Mapping):
            kani_proofs.append(entry)
            continue
        kani_proofs.append(
            {
                "id": entry.get("id"),
                "tool": entry.get("tool"),
                "package": entry.get("package"),
                "working_directory": entry.get("working_directory"),
                "source_files": entry.get("source_files"),
                "result": entry.get("result"),
            }
        )
    lean_proofs = []
    for entry in receipt.get("lean_proofs", []):
        if not isinstance(entry, Mapping):
            lean_proofs.append(entry)
            continue
        lean_proofs.append(
            {
                "id": entry.get("id"),
                "tool": entry.get("tool"),
                "module": entry.get("module"),
                "source_files": entry.get("source_files"),
                "result": entry.get("result"),
            }
        )
    return {
        "ok": receipt.get("ok"),
        "manifest_sha256": receipt.get("manifest_sha256"),
        "toolchain": receipt.get("toolchain"),
        "kernels": kernels,
        "kani_proofs": kani_proofs,
        "lean_proofs": lean_proofs,
    }


def check_receipt_file(receipt_path: Path = DEFAULT_RECEIPT, manifest_path: Path = DEFAULT_MANIFEST) -> dict[str, Any]:
    errors: list[str] = []
    try:
        manifest = _load_json_object(manifest_path, name="kernel assurance manifest")
        manifest_sha256 = _sha256_file(manifest_path)
        receipt = _load_json_object(receipt_path, name="kernel assurance public receipt")
        errors.extend(verify_public_receipt(receipt, manifest=manifest, manifest_sha256=manifest_sha256))
    except ReceiptError as exc:
        errors.append(str(exc))

    return {
        "schema": "zenodex.kernel_assurance.public_receipt_check.v1",
        "ok": not errors,
        "receipt": str(receipt_path),
        "manifest": str(manifest_path),
        "errors": errors,
    }


def _cmd_build(args: argparse.Namespace) -> int:
    manifest_path = Path(args.manifest).expanduser().resolve()
    report_path = Path(args.report).expanduser().resolve()
    out_path = Path(args.out).expanduser().resolve()

    manifest = _load_json_object(manifest_path, name="kernel assurance manifest")
    report_bytes = report_path.read_bytes()
    report = json.loads(report_bytes.decode("utf-8"))
    if not isinstance(report, dict):
        raise ReceiptError("private report must be a JSON object")

    try:
        manifest_relpath = manifest_path.relative_to(ROOT).as_posix()
    except ValueError:
        manifest_relpath = str(manifest_path)

    if "kani_proofs" not in report:
        manifest_kani_by_id = _manifest_kani_proofs(manifest)
        source_pin_errors = _check_kani_source_pin(manifest_kani_by_id)
        if source_pin_errors:
            raise ReceiptError("; ".join(source_pin_errors))
        report["kani_proofs"] = [
            _run_kani_proof(manifest_kani_by_id[pid]) for pid in sorted(manifest_kani_by_id)
        ]
    if "lean_proofs" not in report:
        manifest_lean_by_id = _manifest_lean_proofs(manifest)
        source_pin_errors = _check_lean_source_pin(manifest_lean_by_id)
        if source_pin_errors:
            raise ReceiptError("; ".join(source_pin_errors))
        report["lean_proofs"] = [
            _run_lean_proof(manifest_lean_by_id[pid]) for pid in sorted(manifest_lean_by_id)
        ]

    receipt = build_public_receipt_from_report(
        report,
        manifest=manifest,
        manifest_sha256=_sha256_file(manifest_path),
        manifest_relpath=manifest_relpath,
        source_report_sha256=_sha256_bytes(_canonical_json_bytes(report)),
    )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


def _cmd_check(args: argparse.Namespace) -> int:
    report = check_receipt_file(
        receipt_path=Path(args.receipt).expanduser().resolve(),
        manifest_path=Path(args.manifest).expanduser().resolve(),
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build or verify public kernel-assurance receipts.")
    sub = parser.add_subparsers(dest="command")

    build = sub.add_parser(
        "build",
        help="Build a public receipt from a private dex_kernel_assurance report plus Kani/Lean runs.",
    )
    build.add_argument(
        "--report",
        required=True,
        help=(
            "Private tools/dex_kernel_assurance.py JSON report. "
            "Missing Kani/Lean results are run from the source pin."
        ),
    )
    build.add_argument("--manifest", default=str(DEFAULT_MANIFEST), help="Kernel assurance manifest.")
    build.add_argument("--out", default=str(DEFAULT_RECEIPT), help="Receipt output path.")
    build.set_defaults(func=_cmd_build)

    check = sub.add_parser("check", help="Verify a public receipt against the current manifest.")
    check.add_argument("--receipt", default=str(DEFAULT_RECEIPT), help="Public receipt path.")
    check.add_argument("--manifest", default=str(DEFAULT_MANIFEST), help="Kernel assurance manifest.")
    check.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    check.set_defaults(func=_cmd_check)

    parser.set_defaults(func=_cmd_check, receipt=str(DEFAULT_RECEIPT), manifest=str(DEFAULT_MANIFEST), pretty=False)
    args = parser.parse_args(argv)
    try:
        return int(args.func(args))
    except ReceiptError as exc:
        print(json.dumps({"ok": False, "errors": [str(exc)]}, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

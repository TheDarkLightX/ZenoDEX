#!/usr/bin/env python3
"""Build and verify public kernel-assurance receipts.

ESSO is a private toolchain. Public ZenoDEX checkouts should not need the ESSO
source tree to verify that a release is bound to a specific private-toolchain
run. This checker validates the public receipt emitted from a private
`tools/dex_kernel_assurance.py` report without importing ESSO.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "tools" / "kernel_assurance_manifest.json"
DEFAULT_RECEIPT = ROOT / "docs" / "assurance" / "kernel_assurance_public_receipt.json"
RECEIPT_SCHEMA = "zenodex.kernel_assurance.public_receipt.v1"


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

    missing = sorted(set(manifest_by_id) - set(report_by_id))
    extra = sorted(set(report_by_id) - set(manifest_by_id))
    if missing:
        raise ReceiptError(f"private report missing kernel receipts: {missing}")
    if extra:
        raise ReceiptError(f"private report has kernels outside manifest: {extra}")

    kernels = [
        _kernel_receipt(manifest=manifest, manifest_kernel=manifest_by_id[model_id], report_kernel=report_by_id[model_id])
        for model_id in sorted(manifest_by_id)
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
    return {
        "ok": receipt.get("ok"),
        "manifest_sha256": receipt.get("manifest_sha256"),
        "toolchain": receipt.get("toolchain"),
        "kernels": kernels,
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

    receipt = build_public_receipt_from_report(
        report,
        manifest=manifest,
        manifest_sha256=_sha256_file(manifest_path),
        manifest_relpath=manifest_relpath,
        source_report_sha256=_sha256_bytes(report_bytes),
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

    build = sub.add_parser("build", help="Build a public receipt from a private dex_kernel_assurance report.")
    build.add_argument("--report", required=True, help="Private tools/dex_kernel_assurance.py JSON report.")
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

from __future__ import annotations

import ast
import hashlib
import importlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Any, Mapping, Sequence, get_args

from jsonschema import Draft202012Validator, FormatChecker

from src.fire.pathing_v1 import fire_kernel_receipt_schema_path

if TYPE_CHECKING:
    from src.fire.registry.instance_v1 import FireObjectInstanceManifest
    from src.fire.registry.object_manifest_v1 import FireObjectManifest


FIRE_KERNEL_RECEIPT_SCHEMA = "zenodex/fire-kernel-receipt/v1"
FIRE_KERNEL_RECEIPT_CHECK_REPORT_SCHEMA = "zenodex/fire-kernel-receipt-check-report/v1"


def _require_mapping(name: str, value: object) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _load_json(path: Path) -> Mapping[str, object]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise TypeError(f"{path} must contain a JSON object")
    return payload


def _error_path(error: Any) -> str:
    if not error.path:
        return "/"
    return "/" + "/".join(str(item) for item in error.path)


def _validate_against_schema(
    payload: Mapping[str, object],
    *,
    schema_path: Path,
) -> tuple[bool, str | None]:
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    validator = Draft202012Validator(schema, format_checker=FormatChecker())
    errors = sorted(validator.iter_errors(payload), key=lambda item: tuple(item.path))
    if not errors:
        return True, None
    first = errors[0]
    return False, f"kernel_receipt_schema_invalid:{_error_path(first)}:{first.message}"


def _require_nonempty_str(name: str, value: object) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return value


def _normalize_str_list(name: str, value: object) -> list[str]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a sequence of non-empty strings")
    out: list[str] = []
    for idx, item in enumerate(value):
        if not isinstance(item, str) or not item:
            raise TypeError(f"{name}[{idx}] must be a non-empty string")
        out.append(item)
    return out


def _sha256_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def _kernel_module_name(object_id: str) -> str:
    return f"src.fire.kernel.fire_{object_id}_ref"


def _parse_kernel_header(module: object) -> tuple[str, str]:
    doc = getattr(module, "__doc__", None)
    if not isinstance(doc, str):
        raise RuntimeError("kernel ref module missing docstring header")
    model_match = re.search(r"Auto-generated Python reference model for:\s*([A-Za-z0-9_]+)", doc)
    ir_hash_match = re.search(r"IR hash:\s*(sha256:[0-9a-f]{64})", doc)
    if model_match is None:
        raise RuntimeError("kernel ref module missing model id header")
    if ir_hash_match is None:
        raise RuntimeError("kernel ref module missing ir hash header")
    return model_match.group(1), ir_hash_match.group(1)


def _command_tags_from_annotation(annotation: object) -> list[str]:
    if isinstance(annotation, str):
        try:
            node = ast.parse(annotation, mode="eval").body
        except SyntaxError as exc:  # pragma: no cover - generated refs should stay simple
            raise RuntimeError("kernel ref module has invalid command tag annotation") from exc
        if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name) or node.func.id != "Literal":
            raise RuntimeError("kernel ref module missing command tag literal surface")
        tags: list[str] = []
        for arg in node.args:
            if not isinstance(arg, ast.Constant) or not isinstance(arg.value, str) or not arg.value:
                raise RuntimeError("kernel ref module missing command tag literal surface")
            tags.append(arg.value)
        return tags
    return [str(item) for item in get_args(annotation) if isinstance(item, str) and item]


def load_fire_kernel_metadata(object_id: str) -> dict[str, object]:
    module_name = _kernel_module_name(object_id)
    module = importlib.import_module(module_name)
    module_file = Path(getattr(module, "__file__")).resolve()
    kernel_model_id, kernel_ir_hash = _parse_kernel_header(module)
    phase_symbols = getattr(module, "PHASE_SYMBOLS", None)
    if not isinstance(phase_symbols, tuple) or any(not isinstance(item, str) or not item for item in phase_symbols):
        raise RuntimeError("kernel ref module missing PHASE_SYMBOLS")
    tag_hint = getattr(module, "Command").__annotations__.get("tag")
    command_tags = _command_tags_from_annotation(tag_hint)
    if not command_tags:
        raise RuntimeError("kernel ref module missing command tag literal surface")
    return {
        "kernel_model_id": kernel_model_id,
        "kernel_ir_hash": kernel_ir_hash,
        "kernel_ref_module": module_name,
        "kernel_ref_file_sha256": _sha256_file(module_file),
        "phase_symbols": list(phase_symbols),
        "command_tags": command_tags,
    }


def build_fire_kernel_receipt(
    *,
    object_manifest: "FireObjectManifest",
    object_instance: "FireObjectInstanceManifest",
) -> dict[str, object]:
    from src.fire.compiler.compiler_registry_v1 import resolve_fire_compiler_entry

    entry = resolve_fire_compiler_entry(
        object_manifest.object_name,
        object_manifest.object_version,
        object_manifest.object_family,
    )
    kernel = load_fire_kernel_metadata(entry.object_id)
    return {
        "schema": FIRE_KERNEL_RECEIPT_SCHEMA,
        "object_id": entry.object_id,
        "object_name": object_manifest.object_name,
        "object_version": object_manifest.object_version,
        "object_family": object_manifest.object_family,
        "object_hash": object_manifest.manifest_hash,
        "instance_hash": object_instance.instance_hash,
        "cert_sha256": object_manifest.cert_sha256,
        "ir_hash": object_manifest.ir_hash,
        **kernel,
    }


@dataclass(frozen=True)
class FireKernelReceiptVerification:
    object_id: str
    object_hash: str
    instance_hash: str
    cert_sha256: str
    kernel_ref_file_sha256: str

    def to_report_dict(self) -> dict[str, object]:
        return {
            "object_id": self.object_id,
            "object_hash": self.object_hash,
            "instance_hash": self.instance_hash,
            "cert_sha256": self.cert_sha256,
            "kernel_ref_file_sha256": self.kernel_ref_file_sha256,
        }


@dataclass(frozen=True)
class FireKernelReceiptFileVerification:
    receipt_path: Path
    schema_path: Path
    object_manifest_path: Path
    instance_manifest_path: Path
    receipt_sha256: str
    object_id: str
    object_hash: str
    instance_hash: str
    cert_sha256: str
    kernel_ref_file_sha256: str

    def to_report_dict(self) -> dict[str, object]:
        return {
            "schema": FIRE_KERNEL_RECEIPT_CHECK_REPORT_SCHEMA,
            "ok": True,
            "receipt_path": str(self.receipt_path),
            "schema_path": str(self.schema_path),
            "object_manifest_path": str(self.object_manifest_path),
            "instance_manifest_path": str(self.instance_manifest_path),
            "receipt_sha256": self.receipt_sha256,
            "object_id": self.object_id,
            "object_hash": self.object_hash,
            "instance_hash": self.instance_hash,
            "cert_sha256": self.cert_sha256,
            "kernel_ref_file_sha256": self.kernel_ref_file_sha256,
        }


def verify_fire_kernel_receipt(
    payload: Mapping[str, object],
    *,
    object_manifest: "FireObjectManifest",
    object_instance: "FireObjectInstanceManifest",
) -> tuple[bool, str | None, FireKernelReceiptVerification | None]:
    expected = build_fire_kernel_receipt(
        object_manifest=object_manifest,
        object_instance=object_instance,
    )
    try:
        object_id = _require_nonempty_str("object_id", payload.get("object_id"))
        object_hash = _require_nonempty_str("object_hash", payload.get("object_hash"))
        instance_hash = _require_nonempty_str("instance_hash", payload.get("instance_hash"))
        cert_sha256 = _require_nonempty_str("cert_sha256", payload.get("cert_sha256"))
        kernel_ref_file_sha256 = _require_nonempty_str(
            "kernel_ref_file_sha256",
            payload.get("kernel_ref_file_sha256"),
        )
        _require_nonempty_str("kernel_model_id", payload.get("kernel_model_id"))
        _require_nonempty_str("kernel_ir_hash", payload.get("kernel_ir_hash"))
        _require_nonempty_str("kernel_ref_module", payload.get("kernel_ref_module"))
        _normalize_str_list("phase_symbols", payload.get("phase_symbols"))
        _normalize_str_list("command_tags", payload.get("command_tags"))
    except TypeError as exc:
        return False, f"kernel_receipt_invalid:{exc}", None

    if dict(payload) != expected:
        return False, "kernel_receipt_mismatch", None
    return (
        True,
        None,
        FireKernelReceiptVerification(
            object_id=object_id,
            object_hash=object_hash,
            instance_hash=instance_hash,
            cert_sha256=cert_sha256,
            kernel_ref_file_sha256=kernel_ref_file_sha256,
        ),
    )


def verify_fire_kernel_receipt_file(
    path: str | Path,
    *,
    object_manifest_path: str | Path,
    instance_manifest_path: str | Path,
    expected_receipt_sha256: str | None = None,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_kernel_ref_file_sha256: str | None = None,
) -> tuple[bool, str | None, FireKernelReceiptFileVerification | None]:
    from src.fire.registry.instance_v1 import (
        load_fire_object_instance,
        verify_fire_object_instance_against_manifest,
    )
    from src.fire.registry.object_manifest_v1 import (
        load_fire_object_manifest,
        verify_fire_object_manifest,
    )

    receipt_path = Path(path).resolve()
    manifest_path = Path(object_manifest_path).resolve()
    instance_path = Path(instance_manifest_path).resolve()
    schema_path = fire_kernel_receipt_schema_path().resolve()

    payload = _load_json(receipt_path)
    receipt_sha256 = _sha256_file(receipt_path)
    if expected_receipt_sha256 is not None and receipt_sha256 != expected_receipt_sha256:
        return False, "expected_receipt_sha256_mismatch", None

    object_manifest, _manifest_file_sha256 = load_fire_object_manifest(manifest_path)
    manifest_ok, manifest_err = verify_fire_object_manifest(object_manifest)
    if not manifest_ok:
        return False, f"object_manifest_invalid:{manifest_err or 'unknown'}", None
    if expected_object_hash is not None and object_manifest.manifest_hash != expected_object_hash:
        return False, "expected_object_hash_mismatch", None
    if expected_cert_sha256 is not None and object_manifest.cert_sha256 != expected_cert_sha256:
        return False, "expected_cert_sha256_mismatch", None

    object_instance, _instance_file_sha256 = load_fire_object_instance(instance_path)
    instance_ok, instance_err, _instance_report = verify_fire_object_instance_against_manifest(
        object_instance,
        object_manifest=object_manifest,
    )
    if not instance_ok:
        return False, f"instance_invalid:{instance_err or 'unknown'}", None
    if expected_instance_hash is not None and object_instance.instance_hash != expected_instance_hash:
        return False, "expected_instance_hash_mismatch", None

    schema_ok, schema_err = _validate_against_schema(payload, schema_path=schema_path)
    if not schema_ok:
        return False, schema_err, None

    ok, err, verification = verify_fire_kernel_receipt(
        payload,
        object_manifest=object_manifest,
        object_instance=object_instance,
    )
    if not ok or verification is None:
        return False, err or "kernel_receipt_verification_failed", None
    if expected_kernel_ref_file_sha256 is not None and verification.kernel_ref_file_sha256 != expected_kernel_ref_file_sha256:
        return False, "expected_kernel_ref_file_sha256_mismatch", None

    return (
        True,
        None,
        FireKernelReceiptFileVerification(
            receipt_path=receipt_path,
            schema_path=schema_path,
            object_manifest_path=manifest_path,
            instance_manifest_path=instance_path,
            receipt_sha256=receipt_sha256,
            object_id=verification.object_id,
            object_hash=verification.object_hash,
            instance_hash=verification.instance_hash,
            cert_sha256=verification.cert_sha256,
            kernel_ref_file_sha256=verification.kernel_ref_file_sha256,
        ),
    )


def write_fire_kernel_receipt(
    path: str | Path,
    *,
    object_manifest: "FireObjectManifest",
    object_instance: "FireObjectInstanceManifest",
) -> str:
    receipt_path = Path(path)
    payload = build_fire_kernel_receipt(
        object_manifest=object_manifest,
        object_instance=object_instance,
    )
    receipt_path.write_text(
        json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True),
        encoding="utf-8",
    )
    return _sha256_file(receipt_path)


__all__ = [
    "FIRE_KERNEL_RECEIPT_SCHEMA",
    "FIRE_KERNEL_RECEIPT_CHECK_REPORT_SCHEMA",
    "FireKernelReceiptVerification",
    "FireKernelReceiptFileVerification",
    "build_fire_kernel_receipt",
    "load_fire_kernel_metadata",
    "verify_fire_kernel_receipt",
    "verify_fire_kernel_receipt_file",
    "write_fire_kernel_receipt",
]

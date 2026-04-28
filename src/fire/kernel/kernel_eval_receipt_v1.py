from __future__ import annotations

import hashlib
import importlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Any, Mapping, Sequence

from jsonschema import Draft202012Validator, FormatChecker

from src.fire.kernel.kernel_receipt_v1 import load_fire_kernel_metadata
from src.fire.pathing_v1 import fire_kernel_eval_receipt_schema_path

if TYPE_CHECKING:
    from src.fire.registry.instance_v1 import FireObjectInstanceManifest
    from src.fire.registry.object_manifest_v1 import FireObjectManifest


FIRE_KERNEL_EVAL_RECEIPT_SCHEMA = "zenodex/fire-kernel-eval-receipt/v1"
FIRE_KERNEL_EVAL_RECEIPT_CHECK_REPORT_SCHEMA = "zenodex/fire-kernel-eval-receipt-check-report/v1"

_COMPILE_COMMAND_SPECS: Mapping[str, tuple[str, tuple[tuple[str, str], ...]]] = {
    "burn_boost_call_v1": (
        "compile_burn_boost_call",
        (
            ("n_in", "n_notional"),
            ("strike_in", "strike_index"),
            ("cap_in", "cap_index"),
            ("source_upper_in", "source_upper"),
        ),
    ),
    "fee_note_v1": (
        "compile_fee_note",
        (
            ("n_in", "n_notional"),
            ("cap_in", "cap_index"),
            ("source_upper_in", "source_upper"),
        ),
    ),
    "lp_loss_cover_v1": (
        "compile_lp_loss_cover",
        (
            ("n_in", "n_notional"),
            ("deductible_in", "deductible"),
            ("cap_in", "cap_amount"),
            ("hodl_lower_in", "hodl_lower"),
            ("hodl_upper_in", "hodl_upper"),
            ("lpv_lower_in", "lpv_lower"),
            ("lpv_upper_in", "lpv_upper"),
        ),
    ),
}


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
    return False, f"kernel_eval_receipt_schema_invalid:{_error_path(first)}:{first.message}"


def _require_nonempty_str(name: str, value: object) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return value


def _require_int(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_sha256_prefixed(name: str, value: object) -> str:
    text = _require_nonempty_str(name, value)
    if not text.startswith("sha256:") or len(text) != len("sha256:") + 64:
        raise TypeError(f"{name} must be sha256-prefixed")
    return text


def _sha256_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def _normalize_scalar_mapping(name: str, value: object) -> dict[str, object]:
    mapping = _require_mapping(name, value)
    out: dict[str, object] = {}
    for key, item in sorted(mapping.items()):
        if not isinstance(key, str) or not key:
            raise TypeError(f"{name} keys must be non-empty strings")
        if isinstance(item, bool):
            out[key] = item
        elif isinstance(item, int):
            out[key] = item
        elif isinstance(item, str) and item:
            out[key] = item
        else:
            raise TypeError(f"{name}[{key}] must be int, bool, or non-empty string")
    return out


def _parameter_values_from_instance(object_instance: "FireObjectInstanceManifest") -> dict[str, int]:
    values: dict[str, int] = {}
    for item in object_instance.parameters:
        values[item.name] = item.value
    return values


def _compile_command(object_id: str, parameter_values: Mapping[str, int]) -> tuple[str, dict[str, int]]:
    if object_id not in _COMPILE_COMMAND_SPECS:
        raise KeyError(f"unsupported FIRE kernel eval object_id: {object_id}")
    tag, bindings = _COMPILE_COMMAND_SPECS[object_id]
    args: dict[str, int] = {}
    for arg_name, parameter_name in bindings:
        if parameter_name not in parameter_values:
            raise KeyError(f"missing parameter {parameter_name} for {object_id}")
        value = parameter_values[parameter_name]
        if not isinstance(value, int) or isinstance(value, bool):
            raise TypeError(f"parameter {parameter_name} must be int")
        args[arg_name] = value
    return tag, args


def _run_compile_command(
    *,
    object_id: str,
    object_instance: "FireObjectInstanceManifest",
) -> tuple[dict[str, object], dict[str, object], str]:
    kernel = load_fire_kernel_metadata(object_id)
    module = importlib.import_module(str(kernel["kernel_ref_module"]))
    tag, args = _compile_command(object_id, _parameter_values_from_instance(object_instance))
    result = module.step(
        module.init_state(),
        module.Command(tag=tag, args=dict(args)),
    )
    if not result.ok or result.state is None:
        raise RuntimeError(result.error or f"{tag} rejected")
    state = _normalize_scalar_mapping("compiled_state", asdict(result.state))
    effects = _normalize_scalar_mapping("compiled_effects", dict(result.effects or {}))
    phase = state.get("phase")
    if phase != "Compiled":
        raise RuntimeError("kernel compile command did not reach Compiled phase")
    return state, effects, tag


def build_fire_kernel_eval_receipt(
    *,
    object_manifest: "FireObjectManifest",
    object_instance: "FireObjectInstanceManifest",
    kernel_receipt_sha256: str,
) -> dict[str, object]:
    from src.fire.compiler.compiler_registry_v1 import resolve_fire_compiler_entry

    entry = resolve_fire_compiler_entry(
        object_manifest.object_name,
        object_manifest.object_version,
        object_manifest.object_family,
    )
    kernel = load_fire_kernel_metadata(entry.object_id)
    compiled_state, compiled_effects, compile_command_tag = _run_compile_command(
        object_id=entry.object_id,
        object_instance=object_instance,
    )
    compiled_artifact_lower = _require_int("compiled_state.artifact_lower", compiled_state.get("artifact_lower"))
    compiled_artifact_upper = _require_int("compiled_state.artifact_upper", compiled_state.get("artifact_upper"))
    compiled_upper = _require_int("compiled_effects.compiled_upper", compiled_effects.get("compiled_upper"))
    if compiled_artifact_lower != object_manifest.artifact_lower:
        raise RuntimeError("kernel eval artifact_lower does not match canonical manifest")
    if compiled_artifact_upper != object_manifest.artifact_upper:
        raise RuntimeError("kernel eval artifact_upper does not match canonical manifest")
    if compiled_upper != object_manifest.artifact_upper:
        raise RuntimeError("kernel eval compiled_upper effect does not match canonical manifest")
    return {
        "schema": FIRE_KERNEL_EVAL_RECEIPT_SCHEMA,
        "object_id": entry.object_id,
        "object_name": object_manifest.object_name,
        "object_version": object_manifest.object_version,
        "object_family": object_manifest.object_family,
        "object_hash": object_manifest.manifest_hash,
        "instance_hash": object_instance.instance_hash,
        "cert_sha256": object_manifest.cert_sha256,
        "ir_hash": object_manifest.ir_hash,
        "kernel_model_id": kernel["kernel_model_id"],
        "kernel_ir_hash": kernel["kernel_ir_hash"],
        "kernel_receipt_sha256": kernel_receipt_sha256,
        "compile_command_tag": compile_command_tag,
        "compile_command_args": _compile_command(entry.object_id, _parameter_values_from_instance(object_instance))[1],
        "compiled_state": compiled_state,
        "compiled_effects": compiled_effects,
        "compiled_artifact_lower": compiled_artifact_lower,
        "compiled_artifact_upper": compiled_artifact_upper,
    }


@dataclass(frozen=True)
class FireKernelEvalReceiptVerification:
    object_id: str
    object_hash: str
    instance_hash: str
    cert_sha256: str
    kernel_receipt_sha256: str
    compiled_artifact_lower: int
    compiled_artifact_upper: int

    def to_report_dict(self) -> dict[str, object]:
        return {
            "object_id": self.object_id,
            "object_hash": self.object_hash,
            "instance_hash": self.instance_hash,
            "cert_sha256": self.cert_sha256,
            "kernel_receipt_sha256": self.kernel_receipt_sha256,
            "compiled_artifact_lower": self.compiled_artifact_lower,
            "compiled_artifact_upper": self.compiled_artifact_upper,
        }


@dataclass(frozen=True)
class FireKernelEvalReceiptFileVerification:
    receipt_path: Path
    schema_path: Path
    object_manifest_path: Path
    instance_manifest_path: Path
    receipt_sha256: str
    object_id: str
    object_hash: str
    instance_hash: str
    cert_sha256: str
    kernel_receipt_sha256: str
    compiled_artifact_lower: int
    compiled_artifact_upper: int

    def to_report_dict(self) -> dict[str, object]:
        return {
            "schema": FIRE_KERNEL_EVAL_RECEIPT_CHECK_REPORT_SCHEMA,
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
            "kernel_receipt_sha256": self.kernel_receipt_sha256,
            "compiled_artifact_lower": self.compiled_artifact_lower,
            "compiled_artifact_upper": self.compiled_artifact_upper,
        }


def verify_fire_kernel_eval_receipt(
    payload: Mapping[str, object],
    *,
    object_manifest: "FireObjectManifest",
    object_instance: "FireObjectInstanceManifest",
    expected_kernel_receipt_sha256: str | None = None,
) -> tuple[bool, str | None, FireKernelEvalReceiptVerification | None]:
    try:
        object_id = _require_nonempty_str("object_id", payload.get("object_id"))
        object_hash = _require_sha256_prefixed("object_hash", payload.get("object_hash"))
        instance_hash = _require_sha256_prefixed("instance_hash", payload.get("instance_hash"))
        cert_sha256 = _require_sha256_prefixed("cert_sha256", payload.get("cert_sha256"))
        kernel_receipt_sha256 = _require_sha256_prefixed(
            "kernel_receipt_sha256",
            payload.get("kernel_receipt_sha256"),
        )
        _require_nonempty_str("kernel_model_id", payload.get("kernel_model_id"))
        _require_sha256_prefixed("kernel_ir_hash", payload.get("kernel_ir_hash"))
        _require_nonempty_str("compile_command_tag", payload.get("compile_command_tag"))
        _normalize_scalar_mapping("compile_command_args", payload.get("compile_command_args"))
        _normalize_scalar_mapping("compiled_state", payload.get("compiled_state"))
        _normalize_scalar_mapping("compiled_effects", payload.get("compiled_effects"))
        compiled_artifact_lower = _require_int("compiled_artifact_lower", payload.get("compiled_artifact_lower"))
        compiled_artifact_upper = _require_int("compiled_artifact_upper", payload.get("compiled_artifact_upper"))
    except (TypeError, ValueError) as exc:
        return False, f"kernel_eval_receipt_invalid:{exc}", None

    if expected_kernel_receipt_sha256 is not None and kernel_receipt_sha256 != expected_kernel_receipt_sha256:
        return False, "expected_kernel_receipt_sha256_mismatch", None

    if compiled_artifact_lower != object_manifest.artifact_lower:
        return False, "compiled_artifact_lower_mismatch", None
    if compiled_artifact_upper != object_manifest.artifact_upper:
        return False, "compiled_artifact_upper_mismatch", None

    expected = build_fire_kernel_eval_receipt(
        object_manifest=object_manifest,
        object_instance=object_instance,
        kernel_receipt_sha256=kernel_receipt_sha256,
    )
    if dict(payload) != expected:
        return False, "kernel_eval_receipt_mismatch", None
    return (
        True,
        None,
        FireKernelEvalReceiptVerification(
            object_id=object_id,
            object_hash=object_hash,
            instance_hash=instance_hash,
            cert_sha256=cert_sha256,
            kernel_receipt_sha256=kernel_receipt_sha256,
            compiled_artifact_lower=compiled_artifact_lower,
            compiled_artifact_upper=compiled_artifact_upper,
        ),
    )


def verify_fire_kernel_eval_receipt_file(
    path: str | Path,
    *,
    object_manifest_path: str | Path,
    instance_manifest_path: str | Path,
    expected_receipt_sha256: str | None = None,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_kernel_receipt_sha256: str | None = None,
) -> tuple[bool, str | None, FireKernelEvalReceiptFileVerification | None]:
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
    schema_path = fire_kernel_eval_receipt_schema_path().resolve()

    payload = _load_json(receipt_path)
    valid, schema_err = _validate_against_schema(payload, schema_path=schema_path)
    if not valid:
        return False, schema_err, None

    receipt_sha256 = _sha256_file(receipt_path)
    if expected_receipt_sha256 is not None and receipt_sha256 != expected_receipt_sha256:
        return False, "expected_receipt_sha256_mismatch", None

    object_manifest, _manifest_sha = load_fire_object_manifest(manifest_path)
    ok, err = verify_fire_object_manifest(object_manifest)
    if not ok:
        return False, f"object_manifest_invalid:{err or 'unknown'}", None

    object_instance, _instance_sha = load_fire_object_instance(instance_path)
    ok, err, _report = verify_fire_object_instance_against_manifest(object_instance, object_manifest=object_manifest)
    if not ok:
        return False, f"object_instance_gate_invalid:{err or 'unknown'}", None

    ok, err, verification = verify_fire_kernel_eval_receipt(
        payload,
        object_manifest=object_manifest,
        object_instance=object_instance,
        expected_kernel_receipt_sha256=expected_kernel_receipt_sha256,
    )
    if not ok or verification is None:
        return False, err or "kernel_eval_receipt_verification_failed", None
    if expected_object_hash is not None and verification.object_hash != expected_object_hash:
        return False, "expected_object_hash_mismatch", None
    if expected_instance_hash is not None and verification.instance_hash != expected_instance_hash:
        return False, "expected_instance_hash_mismatch", None
    if expected_cert_sha256 is not None and verification.cert_sha256 != expected_cert_sha256:
        return False, "expected_cert_sha256_mismatch", None
    return (
        True,
        None,
        FireKernelEvalReceiptFileVerification(
            receipt_path=receipt_path,
            schema_path=schema_path,
            object_manifest_path=manifest_path,
            instance_manifest_path=instance_path,
            receipt_sha256=receipt_sha256,
            object_id=verification.object_id,
            object_hash=verification.object_hash,
            instance_hash=verification.instance_hash,
            cert_sha256=verification.cert_sha256,
            kernel_receipt_sha256=verification.kernel_receipt_sha256,
            compiled_artifact_lower=verification.compiled_artifact_lower,
            compiled_artifact_upper=verification.compiled_artifact_upper,
        ),
    )


def write_fire_kernel_eval_receipt(
    path: str | Path,
    *,
    object_manifest: "FireObjectManifest",
    object_instance: "FireObjectInstanceManifest",
    kernel_receipt_sha256: str,
) -> str:
    out_path = Path(path)
    payload = build_fire_kernel_eval_receipt(
        object_manifest=object_manifest,
        object_instance=object_instance,
        kernel_receipt_sha256=kernel_receipt_sha256,
    )
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    out_path.write_bytes(encoded)
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


__all__ = [
    "FIRE_KERNEL_EVAL_RECEIPT_CHECK_REPORT_SCHEMA",
    "FIRE_KERNEL_EVAL_RECEIPT_SCHEMA",
    "FireKernelEvalReceiptFileVerification",
    "FireKernelEvalReceiptVerification",
    "build_fire_kernel_eval_receipt",
    "verify_fire_kernel_eval_receipt",
    "verify_fire_kernel_eval_receipt_file",
    "write_fire_kernel_eval_receipt",
]

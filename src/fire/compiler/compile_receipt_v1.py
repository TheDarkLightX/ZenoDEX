from __future__ import annotations

import hashlib
import json
from collections.abc import Sequence as SequenceABC
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Any, Mapping, Sequence

from jsonschema import Draft202012Validator, FormatChecker

from src.fire.pathing_v1 import fire_compile_receipt_schema_path
from src.fire.verifier.proof_tree_cert_v1 import summarize_fire_interval_certificate

if TYPE_CHECKING:
    from src.fire.registry.instance_v1 import FireObjectInstanceManifest
    from src.fire.registry.object_manifest_v1 import FireObjectManifest


FIRE_COMPILE_RECEIPT_SCHEMA = "zenodex/fire-compile-receipt/v1"
FIRE_COMPILE_RECEIPT_CHECK_REPORT_SCHEMA = "zenodex/fire-compile-receipt-check-report/v1"

FIRE_COMPILE_RECEIPT_FORMAL_PROOF_BINDINGS = (
    {
        "binding_id": "fire_zpl_language_soundness_v1",
        "proof_system": "lean4",
        "module": "Proofs.ZenoPayoffLanguage",
        "checker": "lake env lean Proofs/ZenoPayoffLanguage.lean",
        "theorems": (
            "compile_correct",
            "compile_no_default",
            "VerifiedPayoff.settlement_safe",
            "firev_accept_settlement_safe",
            "twoPartyObject_conserves",
        ),
        "claim": (
            "Successful ZPL compilation preserves expression value, emits sound "
            "interval bounds, and supports collateral-safe two-party settlement "
            "when posted collateral dominates the certified requirements."
        ),
        "source_files": (
            "lean-mathlib/Proofs/ZenoPayoffLanguage.lean",
            "lean-mathlib/Proofs/CertifiedFinancialMathObjects.lean",
        ),
    },
    {
        "binding_id": "fire_cal_core_soundness_v1",
        "proof_system": "lean4",
        "module": "Proofs.CALCoreSoundness",
        "checker": "lake env lean Proofs/CALCoreSoundness.lean",
        "theorems": (
            "collateral_two_party_no_default",
            "integerEvalOK_within_bounds",
            "fireV_accept_soundness",
        ),
        "claim": (
            "FIREVAccept implies SettlementSafe for the modeled CAL/FIRE "
            "admission core under the declared object, instance, witness, "
            "collateral, delta, conservation, and replay obligations."
        ),
        "source_files": (
            "lean-mathlib/Proofs/CALCoreSoundness.lean",
            "lean-mathlib/Proofs/CertifiedFinancialMathObjects.lean",
        ),
    },
    {
        "binding_id": "fire_zpl_fixed_point_bridge_v1",
        "proof_system": "lean4",
        "module": "Proofs.ZenoPayoffPortfolioFixedPointBridge",
        "checker": "lake env lean Proofs/ZenoPayoffPortfolioFixedPointBridge.lean",
        "theorems": (
            "compile_floorDecode_posted_collateral_safe",
            "compile_ceilDecode_posted_collateral_safe",
            "compile_sum_floorDecode_posted_collateral_safe",
            "compile_sum_ceilDecode_posted_collateral_safe",
            "compile_sum_decodeByMode_posted_collateral_safe",
            "compile_sum_decodeByMode_posted_collateral_safe_and_conserves",
            "int_two_party_delta_receipt_conserves",
            "int_two_party_delta_receipt_decode_conserves",
            "int_two_party_delta_receipt_safe_and_conserves",
            "compile_decodeByMode_two_party_delta_conserves",
            "compile_sum_decodeByMode_two_party_delta_conserves",
        ),
        "claim": (
            "Successful FIRE/ZPL compilation composes with fixed-point runtime "
            "rounding: floor-decoded settlements are safe under a one-tick "
            "lower-side buffer, ceil-decoded settlements are safe under a "
            "one-tick upper-side buffer, mixed floor/ceil portfolios are safe "
            "under the corresponding per-leg side buffers, and posted collateral "
            "against those expanded intervals prevents bilateral default. Runtime "
            "delta conservation is exact when the writer leg negates the rounded "
            "holder leg, including the integer receipt delta table and its decoded "
            "fixed-point interpretation."
        ),
        "source_files": (
            "lean-mathlib/Proofs/FixedPointIntervalBridge.lean",
            "lean-mathlib/Proofs/FixedPointPortfolioBridge.lean",
            "lean-mathlib/Proofs/ZenoPayoffFixedPointBridge.lean",
            "lean-mathlib/Proofs/ZenoPayoffPortfolioFixedPointBridge.lean",
        ),
    },
)


def _require_mapping(name: str, value: object) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _load_json(path: Path) -> Mapping[str, object]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise TypeError(f"{path} must contain a JSON object")
    return payload


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _sha256_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def _lean_toolchain(repo_root: Path) -> str:
    toolchain_path = repo_root / "lean-mathlib" / "lean-toolchain"
    value = toolchain_path.read_text(encoding="utf-8").strip()
    if not value:
        raise ValueError("lean-mathlib/lean-toolchain must be non-empty")
    return value


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
    return False, f"compile_receipt_schema_invalid:{_error_path(first)}:{first.message}"


def _normalize_named_interval_items(
    items: Sequence[Mapping[str, object]],
    *,
    field_name: str,
) -> list[dict[str, object]]:
    normalized: list[dict[str, object]] = []
    for idx, item in enumerate(items):
        item_map = _require_mapping(f"{field_name}[{idx}]", item)
        name = item_map.get("name")
        unit = item_map.get("unit")
        lower = item_map.get("lower")
        upper = item_map.get("upper")
        if not isinstance(name, str) or not name:
            raise TypeError(f"{field_name}[{idx}].name must be a non-empty string")
        if not isinstance(unit, str) or not unit:
            raise TypeError(f"{field_name}[{idx}].unit must be a non-empty string")
        if not isinstance(lower, int) or isinstance(lower, bool):
            raise TypeError(f"{field_name}[{idx}].lower must be an int")
        if not isinstance(upper, int) or isinstance(upper, bool):
            raise TypeError(f"{field_name}[{idx}].upper must be an int")
        normalized.append(
            {
                "name": name,
                "unit": unit,
                "lower": lower,
                "upper": upper,
            }
        )
    return normalized


def _normalize_parameter_values(values: Sequence[Mapping[str, object]]) -> list[dict[str, object]]:
    normalized: list[dict[str, object]] = []
    for idx, item in enumerate(values):
        item_map = _require_mapping(f"parameter_values[{idx}]", item)
        name = item_map.get("name")
        value = item_map.get("value")
        if not isinstance(name, str) or not name:
            raise TypeError(f"parameter_values[{idx}].name must be a non-empty string")
        if not isinstance(value, int) or isinstance(value, bool):
            raise TypeError(f"parameter_values[{idx}].value must be an int")
        normalized.append({"name": name, "value": value})
    return normalized


def _normalize_witness_like_items(
    items: Sequence[Mapping[str, object]],
    *,
    field_name: str,
    witness: bool,
) -> list[dict[str, object]]:
    normalized: list[dict[str, object]] = []
    for idx, item in enumerate(items):
        item_map = _require_mapping(f"{field_name}[{idx}]", item)
        name = item_map.get("name")
        lower = item_map.get("lower")
        upper = item_map.get("upper")
        if not isinstance(name, str) or not name:
            raise TypeError(f"{field_name}[{idx}].name must be a non-empty string")
        if not isinstance(lower, int) or isinstance(lower, bool):
            raise TypeError(f"{field_name}[{idx}].lower must be an int")
        if not isinstance(upper, int) or isinstance(upper, bool):
            raise TypeError(f"{field_name}[{idx}].upper must be an int")
        row: dict[str, object] = {
            "name": name,
            "lower": lower,
            "upper": upper,
        }
        if witness:
            freshness = item_map.get("freshness")
            if not isinstance(freshness, str) or not freshness:
                raise TypeError(f"{field_name}[{idx}].freshness must be a non-empty string")
            row["freshness"] = freshness
        else:
            interface_object_id = item_map.get("interface_object_id")
            interface_output = item_map.get("interface_output")
            unit = item_map.get("unit")
            if not isinstance(interface_object_id, str) or not interface_object_id:
                raise TypeError(f"{field_name}[{idx}].interface_object_id must be a non-empty string")
            if not isinstance(interface_output, str) or not interface_output:
                raise TypeError(f"{field_name}[{idx}].interface_output must be a non-empty string")
            if not isinstance(unit, str) or not unit:
                raise TypeError(f"{field_name}[{idx}].unit must be a non-empty string")
            row["interface_object_id"] = interface_object_id
            row["interface_output"] = interface_output
            row["unit"] = unit
        contract_name = item_map.get("contract_name")
        contract_role = item_map.get("contract_role")
        if contract_name is not None or contract_role is not None:
            if not isinstance(contract_name, str) or not contract_name:
                raise TypeError(f"{field_name}[{idx}].contract_name must be a non-empty string when present")
            if not isinstance(contract_role, str) or not contract_role:
                raise TypeError(f"{field_name}[{idx}].contract_role must be a non-empty string when present")
            row["contract_name"] = contract_name
            row["contract_role"] = contract_role
        normalized.append(row)
    return normalized


def build_fire_compile_receipt_formal_proof_bindings(
    *,
    repo_root: Path | None = None,
) -> list[dict[str, object]]:
    resolved_root = (repo_root or _repo_root()).resolve()
    lean_toolchain = _lean_toolchain(resolved_root)
    bindings: list[dict[str, object]] = []
    for raw_binding in FIRE_COMPILE_RECEIPT_FORMAL_PROOF_BINDINGS:
        source_files: list[dict[str, object]] = []
        for rel_path in raw_binding["source_files"]:
            source_path = resolved_root / str(rel_path)
            if not source_path.is_file():
                raise FileNotFoundError(f"formal proof source missing: {rel_path}")
            source_files.append(
                {
                    "path": str(rel_path),
                    "sha256": _sha256_file(source_path),
                }
            )
        bindings.append(
            {
                "binding_id": str(raw_binding["binding_id"]),
                "proof_system": str(raw_binding["proof_system"]),
                "lean_toolchain": lean_toolchain,
                "module": str(raw_binding["module"]),
                "checker": str(raw_binding["checker"]),
                "theorems": [str(item) for item in raw_binding["theorems"]],
                "claim": str(raw_binding["claim"]),
                "source_files": source_files,
            }
        )
    return bindings


def _normalize_formal_proof_bindings(items: object) -> list[dict[str, object]]:
    if not isinstance(items, SequenceABC) or isinstance(items, (str, bytes, bytearray)):
        raise TypeError("formal_proof_bindings must be an array")
    normalized: list[dict[str, object]] = []
    for idx, item in enumerate(items):
        item_map = _require_mapping(f"formal_proof_bindings[{idx}]", item)
        binding_id = item_map.get("binding_id")
        proof_system = item_map.get("proof_system")
        lean_toolchain = item_map.get("lean_toolchain")
        module = item_map.get("module")
        checker = item_map.get("checker")
        claim = item_map.get("claim")
        for field_name, value in (
            ("binding_id", binding_id),
            ("proof_system", proof_system),
            ("lean_toolchain", lean_toolchain),
            ("module", module),
            ("checker", checker),
            ("claim", claim),
        ):
            if not isinstance(value, str) or not value:
                raise TypeError(f"formal_proof_bindings[{idx}].{field_name} must be a non-empty string")
        theorems = item_map.get("theorems")
        if not isinstance(theorems, SequenceABC) or isinstance(theorems, (str, bytes, bytearray)) or not theorems:
            raise TypeError(f"formal_proof_bindings[{idx}].theorems must be a non-empty array")
        normalized_theorems: list[str] = []
        for theorem_idx, theorem in enumerate(theorems):
            if not isinstance(theorem, str) or not theorem:
                raise TypeError(
                    f"formal_proof_bindings[{idx}].theorems[{theorem_idx}] must be a non-empty string"
                )
            normalized_theorems.append(theorem)
        source_files = item_map.get("source_files")
        if (
            not isinstance(source_files, SequenceABC)
            or isinstance(source_files, (str, bytes, bytearray))
            or not source_files
        ):
            raise TypeError(f"formal_proof_bindings[{idx}].source_files must be a non-empty array")
        normalized_sources: list[dict[str, object]] = []
        for source_idx, source in enumerate(source_files):
            source_map = _require_mapping(f"formal_proof_bindings[{idx}].source_files[{source_idx}]", source)
            path = source_map.get("path")
            sha256 = source_map.get("sha256")
            if not isinstance(path, str) or not path:
                raise TypeError(
                    f"formal_proof_bindings[{idx}].source_files[{source_idx}].path must be a non-empty string"
                )
            if not isinstance(sha256, str) or not sha256.startswith("sha256:") or len(sha256) != 71:
                raise TypeError(
                    f"formal_proof_bindings[{idx}].source_files[{source_idx}].sha256 must be sha256-prefixed"
                )
            normalized_sources.append({"path": path, "sha256": sha256})
        normalized.append(
            {
                "binding_id": binding_id,
                "proof_system": proof_system,
                "lean_toolchain": lean_toolchain,
                "module": module,
                "checker": checker,
                "theorems": normalized_theorems,
                "claim": claim,
                "source_files": normalized_sources,
            }
        )
    return normalized


def _interval_item_to_dict(item: object) -> dict[str, object]:
    return {
        "name": getattr(item, "name"),
        "unit": getattr(item, "unit"),
        "lower": getattr(item, "lower"),
        "upper": getattr(item, "upper"),
    }


def _witness_requirement_to_dict(item: object) -> dict[str, object]:
    row = {
        "name": getattr(item, "name"),
        "freshness": getattr(item, "freshness"),
        "lower": getattr(item, "lower"),
        "upper": getattr(item, "upper"),
    }
    contract = getattr(item, "contract", None)
    if contract is not None:
        row["contract_name"] = contract.name
        row["contract_role"] = contract.role
    return row


def _import_requirement_to_dict(item: object) -> dict[str, object]:
    row = {
        "name": getattr(item, "name"),
        "interface_object_id": getattr(item, "interface_object_id"),
        "interface_output": getattr(item, "interface_output"),
        "unit": getattr(item, "unit"),
        "lower": getattr(item, "lower"),
        "upper": getattr(item, "upper"),
    }
    contract = getattr(item, "contract", None)
    if contract is not None:
        row["contract_name"] = contract.name
        row["contract_role"] = contract.role
    return row


def build_fire_compile_receipt(
    *,
    object_manifest: "FireObjectManifest",
    object_instance: "FireObjectInstanceManifest",
) -> dict[str, object]:
    from src.fire.compiler.compiler_registry_v1 import (
        compile_fire_object,
        resolve_fire_compiler_entry,
    )
    from src.fire.compiler.fmos_v1 import build_fmos_manifest

    entry = resolve_fire_compiler_entry(
        object_manifest.object_name,
        object_manifest.object_version,
        object_manifest.object_family,
    )
    raw_terms = {item.name: item.value for item in object_instance.parameters}
    compiled = compile_fire_object(entry.object_id, raw_terms)
    derived_manifest = build_fmos_manifest(compiled.spec, compiled.artifact)
    certificate = compiled.artifact.certificate
    return {
        "schema": FIRE_COMPILE_RECEIPT_SCHEMA,
        "object_id": entry.object_id,
        "object_name": derived_manifest.object_name,
        "object_version": derived_manifest.object_version,
        "object_family": derived_manifest.object_family,
        "ir_hash": derived_manifest.ir_hash,
        "object_hash": derived_manifest.manifest_hash,
        "cert_sha256": derived_manifest.cert_sha256,
        "parameter_values": [
            {"name": item.name, "value": item.value}
            for item in object_instance.parameters
        ],
        "source_requirements": [
            _interval_item_to_dict(item)
            for item in compiled.spec.build_source_requirements(compiled.artifact.terms)
        ],
        "output_guarantees": [
            _interval_item_to_dict(item)
            for item in compiled.spec.build_output_guarantees(compiled.artifact.terms)
        ],
        "witness_requirements": [
            _witness_requirement_to_dict(item)
            for item in compiled.spec.witness_builder(compiled.artifact)
        ],
        "import_requirements": [
            _import_requirement_to_dict(item)
            for item in compiled.spec.build_import_requirements(compiled.artifact.terms)
        ],
        "runtime_certificate_summary": summarize_fire_interval_certificate(certificate),
        "formal_proof_bindings": build_fire_compile_receipt_formal_proof_bindings(),
    }


@dataclass(frozen=True)
class FireCompileReceiptVerification:
    object_id: str
    object_hash: str
    cert_sha256: str

    def to_report_dict(self) -> dict[str, object]:
        return {
            "object_id": self.object_id,
            "object_hash": self.object_hash,
            "cert_sha256": self.cert_sha256,
        }


@dataclass(frozen=True)
class FireCompileReceiptFileVerification:
    receipt_path: Path
    schema_path: Path
    object_manifest_path: Path
    instance_manifest_path: Path
    receipt_sha256: str
    object_id: str
    object_hash: str
    instance_hash: str
    cert_sha256: str

    def to_report_dict(self) -> dict[str, object]:
        return {
            "schema": FIRE_COMPILE_RECEIPT_CHECK_REPORT_SCHEMA,
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
        }


def verify_fire_compile_receipt(
    payload: Mapping[str, object],
    *,
    object_manifest: "FireObjectManifest",
    object_instance: "FireObjectInstanceManifest",
) -> tuple[bool, str | None, FireCompileReceiptVerification | None]:
    expected = build_fire_compile_receipt(
        object_manifest=object_manifest,
        object_instance=object_instance,
    )
    try:
        object_id = payload.get("object_id")
        if not isinstance(object_id, str) or not object_id:
            return False, "compile_receipt_object_id_invalid", None
        object_hash = payload.get("object_hash")
        if not isinstance(object_hash, str) or not object_hash:
            return False, "compile_receipt_object_hash_invalid", None
        cert_sha256 = payload.get("cert_sha256")
        if not isinstance(cert_sha256, str) or not cert_sha256:
            return False, "compile_receipt_cert_sha256_invalid", None
        _normalize_parameter_values(payload.get("parameter_values", []))
        _normalize_named_interval_items(payload.get("source_requirements", []), field_name="source_requirements")
        _normalize_named_interval_items(payload.get("output_guarantees", []), field_name="output_guarantees")
        _normalize_witness_like_items(payload.get("witness_requirements", []), field_name="witness_requirements", witness=True)
        _normalize_witness_like_items(payload.get("import_requirements", []), field_name="import_requirements", witness=False)
        _require_mapping("runtime_certificate_summary", payload.get("runtime_certificate_summary"))
        _normalize_formal_proof_bindings(payload.get("formal_proof_bindings"))
    except TypeError as exc:
        return False, f"compile_receipt_invalid:{exc}", None

    if dict(payload) != expected:
        return False, "compile_receipt_mismatch", None
    return (
        True,
        None,
        FireCompileReceiptVerification(
            object_id=expected["object_id"],
            object_hash=expected["object_hash"],
            cert_sha256=expected["cert_sha256"],
        ),
    )


def verify_fire_compile_receipt_file(
    path: str | Path,
    *,
    object_manifest_path: str | Path,
    instance_manifest_path: str | Path,
    expected_receipt_sha256: str | None = None,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
) -> tuple[bool, str | None, FireCompileReceiptFileVerification | None]:
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
    schema_path = fire_compile_receipt_schema_path().resolve()

    payload = _load_json(receipt_path)
    receipt_sha256 = "sha256:" + hashlib.sha256(receipt_path.read_bytes()).hexdigest()

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

    ok, err, verification = verify_fire_compile_receipt(
        payload,
        object_manifest=object_manifest,
        object_instance=object_instance,
    )
    if not ok or verification is None:
        return False, err or "compile_receipt_verification_failed", None

    return (
        True,
        None,
        FireCompileReceiptFileVerification(
            receipt_path=receipt_path,
            schema_path=schema_path,
            object_manifest_path=manifest_path,
            instance_manifest_path=instance_path,
            receipt_sha256=receipt_sha256,
            object_id=verification.object_id,
            object_hash=verification.object_hash,
            instance_hash=object_instance.instance_hash,
            cert_sha256=verification.cert_sha256,
        ),
    )


def write_fire_compile_receipt(
    path: str | Path,
    *,
    object_manifest: "FireObjectManifest",
    object_instance: "FireObjectInstanceManifest",
) -> str:
    receipt_path = Path(path)
    payload = build_fire_compile_receipt(
        object_manifest=object_manifest,
        object_instance=object_instance,
    )
    receipt_path.write_text(json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True), encoding="utf-8")
    return "sha256:" + hashlib.sha256(receipt_path.read_bytes()).hexdigest()


__all__ = [
    "FIRE_COMPILE_RECEIPT_SCHEMA",
    "FIRE_COMPILE_RECEIPT_CHECK_REPORT_SCHEMA",
    "FIRE_COMPILE_RECEIPT_FORMAL_PROOF_BINDINGS",
    "FireCompileReceiptFileVerification",
    "FireCompileReceiptVerification",
    "build_fire_compile_receipt_formal_proof_bindings",
    "build_fire_compile_receipt",
    "verify_fire_compile_receipt",
    "verify_fire_compile_receipt_file",
    "write_fire_compile_receipt",
]

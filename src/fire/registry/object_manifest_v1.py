from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path

from src.fire.verifier.cert_v1 import FireInstanceGateClaims, _require_sha256_prefixed


MANIFEST_SCHEMA = "zenodex/fire-object-manifest/v1"
_EVIDENCE_LEVELS = frozenset({"proved", "contract", "implemented", "tested_discovery", "hypothesis"})
_AUTHORIZATION_MODES = frozenset({"role_binding"})


def _require_nonempty_str(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    return value


def _require_int(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def _canonical_json_bytes(payload: dict[str, object]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def fire_manifest_sha256(payload_without_hash: dict[str, object]) -> str:
    return "sha256:" + hashlib.sha256(_canonical_json_bytes(payload_without_hash)).hexdigest()


def canonical_manifest_json_bytes(manifest: "FireObjectManifest") -> bytes:
    return _canonical_json_bytes(manifest.to_dict())


def fire_manifest_file_sha256(manifest: "FireObjectManifest") -> str:
    return "sha256:" + hashlib.sha256(canonical_manifest_json_bytes(manifest)).hexdigest()


def _legacy_payload_without_imported_interfaces(manifest: "FireObjectManifest") -> dict[str, object]:
    return {
        "schema": manifest.schema,
        "object_name": manifest.object_name,
        "object_version": manifest.object_version,
        "object_family": manifest.object_family,
        "settlement_asset": manifest.settlement_asset,
        "payoff_summary": manifest.payoff_summary,
        "artifact_bound": {
            "lower": manifest.artifact_lower,
            "upper": manifest.artifact_upper,
        },
        "collateral_required": {
            "holder": manifest.holder_collateral_required,
            "writer": manifest.writer_collateral_required,
        },
        "ir_hash": manifest.ir_hash,
        "cert_sha256": manifest.cert_sha256,
        "witnesses": [item.to_dict() for item in manifest.witnesses],
        "evidence": manifest.evidence.to_dict(),
    }


@dataclass(frozen=True)
class FireParameterRequirement:
    name: str
    unit: str
    minimum: int
    maximum: int
    description: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "name", _require_nonempty_str("name", self.name))
        object.__setattr__(self, "unit", _require_nonempty_str("unit", self.unit))
        object.__setattr__(self, "minimum", _require_int("minimum", self.minimum))
        object.__setattr__(self, "maximum", _require_int("maximum", self.maximum))
        object.__setattr__(self, "description", _require_nonempty_str("description", self.description))
        if self.minimum > self.maximum:
            raise ValueError(f"parameter {self.name} has inverted bounds")

    def to_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "unit": self.unit,
            "minimum": self.minimum,
            "maximum": self.maximum,
            "description": self.description,
        }

    @classmethod
    def from_dict(cls, payload: object) -> "FireParameterRequirement":
        if not isinstance(payload, dict):
            raise TypeError("parameter payload must be a dict")
        return cls(
            name=payload.get("name"),
            unit=payload.get("unit"),
            minimum=payload.get("minimum"),
            maximum=payload.get("maximum"),
            description=payload.get("description"),
        )


@dataclass(frozen=True)
class FireInstancePolicy:
    required_party_roles: tuple[str, ...] = ("holder", "writer")
    authorization_mode: str = "role_binding"
    nonce_required: bool = True
    maturity_required: bool = False
    settlement_window_required: bool = False

    def __post_init__(self) -> None:
        if not isinstance(self.required_party_roles, tuple) or any(
            not isinstance(item, str) or not item for item in self.required_party_roles
        ):
            raise TypeError("required_party_roles must be a tuple of non-empty strings")
        if len(self.required_party_roles) != len(set(self.required_party_roles)):
            raise ValueError("required_party_roles must be unique")
        object.__setattr__(self, "authorization_mode", _require_nonempty_str("authorization_mode", self.authorization_mode))
        if self.authorization_mode not in _AUTHORIZATION_MODES:
            raise ValueError(f"unsupported authorization_mode: {self.authorization_mode}")
        object.__setattr__(self, "nonce_required", _require_bool("nonce_required", self.nonce_required))
        object.__setattr__(self, "maturity_required", _require_bool("maturity_required", self.maturity_required))
        object.__setattr__(
            self,
            "settlement_window_required",
            _require_bool("settlement_window_required", self.settlement_window_required),
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "required_party_roles": list(self.required_party_roles),
            "authorization_mode": self.authorization_mode,
            "nonce_required": self.nonce_required,
            "maturity_required": self.maturity_required,
            "settlement_window_required": self.settlement_window_required,
        }

    @classmethod
    def from_dict(cls, payload: object) -> "FireInstancePolicy":
        if payload is None:
            return cls()
        if not isinstance(payload, dict):
            raise TypeError("instance_policy payload must be a dict")
        required_party_roles = payload.get("required_party_roles", ["holder", "writer"])
        if not isinstance(required_party_roles, list):
            raise TypeError("required_party_roles must be a list")
        return cls(
            required_party_roles=tuple(str(item) for item in required_party_roles),
            authorization_mode=payload.get("authorization_mode", "role_binding"),
            nonce_required=payload.get("nonce_required", True),
            maturity_required=payload.get("maturity_required", False),
            settlement_window_required=payload.get("settlement_window_required", False),
        )


@dataclass(frozen=True)
class FireContractProvenance:
    name: str
    role: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "name", _require_nonempty_str("name", self.name))
        object.__setattr__(self, "role", _require_nonempty_str("role", self.role))

    def to_dict(self) -> dict[str, object]:
        return {"name": self.name, "role": self.role}

    @classmethod
    def from_dict(cls, payload: object) -> "FireContractProvenance":
        if not isinstance(payload, dict):
            raise TypeError("contract provenance payload must be a dict")
        return cls(name=payload.get("name"), role=payload.get("role"))


@dataclass(frozen=True)
class FireWitnessRequirement:
    name: str
    freshness: str
    lower: int
    upper: int
    contract: FireContractProvenance | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "name", _require_nonempty_str("name", self.name))
        object.__setattr__(self, "freshness", _require_nonempty_str("freshness", self.freshness))
        object.__setattr__(self, "lower", _require_int("lower", self.lower))
        object.__setattr__(self, "upper", _require_int("upper", self.upper))
        if self.contract is not None and not isinstance(self.contract, FireContractProvenance):
            raise TypeError("contract must be a FireContractProvenance")
        if self.lower > self.upper:
            raise ValueError("witness bound out of order")

    def to_dict(self) -> dict[str, object]:
        payload = {
            "name": self.name,
            "freshness": self.freshness,
            "bound": {"lower": self.lower, "upper": self.upper},
        }
        if self.contract is not None:
            payload["contract"] = self.contract.to_dict()
        return payload

    @classmethod
    def from_dict(cls, payload: object) -> "FireWitnessRequirement":
        if not isinstance(payload, dict):
            raise TypeError("witness payload must be a dict")
        bound = payload.get("bound")
        if not isinstance(bound, dict):
            raise TypeError("witness bound must be a dict")
        return cls(
            name=payload.get("name"),
            freshness=payload.get("freshness"),
            lower=bound.get("lower"),
            upper=bound.get("upper"),
            contract=None if payload.get("contract") is None else FireContractProvenance.from_dict(payload.get("contract")),
        )


@dataclass(frozen=True)
class FireImportedInterfaceRequirement:
    name: str
    interface_object_id: str
    interface_output: str
    unit: str
    lower: int
    upper: int
    contract: FireContractProvenance | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "name", _require_nonempty_str("name", self.name))
        object.__setattr__(self, "interface_object_id", _require_nonempty_str("interface_object_id", self.interface_object_id))
        object.__setattr__(self, "interface_output", _require_nonempty_str("interface_output", self.interface_output))
        object.__setattr__(self, "unit", _require_nonempty_str("unit", self.unit))
        object.__setattr__(self, "lower", _require_int("lower", self.lower))
        object.__setattr__(self, "upper", _require_int("upper", self.upper))
        if self.contract is not None and not isinstance(self.contract, FireContractProvenance):
            raise TypeError("contract must be a FireContractProvenance")
        if self.lower > self.upper:
            raise ValueError("imported interface bound out of order")

    def to_dict(self) -> dict[str, object]:
        payload = {
            "name": self.name,
            "interface_object_id": self.interface_object_id,
            "interface_output": self.interface_output,
            "unit": self.unit,
            "bound": {"lower": self.lower, "upper": self.upper},
        }
        if self.contract is not None:
            payload["contract"] = self.contract.to_dict()
        return payload

    @classmethod
    def from_dict(cls, payload: object) -> "FireImportedInterfaceRequirement":
        if not isinstance(payload, dict):
            raise TypeError("imported interface payload must be a dict")
        bound = payload.get("bound")
        if not isinstance(bound, dict):
            raise TypeError("imported interface bound must be a dict")
        return cls(
            name=payload.get("name"),
            interface_object_id=payload.get("interface_object_id"),
            interface_output=payload.get("interface_output"),
            unit=payload.get("unit"),
            lower=bound.get("lower"),
            upper=bound.get("upper"),
            contract=None if payload.get("contract") is None else FireContractProvenance.from_dict(payload.get("contract")),
        )


@dataclass(frozen=True)
class FireEvidenceLabels:
    unit_safety: str
    payoff_bound: str
    collateral_sufficiency: str
    witness_policy: str
    settlement_replay: str
    kernel_semantics: str

    def __post_init__(self) -> None:
        for field_name in (
            "unit_safety",
            "payoff_bound",
            "collateral_sufficiency",
            "witness_policy",
            "settlement_replay",
            "kernel_semantics",
        ):
            value = _require_nonempty_str(field_name, getattr(self, field_name))
            if value not in _EVIDENCE_LEVELS:
                raise ValueError(f"{field_name} has unsupported evidence level: {value}")
            object.__setattr__(self, field_name, value)

    def to_dict(self) -> dict[str, object]:
        return {
            "unit_safety": self.unit_safety,
            "payoff_bound": self.payoff_bound,
            "collateral_sufficiency": self.collateral_sufficiency,
            "witness_policy": self.witness_policy,
            "settlement_replay": self.settlement_replay,
            "kernel_semantics": self.kernel_semantics,
        }

    @classmethod
    def from_dict(cls, payload: object) -> "FireEvidenceLabels":
        if not isinstance(payload, dict):
            raise TypeError("evidence payload must be a dict")
        return cls(
            unit_safety=payload.get("unit_safety"),
            payoff_bound=payload.get("payoff_bound"),
            collateral_sufficiency=payload.get("collateral_sufficiency"),
            witness_policy=payload.get("witness_policy"),
            settlement_replay=payload.get("settlement_replay"),
            kernel_semantics=payload.get("kernel_semantics"),
        )


DEFAULT_FIRE_EVIDENCE = FireEvidenceLabels(
    unit_safety="proved",
    payoff_bound="proved",
    collateral_sufficiency="proved",
    witness_policy="contract",
    settlement_replay="implemented",
    kernel_semantics="proved",
)


def default_fire_instance_gate_claims() -> FireInstanceGateClaims:
    return FireInstanceGateClaims(
        param_ok="implemented",
        authorization_ok="implemented",
        nonce_ok="implemented",
        maturity_ok="implemented",
        window_ok="implemented",
    )


@dataclass(frozen=True)
class FireObjectManifest:
    object_name: str
    object_version: str
    object_family: str
    settlement_asset: str
    payoff_summary: str
    artifact_lower: int
    artifact_upper: int
    holder_collateral_required: int
    writer_collateral_required: int
    ir_hash: str
    cert_sha256: str
    parameters: tuple[FireParameterRequirement, ...]
    imported_interfaces: tuple[FireImportedInterfaceRequirement, ...]
    witnesses: tuple[FireWitnessRequirement, ...]
    evidence: FireEvidenceLabels
    instance_policy: FireInstancePolicy
    manifest_hash: str
    schema: str = MANIFEST_SCHEMA

    def __post_init__(self) -> None:
        object.__setattr__(self, "object_name", _require_nonempty_str("object_name", self.object_name))
        object.__setattr__(self, "object_version", _require_nonempty_str("object_version", self.object_version))
        object.__setattr__(self, "object_family", _require_nonempty_str("object_family", self.object_family))
        object.__setattr__(self, "settlement_asset", _require_nonempty_str("settlement_asset", self.settlement_asset))
        object.__setattr__(self, "payoff_summary", _require_nonempty_str("payoff_summary", self.payoff_summary))
        object.__setattr__(self, "artifact_lower", _require_int("artifact_lower", self.artifact_lower))
        object.__setattr__(self, "artifact_upper", _require_int("artifact_upper", self.artifact_upper))
        object.__setattr__(self, "holder_collateral_required", _require_int("holder_collateral_required", self.holder_collateral_required))
        object.__setattr__(self, "writer_collateral_required", _require_int("writer_collateral_required", self.writer_collateral_required))
        object.__setattr__(self, "ir_hash", _require_sha256_prefixed("ir_hash", self.ir_hash))
        object.__setattr__(self, "cert_sha256", _require_sha256_prefixed("cert_sha256", self.cert_sha256))
        object.__setattr__(self, "manifest_hash", _require_sha256_prefixed("manifest_hash", self.manifest_hash))
        if self.schema != MANIFEST_SCHEMA:
            raise ValueError(f"unsupported manifest schema: {self.schema}")
        if not isinstance(self.parameters, tuple):
            raise TypeError("parameters must be a tuple")
        if any(not isinstance(item, FireParameterRequirement) for item in self.parameters):
            raise TypeError("parameters must contain FireParameterRequirement values")
        if not isinstance(self.imported_interfaces, tuple):
            raise TypeError("imported_interfaces must be a tuple")
        if any(not isinstance(item, FireImportedInterfaceRequirement) for item in self.imported_interfaces):
            raise TypeError("imported_interfaces must contain FireImportedInterfaceRequirement values")
        if not isinstance(self.witnesses, tuple):
            raise TypeError("witnesses must be a tuple")
        if any(not isinstance(item, FireWitnessRequirement) for item in self.witnesses):
            raise TypeError("witnesses must contain FireWitnessRequirement values")
        if not isinstance(self.evidence, FireEvidenceLabels):
            raise TypeError("evidence must be a FireEvidenceLabels")
        if not isinstance(self.instance_policy, FireInstancePolicy):
            raise TypeError("instance_policy must be a FireInstancePolicy")
        if self.artifact_lower > self.artifact_upper:
            raise ValueError("artifact interval out of order")
        if self.holder_collateral_required < 0 or self.writer_collateral_required < 0:
            raise ValueError("collateral requirements must be non-negative")
        parameter_names = [item.name for item in self.parameters]
        if len(parameter_names) != len(set(parameter_names)):
            raise ValueError("parameters must have unique names")

    def payload_without_hash(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "object_name": self.object_name,
            "object_version": self.object_version,
            "object_family": self.object_family,
            "settlement_asset": self.settlement_asset,
            "payoff_summary": self.payoff_summary,
            "artifact_bound": {"lower": self.artifact_lower, "upper": self.artifact_upper},
            "collateral_required": {
                "holder": self.holder_collateral_required,
                "writer": self.writer_collateral_required,
            },
            "ir_hash": self.ir_hash,
            "cert_sha256": self.cert_sha256,
            "parameters": [item.to_dict() for item in self.parameters],
            "imported_interfaces": [item.to_dict() for item in self.imported_interfaces],
            "witnesses": [item.to_dict() for item in self.witnesses],
            "evidence": self.evidence.to_dict(),
            "instance_policy": self.instance_policy.to_dict(),
        }

    def to_dict(self) -> dict[str, object]:
        payload = self.payload_without_hash()
        payload["manifest_hash"] = self.manifest_hash
        return payload

    @classmethod
    def build(
        cls,
        *,
        object_name: str,
        object_version: str,
        object_family: str,
        settlement_asset: str,
        payoff_summary: str,
        artifact_lower: int,
        artifact_upper: int,
        holder_collateral_required: int,
        writer_collateral_required: int,
        ir_hash: str,
        cert_sha256: str,
        parameters: tuple[FireParameterRequirement, ...] = (),
        imported_interfaces: tuple[FireImportedInterfaceRequirement, ...],
        witnesses: tuple[FireWitnessRequirement, ...],
        evidence: FireEvidenceLabels,
        instance_policy: FireInstancePolicy = FireInstancePolicy(),
    ) -> "FireObjectManifest":
        payload_without_hash = {
            "schema": MANIFEST_SCHEMA,
            "object_name": object_name,
            "object_version": object_version,
            "object_family": object_family,
            "settlement_asset": settlement_asset,
            "payoff_summary": payoff_summary,
            "artifact_bound": {"lower": artifact_lower, "upper": artifact_upper},
            "collateral_required": {
                "holder": holder_collateral_required,
                "writer": writer_collateral_required,
            },
            "ir_hash": ir_hash,
            "cert_sha256": cert_sha256,
            "parameters": [item.to_dict() for item in parameters],
            "imported_interfaces": [item.to_dict() for item in imported_interfaces],
            "witnesses": [item.to_dict() for item in witnesses],
            "evidence": evidence.to_dict(),
            "instance_policy": instance_policy.to_dict(),
        }
        return cls(
            object_name=object_name,
            object_version=object_version,
            object_family=object_family,
            settlement_asset=settlement_asset,
            payoff_summary=payoff_summary,
            artifact_lower=artifact_lower,
            artifact_upper=artifact_upper,
            holder_collateral_required=holder_collateral_required,
            writer_collateral_required=writer_collateral_required,
            ir_hash=ir_hash,
            cert_sha256=cert_sha256,
            parameters=parameters,
            imported_interfaces=imported_interfaces,
            witnesses=witnesses,
            evidence=evidence,
            instance_policy=instance_policy,
            manifest_hash=fire_manifest_sha256(payload_without_hash),
        )

    @classmethod
    def from_dict(cls, payload: object) -> "FireObjectManifest":
        if not isinstance(payload, dict):
            raise TypeError("manifest payload must be a dict")
        artifact_bound = payload.get("artifact_bound")
        if not isinstance(artifact_bound, dict):
            raise TypeError("artifact_bound must be a dict")
        collateral_required = payload.get("collateral_required")
        if not isinstance(collateral_required, dict):
            raise TypeError("collateral_required must be a dict")
        parameters_payload = payload.get("parameters", [])
        if not isinstance(parameters_payload, list):
            raise TypeError("parameters must be a list")
        imported_interfaces_payload = payload.get("imported_interfaces", [])
        if not isinstance(imported_interfaces_payload, list):
            raise TypeError("imported_interfaces must be a list")
        witnesses_payload = payload.get("witnesses")
        if not isinstance(witnesses_payload, list):
            raise TypeError("witnesses must be a list")
        return cls(
            schema=payload.get("schema", MANIFEST_SCHEMA),
            object_name=payload.get("object_name"),
            object_version=payload.get("object_version"),
            object_family=payload.get("object_family"),
            settlement_asset=payload.get("settlement_asset"),
            payoff_summary=payload.get("payoff_summary"),
            artifact_lower=artifact_bound.get("lower"),
            artifact_upper=artifact_bound.get("upper"),
            holder_collateral_required=collateral_required.get("holder"),
            writer_collateral_required=collateral_required.get("writer"),
            ir_hash=payload.get("ir_hash"),
            cert_sha256=payload.get("cert_sha256"),
            parameters=tuple(FireParameterRequirement.from_dict(item) for item in parameters_payload),
            imported_interfaces=tuple(FireImportedInterfaceRequirement.from_dict(item) for item in imported_interfaces_payload),
            witnesses=tuple(FireWitnessRequirement.from_dict(item) for item in witnesses_payload),
            evidence=FireEvidenceLabels.from_dict(payload.get("evidence")),
            instance_policy=FireInstancePolicy.from_dict(payload.get("instance_policy")),
            manifest_hash=payload.get("manifest_hash"),
        )


def verify_fire_object_manifest(manifest: FireObjectManifest) -> tuple[bool, str | None]:
    expected_holder = max(0, -manifest.artifact_lower)
    expected_writer = max(0, manifest.artifact_upper)
    if manifest.holder_collateral_required != expected_holder:
        return False, "holder_collateral_mismatch"
    if manifest.writer_collateral_required != expected_writer:
        return False, "writer_collateral_mismatch"
    expected_hash = fire_manifest_sha256(manifest.payload_without_hash())
    if manifest.manifest_hash != expected_hash:
        legacy_expected_hash = None
        if not manifest.imported_interfaces:
            legacy_expected_hash = fire_manifest_sha256(_legacy_payload_without_imported_interfaces(manifest))
        if legacy_expected_hash is not None and manifest.manifest_hash == legacy_expected_hash:
            return True, None
        return False, "manifest_hash_mismatch"
    return True, None


def expected_fire_instance_gate_claims(_manifest: FireObjectManifest) -> FireInstanceGateClaims:
    return default_fire_instance_gate_claims()


def write_fire_object_manifest(path: str | Path, manifest: FireObjectManifest) -> str:
    file_path = Path(path)
    file_path.write_bytes(canonical_manifest_json_bytes(manifest))
    return fire_manifest_file_sha256(manifest)


def load_fire_object_manifest(path: str | Path) -> tuple[FireObjectManifest, str]:
    file_path = Path(path)
    payload_bytes = file_path.read_bytes()
    payload = json.loads(payload_bytes.decode("utf-8"))
    manifest = FireObjectManifest.from_dict(payload)
    file_sha256 = "sha256:" + hashlib.sha256(payload_bytes).hexdigest()
    return manifest, file_sha256


def render_fire_object_card(manifest: FireObjectManifest) -> str:
    parameter_lines = "\n".join(
        f"  {item.name} [{item.minimum}, {item.maximum}] unit={item.unit} :: {item.description}"
        for item in manifest.parameters
    )
    imported_interface_lines = "\n".join(
        (
            f"  {item.name} <= {item.interface_object_id}.{item.interface_output} "
            f"[{item.lower}, {item.upper}] unit={item.unit}"
            + ("" if item.contract is None else f" contract={item.contract.name} role={item.contract.role}")
        )
        for item in manifest.imported_interfaces
    )
    witness_lines = "\n".join(
        (
            f"  {item.name} [{item.lower}, {item.upper}] freshness={item.freshness}"
            + ("" if item.contract is None else f" contract={item.contract.name} role={item.contract.role}")
        )
        for item in manifest.witnesses
    )
    evidence = manifest.evidence
    return "\n".join(
        [
            "FIRE Object:",
            f"  {manifest.object_name} {manifest.object_version}",
            "",
            "Payoff:",
            f"  {manifest.payoff_summary}",
            "",
            "Settlement:",
            f"  {manifest.settlement_asset}",
            "",
            "Parameters:",
            parameter_lines or "  none",
            "",
            "Payoff bound:",
            f"  [{manifest.artifact_lower}, {manifest.artifact_upper}]",
            "",
            "Collateral required:",
            f"  holder: {manifest.holder_collateral_required}",
            f"  writer: {manifest.writer_collateral_required}",
            "",
            "Imported interfaces:",
            imported_interface_lines or "  none",
            "",
            "Witnesses:",
            witness_lines or "  none",
            "",
            "Evidence:",
            f"  unit safety: {evidence.unit_safety}",
            f"  payoff bound: {evidence.payoff_bound}",
            f"  collateral sufficiency: {evidence.collateral_sufficiency}",
            f"  witness policy: {evidence.witness_policy}",
            f"  settlement replay: {evidence.settlement_replay}",
            f"  kernel semantics: {evidence.kernel_semantics}",
            "",
            "Instance policy:",
            f"  authorization: {manifest.instance_policy.authorization_mode}",
            f"  required parties: {', '.join(manifest.instance_policy.required_party_roles) or 'none'}",
            f"  nonce required: {manifest.instance_policy.nonce_required}",
            f"  maturity required: {manifest.instance_policy.maturity_required}",
            f"  settlement window required: {manifest.instance_policy.settlement_window_required}",
            "",
            f"Manifest hash: {manifest.manifest_hash}",
        ]
    )


__all__ = [
    "DEFAULT_FIRE_EVIDENCE",
    "MANIFEST_SCHEMA",
    "FireContractProvenance",
    "FireEvidenceLabels",
    "FireImportedInterfaceRequirement",
    "FireInstanceGateClaims",
    "FireInstancePolicy",
    "FireObjectManifest",
    "FireParameterRequirement",
    "FireWitnessRequirement",
    "canonical_manifest_json_bytes",
    "default_fire_instance_gate_claims",
    "expected_fire_instance_gate_claims",
    "fire_manifest_file_sha256",
    "fire_manifest_sha256",
    "load_fire_object_manifest",
    "render_fire_object_card",
    "verify_fire_object_manifest",
    "write_fire_object_manifest",
]

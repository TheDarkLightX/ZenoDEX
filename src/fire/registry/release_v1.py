from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path

from src.fire.registry.index_v1 import (
    FireRegistryContractReceipt,
    FireRegistryInstanceGateClaimSummary,
    FireRegistryInstanceGateSummary,
    verify_fire_registry_index,
)
from src.fire.verifier.cert_v1 import _require_sha256_prefixed


RELEASE_METADATA_SCHEMA = "zenodex/fire-registry-release-metadata/v1"


def _require_nonempty_str(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    return value


def _canonical_json_bytes(payload: dict[str, object]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def _sha256_bytes(payload: bytes) -> str:
    return "sha256:" + hashlib.sha256(payload).hexdigest()


@dataclass(frozen=True)
class FireRegistryReleaseMetadata:
    snapshot_name: str
    index_path: str
    index_hash: str
    index_file_sha256: str
    require_signature: bool
    instance_gate_summary: FireRegistryInstanceGateSummary
    certificate_instance_gate_summary: FireRegistryInstanceGateClaimSummary
    contract_receipts: tuple[FireRegistryContractReceipt, ...] = ()
    signer_pubkey: str | None = None
    schema: str = RELEASE_METADATA_SCHEMA

    def __post_init__(self) -> None:
        object.__setattr__(self, "snapshot_name", _require_nonempty_str("snapshot_name", self.snapshot_name))
        object.__setattr__(self, "index_path", _require_nonempty_str("index_path", self.index_path))
        object.__setattr__(self, "index_hash", _require_sha256_prefixed("index_hash", self.index_hash))
        object.__setattr__(self, "index_file_sha256", _require_sha256_prefixed("index_file_sha256", self.index_file_sha256))
        if not isinstance(self.require_signature, bool):
            raise TypeError("require_signature must be a bool")
        if not isinstance(self.instance_gate_summary, FireRegistryInstanceGateSummary):
            raise TypeError("instance_gate_summary must be a FireRegistryInstanceGateSummary")
        if not isinstance(self.certificate_instance_gate_summary, FireRegistryInstanceGateClaimSummary):
            raise TypeError("certificate_instance_gate_summary must be a FireRegistryInstanceGateClaimSummary")
        if not isinstance(self.contract_receipts, tuple):
            raise TypeError("contract_receipts must be a tuple")
        if any(not isinstance(item, FireRegistryContractReceipt) for item in self.contract_receipts):
            raise TypeError("contract_receipts must contain FireRegistryContractReceipt values")
        if self.signer_pubkey is not None:
            object.__setattr__(self, "signer_pubkey", _require_nonempty_str("signer_pubkey", self.signer_pubkey))
        if self.require_signature and self.signer_pubkey is None:
            raise ValueError("require_signature requires signer_pubkey")
        if self.schema != RELEASE_METADATA_SCHEMA:
            raise ValueError(f"unsupported release metadata schema: {self.schema}")

    def to_dict(self) -> dict[str, object]:
        payload = {
            "schema": self.schema,
            "snapshot_name": self.snapshot_name,
            "index_path": self.index_path,
            "index_hash": self.index_hash,
            "index_file_sha256": self.index_file_sha256,
            "require_signature": self.require_signature,
            "instance_gate_summary": self.instance_gate_summary.to_dict(),
            "certificate_instance_gate_summary": self.certificate_instance_gate_summary.to_dict(),
            "signer_pubkey": self.signer_pubkey,
        }
        if self.contract_receipts:
            payload["contracts"] = [receipt.to_dict() for receipt in self.contract_receipts]
        return payload

    @classmethod
    def from_dict(cls, payload: object) -> "FireRegistryReleaseMetadata":
        if not isinstance(payload, dict):
            raise TypeError("release metadata payload must be an object")
        contracts_raw = payload.get("contracts", [])
        if not isinstance(contracts_raw, list):
            raise TypeError("contracts must be a list")
        instance_gate_summary_raw = payload.get("instance_gate_summary")
        certificate_instance_gate_summary_raw = payload.get("certificate_instance_gate_summary")
        if not isinstance(instance_gate_summary_raw, dict):
            raise TypeError("instance_gate_summary must be an object")
        if not isinstance(certificate_instance_gate_summary_raw, dict):
            raise TypeError("certificate_instance_gate_summary must be an object")
        return cls(
            schema=payload.get("schema", RELEASE_METADATA_SCHEMA),
            snapshot_name=payload.get("snapshot_name"),
            index_path=payload.get("index_path"),
            index_hash=payload.get("index_hash"),
            index_file_sha256=payload.get("index_file_sha256"),
            require_signature=payload.get("require_signature"),
            instance_gate_summary=FireRegistryInstanceGateSummary.from_dict(instance_gate_summary_raw),
            certificate_instance_gate_summary=FireRegistryInstanceGateClaimSummary.from_dict(certificate_instance_gate_summary_raw),
            contract_receipts=tuple(FireRegistryContractReceipt.from_dict(item) for item in contracts_raw),
            signer_pubkey=payload.get("signer_pubkey"),
        )


def fire_registry_release_metadata_file_sha256(metadata: FireRegistryReleaseMetadata) -> str:
    return _sha256_bytes(_canonical_json_bytes(metadata.to_dict()))


def write_fire_registry_release_metadata(
    metadata_path: str | Path,
    *,
    snapshot_name: str,
    index_path: str,
    index_hash: str,
    index_file_sha256: str,
    require_signature: bool,
    instance_gate_summary: FireRegistryInstanceGateSummary,
    certificate_instance_gate_summary: FireRegistryInstanceGateClaimSummary,
    contract_receipts: tuple[FireRegistryContractReceipt, ...] = (),
    signer_pubkey: str | None = None,
) -> tuple[FireRegistryReleaseMetadata, str]:
    metadata = FireRegistryReleaseMetadata(
        snapshot_name=snapshot_name,
        index_path=index_path,
        index_hash=index_hash,
        index_file_sha256=index_file_sha256,
        require_signature=require_signature,
        instance_gate_summary=instance_gate_summary,
        certificate_instance_gate_summary=certificate_instance_gate_summary,
        contract_receipts=contract_receipts,
        signer_pubkey=signer_pubkey,
    )
    path = Path(metadata_path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(_canonical_json_bytes(metadata.to_dict()))
    return metadata, fire_registry_release_metadata_file_sha256(metadata)


def load_fire_registry_release_metadata(metadata_path: str | Path) -> tuple[FireRegistryReleaseMetadata, str]:
    path = Path(metadata_path)
    payload = json.loads(path.read_text(encoding="utf-8"))
    metadata = FireRegistryReleaseMetadata.from_dict(payload)
    return metadata, _sha256_bytes(path.read_bytes())


def verify_fire_registry_release_metadata(
    metadata_path: str | Path,
    *,
    expected_snapshot_name: str | None = None,
    expected_metadata_file_sha256: str | None = None,
) -> tuple[bool, str | None, FireRegistryReleaseMetadata | None]:
    try:
        metadata, metadata_file_sha256 = load_fire_registry_release_metadata(metadata_path)
    except (FileNotFoundError, OSError, ValueError, TypeError, KeyError, IndexError, AttributeError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        return False, f"release_metadata_load_failed:{exc}", None

    if expected_snapshot_name is not None and metadata.snapshot_name != expected_snapshot_name:
        return False, "expected_snapshot_name_mismatch", None
    if expected_metadata_file_sha256 is not None and metadata_file_sha256 != expected_metadata_file_sha256:
        return False, "expected_release_metadata_file_sha_mismatch", None
    return True, None, metadata


def verify_fire_registry_release(
    metadata_path: str | Path,
    *,
    expected_snapshot_name: str | None = None,
    expected_metadata_file_sha256: str | None = None,
) -> tuple[bool, str | None, FireRegistryReleaseMetadata | None]:
    ok, err, metadata = verify_fire_registry_release_metadata(
        metadata_path,
        expected_snapshot_name=expected_snapshot_name,
        expected_metadata_file_sha256=expected_metadata_file_sha256,
    )
    if not ok or metadata is None:
        return ok, err, metadata

    metadata_file = Path(metadata_path).resolve()
    index_path = metadata_file.parent / metadata.index_path
    ok, err, index = verify_fire_registry_index(
        index_path,
        expected_index_hash=metadata.index_hash,
        expected_index_file_sha256=metadata.index_file_sha256,
        expected_signer_pubkey=metadata.signer_pubkey,
        require_signature=metadata.require_signature,
    )
    if not ok:
        return False, f"release_index_invalid:{err or 'unknown'}", None
    if index is not None and metadata.instance_gate_summary != index.instance_gate_summary:
        return False, "release_instance_gate_summary_mismatch", None
    if index is not None and metadata.certificate_instance_gate_summary != index.certificate_instance_gate_summary:
        return False, "release_certificate_instance_gate_summary_mismatch", None
    if index is not None and metadata.contract_receipts and metadata.contract_receipts != index.contract_receipts:
        return False, "release_contract_receipts_mismatch", None
    return True, None, metadata


__all__ = [
    "RELEASE_METADATA_SCHEMA",
    "FireRegistryReleaseMetadata",
    "fire_registry_release_metadata_file_sha256",
    "load_fire_registry_release_metadata",
    "verify_fire_registry_release",
    "verify_fire_registry_release_metadata",
    "write_fire_registry_release_metadata",
]

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from src.fire.registry.index_v1 import FireRegistryContractReceipt
from src.fire.registry.release_v1 import (
    FireRegistryReleaseMetadata,
    load_fire_registry_release_metadata,
    verify_fire_registry_release,
)


FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA = "zenodex/fire-registry-deployment-contract/v1"
FIRE_REGISTRY_DEPLOYMENT_RECEIPT_SCHEMA = "zenodex/fire-registry-deployment-receipt/v1"


def _canonical_json_bytes(payload: object) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _payload_hash(payload: object) -> str:
    return hashlib.sha256(_canonical_json_bytes(payload)).hexdigest()


def _sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _path_for_receipt(path: Path, *, base_dir: Path) -> str:
    resolved = path.resolve()
    if resolved.is_relative_to(base_dir):
        return resolved.relative_to(base_dir).as_posix()
    return str(resolved)


def load_fire_registry_deployment_contract(path: str | Path) -> dict[str, Any]:
    contract_file = Path(path).resolve()
    payload = json.loads(contract_file.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("deployment contract must be a JSON object")
    if payload.get("schema") != FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA:
        raise ValueError("deployment contract schema mismatch")

    contract_id = payload.get("contract_id")
    snapshot_name = payload.get("snapshot_name")
    required_signer_pubkey = payload.get("required_signer_pubkey")
    require_signature = payload.get("require_signature")
    description = payload.get("description", "")
    contracts = payload.get("contracts", [])
    if not isinstance(contract_id, str) or not contract_id:
        raise ValueError("deployment contract contract_id must be a non-empty string")
    if not isinstance(snapshot_name, str) or not snapshot_name:
        raise ValueError("deployment contract snapshot_name must be a non-empty string")
    if not isinstance(required_signer_pubkey, str) or not required_signer_pubkey:
        raise ValueError("deployment contract required_signer_pubkey must be a non-empty string")
    if not isinstance(require_signature, bool):
        raise ValueError("deployment contract require_signature must be a bool")
    if not isinstance(description, str):
        raise ValueError("deployment contract description must be a string")
    if not isinstance(contracts, list):
        raise ValueError("deployment contract contracts must be a list")
    contract_receipts = tuple(FireRegistryContractReceipt.from_dict(item) for item in contracts)

    normalized = {
        "schema": FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA,
        "contract_id": contract_id,
        "snapshot_name": snapshot_name,
        "required_signer_pubkey": required_signer_pubkey,
        "require_signature": require_signature,
        "description": description,
    }
    if contract_receipts:
        normalized["contracts"] = [item.to_dict() for item in contract_receipts]
    return {**normalized, "contract_hash": _payload_hash(normalized)}


def build_fire_registry_deployment_receipt(
    contract_path: str | Path,
    release_metadata_path: str | Path,
) -> dict[str, object]:
    contract_file = Path(contract_path).resolve()
    metadata_file = Path(release_metadata_path).resolve()

    contract = load_fire_registry_deployment_contract(contract_file)
    ok, err, metadata = verify_fire_registry_release(
        metadata_file,
        expected_snapshot_name=contract["snapshot_name"],
    )
    if not ok or metadata is None:
        raise ValueError(f"release metadata not accepted: {err or 'release_verification_failed'}")
    if metadata.signer_pubkey != contract["required_signer_pubkey"]:
        raise ValueError("release signer does not match deployment contract")
    if metadata.require_signature != contract["require_signature"]:
        raise ValueError("release signature requirement does not match deployment contract")
    if "contracts" in contract and contract["contracts"] != [item.to_dict() for item in metadata.contract_receipts]:
        raise ValueError("release contracts do not match deployment contract")

    payload = {
        "schema": FIRE_REGISTRY_DEPLOYMENT_RECEIPT_SCHEMA,
        "contract_path": str(contract_file),
        "contract_sha256": _sha256_path(contract_file),
        "contract_hash": contract["contract_hash"],
        "release_metadata_path": str(metadata_file),
        "release_metadata_sha256": _sha256_path(metadata_file),
        "contract_id": contract["contract_id"],
        "snapshot_name": contract["snapshot_name"],
        "required_signer_pubkey": contract["required_signer_pubkey"],
        "require_signature": contract["require_signature"],
        "index_hash": metadata.index_hash,
        "index_file_sha256": metadata.index_file_sha256,
        "signer_pubkey": metadata.signer_pubkey,
    }
    if metadata.contract_receipts:
        payload["contracts"] = [receipt.to_dict() for receipt in metadata.contract_receipts]
    return {**payload, "receipt_sha256": _payload_hash(payload)}


def write_fire_registry_deployment_receipt(
    receipt_path: str | Path,
    contract_path: str | Path,
    release_metadata_path: str | Path,
) -> dict[str, object]:
    receipt_file = Path(receipt_path).resolve()
    receipt_file.parent.mkdir(parents=True, exist_ok=True)
    base_dir = receipt_file.parent.resolve()
    contract_file = Path(contract_path).resolve()
    metadata_file = Path(release_metadata_path).resolve()

    receipt = build_fire_registry_deployment_receipt(contract_file, metadata_file)
    stored = {
        **receipt,
        "contract_path": _path_for_receipt(contract_file, base_dir=base_dir),
        "release_metadata_path": _path_for_receipt(metadata_file, base_dir=base_dir),
    }
    stored["receipt_sha256"] = _payload_hash({k: v for k, v in stored.items() if k != "receipt_sha256"})
    receipt_file.write_text(json.dumps(stored, sort_keys=True, indent=2), encoding="utf-8")
    return stored


def check_fire_registry_deployment_receipt(
    receipt_path: str | Path,
    *,
    require_current: bool = False,
) -> dict[str, Any]:
    receipt_file = Path(receipt_path).resolve()
    try:
        payload = json.loads(receipt_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return {"accepted": False, "violated_checks": ["parse_error"], "error": str(exc)}

    if not isinstance(payload, dict):
        return {"accepted": False, "violated_checks": ["schema_not_object"]}
    if payload.get("schema") != FIRE_REGISTRY_DEPLOYMENT_RECEIPT_SCHEMA:
        return {"accepted": False, "violated_checks": ["schema_mismatch"]}

    violations: list[str] = []
    expected_hash = payload.get("receipt_sha256")
    observed_hash = _payload_hash({k: v for k, v in payload.items() if k != "receipt_sha256"})
    if expected_hash != observed_hash:
        violations.append("receipt_hash_mismatch")

    contract_path = payload.get("contract_path")
    release_metadata_path = payload.get("release_metadata_path")
    if not isinstance(contract_path, str):
        violations.append("contract_path_invalid")
    if not isinstance(release_metadata_path, str):
        violations.append("release_metadata_path_invalid")
    if violations:
        return {"accepted": False, "violated_checks": violations}

    contract_file = Path(contract_path)
    if not contract_file.is_absolute():
        contract_file = (receipt_file.parent / contract_file).resolve()
    else:
        contract_file = contract_file.resolve()
    metadata_file = Path(release_metadata_path)
    if not metadata_file.is_absolute():
        metadata_file = (receipt_file.parent / metadata_file).resolve()
    else:
        metadata_file = metadata_file.resolve()
    if not contract_file.exists():
        violations.append("contract_missing")
    if not metadata_file.exists():
        violations.append("release_metadata_missing")

    rebuilt = None
    if not violations:
        if payload.get("contract_sha256") != _sha256_path(contract_file):
            violations.append("contract_sha256_mismatch")
        if payload.get("release_metadata_sha256") != _sha256_path(metadata_file):
            violations.append("release_metadata_sha256_mismatch")

        try:
            contract = load_fire_registry_deployment_contract(contract_file)
        except ValueError as exc:
            violations.append(f"contract_error:{exc}")
            contract = None

        try:
            metadata, _ = load_fire_registry_release_metadata(metadata_file)
        except (OSError, ValueError, TypeError, json.JSONDecodeError) as exc:
            violations.append(f"release_metadata_error:{exc}")
            metadata = None

        if contract is not None and payload.get("contract_hash") != contract["contract_hash"]:
            violations.append("contract_hash_mismatch")

        if contract is not None and metadata is not None and not violations:
            try:
                rebuilt = build_fire_registry_deployment_receipt(contract_file, metadata_file)
                rebuilt = {
                    **rebuilt,
                    "contract_path": _path_for_receipt(contract_file, base_dir=receipt_file.parent.resolve()),
                    "release_metadata_path": _path_for_receipt(metadata_file, base_dir=receipt_file.parent.resolve()),
                }
                rebuilt["receipt_sha256"] = _payload_hash({k: v for k, v in rebuilt.items() if k != "receipt_sha256"})
            except ValueError as exc:
                violations.append(f"rebuild_error:{exc}")

    if rebuilt is not None:
        for field in (
            "contract_id",
            "snapshot_name",
            "required_signer_pubkey",
            "require_signature",
            "index_hash",
            "index_file_sha256",
            "signer_pubkey",
        ):
            if payload.get(field) != rebuilt[field]:
                violations.append(f"{field}_mismatch")
        if "contracts" in payload and payload.get("contracts") != rebuilt.get("contracts"):
            violations.append("contracts_mismatch")
        if require_current and payload != rebuilt:
            violations.append("current_receipt_mismatch")

    return {
        "accepted": not violations,
        "violated_checks": violations,
        "rebuilt_receipt": rebuilt if require_current and rebuilt is not None else None,
    }


def enforce_fire_registry_deployment_contract(
    contract_path: str | Path,
    *,
    snapshot_name: str,
    signer_pubkey: str,
    require_signature: bool,
) -> tuple[bool, str | None, dict[str, Any] | None]:
    try:
        contract = load_fire_registry_deployment_contract(contract_path)
    except (OSError, ValueError, TypeError, json.JSONDecodeError) as exc:
        return False, f"deployment_contract_load_failed:{exc}", None

    if snapshot_name != contract["snapshot_name"]:
        return False, "deployment_contract_snapshot_name_mismatch", None
    if signer_pubkey != contract["required_signer_pubkey"]:
        return False, "deployment_contract_signer_pubkey_mismatch", None
    if require_signature != contract["require_signature"]:
        return False, "deployment_contract_require_signature_mismatch", None
    return True, None, contract


__all__ = [
    "FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA",
    "FIRE_REGISTRY_DEPLOYMENT_RECEIPT_SCHEMA",
    "build_fire_registry_deployment_receipt",
    "check_fire_registry_deployment_receipt",
    "enforce_fire_registry_deployment_contract",
    "load_fire_registry_deployment_contract",
    "write_fire_registry_deployment_receipt",
]

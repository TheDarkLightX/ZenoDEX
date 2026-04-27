from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from src.fire.registry.instance_v1 import (
    FireObjectInstanceManifest,
    FireObjectParameterValue,
    FireObjectPartyBinding,
    FireSettlementWindow,
    load_fire_object_instance,
    verify_fire_object_instance,
    verify_fire_object_instance_against_manifest,
    write_fire_object_instance,
)
from src.fire.registry.lock_v1 import (
    FireObjectDependencyLock,
    build_fire_object_dependency_lock,
    load_fire_object_dependency_lock,
    verify_fire_object_dependency_lock,
    write_fire_object_dependency_lock,
)
from src.fire.registry.object_manifest_v1 import (
    FireContractProvenance,
    FireObjectManifest,
    expected_fire_instance_gate_claims,
    load_fire_object_manifest,
    verify_fire_object_manifest,
    write_fire_object_manifest,
)
from src.fire.registry.replay_input_v1 import (
    FireReplayInput,
    build_default_fire_replay_input,
    load_fire_replay_input,
    verify_fire_replay_input,
    write_fire_replay_input,
)
from src.fire.compiler.compile_receipt_v1 import write_fire_compile_receipt
from src.fire.kernel.kernel_eval_receipt_v1 import write_fire_kernel_eval_receipt
from src.fire.kernel.kernel_replay_receipt_v1 import build_fire_kernel_replay_receipt
from src.fire.kernel.kernel_receipt_v1 import write_fire_kernel_receipt
from src.fire.kernel.kernel_settlement_receipt_v1 import (
    build_fire_kernel_settlement_receipt,
)
from src.fire.verifier.cert_v1 import (
    FireIntervalCertificate,
    _require_sha256_prefixed,
    fire_cert_sha256,
    verify_instance_gate_claims,
)
from src.fire.verifier.proof_tree_cert_v1 import build_fire_proof_tree_certificate


BUNDLE_SCHEMA = "zenodex/fire-registry-bundle/v1"


def _require_nonempty_str(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    return value


def _canonical_json_bytes(payload: Mapping[str, object]) -> bytes:
    return json.dumps(dict(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def _sha256_bytes(payload: bytes) -> str:
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def certificate_json_bytes(certificate: FireIntervalCertificate) -> bytes:
    return _canonical_json_bytes(certificate.to_dict())


def card_sha256(card_text: str) -> str:
    if not isinstance(card_text, str):
        raise TypeError("card_text must be a string")
    return _sha256_bytes(card_text.encode("utf-8"))


def replay_receipt_json_bytes(payload: Mapping[str, object]) -> bytes:
    return _canonical_json_bytes(payload)


def fire_registry_bundle_sha256(payload_without_hash: Mapping[str, object]) -> str:
    return _sha256_bytes(_canonical_json_bytes(payload_without_hash))


@dataclass(frozen=True)
class FireBundleContractReceipt:
    name: str
    roles: tuple[str, ...]
    use_sites: tuple[str, ...]

    def __post_init__(self) -> None:
        object.__setattr__(self, "name", _require_nonempty_str("name", self.name))
        if not isinstance(self.roles, tuple) or any(not isinstance(item, str) or not item for item in self.roles):
            raise TypeError("roles must be a tuple of non-empty strings")
        if not isinstance(self.use_sites, tuple) or any(
            not isinstance(item, str) or not item for item in self.use_sites
        ):
            raise TypeError("use_sites must be a tuple of non-empty strings")

    def to_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "roles": list(self.roles),
            "use_sites": list(self.use_sites),
        }

    @classmethod
    def from_dict(cls, payload: object) -> "FireBundleContractReceipt":
        if not isinstance(payload, dict):
            raise TypeError("contract receipt payload must be a dict")
        roles = payload.get("roles")
        use_sites = payload.get("use_sites")
        if not isinstance(roles, list):
            raise TypeError("contract receipt roles must be a list")
        if not isinstance(use_sites, list):
            raise TypeError("contract receipt use_sites must be a list")
        return cls(
            name=payload.get("name"),
            roles=tuple(str(item) for item in roles),
            use_sites=tuple(str(item) for item in use_sites),
        )


def _build_contract_receipts(object_manifest: FireObjectManifest) -> tuple[FireBundleContractReceipt, ...]:
    grouped: dict[str, dict[str, set[str]]] = {}

    def record(contract: FireContractProvenance | None, *, use_site: str) -> None:
        if contract is None:
            return
        entry = grouped.setdefault(contract.name, {"roles": set(), "use_sites": set()})
        entry["roles"].add(contract.role)
        entry["use_sites"].add(use_site)

    for imported in object_manifest.imported_interfaces:
        record(imported.contract, use_site=f"import:{imported.name}")
    for witness in object_manifest.witnesses:
        record(witness.contract, use_site=f"witness:{witness.name}")

    return tuple(
        FireBundleContractReceipt(
            name=name,
            roles=tuple(sorted(entry["roles"])),
            use_sites=tuple(sorted(entry["use_sites"])),
        )
        for name, entry in sorted(grouped.items())
    )


@dataclass(frozen=True)
class FireRegistryBundleManifest:
    object_name: str
    object_version: str
    object_family: str
    object_manifest_path: str
    object_manifest_file_sha256: str
    object_instance_path: str
    object_instance_file_sha256: str
    object_lock_path: str
    object_lock_file_sha256: str
    certificate_path: str
    certificate_file_sha256: str
    compile_receipt_path: str | None
    compile_receipt_sha256: str | None
    kernel_receipt_path: str | None
    kernel_receipt_sha256: str | None
    kernel_eval_receipt_path: str | None
    kernel_eval_receipt_sha256: str | None
    kernel_settlement_receipt_path: str | None
    kernel_settlement_receipt_sha256: str | None
    kernel_replay_receipt_path: str | None
    kernel_replay_receipt_sha256: str | None
    proof_tree_certificate_path: str | None
    proof_tree_certificate_sha256: str | None
    object_card_path: str
    object_card_sha256: str
    replay_input_path: str | None
    replay_input_sha256: str | None
    replay_receipt_path: str | None
    replay_receipt_sha256: str | None
    bundle_hash: str
    contract_receipts: tuple[FireBundleContractReceipt, ...] = ()
    schema: str = BUNDLE_SCHEMA

    def __post_init__(self) -> None:
        object.__setattr__(self, "object_name", _require_nonempty_str("object_name", self.object_name))
        object.__setattr__(self, "object_version", _require_nonempty_str("object_version", self.object_version))
        object.__setattr__(self, "object_family", _require_nonempty_str("object_family", self.object_family))
        object.__setattr__(self, "object_manifest_path", _require_nonempty_str("object_manifest_path", self.object_manifest_path))
        object.__setattr__(self, "object_instance_path", _require_nonempty_str("object_instance_path", self.object_instance_path))
        object.__setattr__(self, "object_lock_path", _require_nonempty_str("object_lock_path", self.object_lock_path))
        object.__setattr__(self, "certificate_path", _require_nonempty_str("certificate_path", self.certificate_path))
        object.__setattr__(self, "object_card_path", _require_nonempty_str("object_card_path", self.object_card_path))
        object.__setattr__(
            self, "object_manifest_file_sha256", _require_sha256_prefixed("object_manifest_file_sha256", self.object_manifest_file_sha256)
        )
        object.__setattr__(
            self, "object_instance_file_sha256", _require_sha256_prefixed("object_instance_file_sha256", self.object_instance_file_sha256)
        )
        object.__setattr__(
            self, "object_lock_file_sha256", _require_sha256_prefixed("object_lock_file_sha256", self.object_lock_file_sha256)
        )
        object.__setattr__(
            self, "certificate_file_sha256", _require_sha256_prefixed("certificate_file_sha256", self.certificate_file_sha256)
        )
        if self.compile_receipt_path is not None:
            object.__setattr__(
                self,
                "compile_receipt_path",
                _require_nonempty_str("compile_receipt_path", self.compile_receipt_path),
            )
        if self.compile_receipt_sha256 is not None:
            object.__setattr__(
                self,
                "compile_receipt_sha256",
                _require_sha256_prefixed("compile_receipt_sha256", self.compile_receipt_sha256),
            )
        if self.kernel_receipt_path is not None:
            object.__setattr__(
                self,
                "kernel_receipt_path",
                _require_nonempty_str("kernel_receipt_path", self.kernel_receipt_path),
            )
        if self.kernel_receipt_sha256 is not None:
            object.__setattr__(
                self,
                "kernel_receipt_sha256",
                _require_sha256_prefixed("kernel_receipt_sha256", self.kernel_receipt_sha256),
            )
        if self.kernel_eval_receipt_path is not None:
            object.__setattr__(
                self,
                "kernel_eval_receipt_path",
                _require_nonempty_str("kernel_eval_receipt_path", self.kernel_eval_receipt_path),
            )
        if self.kernel_eval_receipt_sha256 is not None:
            object.__setattr__(
                self,
                "kernel_eval_receipt_sha256",
                _require_sha256_prefixed("kernel_eval_receipt_sha256", self.kernel_eval_receipt_sha256),
            )
        if self.kernel_settlement_receipt_path is not None:
            object.__setattr__(
                self,
                "kernel_settlement_receipt_path",
                _require_nonempty_str("kernel_settlement_receipt_path", self.kernel_settlement_receipt_path),
            )
        if self.kernel_settlement_receipt_sha256 is not None:
            object.__setattr__(
                self,
                "kernel_settlement_receipt_sha256",
                _require_sha256_prefixed("kernel_settlement_receipt_sha256", self.kernel_settlement_receipt_sha256),
            )
        if self.kernel_replay_receipt_path is not None:
            object.__setattr__(
                self,
                "kernel_replay_receipt_path",
                _require_nonempty_str("kernel_replay_receipt_path", self.kernel_replay_receipt_path),
            )
        if self.kernel_replay_receipt_sha256 is not None:
            object.__setattr__(
                self,
                "kernel_replay_receipt_sha256",
                _require_sha256_prefixed("kernel_replay_receipt_sha256", self.kernel_replay_receipt_sha256),
            )
        if self.proof_tree_certificate_path is not None:
            object.__setattr__(
                self,
                "proof_tree_certificate_path",
                _require_nonempty_str("proof_tree_certificate_path", self.proof_tree_certificate_path),
            )
        if self.proof_tree_certificate_sha256 is not None:
            object.__setattr__(
                self,
                "proof_tree_certificate_sha256",
                _require_sha256_prefixed(
                    "proof_tree_certificate_sha256",
                    self.proof_tree_certificate_sha256,
                ),
            )
        object.__setattr__(self, "object_card_sha256", _require_sha256_prefixed("object_card_sha256", self.object_card_sha256))
        object.__setattr__(self, "bundle_hash", _require_sha256_prefixed("bundle_hash", self.bundle_hash))
        if self.replay_input_path is not None:
            object.__setattr__(self, "replay_input_path", _require_nonempty_str("replay_input_path", self.replay_input_path))
        if self.replay_input_sha256 is not None:
            object.__setattr__(
                self, "replay_input_sha256", _require_sha256_prefixed("replay_input_sha256", self.replay_input_sha256)
            )
        if self.replay_receipt_path is not None:
            object.__setattr__(self, "replay_receipt_path", _require_nonempty_str("replay_receipt_path", self.replay_receipt_path))
        if self.replay_receipt_sha256 is not None:
            object.__setattr__(
                self, "replay_receipt_sha256", _require_sha256_prefixed("replay_receipt_sha256", self.replay_receipt_sha256)
            )
        if not isinstance(self.contract_receipts, tuple):
            raise TypeError("contract_receipts must be a tuple")
        if any(not isinstance(item, FireBundleContractReceipt) for item in self.contract_receipts):
            raise TypeError("contract_receipts must contain FireBundleContractReceipt values")
        if (self.replay_input_path is None) != (self.replay_input_sha256 is None):
            raise ValueError("replay input path/hash must appear together")
        if (self.replay_receipt_path is None) != (self.replay_receipt_sha256 is None):
            raise ValueError("replay receipt path/hash must appear together")
        if (self.compile_receipt_path is None) != (self.compile_receipt_sha256 is None):
            raise ValueError("compile receipt path/hash must appear together")
        if (self.kernel_receipt_path is None) != (self.kernel_receipt_sha256 is None):
            raise ValueError("kernel receipt path/hash must appear together")
        if (self.kernel_eval_receipt_path is None) != (self.kernel_eval_receipt_sha256 is None):
            raise ValueError("kernel eval receipt path/hash must appear together")
        if (self.kernel_settlement_receipt_path is None) != (self.kernel_settlement_receipt_sha256 is None):
            raise ValueError("kernel settlement receipt path/hash must appear together")
        if (self.kernel_replay_receipt_path is None) != (self.kernel_replay_receipt_sha256 is None):
            raise ValueError("kernel replay receipt path/hash must appear together")
        if (self.proof_tree_certificate_path is None) != (self.proof_tree_certificate_sha256 is None):
            raise ValueError("proof-tree certificate path/hash must appear together")
        if self.schema != BUNDLE_SCHEMA:
            raise ValueError(f"unsupported bundle schema: {self.schema}")

    def payload_without_hash(self) -> dict[str, object]:
        payload: dict[str, object] = {
            "schema": self.schema,
            "object_name": self.object_name,
            "object_version": self.object_version,
            "object_family": self.object_family,
            "artifacts": {
                "object_manifest": {
                    "path": self.object_manifest_path,
                    "sha256": self.object_manifest_file_sha256,
                },
                "object_instance": {
                    "path": self.object_instance_path,
                    "sha256": self.object_instance_file_sha256,
                },
                "object_lock": {
                    "path": self.object_lock_path,
                    "sha256": self.object_lock_file_sha256,
                },
                "certificate": {
                    "path": self.certificate_path,
                    "sha256": self.certificate_file_sha256,
                },
                "compile_receipt": (
                    None
                    if self.compile_receipt_path is None or self.compile_receipt_sha256 is None
                    else {
                        "path": self.compile_receipt_path,
                        "sha256": self.compile_receipt_sha256,
                    }
                ),
                "kernel_receipt": (
                    None
                    if self.kernel_receipt_path is None or self.kernel_receipt_sha256 is None
                    else {
                        "path": self.kernel_receipt_path,
                        "sha256": self.kernel_receipt_sha256,
                    }
                ),
                "kernel_eval_receipt": (
                    None
                    if self.kernel_eval_receipt_path is None or self.kernel_eval_receipt_sha256 is None
                    else {
                        "path": self.kernel_eval_receipt_path,
                        "sha256": self.kernel_eval_receipt_sha256,
                    }
                ),
                "kernel_settlement_receipt": (
                    None
                    if self.kernel_settlement_receipt_path is None or self.kernel_settlement_receipt_sha256 is None
                    else {
                        "path": self.kernel_settlement_receipt_path,
                        "sha256": self.kernel_settlement_receipt_sha256,
                    }
                ),
                "kernel_replay_receipt": (
                    None
                    if self.kernel_replay_receipt_path is None or self.kernel_replay_receipt_sha256 is None
                    else {
                        "path": self.kernel_replay_receipt_path,
                        "sha256": self.kernel_replay_receipt_sha256,
                    }
                ),
                "proof_tree_certificate": (
                    None
                    if self.proof_tree_certificate_path is None or self.proof_tree_certificate_sha256 is None
                    else {
                        "path": self.proof_tree_certificate_path,
                        "sha256": self.proof_tree_certificate_sha256,
                    }
                ),
                "object_card": {
                    "path": self.object_card_path,
                    "sha256": self.object_card_sha256,
                },
            },
        }
        if payload["artifacts"]["compile_receipt"] is None:
            del payload["artifacts"]["compile_receipt"]
        if payload["artifacts"]["kernel_receipt"] is None:
            del payload["artifacts"]["kernel_receipt"]
        if payload["artifacts"]["kernel_eval_receipt"] is None:
            del payload["artifacts"]["kernel_eval_receipt"]
        if payload["artifacts"]["kernel_settlement_receipt"] is None:
            del payload["artifacts"]["kernel_settlement_receipt"]
        if payload["artifacts"]["kernel_replay_receipt"] is None:
            del payload["artifacts"]["kernel_replay_receipt"]
        if payload["artifacts"]["proof_tree_certificate"] is None:
            del payload["artifacts"]["proof_tree_certificate"]
        if self.replay_input_path is not None and self.replay_input_sha256 is not None:
            payload["artifacts"]["replay_input"] = {
                "path": self.replay_input_path,
                "sha256": self.replay_input_sha256,
            }
        if self.replay_receipt_path is not None and self.replay_receipt_sha256 is not None:
            payload["artifacts"]["replay_receipt"] = {
                "path": self.replay_receipt_path,
                "sha256": self.replay_receipt_sha256,
            }
        if self.contract_receipts:
            payload["contracts"] = [item.to_dict() for item in self.contract_receipts]
        return payload

    def to_dict(self) -> dict[str, object]:
        payload = self.payload_without_hash()
        payload["bundle_hash"] = self.bundle_hash
        return payload

    @classmethod
    def build(
        cls,
        *,
        object_name: str,
        object_version: str,
        object_family: str,
        object_manifest_path: str,
        object_manifest_file_sha256: str,
        object_instance_path: str,
        object_instance_file_sha256: str,
        object_lock_path: str,
        object_lock_file_sha256: str,
        certificate_path: str,
        certificate_file_sha256: str,
        compile_receipt_path: str | None = None,
        compile_receipt_sha256: str | None = None,
        kernel_receipt_path: str | None = None,
        kernel_receipt_sha256: str | None = None,
        kernel_eval_receipt_path: str | None = None,
        kernel_eval_receipt_sha256: str | None = None,
        kernel_settlement_receipt_path: str | None = None,
        kernel_settlement_receipt_sha256: str | None = None,
        kernel_replay_receipt_path: str | None = None,
        kernel_replay_receipt_sha256: str | None = None,
        proof_tree_certificate_path: str | None = None,
        proof_tree_certificate_sha256: str | None = None,
        object_card_path: str,
        object_card_sha256: str,
        replay_input_path: str | None = None,
        replay_input_sha256: str | None = None,
        replay_receipt_path: str | None = None,
        replay_receipt_sha256: str | None = None,
        contract_receipts: tuple[FireBundleContractReceipt, ...] = (),
    ) -> "FireRegistryBundleManifest":
        payload_without_hash: dict[str, object] = {
            "schema": BUNDLE_SCHEMA,
            "object_name": object_name,
            "object_version": object_version,
            "object_family": object_family,
            "artifacts": {
                "object_manifest": {"path": object_manifest_path, "sha256": object_manifest_file_sha256},
                "object_instance": {"path": object_instance_path, "sha256": object_instance_file_sha256},
                "object_lock": {"path": object_lock_path, "sha256": object_lock_file_sha256},
                "certificate": {"path": certificate_path, "sha256": certificate_file_sha256},
                "object_card": {"path": object_card_path, "sha256": object_card_sha256},
            },
        }
        if compile_receipt_path is not None and compile_receipt_sha256 is not None:
            payload_without_hash["artifacts"]["compile_receipt"] = {
                "path": compile_receipt_path,
                "sha256": compile_receipt_sha256,
            }
        if kernel_receipt_path is not None and kernel_receipt_sha256 is not None:
            payload_without_hash["artifacts"]["kernel_receipt"] = {
                "path": kernel_receipt_path,
                "sha256": kernel_receipt_sha256,
            }
        if kernel_eval_receipt_path is not None and kernel_eval_receipt_sha256 is not None:
            payload_without_hash["artifacts"]["kernel_eval_receipt"] = {
                "path": kernel_eval_receipt_path,
                "sha256": kernel_eval_receipt_sha256,
            }
        if kernel_settlement_receipt_path is not None and kernel_settlement_receipt_sha256 is not None:
            payload_without_hash["artifacts"]["kernel_settlement_receipt"] = {
                "path": kernel_settlement_receipt_path,
                "sha256": kernel_settlement_receipt_sha256,
            }
        if kernel_replay_receipt_path is not None and kernel_replay_receipt_sha256 is not None:
            payload_without_hash["artifacts"]["kernel_replay_receipt"] = {
                "path": kernel_replay_receipt_path,
                "sha256": kernel_replay_receipt_sha256,
            }
        if proof_tree_certificate_path is not None and proof_tree_certificate_sha256 is not None:
            payload_without_hash["artifacts"]["proof_tree_certificate"] = {
                "path": proof_tree_certificate_path,
                "sha256": proof_tree_certificate_sha256,
            }
        if replay_input_path is not None and replay_input_sha256 is not None:
            payload_without_hash["artifacts"]["replay_input"] = {
                "path": replay_input_path,
                "sha256": replay_input_sha256,
            }
        if replay_receipt_path is not None and replay_receipt_sha256 is not None:
            payload_without_hash["artifacts"]["replay_receipt"] = {
                "path": replay_receipt_path,
                "sha256": replay_receipt_sha256,
            }
        if contract_receipts:
            payload_without_hash["contracts"] = [item.to_dict() for item in contract_receipts]
        return cls(
            object_name=object_name,
            object_version=object_version,
            object_family=object_family,
            object_manifest_path=object_manifest_path,
            object_manifest_file_sha256=object_manifest_file_sha256,
            object_instance_path=object_instance_path,
            object_instance_file_sha256=object_instance_file_sha256,
            object_lock_path=object_lock_path,
            object_lock_file_sha256=object_lock_file_sha256,
            certificate_path=certificate_path,
            certificate_file_sha256=certificate_file_sha256,
            compile_receipt_path=compile_receipt_path,
            compile_receipt_sha256=compile_receipt_sha256,
            kernel_receipt_path=kernel_receipt_path,
            kernel_receipt_sha256=kernel_receipt_sha256,
            kernel_eval_receipt_path=kernel_eval_receipt_path,
            kernel_eval_receipt_sha256=kernel_eval_receipt_sha256,
            kernel_settlement_receipt_path=kernel_settlement_receipt_path,
            kernel_settlement_receipt_sha256=kernel_settlement_receipt_sha256,
            kernel_replay_receipt_path=kernel_replay_receipt_path,
            kernel_replay_receipt_sha256=kernel_replay_receipt_sha256,
            proof_tree_certificate_path=proof_tree_certificate_path,
            proof_tree_certificate_sha256=proof_tree_certificate_sha256,
            object_card_path=object_card_path,
            object_card_sha256=object_card_sha256,
            replay_input_path=replay_input_path,
            replay_input_sha256=replay_input_sha256,
            replay_receipt_path=replay_receipt_path,
            replay_receipt_sha256=replay_receipt_sha256,
            contract_receipts=contract_receipts,
            bundle_hash=fire_registry_bundle_sha256(payload_without_hash),
        )

    @classmethod
    def from_dict(cls, payload: object) -> "FireRegistryBundleManifest":
        if not isinstance(payload, dict):
            raise TypeError("bundle payload must be a dict")
        artifacts = payload.get("artifacts")
        if not isinstance(artifacts, dict):
            raise TypeError("artifacts must be a dict")
        object_manifest = artifacts.get("object_manifest")
        object_instance = artifacts.get("object_instance")
        object_lock = artifacts.get("object_lock")
        certificate = artifacts.get("certificate")
        compile_receipt = artifacts.get("compile_receipt")
        kernel_receipt = artifacts.get("kernel_receipt")
        kernel_eval_receipt = artifacts.get("kernel_eval_receipt")
        kernel_settlement_receipt = artifacts.get("kernel_settlement_receipt")
        kernel_replay_receipt = artifacts.get("kernel_replay_receipt")
        proof_tree_certificate = artifacts.get("proof_tree_certificate")
        object_card = artifacts.get("object_card")
        replay_input = artifacts.get("replay_input")
        replay_receipt = artifacts.get("replay_receipt")
        contract_receipts_payload = payload.get("contracts", [])
        if (
            not isinstance(object_manifest, dict)
            or not isinstance(object_instance, dict)
            or not isinstance(object_lock, dict)
            or not isinstance(certificate, dict)
            or not isinstance(object_card, dict)
        ):
            raise TypeError("bundle artifacts are malformed")
        if not isinstance(contract_receipts_payload, list):
            raise TypeError("contracts must be a list")
        return cls(
            schema=payload.get("schema", BUNDLE_SCHEMA),
            object_name=payload.get("object_name"),
            object_version=payload.get("object_version"),
            object_family=payload.get("object_family"),
            object_manifest_path=object_manifest.get("path"),
            object_manifest_file_sha256=object_manifest.get("sha256"),
            object_instance_path=object_instance.get("path"),
            object_instance_file_sha256=object_instance.get("sha256"),
            object_lock_path=object_lock.get("path"),
            object_lock_file_sha256=object_lock.get("sha256"),
            certificate_path=certificate.get("path"),
            certificate_file_sha256=certificate.get("sha256"),
            compile_receipt_path=None if compile_receipt is None else compile_receipt.get("path"),
            compile_receipt_sha256=None if compile_receipt is None else compile_receipt.get("sha256"),
            kernel_receipt_path=None if kernel_receipt is None else kernel_receipt.get("path"),
            kernel_receipt_sha256=None if kernel_receipt is None else kernel_receipt.get("sha256"),
            kernel_eval_receipt_path=None if kernel_eval_receipt is None else kernel_eval_receipt.get("path"),
            kernel_eval_receipt_sha256=None if kernel_eval_receipt is None else kernel_eval_receipt.get("sha256"),
            kernel_settlement_receipt_path=(
                None if kernel_settlement_receipt is None else kernel_settlement_receipt.get("path")
            ),
            kernel_settlement_receipt_sha256=(
                None if kernel_settlement_receipt is None else kernel_settlement_receipt.get("sha256")
            ),
            kernel_replay_receipt_path=(
                None if kernel_replay_receipt is None else kernel_replay_receipt.get("path")
            ),
            kernel_replay_receipt_sha256=(
                None if kernel_replay_receipt is None else kernel_replay_receipt.get("sha256")
            ),
            proof_tree_certificate_path=None if proof_tree_certificate is None else proof_tree_certificate.get("path"),
            proof_tree_certificate_sha256=None if proof_tree_certificate is None else proof_tree_certificate.get("sha256"),
            object_card_path=object_card.get("path"),
            object_card_sha256=object_card.get("sha256"),
            replay_input_path=None if replay_input is None else replay_input.get("path"),
            replay_input_sha256=None if replay_input is None else replay_input.get("sha256"),
            replay_receipt_path=None if replay_receipt is None else replay_receipt.get("path"),
            replay_receipt_sha256=None if replay_receipt is None else replay_receipt.get("sha256"),
            contract_receipts=tuple(FireBundleContractReceipt.from_dict(item) for item in contract_receipts_payload),
            bundle_hash=payload.get("bundle_hash"),
        )


def fire_registry_bundle_file_sha256(bundle_manifest: FireRegistryBundleManifest) -> str:
    return _sha256_bytes(_canonical_json_bytes(bundle_manifest.to_dict()))


def _write_bytes(path: Path, payload: bytes) -> str:
    path.write_bytes(payload)
    return _sha256_bytes(payload)


def _verify_file_sha(path: Path, expected_sha256: str) -> bool:
    return _sha256_bytes(path.read_bytes()) == expected_sha256


def write_fire_registry_bundle(
    bundle_dir: str | Path,
    *,
    artifact: Any,
    build_manifest: Any,
    render_object_card: Any,
    instance_nonce: str | None = None,
    instance_parties: Mapping[str, str] | None = None,
    instance_maturity: str | None = None,
    instance_settlement_window: FireSettlementWindow | None = None,
    replay_input: Mapping[str, object] | None = None,
    replay_receipt: Mapping[str, object] | None = None,
    emit_proof_tree_certificate: bool = False,
) -> tuple[FireRegistryBundleManifest, str]:
    out_dir = Path(bundle_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    object_manifest = build_manifest(artifact)
    object_manifest_path = "object_manifest.json"
    object_manifest_file_sha256 = write_fire_object_manifest(out_dir / object_manifest_path, object_manifest)

    object_lock = build_fire_object_dependency_lock(object_manifest)
    object_lock_path = "object_lock.json"
    object_lock_file_sha256 = write_fire_object_dependency_lock(out_dir / object_lock_path, object_lock)

    parameter_values = tuple(
        sorted(
            (FireObjectParameterValue(name=name, value=value) for name, value in vars(artifact.terms).items()),
            key=lambda item: item.name,
        )
    )
    party_bindings = tuple(
        FireObjectPartyBinding(role=role, party_id=party_id)
        for role, party_id in sorted((instance_parties or {"holder": "role:holder", "writer": "role:writer"}).items())
    )
    object_instance = FireObjectInstanceManifest.build(
        object_hash=object_manifest.manifest_hash,
        lock_hash=object_lock.lock_hash,
        object_name=object_manifest.object_name,
        object_version=object_manifest.object_version,
        object_family=object_manifest.object_family,
        parameters=parameter_values,
        parties=party_bindings,
        nonce=instance_nonce or f"bundle:{object_manifest.object_name}:{object_manifest.object_version}",
        maturity=instance_maturity,
        settlement_window=instance_settlement_window,
    )
    object_instance_path = "instance_manifest.json"
    object_instance_file_sha256 = write_fire_object_instance(out_dir / object_instance_path, object_instance)

    certificate_path = "certificate.json"
    certificate_file_sha256 = _write_bytes(out_dir / certificate_path, certificate_json_bytes(artifact.certificate))

    replay_input_path: str | None = None
    replay_input_sha256: str | None = None
    replay_input_payload = (
        build_default_fire_replay_input(object_manifest=object_manifest, object_instance=object_instance).to_dict()
        if replay_input is None
        else dict(replay_input)
    )
    replay_input_obj: FireReplayInput | None = None
    if replay_input_payload is not None:
        replay_input_path = "replay_input.json"
        replay_input_obj = FireReplayInput.from_dict(replay_input_payload)
        replay_input_sha256 = write_fire_replay_input(out_dir / replay_input_path, replay_input_obj)

    compile_receipt_path = "compile_receipt.json"
    compile_receipt_sha256 = write_fire_compile_receipt(
        out_dir / compile_receipt_path,
        object_manifest=object_manifest,
        object_instance=object_instance,
    )

    kernel_receipt_path = "kernel_receipt.json"
    kernel_receipt_sha256 = write_fire_kernel_receipt(
        out_dir / kernel_receipt_path,
        object_manifest=object_manifest,
        object_instance=object_instance,
    )

    kernel_eval_receipt_path = "kernel_eval_receipt.json"
    kernel_eval_receipt_sha256 = write_fire_kernel_eval_receipt(
        out_dir / kernel_eval_receipt_path,
        object_manifest=object_manifest,
        object_instance=object_instance,
        kernel_receipt_sha256=kernel_receipt_sha256,
    )

    kernel_settlement_receipt_path: str | None = None
    kernel_settlement_receipt_sha256: str | None = None
    kernel_settlement_receipt_payload: Mapping[str, object] | None = None
    if replay_input_obj is not None and replay_input_sha256 is not None:
        kernel_settlement_receipt_path = "kernel_settlement_receipt.json"
        kernel_settlement_receipt_payload = build_fire_kernel_settlement_receipt(
            object_manifest=object_manifest,
            object_instance=object_instance,
            replay_input=replay_input_obj,
            replay_input_sha256=replay_input_sha256,
            kernel_receipt_sha256=kernel_receipt_sha256,
            kernel_eval_receipt_sha256=kernel_eval_receipt_sha256,
        )
        kernel_settlement_receipt_sha256 = _write_bytes(
            out_dir / kernel_settlement_receipt_path,
            _canonical_json_bytes(kernel_settlement_receipt_payload),
        )

    kernel_replay_receipt_path: str | None = None
    kernel_replay_receipt_sha256: str | None = None
    kernel_replay_receipt_payload: Mapping[str, object] | None = None
    if (
        replay_input_obj is not None
        and replay_input_sha256 is not None
        and kernel_settlement_receipt_sha256 is not None
    ):
        kernel_replay_receipt_path = "kernel_replay_receipt.json"
        kernel_replay_receipt_payload = build_fire_kernel_replay_receipt(
            object_manifest=object_manifest,
            object_instance=object_instance,
            replay_input=replay_input_obj,
            replay_input_sha256=replay_input_sha256,
            compile_receipt_sha256=compile_receipt_sha256,
            kernel_receipt_sha256=kernel_receipt_sha256,
            kernel_eval_receipt_sha256=kernel_eval_receipt_sha256,
            kernel_settlement_receipt_sha256=kernel_settlement_receipt_sha256,
        )
        kernel_replay_receipt_sha256 = _write_bytes(
            out_dir / kernel_replay_receipt_path,
            _canonical_json_bytes(kernel_replay_receipt_payload),
        )

    proof_tree_certificate_path: str | None = None
    proof_tree_certificate_sha256: str | None = None
    if emit_proof_tree_certificate:
        proof_tree_certificate_path = "proof_tree_certificate.json"
        proof_tree_certificate_payload = build_fire_proof_tree_certificate(
            object_manifest=object_manifest,
            object_instance=object_instance,
            object_lock=object_lock,
            certificate=artifact.certificate,
            object_manifest_file_sha256=object_manifest_file_sha256,
            object_instance_file_sha256=object_instance_file_sha256,
            object_lock_file_sha256=object_lock_file_sha256,
            replay_input=replay_input_obj,
            replay_input_sha256=replay_input_sha256,
            compile_receipt_sha256=compile_receipt_sha256,
            kernel_receipt_sha256=kernel_receipt_sha256,
            kernel_eval_receipt_sha256=kernel_eval_receipt_sha256,
            kernel_settlement_receipt=kernel_settlement_receipt_payload,
            kernel_settlement_receipt_sha256=kernel_settlement_receipt_sha256,
            kernel_replay_receipt=kernel_replay_receipt_payload,
            kernel_replay_receipt_sha256=kernel_replay_receipt_sha256,
        )
        proof_tree_certificate_sha256 = _write_bytes(
            out_dir / proof_tree_certificate_path,
            _canonical_json_bytes(proof_tree_certificate_payload),
        )

    object_card_path = "object_card.txt"
    object_card_text = render_object_card(artifact)
    object_card_sha = _write_bytes(out_dir / object_card_path, object_card_text.encode("utf-8"))

    replay_receipt_path: str | None = None
    replay_receipt_sha256: str | None = None
    if replay_receipt is not None:
        replay_receipt_path = "replay_receipt.json"
        replay_receipt_sha256 = _write_bytes(out_dir / replay_receipt_path, replay_receipt_json_bytes(replay_receipt))

    bundle_manifest = FireRegistryBundleManifest.build(
        object_name=object_manifest.object_name,
        object_version=object_manifest.object_version,
        object_family=object_manifest.object_family,
        object_manifest_path=object_manifest_path,
        object_manifest_file_sha256=object_manifest_file_sha256,
        object_instance_path=object_instance_path,
        object_instance_file_sha256=object_instance_file_sha256,
        object_lock_path=object_lock_path,
        object_lock_file_sha256=object_lock_file_sha256,
        certificate_path=certificate_path,
        certificate_file_sha256=certificate_file_sha256,
        compile_receipt_path=compile_receipt_path,
        compile_receipt_sha256=compile_receipt_sha256,
        kernel_receipt_path=kernel_receipt_path,
        kernel_receipt_sha256=kernel_receipt_sha256,
        kernel_eval_receipt_path=kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=kernel_eval_receipt_sha256,
        kernel_settlement_receipt_path=kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=kernel_settlement_receipt_sha256,
        kernel_replay_receipt_path=kernel_replay_receipt_path,
        kernel_replay_receipt_sha256=kernel_replay_receipt_sha256,
        proof_tree_certificate_path=proof_tree_certificate_path,
        proof_tree_certificate_sha256=proof_tree_certificate_sha256,
        object_card_path=object_card_path,
        object_card_sha256=object_card_sha,
        replay_input_path=replay_input_path,
        replay_input_sha256=replay_input_sha256,
        replay_receipt_path=replay_receipt_path,
        replay_receipt_sha256=replay_receipt_sha256,
        contract_receipts=_build_contract_receipts(object_manifest),
    )
    bundle_manifest_file_sha256 = _write_bytes(
        out_dir / "bundle_manifest.json",
        _canonical_json_bytes(bundle_manifest.to_dict()),
    )
    return bundle_manifest, bundle_manifest_file_sha256


def load_fire_registry_bundle(
    bundle_dir: str | Path,
) -> tuple[FireRegistryBundleManifest, str, FireObjectManifest, FireObjectInstanceManifest, FireObjectDependencyLock]:
    root = Path(bundle_dir)
    bundle_manifest_path = root / "bundle_manifest.json"
    payload_bytes = bundle_manifest_path.read_bytes()
    bundle_manifest = FireRegistryBundleManifest.from_dict(json.loads(payload_bytes.decode("utf-8")))
    bundle_manifest_file_sha256 = _sha256_bytes(payload_bytes)

    object_manifest, _ = load_fire_object_manifest(root / bundle_manifest.object_manifest_path)
    object_instance, _ = load_fire_object_instance(root / bundle_manifest.object_instance_path)
    object_lock, _ = load_fire_object_dependency_lock(root / bundle_manifest.object_lock_path)
    return bundle_manifest, bundle_manifest_file_sha256, object_manifest, object_instance, object_lock


def verify_fire_registry_bundle(
    bundle_dir: str | Path,
    *,
    expected_bundle_hash: str | None = None,
    expected_bundle_file_sha256: str | None = None,
) -> tuple[
    bool,
    str | None,
    FireRegistryBundleManifest | None,
    FireObjectManifest | None,
    FireObjectInstanceManifest | None,
    FireObjectDependencyLock | None,
]:
    try:
        bundle_manifest, bundle_manifest_file_sha256, object_manifest, object_instance, object_lock = load_fire_registry_bundle(
            bundle_dir
        )
    except (FileNotFoundError, OSError, ValueError, TypeError, KeyError, IndexError, AttributeError, UnicodeDecodeError) as exc:
        return False, f"bundle_load_failed:{exc}", None, None, None, None

    expected_hash = fire_registry_bundle_sha256(bundle_manifest.payload_without_hash())
    if bundle_manifest.bundle_hash != expected_hash:
        return False, "bundle_hash_mismatch", None, None, None, None
    if expected_bundle_hash is not None and bundle_manifest.bundle_hash != expected_bundle_hash:
        return False, "expected_bundle_hash_mismatch", None, None, None, None
    if expected_bundle_file_sha256 is not None and bundle_manifest_file_sha256 != expected_bundle_file_sha256:
        return False, "expected_bundle_file_sha_mismatch", None, None, None, None

    root = Path(bundle_dir)
    object_manifest_path = root / bundle_manifest.object_manifest_path
    object_instance_path = root / bundle_manifest.object_instance_path
    object_lock_path = root / bundle_manifest.object_lock_path
    certificate_path = root / bundle_manifest.certificate_path
    object_card_path = root / bundle_manifest.object_card_path

    if not _verify_file_sha(object_manifest_path, bundle_manifest.object_manifest_file_sha256):
        return False, "object_manifest_file_sha_mismatch", None, None, None, None
    if not _verify_file_sha(object_instance_path, bundle_manifest.object_instance_file_sha256):
        return False, "object_instance_file_sha_mismatch", None, None, None, None
    if not _verify_file_sha(object_lock_path, bundle_manifest.object_lock_file_sha256):
        return False, "object_lock_file_sha_mismatch", None, None, None, None
    ok, err = verify_fire_object_manifest(object_manifest)
    if not ok:
        return False, f"object_manifest_invalid:{err or 'unknown'}", None, None, None, None
    ok, err = verify_fire_object_dependency_lock(object_lock, object_manifest=object_manifest)
    if not ok:
        return False, f"object_lock_invalid:{err or 'unknown'}", None, None, None, None
    ok, err = verify_fire_object_instance(
        object_instance,
        expected_object_hash=object_manifest.manifest_hash,
        expected_lock_hash=object_lock.lock_hash,
    )
    if not ok:
        return False, f"object_instance_invalid:{err or 'unknown'}", None, None, None, None
    ok, err, _gate_report = verify_fire_object_instance_against_manifest(
        object_instance,
        object_manifest=object_manifest,
    )
    if not ok:
        return False, f"object_instance_gate_invalid:{err or 'unknown'}", None, None, None, None
    if bundle_manifest.contract_receipts != _build_contract_receipts(object_manifest):
        return False, "bundle_contract_receipts_mismatch", None, None, None, None
    if object_manifest.object_name != bundle_manifest.object_name:
        return False, "bundle_object_name_mismatch", None, None, None, None
    if object_manifest.object_version != bundle_manifest.object_version:
        return False, "bundle_object_version_mismatch", None, None, None, None
    if object_manifest.object_family != bundle_manifest.object_family:
        return False, "bundle_object_family_mismatch", None, None, None, None

    cert_payload = json.loads(certificate_path.read_text(encoding="utf-8"))
    certificate = FireIntervalCertificate.from_dict(cert_payload)
    if fire_cert_sha256(certificate) != bundle_manifest.certificate_file_sha256:
        return False, "certificate_file_sha_mismatch", None, None, None, None
    if object_manifest.cert_sha256 != bundle_manifest.certificate_file_sha256:
        return False, "certificate_manifest_hash_mismatch", None, None, None, None
    ok, err, _claims = verify_instance_gate_claims(
        certificate,
        expected=expected_fire_instance_gate_claims(object_manifest),
        require_present=True,
    )
    if not ok:
        return False, f"certificate_{err or 'instance_gate_claims_invalid'}", None, None, None, None
    if bundle_manifest.compile_receipt_path is not None and bundle_manifest.compile_receipt_sha256 is not None:
        compile_receipt_path = root / bundle_manifest.compile_receipt_path
        if not _verify_file_sha(compile_receipt_path, bundle_manifest.compile_receipt_sha256):
            return False, "compile_receipt_sha_mismatch", None, None, None, None
    if bundle_manifest.kernel_receipt_path is not None and bundle_manifest.kernel_receipt_sha256 is not None:
        kernel_receipt_path = root / bundle_manifest.kernel_receipt_path
        if not _verify_file_sha(kernel_receipt_path, bundle_manifest.kernel_receipt_sha256):
            return False, "kernel_receipt_sha_mismatch", None, None, None, None
    if bundle_manifest.kernel_eval_receipt_path is not None and bundle_manifest.kernel_eval_receipt_sha256 is not None:
        kernel_eval_receipt_path = root / bundle_manifest.kernel_eval_receipt_path
        if not _verify_file_sha(kernel_eval_receipt_path, bundle_manifest.kernel_eval_receipt_sha256):
            return False, "kernel_eval_receipt_sha_mismatch", None, None, None, None
    if (
        bundle_manifest.kernel_settlement_receipt_path is not None
        and bundle_manifest.kernel_settlement_receipt_sha256 is not None
    ):
        kernel_settlement_receipt_path = root / bundle_manifest.kernel_settlement_receipt_path
        if not _verify_file_sha(kernel_settlement_receipt_path, bundle_manifest.kernel_settlement_receipt_sha256):
            return False, "kernel_settlement_receipt_sha_mismatch", None, None, None, None
    if bundle_manifest.kernel_replay_receipt_path is not None and bundle_manifest.kernel_replay_receipt_sha256 is not None:
        kernel_replay_receipt_path = root / bundle_manifest.kernel_replay_receipt_path
        if not _verify_file_sha(kernel_replay_receipt_path, bundle_manifest.kernel_replay_receipt_sha256):
            return False, "kernel_replay_receipt_sha_mismatch", None, None, None, None
    if (
        bundle_manifest.proof_tree_certificate_path is not None
        and bundle_manifest.proof_tree_certificate_sha256 is not None
    ):
        proof_tree_certificate_path = root / bundle_manifest.proof_tree_certificate_path
        if not _verify_file_sha(proof_tree_certificate_path, bundle_manifest.proof_tree_certificate_sha256):
            return False, "proof_tree_certificate_sha_mismatch", None, None, None, None

    if not _verify_file_sha(object_card_path, bundle_manifest.object_card_sha256):
        return False, "object_card_sha_mismatch", None, None, None, None

    if bundle_manifest.replay_receipt_path is not None and bundle_manifest.replay_receipt_sha256 is not None:
        replay_receipt_path = root / bundle_manifest.replay_receipt_path
        if not _verify_file_sha(replay_receipt_path, bundle_manifest.replay_receipt_sha256):
            return False, "replay_receipt_sha_mismatch", None, None, None, None
    if bundle_manifest.replay_input_path is not None and bundle_manifest.replay_input_sha256 is not None:
        replay_input_path = root / bundle_manifest.replay_input_path
        if not _verify_file_sha(replay_input_path, bundle_manifest.replay_input_sha256):
            return False, "replay_input_sha_mismatch", None, None, None, None
        replay_input, _ = load_fire_replay_input(replay_input_path)
        ok, err = verify_fire_replay_input(
            replay_input,
            object_manifest=object_manifest,
            object_instance=object_instance,
        )
        if not ok:
            return False, f"replay_input_invalid:{err or 'unknown'}", None, None, None, None

    return True, None, bundle_manifest, object_manifest, object_instance, object_lock


__all__ = [
    "BUNDLE_SCHEMA",
    "FireBundleContractReceipt",
    "FireObjectDependencyLock",
    "FireObjectInstanceManifest",
    "FireObjectManifest",
    "FireRegistryBundleManifest",
    "card_sha256",
    "certificate_json_bytes",
    "fire_registry_bundle_file_sha256",
    "fire_registry_bundle_sha256",
    "load_fire_registry_bundle",
    "replay_receipt_json_bytes",
    "verify_fire_registry_bundle",
    "write_fire_registry_bundle",
]

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path

from src.agents.policy_artifacts import G2Basic, _parse_privkey_to_int, _require_bls
from src.fire.registry.bundle_v1 import (
    FireBundleContractReceipt,
    load_fire_registry_bundle,
    verify_fire_registry_bundle,
)
from src.fire.registry.instance_v1 import (
    FireInstanceGateReport,
    verify_fire_object_instance_against_manifest,
)
from src.fire.verifier.cert_v1 import (
    FireInstanceGateClaims,
    FireIntervalCertificate,
    _require_evidence_level,
    _require_sha256_prefixed,
)
from src.integration.bls_intent_signing import bls_pubkey_hex_from_privkey
from src.state.canonical import canonical_json_bytes

INDEX_SCHEMA = "zenodex/fire-registry-index/v1"
_EVIDENCE_RANK = {
    "proved": 0,
    "contract": 1,
    "implemented": 2,
    "tested_discovery": 3,
    "hypothesis": 4,
}


def _require_nonempty_str(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    return value


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def _require_string_tuple(name: str, values: list[object]) -> tuple[str, ...]:
    return tuple(_require_nonempty_str(f"{name}[{idx}]", item) for idx, item in enumerate(values))


def _require_0x_hex(name: str, value: object, *, expected_nbytes: int | None = None) -> str:
    text = _require_nonempty_str(name, value)
    if not text.startswith("0x"):
        raise ValueError(f"{name} must be 0x-prefixed hex")
    try:
        raw = bytes.fromhex(text[2:])
    except ValueError as exc:
        raise ValueError(f"{name} must be valid hex") from exc
    if expected_nbytes is not None and len(raw) != expected_nbytes:
        raise ValueError(f"{name} must be {expected_nbytes} bytes")
    return text


def _canonical_json_bytes(payload: dict[str, object]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def _sha256_bytes(payload: bytes) -> str:
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def _evidence_meet(levels: tuple[str, ...]) -> str:
    if not levels:
        return "proved"
    return max(levels, key=lambda level: _EVIDENCE_RANK[level])


@dataclass(frozen=True)
class FireRegistryContractReceipt:
    name: str
    roles: tuple[str, ...]
    object_refs: tuple[str, ...]
    use_sites: tuple[str, ...]

    def __post_init__(self) -> None:
        object.__setattr__(self, "name", _require_nonempty_str("name", self.name))
        if not isinstance(self.roles, tuple) or any(not isinstance(item, str) or not item for item in self.roles):
            raise TypeError("roles must be a tuple of non-empty strings")
        if not isinstance(self.object_refs, tuple) or any(not isinstance(item, str) or not item for item in self.object_refs):
            raise TypeError("object_refs must be a tuple of non-empty strings")
        if not isinstance(self.use_sites, tuple) or any(not isinstance(item, str) or not item for item in self.use_sites):
            raise TypeError("use_sites must be a tuple of non-empty strings")

    def to_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "roles": list(self.roles),
            "object_refs": list(self.object_refs),
            "use_sites": list(self.use_sites),
        }

    @classmethod
    def from_dict(cls, payload: object) -> "FireRegistryContractReceipt":
        if not isinstance(payload, dict):
            raise TypeError("registry contract receipt payload must be an object")
        roles = payload.get("roles")
        object_refs = payload.get("object_refs")
        use_sites = payload.get("use_sites")
        if not isinstance(roles, list):
            raise TypeError("registry contract receipt roles must be a list")
        if not isinstance(object_refs, list):
            raise TypeError("registry contract receipt object_refs must be a list")
        if not isinstance(use_sites, list):
            raise TypeError("registry contract receipt use_sites must be a list")
        return cls(
            name=payload.get("name"),
            roles=_require_string_tuple("registry contract receipt roles", roles),
            object_refs=_require_string_tuple("registry contract receipt object_refs", object_refs),
            use_sites=_require_string_tuple("registry contract receipt use_sites", use_sites),
        )


def _registry_object_ref(object_name: str, object_version: str) -> str:
    return f"{object_name}@{object_version}"


def _build_registry_contract_receipts(
    entries: tuple["FireRegistryIndexEntry", ...],
) -> tuple[FireRegistryContractReceipt, ...]:
    grouped: dict[str, dict[str, set[str]]] = {}
    for entry in entries:
        object_ref = _registry_object_ref(entry.object_name, entry.object_version)
        for contract in entry.contract_receipts:
            grouped_entry = grouped.setdefault(contract.name, {"roles": set(), "object_refs": set(), "use_sites": set()})
            grouped_entry["roles"].update(contract.roles)
            grouped_entry["object_refs"].add(object_ref)
            grouped_entry["use_sites"].update(f"{object_ref}:{use_site}" for use_site in contract.use_sites)
    return tuple(
        FireRegistryContractReceipt(
            name=name,
            roles=tuple(sorted(group["roles"])),
            object_refs=tuple(sorted(group["object_refs"])),
            use_sites=tuple(sorted(group["use_sites"])),
        )
        for name, group in sorted(grouped.items())
    )


@dataclass(frozen=True)
class FireRegistryIndexEntry:
    object_name: str
    object_version: str
    object_family: str
    bundle_path: str
    bundle_hash: str
    bundle_file_sha256: str
    manifest_hash: str
    instance_hash: str
    lock_hash: str
    cert_sha256: str
    instance_gate_report: FireInstanceGateReport
    certificate_instance_gate_claims: FireInstanceGateClaims
    contract_receipts: tuple[FireBundleContractReceipt, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(self, "object_name", _require_nonempty_str("object_name", self.object_name))
        object.__setattr__(self, "object_version", _require_nonempty_str("object_version", self.object_version))
        object.__setattr__(self, "object_family", _require_nonempty_str("object_family", self.object_family))
        object.__setattr__(self, "bundle_path", _require_nonempty_str("bundle_path", self.bundle_path))
        object.__setattr__(self, "bundle_hash", _require_sha256_prefixed("bundle_hash", self.bundle_hash))
        object.__setattr__(self, "bundle_file_sha256", _require_sha256_prefixed("bundle_file_sha256", self.bundle_file_sha256))
        object.__setattr__(self, "manifest_hash", _require_sha256_prefixed("manifest_hash", self.manifest_hash))
        object.__setattr__(self, "instance_hash", _require_sha256_prefixed("instance_hash", self.instance_hash))
        object.__setattr__(self, "lock_hash", _require_sha256_prefixed("lock_hash", self.lock_hash))
        object.__setattr__(self, "cert_sha256", _require_sha256_prefixed("cert_sha256", self.cert_sha256))
        if not isinstance(self.instance_gate_report, FireInstanceGateReport):
            raise TypeError("instance_gate_report must be a FireInstanceGateReport")
        if not isinstance(self.certificate_instance_gate_claims, FireInstanceGateClaims):
            raise TypeError("certificate_instance_gate_claims must be a FireInstanceGateClaims")
        if not isinstance(self.contract_receipts, tuple):
            raise TypeError("contract_receipts must be a tuple")
        if any(not isinstance(item, FireBundleContractReceipt) for item in self.contract_receipts):
            raise TypeError("contract_receipts must contain FireBundleContractReceipt values")

    def to_dict(self) -> dict[str, object]:
        payload = {
            "object_name": self.object_name,
            "object_version": self.object_version,
            "object_family": self.object_family,
            "bundle_path": self.bundle_path,
            "bundle_hash": self.bundle_hash,
            "bundle_file_sha256": self.bundle_file_sha256,
            "manifest_hash": self.manifest_hash,
            "instance_hash": self.instance_hash,
            "lock_hash": self.lock_hash,
            "cert_sha256": self.cert_sha256,
            "instance_gates": self.instance_gate_report.to_dict(),
            "certificate_instance_gate_claims": self.certificate_instance_gate_claims.to_dict(),
        }
        if self.contract_receipts:
            payload["contracts"] = [item.to_dict() for item in self.contract_receipts]
        return payload

    @classmethod
    def from_dict(cls, payload: object) -> "FireRegistryIndexEntry":
        if not isinstance(payload, dict):
            raise TypeError("index entry must be an object")
        contracts = payload.get("contracts", [])
        instance_gates = payload.get("instance_gates")
        certificate_instance_gate_claims = payload.get("certificate_instance_gate_claims")
        if not isinstance(contracts, list):
            raise TypeError("index entry contracts must be a list")
        if not isinstance(instance_gates, dict):
            raise TypeError("index entry instance_gates must be an object")
        if not isinstance(certificate_instance_gate_claims, dict):
            raise TypeError("index entry certificate_instance_gate_claims must be an object")
        return cls(
            object_name=payload.get("object_name"),
            object_version=payload.get("object_version"),
            object_family=payload.get("object_family"),
            bundle_path=payload.get("bundle_path"),
            bundle_hash=payload.get("bundle_hash"),
            bundle_file_sha256=payload.get("bundle_file_sha256"),
            manifest_hash=payload.get("manifest_hash"),
            instance_hash=payload.get("instance_hash"),
            lock_hash=payload.get("lock_hash"),
            cert_sha256=payload.get("cert_sha256"),
            instance_gate_report=FireInstanceGateReport(
                param_ok=_require_bool("instance_gates.param_ok", instance_gates.get("param_ok")),
                authorization_ok=_require_bool(
                    "instance_gates.authorization_ok",
                    instance_gates.get("authorization_ok"),
                ),
                nonce_ok=_require_bool("instance_gates.nonce_ok", instance_gates.get("nonce_ok")),
                maturity_ok=_require_bool("instance_gates.maturity_ok", instance_gates.get("maturity_ok")),
                window_ok=_require_bool("instance_gates.window_ok", instance_gates.get("window_ok")),
                ok=_require_bool("instance_gates.ok", instance_gates.get("ok")),
                error=instance_gates.get("error"),
            ),
            certificate_instance_gate_claims=FireInstanceGateClaims.from_dict(certificate_instance_gate_claims),
            contract_receipts=tuple(FireBundleContractReceipt.from_dict(item) for item in contracts),
        )


@dataclass(frozen=True)
class FireRegistryInstanceGateSummary:
    entry_count: int
    all_ok: bool
    param_ok_count: int
    authorization_ok_count: int
    nonce_ok_count: int
    maturity_ok_count: int
    window_ok_count: int

    def __post_init__(self) -> None:
        for field_name in (
            "entry_count",
            "param_ok_count",
            "authorization_ok_count",
            "nonce_ok_count",
            "maturity_ok_count",
            "window_ok_count",
        ):
            value = getattr(self, field_name)
            if not isinstance(value, int) or isinstance(value, bool):
                raise TypeError(f"{field_name} must be an int")
            if value < 0:
                raise ValueError(f"{field_name} must be non-negative")
        if not isinstance(self.all_ok, bool):
            raise TypeError("all_ok must be a bool")

    def to_dict(self) -> dict[str, object]:
        return {
            "entry_count": self.entry_count,
            "all_ok": self.all_ok,
            "param_ok_count": self.param_ok_count,
            "authorization_ok_count": self.authorization_ok_count,
            "nonce_ok_count": self.nonce_ok_count,
            "maturity_ok_count": self.maturity_ok_count,
            "window_ok_count": self.window_ok_count,
        }

    @classmethod
    def from_entries(cls, entries: tuple["FireRegistryIndexEntry", ...]) -> "FireRegistryInstanceGateSummary":
        return cls(
            entry_count=len(entries),
            all_ok=all(entry.instance_gate_report.ok for entry in entries),
            param_ok_count=sum(1 for entry in entries if entry.instance_gate_report.param_ok),
            authorization_ok_count=sum(1 for entry in entries if entry.instance_gate_report.authorization_ok),
            nonce_ok_count=sum(1 for entry in entries if entry.instance_gate_report.nonce_ok),
            maturity_ok_count=sum(1 for entry in entries if entry.instance_gate_report.maturity_ok),
            window_ok_count=sum(1 for entry in entries if entry.instance_gate_report.window_ok),
        )

    @classmethod
    def from_dict(cls, payload: object) -> "FireRegistryInstanceGateSummary":
        if not isinstance(payload, dict):
            raise TypeError("instance_gate_summary must be an object")
        return cls(
            entry_count=payload.get("entry_count"),
            all_ok=payload.get("all_ok"),
            param_ok_count=payload.get("param_ok_count"),
            authorization_ok_count=payload.get("authorization_ok_count"),
            nonce_ok_count=payload.get("nonce_ok_count"),
            maturity_ok_count=payload.get("maturity_ok_count"),
            window_ok_count=payload.get("window_ok_count"),
        )


@dataclass(frozen=True)
class FireRegistryInstanceGateClaimSummary:
    entry_count: int
    param_ok: str
    authorization_ok: str
    nonce_ok: str
    maturity_ok: str
    window_ok: str

    def __post_init__(self) -> None:
        if not isinstance(self.entry_count, int) or isinstance(self.entry_count, bool):
            raise TypeError("entry_count must be an int")
        if self.entry_count < 0:
            raise ValueError("entry_count must be non-negative")
        object.__setattr__(self, "param_ok", _require_evidence_level("param_ok", self.param_ok))
        object.__setattr__(self, "authorization_ok", _require_evidence_level("authorization_ok", self.authorization_ok))
        object.__setattr__(self, "nonce_ok", _require_evidence_level("nonce_ok", self.nonce_ok))
        object.__setattr__(self, "maturity_ok", _require_evidence_level("maturity_ok", self.maturity_ok))
        object.__setattr__(self, "window_ok", _require_evidence_level("window_ok", self.window_ok))

    def to_dict(self) -> dict[str, object]:
        return {
            "entry_count": self.entry_count,
            "param_ok": self.param_ok,
            "authorization_ok": self.authorization_ok,
            "nonce_ok": self.nonce_ok,
            "maturity_ok": self.maturity_ok,
            "window_ok": self.window_ok,
        }

    @classmethod
    def from_entries(cls, entries: tuple["FireRegistryIndexEntry", ...]) -> "FireRegistryInstanceGateClaimSummary":
        return cls(
            entry_count=len(entries),
            param_ok=_evidence_meet(tuple(entry.certificate_instance_gate_claims.param_ok for entry in entries)),
            authorization_ok=_evidence_meet(tuple(entry.certificate_instance_gate_claims.authorization_ok for entry in entries)),
            nonce_ok=_evidence_meet(tuple(entry.certificate_instance_gate_claims.nonce_ok for entry in entries)),
            maturity_ok=_evidence_meet(tuple(entry.certificate_instance_gate_claims.maturity_ok for entry in entries)),
            window_ok=_evidence_meet(tuple(entry.certificate_instance_gate_claims.window_ok for entry in entries)),
        )

    @classmethod
    def from_dict(cls, payload: object) -> "FireRegistryInstanceGateClaimSummary":
        if not isinstance(payload, dict):
            raise TypeError("certificate_instance_gate_summary must be an object")
        return cls(
            entry_count=payload.get("entry_count"),
            param_ok=payload.get("param_ok"),
            authorization_ok=payload.get("authorization_ok"),
            nonce_ok=payload.get("nonce_ok"),
            maturity_ok=payload.get("maturity_ok"),
            window_ok=payload.get("window_ok"),
        )


@dataclass(frozen=True)
class FireRegistryIndex:
    entries: tuple[FireRegistryIndexEntry, ...]
    index_hash: str
    instance_gate_summary: FireRegistryInstanceGateSummary
    certificate_instance_gate_summary: FireRegistryInstanceGateClaimSummary
    contract_receipts: tuple[FireRegistryContractReceipt, ...] = ()
    signature: str | None = None
    signer_pubkey: str | None = None
    schema: str = INDEX_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != INDEX_SCHEMA:
            raise ValueError(f"unsupported index schema: {self.schema}")
        if not isinstance(self.entries, tuple):
            raise TypeError("entries must be a tuple")
        if any(not isinstance(item, FireRegistryIndexEntry) for item in self.entries):
            raise TypeError("entries must contain FireRegistryIndexEntry values")
        if not isinstance(self.instance_gate_summary, FireRegistryInstanceGateSummary):
            raise TypeError("instance_gate_summary must be a FireRegistryInstanceGateSummary")
        if not isinstance(self.certificate_instance_gate_summary, FireRegistryInstanceGateClaimSummary):
            raise TypeError("certificate_instance_gate_summary must be a FireRegistryInstanceGateClaimSummary")
        if not isinstance(self.contract_receipts, tuple):
            raise TypeError("contract_receipts must be a tuple")
        if any(not isinstance(item, FireRegistryContractReceipt) for item in self.contract_receipts):
            raise TypeError("contract_receipts must contain FireRegistryContractReceipt values")
        object.__setattr__(self, "index_hash", _require_sha256_prefixed("index_hash", self.index_hash))
        if (self.signature is None) != (self.signer_pubkey is None):
            raise ValueError("signature and signer_pubkey must either both be present or both be absent")
        if self.signature is not None:
            object.__setattr__(self, "signature", _require_0x_hex("signature", self.signature, expected_nbytes=96))
            object.__setattr__(self, "signer_pubkey", _require_0x_hex("signer_pubkey", self.signer_pubkey, expected_nbytes=48))

    def payload_without_hash(self) -> dict[str, object]:
        payload = {
            "schema": self.schema,
            "entry_count": len(self.entries),
            "entries": [entry.to_dict() for entry in self.entries],
            "instance_gate_summary": self.instance_gate_summary.to_dict(),
            "certificate_instance_gate_summary": self.certificate_instance_gate_summary.to_dict(),
        }
        if self.contract_receipts:
            payload["contracts"] = [receipt.to_dict() for receipt in self.contract_receipts]
        return payload

    def to_dict(self) -> dict[str, object]:
        payload = self.payload_without_hash()
        payload["index_hash"] = self.index_hash
        payload["signature"] = self.signature
        payload["signer_pubkey"] = self.signer_pubkey
        return payload

    @classmethod
    def build(cls, entries: tuple[FireRegistryIndexEntry, ...]) -> "FireRegistryIndex":
        canonical_entries = tuple(
            sorted(
                entries,
                key=lambda row: (
                    row.object_name,
                    row.object_version,
                    row.object_family,
                    row.bundle_hash,
                    row.bundle_path,
                ),
            )
        )
        contract_receipts = _build_registry_contract_receipts(canonical_entries)
        instance_gate_summary = FireRegistryInstanceGateSummary.from_entries(canonical_entries)
        certificate_instance_gate_summary = FireRegistryInstanceGateClaimSummary.from_entries(canonical_entries)
        payload_without_hash = {
            "schema": INDEX_SCHEMA,
            "entry_count": len(canonical_entries),
            "entries": [entry.to_dict() for entry in canonical_entries],
            "instance_gate_summary": instance_gate_summary.to_dict(),
            "certificate_instance_gate_summary": certificate_instance_gate_summary.to_dict(),
        }
        if contract_receipts:
            payload_without_hash["contracts"] = [receipt.to_dict() for receipt in contract_receipts]
        return cls(
            entries=canonical_entries,
            instance_gate_summary=instance_gate_summary,
            certificate_instance_gate_summary=certificate_instance_gate_summary,
            contract_receipts=contract_receipts,
            index_hash=_sha256_bytes(_canonical_json_bytes(payload_without_hash)),
        )

    @classmethod
    def from_dict(cls, payload: object) -> "FireRegistryIndex":
        if not isinstance(payload, dict):
            raise TypeError("index payload must be an object")
        entries_raw = payload.get("entries")
        if not isinstance(entries_raw, list):
            raise TypeError("entries must be a list")
        entries = tuple(FireRegistryIndexEntry.from_dict(row) for row in entries_raw)
        contracts_raw = payload.get("contracts", [])
        if not isinstance(contracts_raw, list):
            raise TypeError("contracts must be a list")
        instance_gate_summary_raw = payload.get("instance_gate_summary")
        certificate_instance_gate_summary_raw = payload.get("certificate_instance_gate_summary")
        entry_count = payload.get("entry_count")
        if not isinstance(entry_count, int) or isinstance(entry_count, bool):
            raise TypeError("entry_count must be an int")
        if entry_count != len(entries):
            raise ValueError("entry_count mismatch")
        if not isinstance(instance_gate_summary_raw, dict):
            raise TypeError("instance_gate_summary must be an object")
        if not isinstance(certificate_instance_gate_summary_raw, dict):
            raise TypeError("certificate_instance_gate_summary must be an object")
        return cls(
            schema=payload.get("schema", INDEX_SCHEMA),
            entries=entries,
            instance_gate_summary=FireRegistryInstanceGateSummary.from_dict(instance_gate_summary_raw),
            certificate_instance_gate_summary=FireRegistryInstanceGateClaimSummary.from_dict(certificate_instance_gate_summary_raw),
            contract_receipts=tuple(FireRegistryContractReceipt.from_dict(item) for item in contracts_raw),
            index_hash=payload.get("index_hash"),
            signature=payload.get("signature"),
            signer_pubkey=payload.get("signer_pubkey"),
        )

    def to_json_bytes(self) -> bytes:
        return canonical_json_bytes(self.payload_without_hash())


def fire_registry_index_file_sha256(index: FireRegistryIndex) -> str:
    return _sha256_bytes(_canonical_json_bytes(index.to_dict()))


def sign_fire_registry_index(
    index: FireRegistryIndex,
    *,
    privkey: str | int | bytes | bytearray,
) -> FireRegistryIndex:
    if not isinstance(index, FireRegistryIndex):
        raise TypeError("index must be a FireRegistryIndex")
    _require_bls()
    sk = _parse_privkey_to_int(privkey)
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(sk)
    if G2Basic is None:  # pragma: no cover
        raise RuntimeError("py_ecc.bls.G2Basic unavailable after BLS availability check")
    signature = "0x" + G2Basic.Sign(sk, index.to_json_bytes()).hex()
    return FireRegistryIndex(
        entries=index.entries,
        index_hash=index.index_hash,
        instance_gate_summary=index.instance_gate_summary,
        certificate_instance_gate_summary=index.certificate_instance_gate_summary,
        contract_receipts=index.contract_receipts,
        signature=signature,
        signer_pubkey=signer_pubkey,
    )


def verify_fire_registry_index_signature(index: FireRegistryIndex) -> bool:
    if index.signature is None or index.signer_pubkey is None:
        return False
    _require_bls()
    try:
        if G2Basic is None:
            return False
        pk = bytes.fromhex(index.signer_pubkey.removeprefix("0x"))
        sig = bytes.fromhex(index.signature.removeprefix("0x"))
    except ValueError:
        return False
    return bool(G2Basic.Verify(pk, index.to_json_bytes(), sig))


def write_fire_registry_index(
    index_path: str | Path,
    bundle_dirs: list[str | Path],
    *,
    signer_privkey: str | int | bytes | bytearray | None = None,
) -> tuple[FireRegistryIndex, str]:
    path = Path(index_path)
    base_dir = path.parent.resolve()
    built_entries: list[FireRegistryIndexEntry] = []
    for bundle_dir in bundle_dirs:
        bundle_root = Path(bundle_dir).resolve()
        bundle_manifest, bundle_file_sha256, object_manifest, object_instance, object_lock = load_fire_registry_bundle(bundle_root)
        cert_payload = json.loads((bundle_root / bundle_manifest.certificate_path).read_text(encoding="utf-8"))
        certificate = FireIntervalCertificate.from_dict(cert_payload)
        if certificate.instance_gate_claims is None:
            raise ValueError(f"certificate instance gate claims missing for {bundle_root}")
        gate_ok, gate_err, gate_report = verify_fire_object_instance_against_manifest(object_instance, object_manifest=object_manifest)
        if not gate_ok or gate_report is None:
            raise ValueError(f"instance gate verification failed for {bundle_root}: {gate_err or 'unknown'}")
        rel_bundle_path = bundle_root.relative_to(base_dir).as_posix() if bundle_root.is_relative_to(base_dir) else bundle_root.as_posix()
        built_entries.append(
            FireRegistryIndexEntry(
                object_name=object_manifest.object_name,
                object_version=object_manifest.object_version,
                object_family=object_manifest.object_family,
                bundle_path=rel_bundle_path,
                bundle_hash=bundle_manifest.bundle_hash,
                bundle_file_sha256=bundle_file_sha256,
                manifest_hash=object_manifest.manifest_hash,
                instance_hash=object_instance.instance_hash,
                lock_hash=object_lock.lock_hash,
                cert_sha256=object_manifest.cert_sha256,
                instance_gate_report=gate_report,
                certificate_instance_gate_claims=certificate.instance_gate_claims,
                contract_receipts=bundle_manifest.contract_receipts,
            )
        )

    index = FireRegistryIndex.build(tuple(built_entries))
    if signer_privkey is not None:
        index = sign_fire_registry_index(index, privkey=signer_privkey)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(_canonical_json_bytes(index.to_dict()))
    return index, fire_registry_index_file_sha256(index)


def load_fire_registry_index(index_path: str | Path) -> tuple[FireRegistryIndex, str]:
    path = Path(index_path)
    payload = json.loads(path.read_text(encoding="utf-8"))
    index = FireRegistryIndex.from_dict(payload)
    return index, _sha256_bytes(path.read_bytes())


def verify_fire_registry_index(
    index_path: str | Path,
    *,
    expected_index_hash: str | None = None,
    expected_index_file_sha256: str | None = None,
    expected_signer_pubkey: str | None = None,
    require_signature: bool = False,
) -> tuple[bool, str | None, FireRegistryIndex | None]:
    try:
        index, index_file_sha256 = load_fire_registry_index(index_path)
    except (FileNotFoundError, OSError, ValueError, TypeError, KeyError, IndexError, AttributeError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        return False, f"index_load_failed:{exc}", None

    expected_hash = _sha256_bytes(_canonical_json_bytes(index.payload_without_hash()))
    if index.index_hash != expected_hash:
        return False, "index_hash_mismatch", None
    derived_instance_gate_summary = FireRegistryInstanceGateSummary.from_entries(index.entries)
    if index.instance_gate_summary != derived_instance_gate_summary:
        return False, "index_instance_gate_summary_mismatch", None
    derived_certificate_instance_gate_summary = FireRegistryInstanceGateClaimSummary.from_entries(index.entries)
    if index.certificate_instance_gate_summary != derived_certificate_instance_gate_summary:
        return False, "index_certificate_instance_gate_summary_mismatch", None
    derived_contract_receipts = _build_registry_contract_receipts(index.entries)
    if index.contract_receipts and index.contract_receipts != derived_contract_receipts:
        return False, "index_contract_receipts_mismatch", None
    if expected_index_hash is not None and index.index_hash != expected_index_hash:
        return False, "expected_index_hash_mismatch", None
    if expected_index_file_sha256 is not None and index_file_sha256 != expected_index_file_sha256:
        return False, "expected_index_file_sha_mismatch", None
    if index.signature is not None or index.signer_pubkey is not None:
        if not verify_fire_registry_index_signature(index):
            return False, "index_signature_invalid", None
        if expected_signer_pubkey is not None and index.signer_pubkey != expected_signer_pubkey:
            return False, "expected_signer_pubkey_mismatch", None
    elif require_signature or expected_signer_pubkey is not None:
        return False, "index_signature_missing", None

    seen_keys: set[tuple[str, str]] = set()
    base_dir = Path(index_path).resolve().parent
    for entry in index.entries:
        key = (entry.object_name, entry.object_version)
        if key in seen_keys:
            return False, "duplicate_object_name_version", None
        seen_keys.add(key)

        bundle_root = Path(entry.bundle_path)
        if not bundle_root.is_absolute():
            bundle_root = (base_dir / bundle_root).resolve()
        ok, err, bundle_manifest, object_manifest, object_instance, object_lock = verify_fire_registry_bundle(
            bundle_root,
            expected_bundle_hash=entry.bundle_hash,
            expected_bundle_file_sha256=entry.bundle_file_sha256,
        )
        if not ok or bundle_manifest is None or object_manifest is None or object_instance is None or object_lock is None:
            return False, f"bundle_invalid:{entry.bundle_path}:{err or 'unknown'}", None
        if object_manifest.object_name != entry.object_name:
            return False, f"object_name_mismatch:{entry.bundle_path}", None
        if object_manifest.object_version != entry.object_version:
            return False, f"object_version_mismatch:{entry.bundle_path}", None
        if object_manifest.object_family != entry.object_family:
            return False, f"object_family_mismatch:{entry.bundle_path}", None
        if object_manifest.manifest_hash != entry.manifest_hash:
            return False, f"manifest_hash_mismatch:{entry.bundle_path}", None
        if object_instance.instance_hash != entry.instance_hash:
            return False, f"instance_hash_mismatch:{entry.bundle_path}", None
        if object_lock.lock_hash != entry.lock_hash:
            return False, f"lock_hash_mismatch:{entry.bundle_path}", None
        if object_manifest.cert_sha256 != entry.cert_sha256:
            return False, f"cert_hash_mismatch:{entry.bundle_path}", None
        cert_payload = json.loads((bundle_root / bundle_manifest.certificate_path).read_text(encoding="utf-8"))
        certificate = FireIntervalCertificate.from_dict(cert_payload)
        if certificate.instance_gate_claims is None:
            return False, f"certificate_instance_gate_claims_missing:{entry.bundle_path}", None
        if certificate.instance_gate_claims != entry.certificate_instance_gate_claims:
            return False, f"certificate_instance_gate_claims_mismatch:{entry.bundle_path}", None
        gate_ok, gate_err, gate_report = verify_fire_object_instance_against_manifest(object_instance, object_manifest=object_manifest)
        if not gate_ok or gate_report is None:
            return False, f"instance_gate_invalid:{entry.bundle_path}:{gate_err or 'unknown'}", None
        if gate_report != entry.instance_gate_report:
            return False, f"instance_gate_report_mismatch:{entry.bundle_path}", None
        if entry.contract_receipts and entry.contract_receipts != bundle_manifest.contract_receipts:
            return False, f"contract_receipts_mismatch:{entry.bundle_path}", None

    return True, None, index


__all__ = [
    "INDEX_SCHEMA",
    "FireRegistryContractReceipt",
    "FireRegistryIndex",
    "FireRegistryIndexEntry",
    "FireRegistryInstanceGateClaimSummary",
    "FireRegistryInstanceGateSummary",
    "fire_registry_index_file_sha256",
    "load_fire_registry_index",
    "sign_fire_registry_index",
    "verify_fire_registry_index",
    "verify_fire_registry_index_signature",
    "write_fire_registry_index",
]

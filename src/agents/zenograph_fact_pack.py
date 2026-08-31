from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from ..integration.bls_intent_signing import bls_pubkey_hex_from_privkey
from ..state.canonical import canonical_json_bytes, sha256_hex
from .krr_bundle_artifacts import KRRReviewRecord, krr_review_record_from_dict
from .policy_artifacts import G2Basic, _parse_privkey_to_int, _require_bls
from .zenograph_schema import ZGFact, ZGFactStatus

ZENOGRAPH_FACT_RECORD_SCHEMA = "zenodex/zenograph-fact-record/v1"
ZENOGRAPH_FACT_PACK_SCHEMA = "zenodex/zenograph-fact-pack/v1"
_SAFE_TOKEN_CHARS = set("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_.:-")


def _require_text(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    text = value.strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    return text


def _require_safe_token(value: object, *, name: str) -> str:
    text = _require_text(value, name=name)
    if any(ch not in _SAFE_TOKEN_CHARS for ch in text):
        raise ValueError(f"{name} contains unsupported characters: {value!r}")
    return text


def _require_isoish_timestamp(value: object, *, name: str) -> str:
    text = _require_text(value, name=name)
    if "T" not in text:
        raise ValueError(f"{name} must be an ISO-like timestamp")
    return text


def _require_sha256_hex(value: object, *, name: str) -> str:
    text = _require_text(value, name=name)
    if not text.startswith("0x") or len(text) != 66:
        raise ValueError(f"{name} must be a 0x-prefixed sha256 hex string")
    try:
        bytes.fromhex(text[2:])
    except ValueError as exc:
        raise ValueError(f"{name} must be valid hex") from exc
    return text.lower()


def _canonical_json_sha256(value: Mapping[str, Any]) -> str:
    return sha256_hex(canonical_json_bytes(dict(value)))


def _canonicalize_value(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {str(key): _canonicalize_value(item) for key, item in value.items()}
    if isinstance(value, tuple):
        return [_canonicalize_value(item) for item in value]
    if isinstance(value, list):
        return [_canonicalize_value(item) for item in value]
    if isinstance(value, float):
        return format(value, ".12g")
    return value


@dataclass(frozen=True)
class ZenoGraphFactRecord:
    fact_id: str
    subject_id: str
    predicate: str
    value: object | None = None
    object_id: str | None = None
    source_id: str | None = None
    microtheory: str | None = None
    observed_at: str | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "fact_id", _require_safe_token(self.fact_id, name="fact_id"))
        object.__setattr__(self, "subject_id", _require_safe_token(self.subject_id, name="subject_id"))
        object.__setattr__(self, "predicate", _require_safe_token(self.predicate, name="predicate"))
        if self.value is None and self.object_id is None:
            raise ValueError("fact record requires value or object_id")
        if self.object_id is not None:
            object.__setattr__(self, "object_id", _require_safe_token(self.object_id, name="object_id"))
        if self.source_id is not None:
            object.__setattr__(self, "source_id", _require_safe_token(self.source_id, name="source_id"))
        if self.microtheory is not None:
            object.__setattr__(self, "microtheory", _require_safe_token(self.microtheory, name="microtheory"))
        if self.observed_at is not None:
            object.__setattr__(self, "observed_at", _require_isoish_timestamp(self.observed_at, name="observed_at"))

    def runtime_value(self) -> object:
        return self.value if self.value is not None else self.object_id

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": ZENOGRAPH_FACT_RECORD_SCHEMA,
            "fact_id": self.fact_id,
            "subject_id": self.subject_id,
            "predicate": self.predicate,
            "value": self.value,
            "object_id": self.object_id,
            "source_id": self.source_id,
            "microtheory": self.microtheory,
            "observed_at": self.observed_at,
        }


@dataclass(frozen=True)
class ZenoGraphFactPack:
    pack_name: str
    built_at: str
    compiler_version: str
    facts: tuple[ZenoGraphFactRecord, ...]
    review_records: tuple[KRRReviewRecord, ...]
    parent_pack_hash: str | None = None
    signature: str | None = None
    signer_pubkey: str | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "pack_name", _require_safe_token(self.pack_name, name="pack_name"))
        object.__setattr__(self, "built_at", _require_isoish_timestamp(self.built_at, name="built_at"))
        object.__setattr__(self, "compiler_version", _require_safe_token(self.compiler_version, name="compiler_version"))
        if self.parent_pack_hash is not None:
            object.__setattr__(self, "parent_pack_hash", _require_sha256_hex(self.parent_pack_hash, name="parent_pack_hash"))
        if self.signature is not None:
            object.__setattr__(self, "signature", _require_text(self.signature, name="signature"))
        if self.signer_pubkey is not None:
            object.__setattr__(self, "signer_pubkey", _require_text(self.signer_pubkey, name="signer_pubkey"))

        fact_ids: set[str] = set()
        normalized_facts: list[ZenoGraphFactRecord] = []
        for row in self.facts:
            if not isinstance(row, ZenoGraphFactRecord):
                raise TypeError("facts must contain ZenoGraphFactRecord rows")
            if row.fact_id in fact_ids:
                raise ValueError(f"duplicate fact_id: {row.fact_id}")
            fact_ids.add(row.fact_id)
            normalized_facts.append(row)
        object.__setattr__(self, "facts", tuple(normalized_facts))

        review_ids: set[str] = set()
        normalized_reviews: list[KRRReviewRecord] = []
        for row in self.review_records:
            if not isinstance(row, KRRReviewRecord):
                raise TypeError("review_records must contain KRRReviewRecord rows")
            if row.review_id in review_ids:
                raise ValueError(f"duplicate review record: {row.review_id}")
            if row.target_kind == "bundle" and row.target_id != self.pack_name:
                raise ValueError("bundle review target_id must equal pack_name")
            review_ids.add(row.review_id)
            normalized_reviews.append(row)
        object.__setattr__(self, "review_records", tuple(normalized_reviews))

    def to_unsigned_dict(self) -> dict[str, Any]:
        payload = {
            "schema": ZENOGRAPH_FACT_PACK_SCHEMA,
            "pack_name": self.pack_name,
            "built_at": self.built_at,
            "compiler_version": self.compiler_version,
            "facts": [row.to_dict() for row in self.facts],
            "review_records": [row.to_dict() for row in self.review_records],
            "parent_pack_hash": self.parent_pack_hash,
        }
        normalized = _canonicalize_value(payload)
        if not isinstance(normalized, dict):
            raise TypeError("fact pack payload must canonicalize to an object")
        return normalized

    def pack_hash_hex(self) -> str:
        return _canonical_json_sha256(self.to_unsigned_dict())

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["pack_hash"] = self.pack_hash_hex()
        payload["signature"] = self.signature
        payload["signer_pubkey"] = self.signer_pubkey
        return payload

    def runtime_approved(self) -> bool:
        return any(
            row.target_kind == "bundle"
            and row.target_id == self.pack_name
            and row.decision == "approve"
            and row.approved_for_runtime
            and row.provenance_ok
            for row in self.review_records
        )


def build_zenograph_fact_pack(
    *,
    pack_name: str,
    built_at: str,
    compiler_version: str,
    facts: tuple[ZenoGraphFactRecord, ...],
    review_records: tuple[KRRReviewRecord, ...],
    parent_pack_hash: str | None = None,
) -> ZenoGraphFactPack:
    pack = ZenoGraphFactPack(
        pack_name=pack_name,
        built_at=built_at,
        compiler_version=compiler_version,
        facts=facts,
        review_records=review_records,
        parent_pack_hash=parent_pack_hash,
    )
    _enforce_review_gate(pack)
    return pack


def sign_zenograph_fact_pack(
    pack: ZenoGraphFactPack,
    *,
    privkey: str | int | bytes | bytearray,
) -> ZenoGraphFactPack:
    if not isinstance(pack, ZenoGraphFactPack):
        raise TypeError("pack must be a ZenoGraphFactPack")
    _require_bls()
    sk = _parse_privkey_to_int(privkey)
    message = canonical_json_bytes(pack.to_unsigned_dict())
    signature_bytes = G2Basic.Sign(sk, message)
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(sk)
    return ZenoGraphFactPack(
        pack_name=pack.pack_name,
        built_at=pack.built_at,
        compiler_version=pack.compiler_version,
        facts=pack.facts,
        review_records=pack.review_records,
        parent_pack_hash=pack.parent_pack_hash,
        signature="0x" + signature_bytes.hex(),
        signer_pubkey=signer_pubkey,
    )


def verify_zenograph_fact_pack_signature(pack: ZenoGraphFactPack) -> bool:
    if pack.signature is None or pack.signer_pubkey is None:
        return False
    _require_bls()
    if not pack.signer_pubkey.startswith("0x"):
        return False
    try:
        pk = bytes.fromhex(pack.signer_pubkey[2:])
        sig = bytes.fromhex(pack.signature[2:] if pack.signature.startswith("0x") else pack.signature)
    except ValueError:
        return False
    message = canonical_json_bytes(pack.to_unsigned_dict())
    return bool(G2Basic.Verify(pk, message, sig))


def zenograph_runtime_facts(pack: ZenoGraphFactPack) -> dict[tuple[str, str], object]:
    if not isinstance(pack, ZenoGraphFactPack):
        raise TypeError("pack must be a ZenoGraphFactPack")
    return {
        (row.subject_id, row.predicate): row.runtime_value()
        for row in pack.facts
    }


def zenograph_fact_record_from_accepted_fact(fact: ZGFact) -> ZenoGraphFactRecord:
    if not isinstance(fact, ZGFact):
        raise TypeError("fact must be a ZGFact")
    if fact.status is not ZGFactStatus.ACCEPTED:
        raise ValueError("only accepted facts can be exported into a runtime fact pack")
    return ZenoGraphFactRecord(
        fact_id=fact.fact_id,
        subject_id=fact.subject_id,
        predicate=fact.predicate,
        value=fact.value,
        object_id=fact.object_id,
        source_id=fact.source_id,
        microtheory=fact.microtheory,
        observed_at=None,
    )


def load_zenograph_fact_pack_file(
    path: str | Path,
    *,
    require_signature: bool = True,
    require_review: bool = True,
) -> ZenoGraphFactPack:
    obj = json.loads(Path(path).expanduser().resolve().read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("fact pack file must be a JSON object")
    pack = zenograph_fact_pack_from_dict(obj)
    expected_pack_hash = obj.get("pack_hash")
    if expected_pack_hash is not None:
        expected_pack_hash = _require_sha256_hex(expected_pack_hash, name="pack_hash")
        if expected_pack_hash != pack.pack_hash_hex():
            raise ValueError("fact pack hash mismatch")
    if require_review:
        _enforce_review_gate(pack)
    if require_signature and not verify_zenograph_fact_pack_signature(pack):
        raise ValueError("fact pack signature verification failed")
    return pack


def zenograph_fact_record_from_dict(data: Mapping[str, Any]) -> ZenoGraphFactRecord:
    schema = data.get("schema")
    if schema is not None and schema != ZENOGRAPH_FACT_RECORD_SCHEMA:
        raise ValueError("unsupported zenograph fact record schema")
    return ZenoGraphFactRecord(
        fact_id=data.get("fact_id"),
        subject_id=data.get("subject_id"),
        predicate=data.get("predicate"),
        value=data.get("value"),
        object_id=data.get("object_id"),
        source_id=data.get("source_id"),
        microtheory=data.get("microtheory"),
        observed_at=data.get("observed_at"),
    )


def zenograph_fact_pack_from_dict(data: Mapping[str, Any]) -> ZenoGraphFactPack:
    schema = data.get("schema")
    if schema is not None and schema != ZENOGRAPH_FACT_PACK_SCHEMA:
        raise ValueError("unsupported zenograph fact pack schema")
    return ZenoGraphFactPack(
        pack_name=data.get("pack_name"),
        built_at=data.get("built_at"),
        compiler_version=data.get("compiler_version"),
        facts=tuple(
            zenograph_fact_record_from_dict(row) for row in data.get("facts", ())
        ),
        review_records=tuple(
            krr_review_record_from_dict(row) for row in data.get("review_records", ())
        ),
        parent_pack_hash=data.get("parent_pack_hash"),
        signature=data.get("signature"),
        signer_pubkey=data.get("signer_pubkey"),
    )


def _enforce_review_gate(pack: ZenoGraphFactPack) -> None:
    if not pack.runtime_approved():
        raise ValueError("fact pack is missing an approved runtime review record")


__all__ = [
    "ZENOGRAPH_FACT_PACK_SCHEMA",
    "ZENOGRAPH_FACT_RECORD_SCHEMA",
    "ZenoGraphFactPack",
    "ZenoGraphFactRecord",
    "build_zenograph_fact_pack",
    "load_zenograph_fact_pack_file",
    "sign_zenograph_fact_pack",
    "verify_zenograph_fact_pack_signature",
    "zenograph_fact_pack_from_dict",
    "zenograph_fact_record_from_accepted_fact",
    "zenograph_fact_record_from_dict",
    "zenograph_runtime_facts",
]

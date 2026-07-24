"""Canonical ZenoLedger record for sampled-response evidence inclusion.

The record is data only.  It commits the exact sampled-evidence digest and the
ordered provider response/envelope digests at one proposed ZenoLedger height.
Finality and deadline authority are established by a separate sealed adapter.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final

from src.integration.zeno_ledger_v0 import canonical_json_bytes_v0, hash_v0

from .codec import (
    decode_exact_evidence_document_v1,
    decode_exact_response_document_v1,
)
from .model import MAX_PROVIDERS_V1, require_root, require_token, require_u64

SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_SCHEMA_V1: Final = (
    "zenodex.zrpf.sampled_response_ledger_inclusion_record.v1"
)
SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_ROOT_DOMAIN_V1: Final = (
    "zrpf_sampled_response_ledger_inclusion_record_v1"
)
SAMPLED_RESPONSE_LEDGER_RESPONSE_SET_ROOT_DOMAIN_V1: Final = (
    "zrpf_sampled_response_ledger_response_set_v1"
)
SAMPLED_RESPONSE_LEDGER_CARRIER_V1: Final = "evidence.oracle_packets"
MAX_SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_BYTES_V1: Final = 32 * 1_024

_RECORD_FIELDS_V1: Final = frozenset(
    {
        "accepted_provider_ids",
        "accepted_provider_set_root",
        "application_id",
        "beacon_commitment",
        "certificate_root",
        "chain_or_domain_id",
        "checked_epoch",
        "data_epoch_id",
        "data_root",
        "inclusion_height",
        "policy_root",
        "response_deadline_epoch",
        "response_records",
        "response_records_root",
        "sampled_evidence_sha256",
        "schema",
        "zeno_ledger_chain_id",
    }
)
_RESPONSE_RECORD_FIELDS_V1: Final = frozenset(
    {
        "key_id",
        "provider_id",
        "response_deadline_epoch",
        "response_epoch",
        "response_sha256",
        "signature_envelope_sha256",
    }
)


@dataclass(frozen=True, slots=True)
class SampledResponseLedgerResponseRecordV1:
    """One exact provider response and signature-envelope commitment."""

    provider_id: str
    key_id: str
    response_epoch: int
    response_deadline_epoch: int
    response_sha256: str
    signature_envelope_sha256: str

    def __post_init__(self) -> None:
        require_token(self.provider_id, name="ledger response provider_id")
        require_token(self.key_id, name="ledger response key_id")
        require_u64(self.response_epoch, name="ledger response response_epoch")
        require_u64(
            self.response_deadline_epoch,
            name="ledger response response_deadline_epoch",
        )
        require_root(self.response_sha256, name="ledger response response_sha256")
        require_root(
            self.signature_envelope_sha256,
            name="ledger response signature_envelope_sha256",
        )
        if self.response_epoch > self.response_deadline_epoch:
            raise ValueError("ledger response epoch exceeds its deadline")

    def to_document(self) -> dict[str, object]:
        return {
            "key_id": self.key_id,
            "provider_id": self.provider_id,
            "response_deadline_epoch": self.response_deadline_epoch,
            "response_epoch": self.response_epoch,
            "response_sha256": self.response_sha256,
            "signature_envelope_sha256": self.signature_envelope_sha256,
        }


@dataclass(frozen=True, slots=True)
class SampledResponseLedgerInclusionRecordV1:
    """Authority-neutral projection proposed for one finalized ledger body."""

    application_id: str
    chain_or_domain_id: str
    zeno_ledger_chain_id: str
    data_epoch_id: int
    checked_epoch: int
    response_deadline_epoch: int
    inclusion_height: int
    policy_root: str
    certificate_root: str
    data_root: str
    beacon_commitment: str
    sampled_evidence_sha256: str
    accepted_provider_ids: tuple[str, ...]
    accepted_provider_set_root: str
    response_records: tuple[SampledResponseLedgerResponseRecordV1, ...]
    response_records_root: str

    def __post_init__(self) -> None:
        _validate_inclusion_identity_and_epochs(self)
        _validate_inclusion_response_set(self)
        _validate_inclusion_derived_roots(self)

    @property
    def record_root(self) -> str:
        return hash_v0(
            SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_ROOT_DOMAIN_V1,
            self.to_document(),
        )

    def to_document(self) -> dict[str, object]:
        return {
            "accepted_provider_ids": list(self.accepted_provider_ids),
            "accepted_provider_set_root": self.accepted_provider_set_root,
            "application_id": self.application_id,
            "beacon_commitment": self.beacon_commitment,
            "certificate_root": self.certificate_root,
            "chain_or_domain_id": self.chain_or_domain_id,
            "checked_epoch": self.checked_epoch,
            "data_epoch_id": self.data_epoch_id,
            "data_root": self.data_root,
            "inclusion_height": self.inclusion_height,
            "policy_root": self.policy_root,
            "response_deadline_epoch": self.response_deadline_epoch,
            "response_records": [item.to_document() for item in self.response_records],
            "response_records_root": self.response_records_root,
            "sampled_evidence_sha256": self.sampled_evidence_sha256,
            "schema": SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_SCHEMA_V1,
            "zeno_ledger_chain_id": self.zeno_ledger_chain_id,
        }


def _validate_inclusion_identity_and_epochs(
    record: SampledResponseLedgerInclusionRecordV1,
) -> None:
    for name in (
        "application_id",
        "chain_or_domain_id",
        "policy_root",
        "certificate_root",
        "data_root",
        "beacon_commitment",
        "sampled_evidence_sha256",
        "accepted_provider_set_root",
        "response_records_root",
    ):
        require_root(getattr(record, name), name=f"ledger inclusion {name}")
    require_token(
        record.zeno_ledger_chain_id,
        name="ledger inclusion zeno_ledger_chain_id",
    )
    for name in (
        "data_epoch_id",
        "checked_epoch",
        "response_deadline_epoch",
        "inclusion_height",
    ):
        require_u64(getattr(record, name), name=f"ledger inclusion {name}")
    if not record.checked_epoch <= record.inclusion_height <= record.response_deadline_epoch:
        raise ValueError("ledger inclusion height is outside the response window")
    if record.data_epoch_id > record.checked_epoch:
        raise ValueError("ledger inclusion data epoch follows the checked epoch")


def _validate_inclusion_response_set(
    record: SampledResponseLedgerInclusionRecordV1,
) -> None:
    provider_ids = record.accepted_provider_ids
    if type(provider_ids) is not tuple or not provider_ids or len(provider_ids) > MAX_PROVIDERS_V1:
        raise ValueError("ledger inclusion provider IDs are empty or oversized")
    for provider_id in provider_ids:
        require_token(provider_id, name="ledger inclusion provider_id")
    if tuple(sorted(set(provider_ids))) != provider_ids:
        raise ValueError("ledger inclusion provider IDs are not canonical and distinct")
    responses = record.response_records
    if (
        type(responses) is not tuple
        or not responses
        or len(responses) > MAX_PROVIDERS_V1
        or any(type(item) is not SampledResponseLedgerResponseRecordV1 for item in responses)
    ):
        raise TypeError("ledger inclusion response records are empty or invalid")
    identities = tuple((item.provider_id, item.key_id) for item in responses)
    if identities != tuple(sorted(set(identities))):
        raise ValueError("ledger inclusion response identities are not canonical and distinct")
    if tuple(item.provider_id for item in responses) != provider_ids:
        raise ValueError("ledger inclusion responses disagree with accepted providers")
    if any(
        item.response_deadline_epoch != record.response_deadline_epoch
        or item.response_epoch > record.inclusion_height
        for item in responses
    ):
        raise ValueError("ledger inclusion response timing disagrees with inclusion height")


def _validate_inclusion_derived_roots(
    record: SampledResponseLedgerInclusionRecordV1,
) -> None:
    expected_provider_root = hash_v0(
        "zrpf_spot_v7_sampled_provider_set_v1",
        list(record.accepted_provider_ids),
    )
    if record.accepted_provider_set_root != expected_provider_root:
        raise ValueError("ledger inclusion provider-set root mismatch")
    expected_response_root = hash_v0(
        SAMPLED_RESPONSE_LEDGER_RESPONSE_SET_ROOT_DOMAIN_V1,
        {"responses": [item.to_document() for item in record.response_records]},
    )
    if record.response_records_root != expected_response_root:
        raise ValueError("ledger inclusion response-record root mismatch")


def build_sampled_response_ledger_inclusion_record_v1(
    exact_evidence_bytes: bytes,
    *,
    zeno_ledger_chain_id: str,
    inclusion_height: int,
) -> dict[str, object]:
    """Build one authority-neutral record from exact canonical evidence bytes."""

    chain_id = require_token(zeno_ledger_chain_id, name="zeno_ledger_chain_id")
    included = require_u64(inclusion_height, name="inclusion_height")
    evidence = decode_exact_evidence_document_v1(exact_evidence_bytes)
    full_blob = _require_exact_dict(evidence.get("full_blob_target"), name="full_blob_target")
    beacon = _require_exact_dict(evidence.get("beacon"), name="beacon")
    checked = require_u64(evidence.get("checked_epoch"), name="checked_epoch")
    responses = _build_response_records(evidence.get("responses"))
    deadlines = {item.response_deadline_epoch for item in responses}
    if len(deadlines) != 1:
        raise ValueError("sampled responses do not share one deadline")
    deadline = deadlines.pop()
    if not checked <= included <= deadline:
        raise ValueError("proposed inclusion height is outside the response window")
    provider_ids = tuple(item.provider_id for item in responses)
    provider_set_root = hash_v0(
        "zrpf_spot_v7_sampled_provider_set_v1",
        list(provider_ids),
    )
    response_root = hash_v0(
        SAMPLED_RESPONSE_LEDGER_RESPONSE_SET_ROOT_DOMAIN_V1,
        {"responses": [item.to_document() for item in responses]},
    )
    record = SampledResponseLedgerInclusionRecordV1(
        application_id=_require_root_field(full_blob, "application_id"),
        chain_or_domain_id=_require_root_field(full_blob, "chain_or_domain_id"),
        zeno_ledger_chain_id=chain_id,
        data_epoch_id=require_u64(full_blob.get("epoch_id"), name="data epoch_id"),
        checked_epoch=checked,
        response_deadline_epoch=deadline,
        inclusion_height=included,
        policy_root=_require_root_field(evidence, "policy_root"),
        certificate_root=_require_root_field(full_blob, "certificate_root"),
        data_root=_require_root_field(full_blob, "data_root"),
        beacon_commitment=_require_root_field(beacon, "commitment"),
        sampled_evidence_sha256=_sha256_prefixed(exact_evidence_bytes),
        accepted_provider_ids=provider_ids,
        accepted_provider_set_root=provider_set_root,
        response_records=responses,
        response_records_root=response_root,
    )
    encoded = canonical_json_bytes_v0(record.to_document())
    if len(encoded) > MAX_SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_BYTES_V1:
        raise ValueError("sampled-response ledger inclusion record exceeds its byte bound")
    return record.to_document()


def parse_sampled_response_ledger_inclusion_record_v1(
    value: object,
) -> SampledResponseLedgerInclusionRecordV1:
    """Parse one exact-field V1 record without granting authority."""

    record = _require_exact_dict(value, name="sampled-response inclusion record")
    if set(record) != _RECORD_FIELDS_V1:
        raise ValueError("sampled-response inclusion record fields mismatch")
    if record.get("schema") != SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_SCHEMA_V1:
        raise ValueError("sampled-response inclusion record schema mismatch")
    response_values = record.get("response_records")
    if type(response_values) is not list or not 1 <= len(response_values) <= MAX_PROVIDERS_V1:
        raise ValueError("sampled-response inclusion response records are invalid")
    responses = tuple(_parse_response_record(item) for item in response_values)
    provider_values = record.get("accepted_provider_ids")
    if type(provider_values) is not list:
        raise TypeError("sampled-response inclusion provider IDs must be an exact list")
    parsed = SampledResponseLedgerInclusionRecordV1(
        application_id=_require_root_field(record, "application_id"),
        chain_or_domain_id=_require_root_field(record, "chain_or_domain_id"),
        zeno_ledger_chain_id=require_token(
            record.get("zeno_ledger_chain_id"),
            name="zeno_ledger_chain_id",
        ),
        data_epoch_id=require_u64(record.get("data_epoch_id"), name="data_epoch_id"),
        checked_epoch=require_u64(record.get("checked_epoch"), name="checked_epoch"),
        response_deadline_epoch=require_u64(
            record.get("response_deadline_epoch"),
            name="response_deadline_epoch",
        ),
        inclusion_height=require_u64(
            record.get("inclusion_height"),
            name="inclusion_height",
        ),
        policy_root=_require_root_field(record, "policy_root"),
        certificate_root=_require_root_field(record, "certificate_root"),
        data_root=_require_root_field(record, "data_root"),
        beacon_commitment=_require_root_field(record, "beacon_commitment"),
        sampled_evidence_sha256=_require_root_field(record, "sampled_evidence_sha256"),
        accepted_provider_ids=tuple(
            require_token(item, name="accepted_provider_id") for item in provider_values
        ),
        accepted_provider_set_root=_require_root_field(
            record,
            "accepted_provider_set_root",
        ),
        response_records=responses,
        response_records_root=_require_root_field(record, "response_records_root"),
    )
    if canonical_json_bytes_v0(parsed.to_document()) != canonical_json_bytes_v0(record):
        raise ValueError("sampled-response inclusion record is not canonical")
    return parsed


def _build_response_records(value: object) -> tuple[SampledResponseLedgerResponseRecordV1, ...]:
    if type(value) is not list or not 1 <= len(value) <= MAX_PROVIDERS_V1:
        raise ValueError("sampled evidence responses are empty or oversized")
    records: list[SampledResponseLedgerResponseRecordV1] = []
    for index, item in enumerate(value):
        outer = _require_exact_dict(item, name=f"responses[{index}]")
        if set(outer) != {"response_bytes_hex", "signature_envelope"}:
            raise ValueError("sampled evidence response wrapper fields mismatch")
        response_hex = outer.get("response_bytes_hex")
        if type(response_hex) is not str or len(response_hex) % 2 != 0:
            raise ValueError("sampled evidence response hex is invalid")
        try:
            response_bytes = bytes.fromhex(response_hex)
        except ValueError as exc:
            raise ValueError("sampled evidence response hex is invalid") from exc
        response = decode_exact_response_document_v1(response_bytes)
        envelope = _require_exact_dict(
            outer.get("signature_envelope"),
            name=f"responses[{index}].signature_envelope",
        )
        records.append(
            SampledResponseLedgerResponseRecordV1(
                provider_id=require_token(response.get("provider_id"), name="provider_id"),
                key_id=require_token(response.get("key_id"), name="key_id"),
                response_epoch=require_u64(response.get("response_epoch"), name="response_epoch"),
                response_deadline_epoch=require_u64(
                    response.get("response_deadline_epoch"),
                    name="response_deadline_epoch",
                ),
                response_sha256=_sha256_prefixed(response_bytes),
                signature_envelope_sha256=_sha256_prefixed(canonical_json_bytes_v0(envelope)),
            )
        )
    result = tuple(sorted(records, key=lambda item: (item.provider_id, item.key_id)))
    if len({(item.provider_id, item.key_id) for item in result}) != len(result):
        raise ValueError("sampled evidence contains duplicate provider response identities")
    return result


def _parse_response_record(value: object) -> SampledResponseLedgerResponseRecordV1:
    record = _require_exact_dict(value, name="sampled-response response record")
    if set(record) != _RESPONSE_RECORD_FIELDS_V1:
        raise ValueError("sampled-response response-record fields mismatch")
    return SampledResponseLedgerResponseRecordV1(
        provider_id=require_token(record.get("provider_id"), name="provider_id"),
        key_id=require_token(record.get("key_id"), name="key_id"),
        response_epoch=require_u64(record.get("response_epoch"), name="response_epoch"),
        response_deadline_epoch=require_u64(
            record.get("response_deadline_epoch"),
            name="response_deadline_epoch",
        ),
        response_sha256=_require_root_field(record, "response_sha256"),
        signature_envelope_sha256=_require_root_field(
            record,
            "signature_envelope_sha256",
        ),
    )


def _require_exact_dict(value: object, *, name: str) -> dict[str, object]:
    if type(value) is not dict:
        raise TypeError(f"{name} must be an exact dict")
    return value


def _require_root_field(value: dict[str, object], field: str) -> str:
    return require_root(value.get(field), name=field)


def _sha256_prefixed(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


__all__ = [
    "MAX_SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_BYTES_V1",
    "SAMPLED_RESPONSE_LEDGER_CARRIER_V1",
    "SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_ROOT_DOMAIN_V1",
    "SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_SCHEMA_V1",
    "SAMPLED_RESPONSE_LEDGER_RESPONSE_SET_ROOT_DOMAIN_V1",
    "SampledResponseLedgerInclusionRecordV1",
    "SampledResponseLedgerResponseRecordV1",
    "build_sampled_response_ledger_inclusion_record_v1",
    "parse_sampled_response_ledger_inclusion_record_v1",
]

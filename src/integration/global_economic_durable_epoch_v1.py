"""Pure byte bundle for one complete ordinary economic epoch publication.

The bundle is an unmounted durability contract.  It binds bodies that were
already admitted by the economic publisher, but it neither verifies a receipt
nor grants settlement, finality, or writer authority.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, replace
from typing import Final

from ..core.global_economic_durable_activation_v1 import DurableEconomicHeadV1
from ..core.global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from ..core.global_economic_proof_v1 import GlobalEconomicEpochCertificateV1
from ..core.global_economic_refinement_snapshot_v1 import (
    _snapshot_effect_plan_v1,
    _snapshot_epoch_certificate_v1,
)
from ..core.global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_CYCLE_BUDGET_V1,
    MAX_JOURNAL_BYTES_V1,
    ZERO_ROOT_V1,
    EconomicProfileSnapshotV1,
    GlobalEconomicEffectPlanV1,
    _require_root,
    _require_token,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .global_economic_commit_v1 import (
    EconomicEpochBodyAndStateV1,
    PublishedEconomicEpochV1,
    _snapshot_body_and_state_v1,
)

DURABLE_ECONOMIC_EPOCH_SCHEMA_V1: Final = "global-economic-durable-epoch-v1"
MAX_DURABLE_ECONOMIC_EPOCH_PAYLOAD_BYTES_V1: Final = 12 * 1024 * 1024
MAX_DURABLE_ECONOMIC_EPOCH_RECEIPT_BYTES_V1: Final = 4 * 1024 * 1024
MAX_DURABLE_ECONOMIC_EPOCH_RECORD_BYTES_V1: Final = 64 * 1024
MAX_DURABLE_ECONOMIC_EPOCH_BUNDLE_BYTES_V1: Final = 16 * 1024 * 1024
_BUNDLE_MAGIC_V1: Final = b"ZGDEJ1\x00"
_U64_MAX_V1: Final = (1 << 64) - 1


def _require_exact_u64_v1(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    if not 0 <= value <= _U64_MAX_V1:
        raise ValueError(f"{name} must fit an unsigned 64-bit integer")
    return value


def _require_exact_str_v1(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be exact str")
    return value


def _payload_root_v1(payload: bytes) -> str:
    digest = hashlib.sha256()
    digest.update(b"ZenoDEX-DurableEconomicEpochPayload-V1\x00")
    digest.update(len(payload).to_bytes(8, "big"))
    digest.update(payload)
    return "0x" + digest.hexdigest()


@dataclass(frozen=True, slots=True)
class DurableEconomicPublicationHeadV1:
    publication_id: str
    sequence: int
    activation_id: str
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    height: int
    state_root: str
    commit_id: str
    certificate_root: str

    def __post_init__(self) -> None:
        for field_name in (
            "publication_id",
            "activation_id",
            "deployment_root",
            "profile_root",
            "state_root",
            "commit_id",
            "certificate_root",
        ):
            value = _require_exact_str_v1(
                getattr(self, field_name),
                name=f"durable publication head {field_name}",
            )
            _require_root(
                value,
                name=f"durable publication head {field_name}",
                allow_zero=field_name == "commit_id" and self.sequence == 0,
            )
        _require_exact_str_v1(self.chain_id, name="durable publication head chain id")
        _require_token(self.chain_id, name="durable publication head chain id")
        for field_name in ("sequence", "writer_epoch", "height"):
            _require_exact_u64_v1(
                getattr(self, field_name),
                name=f"durable publication head {field_name}",
            )
        if self.sequence == 0:
            if self.publication_id != self.activation_id or self.commit_id != ZERO_ROOT_V1:
                raise ValueError("durable activation head identity mismatch")
        elif self.commit_id == ZERO_ROOT_V1:
            raise ValueError("durable epoch head must declare a commit id")

    @classmethod
    def from_activation(
        cls,
        activation: DurableEconomicHeadV1,
    ) -> DurableEconomicPublicationHeadV1:
        if type(activation) is not DurableEconomicHeadV1:
            raise TypeError("durable publication head requires exact activation head")
        return cls(
            publication_id=activation.activation_id,
            sequence=0,
            activation_id=activation.activation_id,
            chain_id=activation.chain_id,
            deployment_root=activation.deployment_root,
            profile_root=activation.profile_root,
            writer_epoch=activation.writer_epoch,
            height=activation.height,
            state_root=activation.state_root,
            commit_id=ZERO_ROOT_V1,
            certificate_root=activation.certificate_root,
        )


@dataclass(frozen=True, slots=True)
class DurableEconomicEpochRecordV1:
    publication_id: str
    sequence: int
    activation_id: str
    source_publication_id: str
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    height: int
    pre_state_root: str
    post_state_root: str
    commit_id: str
    certificate_root: str
    body_commitment: str
    effect_plan_root: str
    receipt_root: str
    release_observation_root: str
    payload_byte_count: int
    payload_root: str
    receipt_byte_count: int

    def __post_init__(self) -> None:
        for field_name in (
            "publication_id",
            "activation_id",
            "source_publication_id",
            "deployment_root",
            "profile_root",
            "pre_state_root",
            "post_state_root",
            "commit_id",
            "certificate_root",
            "body_commitment",
            "effect_plan_root",
            "receipt_root",
            "release_observation_root",
            "payload_root",
        ):
            value = _require_exact_str_v1(
                getattr(self, field_name),
                name=f"durable epoch {field_name}",
            )
            _require_root(value, name=f"durable epoch {field_name}")
        _require_exact_str_v1(self.chain_id, name="durable epoch chain id")
        _require_token(self.chain_id, name="durable epoch chain id")
        for field_name in (
            "sequence",
            "writer_epoch",
            "height",
            "payload_byte_count",
            "receipt_byte_count",
        ):
            _require_exact_u64_v1(
                getattr(self, field_name),
                name=f"durable epoch {field_name}",
            )
        if self.sequence == 0:
            raise ValueError("durable ordinary epoch sequence must be positive")
        if not 1 <= self.payload_byte_count <= MAX_DURABLE_ECONOMIC_EPOCH_PAYLOAD_BYTES_V1:
            raise ValueError("durable epoch payload is outside the byte bound")
        if not 1 <= self.receipt_byte_count <= MAX_DURABLE_ECONOMIC_EPOCH_RECEIPT_BYTES_V1:
            raise ValueError("durable epoch receipt is outside the byte bound")
        if self.publication_id != self.derived_publication_id:
            raise ValueError("durable epoch publication id is not content-derived")

    @staticmethod
    def _body(**values: object) -> dict[str, object]:
        return {
            "schema": DURABLE_ECONOMIC_EPOCH_SCHEMA_V1,
            "global_settlement_abi": GLOBAL_SETTLEMENT_ABI_V1,
            **values,
        }

    @classmethod
    def build(cls, **values: object) -> DurableEconomicEpochRecordV1:
        publication_id = hash_global_v1(
            "global-economic-durable-epoch-record-v1",
            cls._body(**values),
        )
        return cls(publication_id=publication_id, **values)  # type: ignore[arg-type]

    @property
    def derived_publication_id(self) -> str:
        return hash_global_v1(
            "global-economic-durable-epoch-record-v1",
            self._body(
                sequence=self.sequence,
                activation_id=self.activation_id,
                source_publication_id=self.source_publication_id,
                chain_id=self.chain_id,
                deployment_root=self.deployment_root,
                profile_root=self.profile_root,
                writer_epoch=self.writer_epoch,
                height=self.height,
                pre_state_root=self.pre_state_root,
                post_state_root=self.post_state_root,
                commit_id=self.commit_id,
                certificate_root=self.certificate_root,
                body_commitment=self.body_commitment,
                effect_plan_root=self.effect_plan_root,
                receipt_root=self.receipt_root,
                release_observation_root=self.release_observation_root,
                payload_byte_count=self.payload_byte_count,
                payload_root=self.payload_root,
                receipt_byte_count=self.receipt_byte_count,
            ),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            **self._body(
                sequence=self.sequence,
                activation_id=self.activation_id,
                source_publication_id=self.source_publication_id,
                chain_id=self.chain_id,
                deployment_root=self.deployment_root,
                profile_root=self.profile_root,
                writer_epoch=self.writer_epoch,
                height=self.height,
                pre_state_root=self.pre_state_root,
                post_state_root=self.post_state_root,
                commit_id=self.commit_id,
                certificate_root=self.certificate_root,
                body_commitment=self.body_commitment,
                effect_plan_root=self.effect_plan_root,
                receipt_root=self.receipt_root,
                release_observation_root=self.release_observation_root,
                payload_byte_count=self.payload_byte_count,
                payload_root=self.payload_root,
                receipt_byte_count=self.receipt_byte_count,
            ),
            "publication_id": self.publication_id,
        }


@dataclass(frozen=True, slots=True)
class DurableEconomicEpochBundleV1:
    record: DurableEconomicEpochRecordV1
    payload: bytes
    receipt_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.record) is not DurableEconomicEpochRecordV1:
            raise TypeError("durable epoch bundle record type is not closed")
        if type(self.payload) is not bytes or type(self.receipt_bytes) is not bytes:
            raise TypeError("durable epoch bundle bodies must be exact bytes")
        if len(self.payload) != self.record.payload_byte_count:
            raise ValueError("durable epoch payload byte count mismatch")
        if _payload_root_v1(self.payload) != self.record.payload_root:
            raise ValueError("durable epoch payload root mismatch")
        if len(self.receipt_bytes) != self.record.receipt_byte_count:
            raise ValueError("durable epoch receipt byte count mismatch")
        receipt_root = "0x" + hashlib.sha256(self.receipt_bytes).hexdigest()
        if receipt_root != self.record.receipt_root:
            raise ValueError("durable epoch receipt root mismatch")
        _validate_payload_bindings_v1(self.record, self.payload)

    @property
    def head(self) -> DurableEconomicPublicationHeadV1:
        return DurableEconomicPublicationHeadV1(
            publication_id=self.record.publication_id,
            sequence=self.record.sequence,
            activation_id=self.record.activation_id,
            chain_id=self.record.chain_id,
            deployment_root=self.record.deployment_root,
            profile_root=self.record.profile_root,
            writer_epoch=self.record.writer_epoch,
            height=self.record.height,
            state_root=self.record.post_state_root,
            commit_id=self.record.commit_id,
            certificate_root=self.record.certificate_root,
        )

    @property
    def canonical_bytes(self) -> bytes:
        record_bytes = canonical_global_bytes_v1(self.record)
        if len(record_bytes) > MAX_DURABLE_ECONOMIC_EPOCH_RECORD_BYTES_V1:
            raise ValueError("durable epoch record exceeds its byte bound")
        encoded = bytearray(_BUNDLE_MAGIC_V1)
        encoded.extend(len(record_bytes).to_bytes(4, "big"))
        encoded.extend(record_bytes)
        encoded.extend(len(self.payload).to_bytes(8, "big"))
        encoded.extend(self.payload)
        encoded.extend(len(self.receipt_bytes).to_bytes(8, "big"))
        encoded.extend(self.receipt_bytes)
        bundle = bytes(encoded)
        if len(bundle) > MAX_DURABLE_ECONOMIC_EPOCH_BUNDLE_BYTES_V1:
            raise ValueError("durable epoch bundle exceeds its byte bound")
        return bundle


@dataclass(frozen=True, slots=True)
class DurableEconomicEpochMaterialV1:
    """Exact publisher output required to prepare one durable epoch bundle."""

    source_head: DurableEconomicPublicationHeadV1
    profile: EconomicProfileSnapshotV1
    certificate: GlobalEconomicEpochCertificateV1
    effect_plan: GlobalEconomicEffectPlanV1
    body_and_state: EconomicEpochBodyAndStateV1
    published_epoch: PublishedEconomicEpochV1
    receipt_bytes: bytes


@dataclass(frozen=True, slots=True)
class _OwnedEconomicEpochMaterialV1:
    source_head: DurableEconomicPublicationHeadV1
    profile: EconomicProfileSnapshotV1
    certificate: GlobalEconomicEpochCertificateV1
    effect_plan: GlobalEconomicEffectPlanV1
    body: EconomicEpochBodyAndStateV1
    published: PublishedEconomicEpochV1
    receipt: bytes


def _reject_json_constant_v1(value: str) -> object:
    raise ValueError(f"non-finite JSON constant is forbidden: {value}")


def _reject_duplicate_pairs_v1(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if type(key) is not str:
            raise TypeError("durable epoch JSON key must be exact str")
        if key in result:
            raise ValueError("durable epoch JSON contains a duplicate key")
        result[key] = value
    return result


def _decode_json_v1(payload: bytes, *, name: str) -> object:
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError(f"{name} is not UTF-8") from exc
    try:
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_pairs_v1,
            parse_constant=_reject_json_constant_v1,
        )
    except json.JSONDecodeError as exc:
        raise ValueError(f"{name} is not valid JSON") from exc
    if canonical_global_bytes_v1(value) != payload:
        raise ValueError(f"{name} encoding is not canonical")
    return value


def _object_v1(value: object, *, name: str, fields: frozenset[str]) -> dict[str, object]:
    if type(value) is not dict or set(value) != fields:
        raise ValueError(f"{name} field set is not closed")
    return value


def _str_v1(value: dict[str, object], field: str, *, name: str) -> str:
    result = value[field]
    if type(result) is not str:
        raise TypeError(f"{name} {field} must be exact str")
    return result


def _int_v1(value: dict[str, object], field: str, *, name: str) -> int:
    result = value[field]
    if type(result) is not int:
        raise TypeError(f"{name} {field} must be exact int")
    return result


_RECORD_FIELDS_V1: Final = frozenset(
    {
        "schema", "global_settlement_abi", "publication_id", "sequence",
        "activation_id", "source_publication_id", "chain_id", "deployment_root",
        "profile_root", "writer_epoch", "height", "pre_state_root",
        "post_state_root", "commit_id", "certificate_root", "body_commitment",
        "effect_plan_root", "receipt_root", "release_observation_root",
        "payload_byte_count", "payload_root", "receipt_byte_count",
    }
)
_PAYLOAD_FIELDS_V1: Final = frozenset(
    {"schema", "certificate", "effect_plan", "body_and_state", "published_epoch"}
)
_CERTIFICATE_FIELDS_V1: Final = frozenset(
    {
        "schema", "chain_id", "deployment_root", "profile_root", "writer_epoch",
        "height", "pre_state_root", "post_state_root", "ordered_occurrence_ids",
        "ordered_route_journal_roots", "ordered_route_assumption_roots",
        "module_leaf_occurrences", "aggregation_fanout", "aggregation_levels",
        "effect_plan_root", "terminal_obligations_root", "body_commitment",
        "data_availability_root", "finality_root", "source_manifest_root",
        "toolchain_manifest_root", "root_image_id", "receipt_root", "receipt_kind",
        "journal_bytes", "cycle_budget",
    }
)
_EFFECT_FIELDS_V1: Final = frozenset(
    {
        "schema", "rows", "asset_conservation", "fee_conservation", "lane_writes",
        "occurrence_consumptions", "external_outbox_enqueue",
    }
)
_BODY_FIELDS_V1: Final = frozenset(
    {
        "pre_state_root", "post_state", "ordered_command_body_hashes",
        "receipt_archive_root", "data_availability_root", "finality_root",
    }
)
_STATE_FIELDS_V1: Final = frozenset(
    {
        "schema", "chain_id", "deployment_root", "writer_epoch", "height",
        "profile_root", "lane_roots", "balances", "supplies", "custody",
        "liabilities", "reserves", "oracle_occurrences", "replay_state",
        "terminal_obligations", "history_root", "outbox",
    }
)
_PUBLISHED_FIELDS_V1: Final = frozenset(
    {
        "commit_id", "certificate_root", "profile_root", "writer_epoch",
        "pre_state_root", "post_state_root", "body_commitment",
        "data_availability_root", "finality_root", "receipt_root",
        "receipt_archive_root", "effect_plan_root",
        "route_state_effect_refinement_roots", "route_state_projection_roots",
        "release_observation_root",
    }
)


@dataclass(frozen=True, slots=True)
class _PayloadSectionsV1:
    certificate: dict[str, object]
    effect_plan: dict[str, object]
    body: dict[str, object]
    state: dict[str, object]
    published: dict[str, object]


def _decode_payload_sections_v1(payload_bytes: bytes) -> _PayloadSectionsV1:
    payload = _object_v1(
        _decode_json_v1(payload_bytes, name="durable epoch payload"),
        name="durable epoch payload",
        fields=_PAYLOAD_FIELDS_V1,
    )
    if payload["schema"] != DURABLE_ECONOMIC_EPOCH_SCHEMA_V1:
        raise ValueError("durable epoch payload schema mismatch")
    certificate = _object_v1(payload["certificate"], name="durable epoch certificate", fields=_CERTIFICATE_FIELDS_V1)
    effect_plan = _object_v1(payload["effect_plan"], name="durable epoch effect plan", fields=_EFFECT_FIELDS_V1)
    body = _object_v1(payload["body_and_state"], name="durable epoch body", fields=_BODY_FIELDS_V1)
    return _PayloadSectionsV1(
        certificate=certificate,
        effect_plan=effect_plan,
        body=body,
        state=_object_v1(body["post_state"], name="durable epoch state", fields=_STATE_FIELDS_V1),
        published=_object_v1(
            payload["published_epoch"],
            name="durable published epoch",
            fields=_PUBLISHED_FIELDS_V1,
        ),
    )


def _validate_ordered_roots_v1(sections: _PayloadSectionsV1) -> int:
    command_hashes = sections.body["ordered_command_body_hashes"]
    occurrences = sections.certificate["ordered_occurrence_ids"]
    if type(command_hashes) is not list or type(occurrences) is not list:
        raise TypeError("durable epoch ordered bodies must be exact arrays")
    if not 1 <= len(command_hashes) == len(occurrences) <= 64:
        raise ValueError("durable epoch command cardinality mismatch")
    root_groups = (
        ("command hash", command_hashes, False),
        ("occurrence", occurrences, True),
        ("route journal", sections.certificate["ordered_route_journal_roots"], True),
        ("route assumption", sections.certificate["ordered_route_assumption_roots"], True),
        ("route projection", sections.published["route_state_projection_roots"], True),
        (
            "route state/effect refinement",
            sections.published["route_state_effect_refinement_roots"],
            True,
        ),
    )
    for label, roots, unique in root_groups:
        if type(roots) is not list or any(type(root) is not str for root in roots):
            raise TypeError(f"durable epoch {label} roots must be an exact array")
        if label != "command hash" and len(roots) != len(occurrences):
            raise ValueError(f"durable epoch {label} cardinality mismatch")
        if unique and len(roots) != len(set(roots)):
            raise ValueError(f"durable epoch {label} roots must be unique")
        for index, root in enumerate(roots):
            _require_root(root, name=f"durable epoch {label}[{index}]")
    return len(occurrences)


def _validate_array_shapes_v1(sections: _PayloadSectionsV1) -> None:
    for label, section in (
        ("certificate", sections.certificate),
        ("effect plan", sections.effect_plan),
        ("state", sections.state),
    ):
        if section["schema"] != GLOBAL_SETTLEMENT_ABI_V1:
            raise ValueError(f"durable epoch {label} schema mismatch")
    for field in (
        "rows",
        "asset_conservation",
        "fee_conservation",
        "lane_writes",
        "occurrence_consumptions",
        "external_outbox_enqueue",
    ):
        if type(sections.effect_plan[field]) is not list:
            raise TypeError(f"durable epoch effect plan {field} must be an exact array")
    for field in (
        "lane_roots",
        "balances",
        "supplies",
        "custody",
        "liabilities",
        "reserves",
        "oracle_occurrences",
        "replay_state",
        "terminal_obligations",
        "outbox",
    ):
        if type(sections.state[field]) is not list:
            raise TypeError(f"durable epoch state {field} must be an exact array")

    occurrences = sections.certificate["ordered_occurrence_ids"]
    consumed = sections.effect_plan["occurrence_consumptions"]
    if type(occurrences) is not list or any(type(item) is not str for item in occurrences):
        raise TypeError("durable epoch certificate occurrences must be exact strings")
    if type(consumed) is not list or any(type(item) is not str for item in consumed):
        raise TypeError("durable epoch effect consumptions must be exact strings")
    if consumed != sorted(occurrences):
        raise ValueError("durable epoch effect occurrence consumption mismatch")


def _validate_proof_shape_v1(sections: _PayloadSectionsV1, command_count: int) -> None:
    certificate = sections.certificate
    leaf_count = _int_v1(certificate, "module_leaf_occurrences", name="certificate")
    fanout = _int_v1(certificate, "aggregation_fanout", name="certificate")
    levels = _int_v1(certificate, "aggregation_levels", name="certificate")
    journal_bytes = _int_v1(certificate, "journal_bytes", name="certificate")
    cycle_budget = _int_v1(certificate, "cycle_budget", name="certificate")
    if not command_count <= leaf_count <= 64:
        raise ValueError("durable epoch module leaf count is outside the ABI bound")
    if fanout != 8 or not 0 <= levels <= 2:
        raise ValueError("durable epoch aggregation shape is outside the ABI bound")
    if journal_bytes <= 0 or cycle_budget <= 0:
        raise ValueError("durable epoch proof resource declarations must be positive")
    if journal_bytes > MAX_JOURNAL_BYTES_V1 or cycle_budget > MAX_CYCLE_BUDGET_V1:
        raise ValueError("durable epoch proof resources exceed the ABI ceiling")
    journal = dict(certificate)
    for field in ("receipt_root", "receipt_kind", "journal_bytes", "cycle_budget"):
        del journal[field]
    if journal_bytes != len(canonical_global_bytes_v1(journal)):
        raise ValueError("durable epoch journal byte declaration mismatch")
    if certificate["receipt_kind"] != "SUCCINCT":
        raise ValueError("durable epoch receipt kind must be succinct")


def _derived_payload_roots_v1(
    sections: _PayloadSectionsV1,
) -> tuple[str, str, str, str]:
    derived_state_root = hash_global_v1("global-economic-state-root-v1", sections.state)
    derived_certificate_root = hash_global_v1(
        "global-economic-epoch-certificate-v1", sections.certificate
    )
    derived_effect_root = hash_global_v1(
        "global-economic-effect-plan-v1", sections.effect_plan
    )
    derived_body = hash_global_v1(
        "global-economic-epoch-body-v1",
        {
            "pre_state_root": sections.body["pre_state_root"],
            "post_state_root": derived_state_root,
            "ordered_command_body_hashes": sections.body["ordered_command_body_hashes"],
            "receipt_archive_root": sections.body["receipt_archive_root"],
            "outbox": sections.state["outbox"],
        },
    )
    return derived_state_root, derived_certificate_root, derived_effect_root, derived_body


def _require_payload_cross_bindings_v1(
    record: DurableEconomicEpochRecordV1,
    sections: _PayloadSectionsV1,
    derived_roots: tuple[str, str, str, str],
) -> None:
    certificate = sections.certificate
    body = sections.body
    state = sections.state
    published = sections.published
    derived_state_root, derived_certificate_root, derived_effect_root, derived_body = derived_roots
    bindings = (
        (_str_v1(certificate, "chain_id", name="certificate"), record.chain_id),
        (_str_v1(certificate, "deployment_root", name="certificate"), record.deployment_root),
        (_str_v1(certificate, "profile_root", name="certificate"), record.profile_root),
        (_int_v1(certificate, "writer_epoch", name="certificate"), record.writer_epoch),
        (_int_v1(certificate, "height", name="certificate"), record.height),
        (_str_v1(certificate, "pre_state_root", name="certificate"), record.pre_state_root),
        (_str_v1(certificate, "post_state_root", name="certificate"), record.post_state_root),
        (_str_v1(certificate, "effect_plan_root", name="certificate"), record.effect_plan_root),
        (_str_v1(certificate, "body_commitment", name="certificate"), record.body_commitment),
        (_str_v1(certificate, "receipt_root", name="certificate"), record.receipt_root),
        (derived_certificate_root, record.certificate_root),
        (derived_effect_root, record.effect_plan_root),
        (derived_body, record.body_commitment),
        (derived_state_root, record.post_state_root),
        (_str_v1(body, "pre_state_root", name="body"), record.pre_state_root),
        (_str_v1(state, "chain_id", name="state"), record.chain_id),
        (_str_v1(state, "deployment_root", name="state"), record.deployment_root),
        (_str_v1(state, "profile_root", name="state"), record.profile_root),
        (_int_v1(state, "writer_epoch", name="state"), record.writer_epoch),
        (_int_v1(state, "height", name="state"), record.height),
        (_str_v1(published, "commit_id", name="published"), record.commit_id),
        (_str_v1(published, "certificate_root", name="published"), record.certificate_root),
        (_str_v1(published, "profile_root", name="published"), record.profile_root),
        (_int_v1(published, "writer_epoch", name="published"), record.writer_epoch),
        (_str_v1(published, "pre_state_root", name="published"), record.pre_state_root),
        (_str_v1(published, "post_state_root", name="published"), record.post_state_root),
        (_str_v1(published, "body_commitment", name="published"), record.body_commitment),
        (_str_v1(published, "receipt_root", name="published"), record.receipt_root),
        (_str_v1(published, "effect_plan_root", name="published"), record.effect_plan_root),
        (
            _str_v1(published, "release_observation_root", name="published"),
            record.release_observation_root,
        ),
        (
            _str_v1(certificate, "data_availability_root", name="certificate"),
            _str_v1(body, "data_availability_root", name="body"),
        ),
        (
            _str_v1(published, "data_availability_root", name="published"),
            _str_v1(body, "data_availability_root", name="body"),
        ),
        (
            _str_v1(certificate, "finality_root", name="certificate"),
            _str_v1(body, "finality_root", name="body"),
        ),
        (
            _str_v1(published, "finality_root", name="published"),
            _str_v1(body, "finality_root", name="body"),
        ),
        (
            _str_v1(published, "receipt_archive_root", name="published"),
            _str_v1(body, "receipt_archive_root", name="body"),
        ),
    )
    if any(actual != expected for actual, expected in bindings):
        raise ValueError("durable epoch payload binding mismatch")


def _validate_payload_bindings_v1(
    record: DurableEconomicEpochRecordV1,
    payload_bytes: bytes,
) -> None:
    sections = _decode_payload_sections_v1(payload_bytes)
    command_count = _validate_ordered_roots_v1(sections)
    _validate_array_shapes_v1(sections)
    _validate_proof_shape_v1(sections, command_count)
    _require_payload_cross_bindings_v1(
        record,
        sections,
        _derived_payload_roots_v1(sections),
    )


def _snapshot_material_v1(
    material: DurableEconomicEpochMaterialV1,
) -> _OwnedEconomicEpochMaterialV1:
    if type(material) is not DurableEconomicEpochMaterialV1:
        raise TypeError("durable epoch material type is not closed")
    if type(material.source_head) is not DurableEconomicPublicationHeadV1:
        raise TypeError("durable epoch source head type is not closed")
    if type(material.published_epoch) is not PublishedEconomicEpochV1:
        raise TypeError("durable epoch published record type is not closed")
    if type(material.receipt_bytes) is not bytes:
        raise TypeError("durable epoch receipt must be exact bytes")
    return _OwnedEconomicEpochMaterialV1(
        source_head=material.source_head,
        profile=snapshot_economic_profile_v1(material.profile),
        certificate=_snapshot_epoch_certificate_v1(material.certificate),
        effect_plan=_snapshot_effect_plan_v1(material.effect_plan),
        body=_snapshot_body_and_state_v1(material.body_and_state),
        published=replace(material.published_epoch),
        receipt=bytes(material.receipt_bytes),
    )


def _release_observation_root_v1(profile: EconomicProfileSnapshotV1) -> str:
    return hash_global_v1(
        "global-economic-release-observation-v1",
        {
            "profile_root": profile.profile_id,
            "lane_registry_root": profile.lane_registry.registry_root,
            "route_registry_root": profile.route_registry.registry_root,
        },
    )


def _validate_typed_material_bindings_v1(
    material: _OwnedEconomicEpochMaterialV1,
    receipt_root: str,
    release_observation_root: str,
) -> None:
    source_head = material.source_head
    profile = material.profile
    certificate = material.certificate
    effect_plan = material.effect_plan
    body = material.body
    published = material.published
    if source_head.sequence == _U64_MAX_V1 or source_head.height == _U64_MAX_V1:
        raise ValueError("durable epoch source coordinates cannot advance")
    expected = (
        (certificate.chain_id, source_head.chain_id),
        (certificate.deployment_root, source_head.deployment_root),
        (certificate.profile_root, source_head.profile_root),
        (certificate.profile_root, profile.profile_id),
        (certificate.writer_epoch, source_head.writer_epoch),
        (certificate.writer_epoch, profile.authority_epoch),
        (certificate.height, source_head.height + 1),
        (certificate.pre_state_root, source_head.state_root),
        (certificate.post_state_root, body.post_state.state_root),
        (certificate.effect_plan_root, effect_plan.effect_plan_root),
        (certificate.body_commitment, body.body_commitment),
        (certificate.receipt_root, receipt_root),
        (certificate.data_availability_root, body.data_availability_root),
        (certificate.finality_root, body.finality_root),
        (body.pre_state_root, source_head.state_root),
        (body.post_state.chain_id, source_head.chain_id),
        (body.post_state.deployment_root, source_head.deployment_root),
        (body.post_state.profile_root, source_head.profile_root),
        (body.post_state.writer_epoch, source_head.writer_epoch),
        (body.post_state.height, source_head.height + 1),
        (published.certificate_root, certificate.certificate_root),
        (published.profile_root, profile.profile_id),
        (published.writer_epoch, source_head.writer_epoch),
        (published.pre_state_root, source_head.state_root),
        (published.post_state_root, body.post_state.state_root),
        (published.body_commitment, body.body_commitment),
        (published.effect_plan_root, effect_plan.effect_plan_root),
        (published.receipt_root, receipt_root),
        (published.receipt_archive_root, body.receipt_archive_root),
        (published.data_availability_root, body.data_availability_root),
        (published.finality_root, body.finality_root),
        (published.release_observation_root, release_observation_root),
    )
    if any(actual != wanted for actual, wanted in expected):
        raise ValueError("durable epoch typed source or body binding mismatch")


def prepare_durable_economic_epoch_bundle_v1(
    material: DurableEconomicEpochMaterialV1,
) -> DurableEconomicEpochBundleV1:
    """Snapshot one publisher-admitted epoch into a complete canonical bundle."""

    owned = _snapshot_material_v1(material)
    receipt_root = "0x" + hashlib.sha256(owned.receipt).hexdigest()
    release_root = _release_observation_root_v1(owned.profile)
    _validate_typed_material_bindings_v1(
        owned,
        receipt_root,
        release_root,
    )
    payload = canonical_global_bytes_v1(
        {
            "schema": DURABLE_ECONOMIC_EPOCH_SCHEMA_V1,
            "certificate": owned.certificate,
            "effect_plan": owned.effect_plan,
            "body_and_state": owned.body,
            "published_epoch": owned.published,
        }
    )
    record = DurableEconomicEpochRecordV1.build(
        sequence=owned.source_head.sequence + 1,
        activation_id=owned.source_head.activation_id,
        source_publication_id=owned.source_head.publication_id,
        chain_id=owned.source_head.chain_id,
        deployment_root=owned.source_head.deployment_root,
        profile_root=owned.source_head.profile_root,
        writer_epoch=owned.source_head.writer_epoch,
        height=owned.certificate.height,
        pre_state_root=owned.source_head.state_root,
        post_state_root=owned.body.post_state.state_root,
        commit_id=owned.published.commit_id,
        certificate_root=owned.certificate.certificate_root,
        body_commitment=owned.body.body_commitment,
        effect_plan_root=owned.effect_plan.effect_plan_root,
        receipt_root=receipt_root,
        release_observation_root=release_root,
        payload_byte_count=len(payload),
        payload_root=_payload_root_v1(payload),
        receipt_byte_count=len(owned.receipt),
    )
    return DurableEconomicEpochBundleV1(record, payload, owned.receipt)


def _decode_record_v1(record_bytes: bytes) -> DurableEconomicEpochRecordV1:
    value = _object_v1(
        _decode_json_v1(record_bytes, name="durable epoch record"),
        name="durable epoch record",
        fields=_RECORD_FIELDS_V1,
    )
    if value["schema"] != DURABLE_ECONOMIC_EPOCH_SCHEMA_V1:
        raise ValueError("durable epoch record schema mismatch")
    if value["global_settlement_abi"] != GLOBAL_SETTLEMENT_ABI_V1:
        raise ValueError("durable epoch record ABI mismatch")
    return DurableEconomicEpochRecordV1(
        publication_id=_str_v1(value, "publication_id", name="record"),
        sequence=_int_v1(value, "sequence", name="record"),
        activation_id=_str_v1(value, "activation_id", name="record"),
        source_publication_id=_str_v1(value, "source_publication_id", name="record"),
        chain_id=_str_v1(value, "chain_id", name="record"),
        deployment_root=_str_v1(value, "deployment_root", name="record"),
        profile_root=_str_v1(value, "profile_root", name="record"),
        writer_epoch=_int_v1(value, "writer_epoch", name="record"),
        height=_int_v1(value, "height", name="record"),
        pre_state_root=_str_v1(value, "pre_state_root", name="record"),
        post_state_root=_str_v1(value, "post_state_root", name="record"),
        commit_id=_str_v1(value, "commit_id", name="record"),
        certificate_root=_str_v1(value, "certificate_root", name="record"),
        body_commitment=_str_v1(value, "body_commitment", name="record"),
        effect_plan_root=_str_v1(value, "effect_plan_root", name="record"),
        receipt_root=_str_v1(value, "receipt_root", name="record"),
        release_observation_root=_str_v1(value, "release_observation_root", name="record"),
        payload_byte_count=_int_v1(value, "payload_byte_count", name="record"),
        payload_root=_str_v1(value, "payload_root", name="record"),
        receipt_byte_count=_int_v1(value, "receipt_byte_count", name="record"),
    )


def decode_durable_economic_epoch_bundle_v1(
    bundle_bytes: bytes,
) -> DurableEconomicEpochBundleV1:
    """Decode one exact bundle and reject truncation, surplus, or mutation."""

    if type(bundle_bytes) is not bytes:
        raise TypeError("durable epoch bundle must be exact bytes")
    if len(bundle_bytes) > MAX_DURABLE_ECONOMIC_EPOCH_BUNDLE_BYTES_V1:
        raise ValueError("durable epoch bundle exceeds its byte bound")
    if not bundle_bytes.startswith(_BUNDLE_MAGIC_V1):
        raise ValueError("durable epoch bundle magic mismatch")
    cursor = len(_BUNDLE_MAGIC_V1)
    if len(bundle_bytes) < cursor + 4:
        raise ValueError("durable epoch bundle is truncated before its record")
    record_size = int.from_bytes(bundle_bytes[cursor : cursor + 4], "big")
    cursor += 4
    if not 1 <= record_size <= MAX_DURABLE_ECONOMIC_EPOCH_RECORD_BYTES_V1:
        raise ValueError("durable epoch record is outside the byte bound")
    record_end = cursor + record_size
    if record_end > len(bundle_bytes):
        raise ValueError("durable epoch record is truncated")
    record = _decode_record_v1(bundle_bytes[cursor:record_end])
    cursor = record_end
    if len(bundle_bytes) < cursor + 8:
        raise ValueError("durable epoch bundle is truncated before its payload")
    payload_size = int.from_bytes(bundle_bytes[cursor : cursor + 8], "big")
    cursor += 8
    if payload_size != record.payload_byte_count:
        raise ValueError("durable epoch framed payload byte count mismatch")
    payload_end = cursor + payload_size
    if payload_end > len(bundle_bytes):
        raise ValueError("durable epoch payload is truncated")
    payload = bundle_bytes[cursor:payload_end]
    cursor = payload_end
    if len(bundle_bytes) < cursor + 8:
        raise ValueError("durable epoch bundle is truncated before its receipt")
    receipt_size = int.from_bytes(bundle_bytes[cursor : cursor + 8], "big")
    cursor += 8
    if receipt_size != record.receipt_byte_count:
        raise ValueError("durable epoch framed receipt byte count mismatch")
    receipt_end = cursor + receipt_size
    if receipt_end != len(bundle_bytes):
        if receipt_end > len(bundle_bytes):
            raise ValueError("durable epoch receipt is truncated")
        raise ValueError("durable epoch bundle has trailing bytes")
    bundle = DurableEconomicEpochBundleV1(
        record,
        payload,
        bundle_bytes[cursor:receipt_end],
    )
    if bundle.canonical_bytes != bundle_bytes:
        raise ValueError("durable epoch bundle encoding is not canonical")
    return bundle


__all__ = [
    "DURABLE_ECONOMIC_EPOCH_SCHEMA_V1",
    "MAX_DURABLE_ECONOMIC_EPOCH_BUNDLE_BYTES_V1",
    "DurableEconomicEpochBundleV1",
    "DurableEconomicEpochMaterialV1",
    "DurableEconomicEpochRecordV1",
    "DurableEconomicPublicationHeadV1",
    "decode_durable_economic_epoch_bundle_v1",
    "prepare_durable_economic_epoch_bundle_v1",
]

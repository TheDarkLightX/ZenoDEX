"""Pure durable-activation bundle contracts for global economic migrations.

This module prepares a complete, content-addressed byte bundle for a genesis or
migration activation.  It performs no IO and grants no publication authority.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from enum import Enum
from typing import Final

from .economic_initial_state_atom_coverage_v1 import EconomicInitialStateKindV1
from .economic_initial_state_v1 import (
    EconomicInitialStateAdmissionV1,
    _OwnedEconomicInitialStateAdmissionV1,
    _snapshot_economic_initial_state_admission_v1,
    _validate_owned_economic_initial_state_admission_v1,
)
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    ZERO_ROOT_V1,
    _require_root,
    _require_token,
    canonical_global_bytes_v1,
    hash_global_v1,
)

DURABLE_ECONOMIC_ACTIVATION_SCHEMA_V1: Final = (
    "global-economic-durable-activation-v1"
)
MAX_DURABLE_ECONOMIC_COMPONENT_BYTES_V1: Final = 8 * 1024 * 1024
MAX_DURABLE_ECONOMIC_RECORD_BYTES_V1: Final = 256 * 1024
MAX_DURABLE_ECONOMIC_BUNDLE_BYTES_V1: Final = 16 * 1024 * 1024
_BUNDLE_MAGIC_V1: Final = b"ZGDAJ1\x00"
_U64_MAX_V1: Final = (1 << 64) - 1


def _require_exact_u64_v1(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    if not 0 <= value <= _U64_MAX_V1:
        raise ValueError(f"{name} must fit an unsigned 64-bit integer")
    return value


def _require_exact_text_v1(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be exact str")
    return value


class DurableEconomicComponentKindV1(str, Enum):
    PROFILE = "PROFILE"
    POLICY_REGISTRY = "POLICY_REGISTRY"
    STATE = "STATE"
    PREDECESSOR_STATE = "PREDECESSOR_STATE"
    SOURCE_MANIFEST = "SOURCE_MANIFEST"
    CERTIFICATE = "CERTIFICATE"
    RECEIPT = "RECEIPT"


_COMPONENT_KINDS_V1: Final = tuple(DurableEconomicComponentKindV1)


def _component_root_v1(
    kind: DurableEconomicComponentKindV1,
    payload: bytes,
) -> str:
    digest = hashlib.sha256()
    digest.update(b"ZenoDEX-DurableEconomicComponent-V1\x00")
    encoded_kind = kind.value.encode("ascii")
    digest.update(len(encoded_kind).to_bytes(2, "big"))
    digest.update(encoded_kind)
    digest.update(len(payload).to_bytes(8, "big"))
    digest.update(payload)
    return "0x" + digest.hexdigest()


@dataclass(frozen=True, slots=True)
class DurableEconomicComponentCommitmentV1:
    kind: DurableEconomicComponentKindV1
    byte_count: int
    root: str

    def __post_init__(self) -> None:
        if type(self.kind) is not DurableEconomicComponentKindV1:
            raise TypeError("durable activation component kind is not closed")
        _require_exact_u64_v1(
            self.byte_count,
            name="durable activation component byte count",
        )
        if not 1 <= self.byte_count <= MAX_DURABLE_ECONOMIC_COMPONENT_BYTES_V1:
            raise ValueError("durable activation component is outside the byte bound")
        _require_exact_text_v1(self.root, name="durable activation component root")
        _require_root(self.root, name="durable activation component root")

    def to_canonical(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "byte_count": self.byte_count,
            "root": self.root,
        }


@dataclass(frozen=True, slots=True)
class DurableEconomicComponentV1:
    kind: DurableEconomicComponentKindV1
    payload: bytes

    def __post_init__(self) -> None:
        if type(self.kind) is not DurableEconomicComponentKindV1:
            raise TypeError("durable activation component kind is not closed")
        if type(self.payload) is not bytes:
            raise TypeError("durable activation component payload must be exact bytes")
        if not 1 <= len(self.payload) <= MAX_DURABLE_ECONOMIC_COMPONENT_BYTES_V1:
            raise ValueError("durable activation component is outside the byte bound")

    @property
    def commitment(self) -> DurableEconomicComponentCommitmentV1:
        return DurableEconomicComponentCommitmentV1(
            kind=self.kind,
            byte_count=len(self.payload),
            root=_component_root_v1(self.kind, self.payload),
        )


@dataclass(frozen=True, slots=True)
class DurableEconomicActivationRecordV1:
    activation_id: str
    kind: EconomicInitialStateKindV1
    generation: int
    chain_id: str
    deployment_root: str
    profile_root: str
    state_root: str
    writer_epoch: int
    height: int
    source_activation_id: str
    source_profile_root: str
    source_state_root: str
    source_writer_epoch: int
    source_height: int
    certificate_root: str
    component_commitments: tuple[DurableEconomicComponentCommitmentV1, ...]

    def __post_init__(self) -> None:
        _require_exact_text_v1(self.activation_id, name="durable activation id")
        _require_root(self.activation_id, name="durable activation id")
        if type(self.kind) is not EconomicInitialStateKindV1:
            raise TypeError("durable activation kind is not closed")
        for field_name in (
            "generation",
            "writer_epoch",
            "height",
            "source_writer_epoch",
            "source_height",
        ):
            _require_exact_u64_v1(
                getattr(self, field_name),
                name=f"durable activation {field_name}",
            )
        _require_exact_text_v1(self.chain_id, name="durable activation chain id")
        _require_token(self.chain_id, name="durable activation chain id")
        for field_name in (
            "deployment_root",
            "profile_root",
            "state_root",
            "certificate_root",
        ):
            value = _require_exact_text_v1(
                getattr(self, field_name),
                name=f"durable activation {field_name}",
            )
            _require_root(value, name=f"durable activation {field_name}")
        for field_name in (
            "source_activation_id",
            "source_profile_root",
            "source_state_root",
        ):
            value = _require_exact_text_v1(
                getattr(self, field_name),
                name=f"durable activation {field_name}",
            )
            _require_root(
                value,
                name=f"durable activation {field_name}",
                allow_zero=self.kind is EconomicInitialStateKindV1.GENESIS,
            )
        if type(self.component_commitments) is not tuple:
            raise TypeError("durable activation commitments must be an exact tuple")
        if any(
            type(item) is not DurableEconomicComponentCommitmentV1
            for item in self.component_commitments
        ):
            raise TypeError("durable activation has an invalid component commitment")
        if tuple(item.kind for item in self.component_commitments) != _COMPONENT_KINDS_V1:
            raise ValueError("durable activation component order is not canonical")
        if self.kind is EconomicInitialStateKindV1.GENESIS:
            if self.generation != 0:
                raise ValueError("durable genesis generation must be zero")
            if (
                self.source_activation_id,
                self.source_profile_root,
                self.source_state_root,
            ) != (ZERO_ROOT_V1, ZERO_ROOT_V1, ZERO_ROOT_V1):
                raise ValueError("durable genesis must not declare a source head")
            if self.source_writer_epoch != 0 or self.source_height != 0:
                raise ValueError("durable genesis source coordinates must be zero")
        else:
            if self.generation == 0:
                raise ValueError("durable migration generation must be positive")
            if self.source_writer_epoch == _U64_MAX_V1:
                raise ValueError("durable migration source writer epoch cannot advance")
            if self.writer_epoch != self.source_writer_epoch + 1:
                raise ValueError("durable migration must rotate writer epoch exactly once")
            if self.source_height == _U64_MAX_V1:
                raise ValueError("durable migration source height cannot advance")
            if self.height != self.source_height + 1:
                raise ValueError("durable migration must advance height exactly once")
        if self.activation_id != self.derived_activation_id:
            raise ValueError("durable activation id is not content-derived")

    @classmethod
    def build(
        cls,
        *,
        kind: EconomicInitialStateKindV1,
        generation: int,
        chain_id: str,
        deployment_root: str,
        profile_root: str,
        state_root: str,
        writer_epoch: int,
        height: int,
        source_activation_id: str,
        source_profile_root: str,
        source_state_root: str,
        source_writer_epoch: int,
        source_height: int,
        certificate_root: str,
        component_commitments: tuple[DurableEconomicComponentCommitmentV1, ...],
    ) -> DurableEconomicActivationRecordV1:
        values = {
            "kind": kind,
            "generation": generation,
            "chain_id": chain_id,
            "deployment_root": deployment_root,
            "profile_root": profile_root,
            "state_root": state_root,
            "writer_epoch": writer_epoch,
            "height": height,
            "source_activation_id": source_activation_id,
            "source_profile_root": source_profile_root,
            "source_state_root": source_state_root,
            "source_writer_epoch": source_writer_epoch,
            "source_height": source_height,
            "certificate_root": certificate_root,
            "component_commitments": component_commitments,
        }
        activation_id = hash_global_v1(
            "global-economic-durable-activation-record-v1",
            cls._canonical_body(**values),
        )
        return cls(activation_id=activation_id, **values)

    @staticmethod
    def _canonical_body(**values: object) -> dict[str, object]:
        return {
            "schema": DURABLE_ECONOMIC_ACTIVATION_SCHEMA_V1,
            "global_settlement_abi": GLOBAL_SETTLEMENT_ABI_V1,
            **values,
        }

    @property
    def derived_activation_id(self) -> str:
        return hash_global_v1(
            "global-economic-durable-activation-record-v1",
            self._canonical_body(
                kind=self.kind,
                generation=self.generation,
                chain_id=self.chain_id,
                deployment_root=self.deployment_root,
                profile_root=self.profile_root,
                state_root=self.state_root,
                writer_epoch=self.writer_epoch,
                height=self.height,
                source_activation_id=self.source_activation_id,
                source_profile_root=self.source_profile_root,
                source_state_root=self.source_state_root,
                source_writer_epoch=self.source_writer_epoch,
                source_height=self.source_height,
                certificate_root=self.certificate_root,
                component_commitments=self.component_commitments,
            ),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            **self._canonical_body(
                kind=self.kind,
                generation=self.generation,
                chain_id=self.chain_id,
                deployment_root=self.deployment_root,
                profile_root=self.profile_root,
                state_root=self.state_root,
                writer_epoch=self.writer_epoch,
                height=self.height,
                source_activation_id=self.source_activation_id,
                source_profile_root=self.source_profile_root,
                source_state_root=self.source_state_root,
                source_writer_epoch=self.source_writer_epoch,
                source_height=self.source_height,
                certificate_root=self.certificate_root,
                component_commitments=self.component_commitments,
            ),
            "activation_id": self.activation_id,
        }


@dataclass(frozen=True, slots=True)
class DurableEconomicHeadV1:
    activation_id: str
    kind: EconomicInitialStateKindV1
    generation: int
    chain_id: str
    deployment_root: str
    profile_root: str
    state_root: str
    writer_epoch: int
    height: int
    certificate_root: str

    def __post_init__(self) -> None:
        _require_exact_text_v1(self.activation_id, name="durable economic head id")
        _require_root(self.activation_id, name="durable economic head id")
        if type(self.kind) is not EconomicInitialStateKindV1:
            raise TypeError("durable economic head kind is not closed")
        for field_name in ("generation", "writer_epoch", "height"):
            _require_exact_u64_v1(
                getattr(self, field_name),
                name=f"durable economic head {field_name}",
            )
        _require_exact_text_v1(self.chain_id, name="durable economic head chain id")
        _require_token(self.chain_id, name="durable economic head chain id")
        for field_name in (
            "deployment_root",
            "profile_root",
            "state_root",
            "certificate_root",
        ):
            value = _require_exact_text_v1(
                getattr(self, field_name),
                name=f"durable economic head {field_name}",
            )
            _require_root(value, name=f"durable economic head {field_name}")

    @classmethod
    def from_record(
        cls,
        record: DurableEconomicActivationRecordV1,
    ) -> DurableEconomicHeadV1:
        if type(record) is not DurableEconomicActivationRecordV1:
            raise TypeError("durable economic head requires an exact activation record")
        return cls(
            activation_id=record.activation_id,
            kind=record.kind,
            generation=record.generation,
            chain_id=record.chain_id,
            deployment_root=record.deployment_root,
            profile_root=record.profile_root,
            state_root=record.state_root,
            writer_epoch=record.writer_epoch,
            height=record.height,
            certificate_root=record.certificate_root,
        )


@dataclass(frozen=True, slots=True)
class DurableEconomicInitialStateBundleV1:
    record: DurableEconomicActivationRecordV1
    components: tuple[DurableEconomicComponentV1, ...]

    def __post_init__(self) -> None:
        if type(self.record) is not DurableEconomicActivationRecordV1:
            raise TypeError("durable economic bundle record type is not closed")
        if type(self.components) is not tuple:
            raise TypeError("durable economic bundle components must be an exact tuple")
        if any(type(item) is not DurableEconomicComponentV1 for item in self.components):
            raise TypeError("durable economic bundle contains an invalid component")
        if tuple(item.kind for item in self.components) != _COMPONENT_KINDS_V1:
            raise ValueError("durable economic bundle component order is not canonical")
        commitments = tuple(item.commitment for item in self.components)
        if commitments != self.record.component_commitments:
            raise ValueError("durable economic bundle component commitment mismatch")
        _validate_bundle_body_bindings_v1(self)

    @property
    def head(self) -> DurableEconomicHeadV1:
        return DurableEconomicHeadV1.from_record(self.record)

    @property
    def canonical_bytes(self) -> bytes:
        record_bytes = canonical_global_bytes_v1(self.record)
        if len(record_bytes) > MAX_DURABLE_ECONOMIC_RECORD_BYTES_V1:
            raise ValueError("durable activation record exceeds its byte bound")
        encoded = bytearray(_BUNDLE_MAGIC_V1)
        encoded.extend(len(record_bytes).to_bytes(4, "big"))
        encoded.extend(record_bytes)
        for component in self.components:
            encoded.extend(len(component.payload).to_bytes(8, "big"))
            encoded.extend(component.payload)
        bundle_bytes = bytes(encoded)
        if len(bundle_bytes) > MAX_DURABLE_ECONOMIC_BUNDLE_BYTES_V1:
            raise ValueError("durable activation bundle exceeds its byte bound")
        return bundle_bytes


def _profile_payload_v1(owned: _OwnedEconomicInitialStateAdmissionV1) -> bytes:
    profile = owned.profile
    return canonical_global_bytes_v1(
        {
            "schema": DURABLE_ECONOMIC_ACTIVATION_SCHEMA_V1,
            "profile": profile,
            "lane_registry": profile.lane_registry,
            "lane_coordinator_registry": profile.lane_coordinator_registry,
            "route_registry": profile.route_registry,
        }
    )


def _resolve_source_coordinates_v1(
    owned: _OwnedEconomicInitialStateAdmissionV1,
    source_head: DurableEconomicHeadV1 | None,
) -> tuple[int, str]:
    certificate = owned.certificate
    if certificate.kind is EconomicInitialStateKindV1.GENESIS:
        if source_head is not None:
            raise ValueError("durable genesis must not receive a source head")
        return 0, ZERO_ROOT_V1
    if type(source_head) is not DurableEconomicHeadV1:
        raise TypeError("durable migration requires an exact source head")
    if source_head.generation == _U64_MAX_V1:
        raise ValueError("durable source generation cannot advance")
    source_bindings = (
        (source_head.chain_id, certificate.chain_id, "chain id"),
        (source_head.deployment_root, certificate.deployment_root, "deployment root"),
        (source_head.profile_root, certificate.source_profile_root, "profile root"),
        (source_head.state_root, certificate.source_state_root, "state root"),
        (source_head.writer_epoch, certificate.source_writer_epoch, "writer epoch"),
        (source_head.height, certificate.source_height, "height"),
    )
    for actual, expected, label in source_bindings:
        if actual != expected:
            raise ValueError(f"durable migration source {label} mismatch")
    return source_head.generation + 1, source_head.activation_id


def _activation_components_v1(
    owned: _OwnedEconomicInitialStateAdmissionV1,
) -> tuple[DurableEconomicComponentV1, ...]:
    values = (
        (DurableEconomicComponentKindV1.PROFILE, _profile_payload_v1(owned)),
        (
            DurableEconomicComponentKindV1.POLICY_REGISTRY,
            canonical_global_bytes_v1(owned.policy_registry),
        ),
        (
            DurableEconomicComponentKindV1.STATE,
            canonical_global_bytes_v1(owned.state),
        ),
        (
            DurableEconomicComponentKindV1.PREDECESSOR_STATE,
            canonical_global_bytes_v1(owned.predecessor_state),
        ),
        (
            DurableEconomicComponentKindV1.SOURCE_MANIFEST,
            canonical_global_bytes_v1(owned.source_manifest),
        ),
        (
            DurableEconomicComponentKindV1.CERTIFICATE,
            canonical_global_bytes_v1(owned.certificate),
        ),
        (DurableEconomicComponentKindV1.RECEIPT, owned.receipt_bytes),
    )
    return tuple(DurableEconomicComponentV1(kind, payload) for kind, payload in values)


def prepare_durable_economic_initial_state_bundle_v1(
    admission: EconomicInitialStateAdmissionV1,
    *,
    source_head: DurableEconomicHeadV1 | None,
) -> DurableEconomicInitialStateBundleV1:
    """Prepare one structurally validated complete activation bundle."""

    owned = _snapshot_economic_initial_state_admission_v1(admission)
    _validate_owned_economic_initial_state_admission_v1(owned)
    certificate = owned.certificate
    generation, source_activation_id = _resolve_source_coordinates_v1(
        owned,
        source_head,
    )
    components = _activation_components_v1(owned)
    record = DurableEconomicActivationRecordV1.build(
        kind=certificate.kind,
        generation=generation,
        chain_id=certificate.chain_id,
        deployment_root=certificate.deployment_root,
        profile_root=certificate.profile_root,
        state_root=certificate.state_root,
        writer_epoch=certificate.writer_epoch,
        height=certificate.height,
        source_activation_id=source_activation_id,
        source_profile_root=certificate.source_profile_root,
        source_state_root=certificate.source_state_root,
        source_writer_epoch=certificate.source_writer_epoch,
        source_height=certificate.source_height,
        certificate_root=certificate.certificate_root,
        component_commitments=tuple(item.commitment for item in components),
    )
    return DurableEconomicInitialStateBundleV1(record, components)


def _reject_json_constant_v1(value: str) -> object:
    raise ValueError(f"non-finite JSON constant is forbidden: {value}")


def _reject_duplicate_object_pairs_v1(
    pairs: list[tuple[str, object]],
) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if type(key) is not str:
            raise TypeError("durable activation JSON key must be exact str")
        if key in result:
            raise ValueError("durable activation JSON contains a duplicate key")
        result[key] = value
    return result


def _decode_exact_canonical_json_v1(payload: bytes, *, name: str) -> object:
    try:
        decoded_text = payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError(f"{name} is not UTF-8") from exc
    try:
        value = json.loads(
            decoded_text,
            object_pairs_hook=_reject_duplicate_object_pairs_v1,
            parse_constant=_reject_json_constant_v1,
        )
    except json.JSONDecodeError as exc:
        raise ValueError(f"{name} is not valid JSON") from exc
    if canonical_global_bytes_v1(value) != payload:
        raise ValueError(f"{name} encoding is not canonical")
    return value


def _exact_object_v1(
    value: object,
    *,
    name: str,
    fields: frozenset[str],
) -> dict[str, object]:
    if type(value) is not dict or set(value) != fields:
        raise ValueError(f"{name} field set is not closed")
    return value


def _exact_str_field_v1(value: dict[str, object], field: str, *, name: str) -> str:
    item = value[field]
    if type(item) is not str:
        raise TypeError(f"{name} {field} must be exact str")
    return item


def _exact_int_field_v1(value: dict[str, object], field: str, *, name: str) -> int:
    item = value[field]
    if type(item) is not int:
        raise TypeError(f"{name} {field} must be exact int")
    return item


_PROFILE_FIELDS_V1: Final = frozenset(
    {
        "schema",
        "authority_epoch",
        "lane_registry_root",
        "lane_coordinator_registry_root",
        "route_registry_root",
        "proof_shape_root",
        "root_image_id",
        "verifier_registry_root",
        "migration_registry_root",
        "policy_registry_root",
        "terminal_registry_root",
        "profile_id",
        "status",
    }
)
_STATE_FIELDS_V1: Final = frozenset(
    {
        "schema",
        "chain_id",
        "deployment_root",
        "writer_epoch",
        "height",
        "profile_root",
        "lane_roots",
        "balances",
        "supplies",
        "custody",
        "liabilities",
        "reserves",
        "oracle_occurrences",
        "replay_state",
        "terminal_obligations",
        "history_root",
        "outbox",
    }
)
_CERTIFICATE_FIELDS_V1: Final = frozenset(
    {
        "schema",
        "kind",
        "chain_id",
        "deployment_root",
        "profile_root",
        "writer_epoch",
        "height",
        "state_root",
        "source_profile_root",
        "source_state_root",
        "source_writer_epoch",
        "source_height",
        "state_atom_coverage_root",
        "lane_object_coverage_root",
        "replay_continuity_root",
        "terminal_continuity_root",
        "outbox_continuity_root",
        "source_manifest_root",
        "toolchain_manifest_root",
        "root_image_id",
        "receipt_root",
        "receipt_kind",
        "journal_bytes",
        "cycle_budget",
    }
)
_CERTIFICATE_JOURNAL_FIELDS_V1: Final = (
    "schema",
    "kind",
    "chain_id",
    "deployment_root",
    "profile_root",
    "writer_epoch",
    "height",
    "state_root",
    "source_profile_root",
    "source_state_root",
    "source_writer_epoch",
    "source_height",
    "state_atom_coverage_root",
    "lane_object_coverage_root",
    "replay_continuity_root",
    "terminal_continuity_root",
    "outbox_continuity_root",
    "source_manifest_root",
    "toolchain_manifest_root",
    "root_image_id",
)


def _component_payload_by_kind_v1(
    bundle: DurableEconomicInitialStateBundleV1,
    kind: DurableEconomicComponentKindV1,
) -> bytes:
    return bundle.components[_COMPONENT_KINDS_V1.index(kind)].payload


def _validate_profile_payload_v1(
    bundle: DurableEconomicInitialStateBundleV1,
) -> dict[str, object]:
    envelope = _exact_object_v1(
        _decode_exact_canonical_json_v1(
            _component_payload_by_kind_v1(
                bundle,
                DurableEconomicComponentKindV1.PROFILE,
            ),
            name="durable profile component",
        ),
        name="durable profile envelope",
        fields=frozenset(
            {
                "schema",
                "profile",
                "lane_registry",
                "lane_coordinator_registry",
                "route_registry",
            }
        ),
    )
    if envelope["schema"] != DURABLE_ECONOMIC_ACTIVATION_SCHEMA_V1:
        raise ValueError("durable profile envelope schema mismatch")
    profile = _exact_object_v1(
        envelope["profile"],
        name="durable profile",
        fields=_PROFILE_FIELDS_V1,
    )
    registry_bindings = (
        (
            "lane_registry_root",
            "global-lane-registry-v1",
            envelope["lane_registry"],
        ),
        (
            "lane_coordinator_registry_root",
            "global-lane-coordinator-registry-v1",
            envelope["lane_coordinator_registry"],
        ),
        (
            "route_registry_root",
            "global-route-registry-v1",
            envelope["route_registry"],
        ),
    )
    for field, domain, registry in registry_bindings:
        if _exact_str_field_v1(profile, field, name="durable profile") != hash_global_v1(
            domain,
            registry,
        ):
            raise ValueError(f"durable profile {field} content mismatch")
    profile_body = {
        field: profile[field]
        for field in _PROFILE_FIELDS_V1
        if field not in {"profile_id", "status"}
    }
    if _exact_str_field_v1(profile, "profile_id", name="durable profile") != hash_global_v1(
        "global-economic-profile-content-v1",
        profile_body,
    ):
        raise ValueError("durable profile id content mismatch")
    return profile


def _validate_policy_payload_v1(
    bundle: DurableEconomicInitialStateBundleV1,
    profile: dict[str, object],
) -> None:
    policy = _exact_object_v1(
        _decode_exact_canonical_json_v1(
            _component_payload_by_kind_v1(
                bundle,
                DurableEconomicComponentKindV1.POLICY_REGISTRY,
            ),
            name="durable policy component",
        ),
        name="durable policy registry",
        fields=frozenset({"schema", "bindings"}),
    )
    if _exact_str_field_v1(
        profile,
        "policy_registry_root",
        name="durable profile",
    ) != hash_global_v1("global-economic-policy-registry-v1", policy):
        raise ValueError("durable profile policy registry content mismatch")


def _validate_state_payload_v1(
    bundle: DurableEconomicInitialStateBundleV1,
    profile: dict[str, object],
) -> dict[str, object]:
    state = _exact_object_v1(
        _decode_exact_canonical_json_v1(
            _component_payload_by_kind_v1(bundle, DurableEconomicComponentKindV1.STATE),
            name="durable state component",
        ),
        name="durable state",
        fields=_STATE_FIELDS_V1,
    )
    record = bundle.record
    bindings = (
        (_exact_str_field_v1(state, "chain_id", name="durable state"), record.chain_id),
        (
            _exact_str_field_v1(state, "deployment_root", name="durable state"),
            record.deployment_root,
        ),
        (
            _exact_str_field_v1(state, "profile_root", name="durable state"),
            record.profile_root,
        ),
        (_exact_int_field_v1(state, "writer_epoch", name="durable state"), record.writer_epoch),
        (_exact_int_field_v1(state, "height", name="durable state"), record.height),
        (
            _exact_str_field_v1(profile, "profile_id", name="durable profile"),
            record.profile_root,
        ),
        (
            _exact_int_field_v1(profile, "authority_epoch", name="durable profile"),
            record.writer_epoch,
        ),
    )
    if any(actual != expected for actual, expected in bindings):
        raise ValueError("durable target profile or state binding mismatch")
    if hash_global_v1("global-economic-state-root-v1", state) != record.state_root:
        raise ValueError("durable target state root content mismatch")
    return state


def _validate_predecessor_payload_v1(
    bundle: DurableEconomicInitialStateBundleV1,
) -> None:
    payload = _component_payload_by_kind_v1(
        bundle,
        DurableEconomicComponentKindV1.PREDECESSOR_STATE,
    )
    record = bundle.record
    value = _decode_exact_canonical_json_v1(
        payload,
        name="durable predecessor component",
    )
    if record.kind is EconomicInitialStateKindV1.GENESIS:
        if value is not None:
            raise ValueError("durable genesis predecessor component must be null")
        return
    predecessor = _exact_object_v1(
        value,
        name="durable predecessor state",
        fields=_STATE_FIELDS_V1,
    )
    bindings = (
        (
            hash_global_v1("global-economic-state-root-v1", predecessor),
            record.source_state_root,
        ),
        (
            _exact_str_field_v1(predecessor, "chain_id", name="durable predecessor"),
            record.chain_id,
        ),
        (
            _exact_str_field_v1(
                predecessor,
                "deployment_root",
                name="durable predecessor",
            ),
            record.deployment_root,
        ),
        (
            _exact_str_field_v1(predecessor, "profile_root", name="durable predecessor"),
            record.source_profile_root,
        ),
        (
            _exact_int_field_v1(predecessor, "writer_epoch", name="durable predecessor"),
            record.source_writer_epoch,
        ),
        (
            _exact_int_field_v1(predecessor, "height", name="durable predecessor"),
            record.source_height,
        ),
    )
    if any(actual != expected for actual, expected in bindings):
        raise ValueError("durable predecessor state content mismatch")


def _validate_manifest_payload_v1(
    bundle: DurableEconomicInitialStateBundleV1,
) -> dict[str, object]:
    manifest = _exact_object_v1(
        _decode_exact_canonical_json_v1(
            _component_payload_by_kind_v1(
                bundle,
                DurableEconomicComponentKindV1.SOURCE_MANIFEST,
            ),
            name="durable source manifest component",
        ),
        name="durable source manifest",
        fields=frozenset({"schema", "kind", "rows"}),
    )
    if manifest["kind"] != bundle.record.kind.value:
        raise ValueError("durable source manifest kind mismatch")
    return manifest


def _validate_certificate_payload_v1(
    bundle: DurableEconomicInitialStateBundleV1,
    profile: dict[str, object],
    manifest: dict[str, object],
) -> None:
    certificate = _exact_object_v1(
        _decode_exact_canonical_json_v1(
            _component_payload_by_kind_v1(
                bundle,
                DurableEconomicComponentKindV1.CERTIFICATE,
            ),
            name="durable certificate component",
        ),
        name="durable certificate",
        fields=_CERTIFICATE_FIELDS_V1,
    )
    record = bundle.record
    bindings = (
        (certificate["kind"], record.kind.value),
        (_exact_str_field_v1(certificate, "chain_id", name="durable certificate"), record.chain_id),
        (
            _exact_str_field_v1(certificate, "deployment_root", name="durable certificate"),
            record.deployment_root,
        ),
        (_exact_str_field_v1(certificate, "profile_root", name="durable certificate"), record.profile_root),
        (_exact_str_field_v1(certificate, "state_root", name="durable certificate"), record.state_root),
        (_exact_int_field_v1(certificate, "writer_epoch", name="durable certificate"), record.writer_epoch),
        (_exact_int_field_v1(certificate, "height", name="durable certificate"), record.height),
        (
            _exact_str_field_v1(certificate, "source_profile_root", name="durable certificate"),
            record.source_profile_root,
        ),
        (
            _exact_str_field_v1(certificate, "source_state_root", name="durable certificate"),
            record.source_state_root,
        ),
        (
            _exact_int_field_v1(certificate, "source_writer_epoch", name="durable certificate"),
            record.source_writer_epoch,
        ),
        (
            _exact_int_field_v1(certificate, "source_height", name="durable certificate"),
            record.source_height,
        ),
        (
            _exact_str_field_v1(certificate, "root_image_id", name="durable certificate"),
            _exact_str_field_v1(profile, "root_image_id", name="durable profile"),
        ),
        (
            _exact_str_field_v1(
                certificate,
                "state_atom_coverage_root",
                name="durable certificate",
            ),
            hash_global_v1("economic-initial-state-atom-coverage-v1", manifest),
        ),
        (
            hash_global_v1("economic-initial-state-certificate-v1", certificate),
            record.certificate_root,
        ),
    )
    if any(actual != expected for actual, expected in bindings):
        raise ValueError("durable certificate content binding mismatch")
    receipt = _component_payload_by_kind_v1(
        bundle,
        DurableEconomicComponentKindV1.RECEIPT,
    )
    receipt_root = "0x" + hashlib.sha256(receipt).hexdigest()
    if _exact_str_field_v1(
        certificate,
        "receipt_root",
        name="durable certificate",
    ) != receipt_root:
        raise ValueError("durable certificate receipt content mismatch")
    if certificate["receipt_kind"] != "SUCCINCT":
        raise ValueError("durable certificate receipt kind mismatch")
    journal = {field: certificate[field] for field in _CERTIFICATE_JOURNAL_FIELDS_V1}
    if _exact_int_field_v1(
        certificate,
        "journal_bytes",
        name="durable certificate",
    ) != len(canonical_global_bytes_v1(journal)):
        raise ValueError("durable certificate journal byte count mismatch")


def _validate_bundle_body_bindings_v1(
    bundle: DurableEconomicInitialStateBundleV1,
) -> None:
    profile = _validate_profile_payload_v1(bundle)
    _validate_policy_payload_v1(bundle, profile)
    _validate_state_payload_v1(bundle, profile)
    _validate_predecessor_payload_v1(bundle)
    manifest = _validate_manifest_payload_v1(bundle)
    _validate_certificate_payload_v1(bundle, profile, manifest)


def _decode_record_v1(record_bytes: bytes) -> DurableEconomicActivationRecordV1:
    try:
        decoded_text = record_bytes.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError("durable activation record is not UTF-8") from exc
    try:
        value = json.loads(
            decoded_text,
            object_pairs_hook=_reject_duplicate_object_pairs_v1,
            parse_constant=_reject_json_constant_v1,
        )
    except json.JSONDecodeError as exc:
        raise ValueError("durable activation record is not valid JSON") from exc
    if type(value) is not dict:
        raise TypeError("durable activation record must decode to an object")
    expected_fields = {
        "schema",
        "global_settlement_abi",
        "activation_id",
        "kind",
        "generation",
        "chain_id",
        "deployment_root",
        "profile_root",
        "state_root",
        "writer_epoch",
        "height",
        "source_activation_id",
        "source_profile_root",
        "source_state_root",
        "source_writer_epoch",
        "source_height",
        "certificate_root",
        "component_commitments",
    }
    if set(value) != expected_fields:
        raise ValueError("durable activation record field set is not closed")
    if value["schema"] != DURABLE_ECONOMIC_ACTIVATION_SCHEMA_V1:
        raise ValueError("durable activation record schema mismatch")
    if value["global_settlement_abi"] != GLOBAL_SETTLEMENT_ABI_V1:
        raise ValueError("durable activation global ABI mismatch")
    commitments = _decode_component_commitments_v1(value["component_commitments"])
    try:
        record_kind = EconomicInitialStateKindV1(value["kind"])
    except (TypeError, ValueError) as exc:
        raise ValueError("durable activation record kind is unknown") from exc
    record = DurableEconomicActivationRecordV1(
        activation_id=value["activation_id"],
        kind=record_kind,
        generation=value["generation"],
        chain_id=value["chain_id"],
        deployment_root=value["deployment_root"],
        profile_root=value["profile_root"],
        state_root=value["state_root"],
        writer_epoch=value["writer_epoch"],
        height=value["height"],
        source_activation_id=value["source_activation_id"],
        source_profile_root=value["source_profile_root"],
        source_state_root=value["source_state_root"],
        source_writer_epoch=value["source_writer_epoch"],
        source_height=value["source_height"],
        certificate_root=value["certificate_root"],
        component_commitments=commitments,
    )
    if canonical_global_bytes_v1(record) != record_bytes:
        raise ValueError("durable activation record encoding is not canonical")
    return record


def _decode_component_commitments_v1(
    raw_commitments: object,
) -> tuple[DurableEconomicComponentCommitmentV1, ...]:
    if type(raw_commitments) is not list:
        raise TypeError("durable activation commitments must decode to a list")
    commitments: list[DurableEconomicComponentCommitmentV1] = []
    for raw in raw_commitments:
        if type(raw) is not dict or set(raw) != {"kind", "byte_count", "root"}:
            raise ValueError("durable activation component commitment is malformed")
        try:
            kind = DurableEconomicComponentKindV1(raw["kind"])
        except (TypeError, ValueError) as exc:
            raise ValueError("durable activation component kind is unknown") from exc
        commitments.append(
            DurableEconomicComponentCommitmentV1(
                kind=kind,
                byte_count=raw["byte_count"],
                root=raw["root"],
            )
        )
    return tuple(commitments)


def decode_durable_economic_initial_state_bundle_v1(
    bundle_bytes: bytes,
) -> DurableEconomicInitialStateBundleV1:
    """Decode one exact canonical durable bundle and reject all extra bytes."""

    if type(bundle_bytes) is not bytes:
        raise TypeError("durable activation bundle must be exact bytes")
    if len(bundle_bytes) > MAX_DURABLE_ECONOMIC_BUNDLE_BYTES_V1:
        raise ValueError("durable activation bundle exceeds its byte bound")
    if not bundle_bytes.startswith(_BUNDLE_MAGIC_V1):
        raise ValueError("durable activation bundle magic mismatch")
    cursor = len(_BUNDLE_MAGIC_V1)
    if len(bundle_bytes) < cursor + 4:
        raise ValueError("durable activation bundle is truncated before its record")
    record_size = int.from_bytes(bundle_bytes[cursor : cursor + 4], "big")
    cursor += 4
    if not 1 <= record_size <= MAX_DURABLE_ECONOMIC_RECORD_BYTES_V1:
        raise ValueError("durable activation record is outside the byte bound")
    record_end = cursor + record_size
    if record_end > len(bundle_bytes):
        raise ValueError("durable activation bundle record is truncated")
    record = _decode_record_v1(bundle_bytes[cursor:record_end])
    cursor = record_end
    components: list[DurableEconomicComponentV1] = []
    for kind in _COMPONENT_KINDS_V1:
        if len(bundle_bytes) < cursor + 8:
            raise ValueError("durable activation bundle is truncated before a component")
        component_size = int.from_bytes(bundle_bytes[cursor : cursor + 8], "big")
        cursor += 8
        if not 1 <= component_size <= MAX_DURABLE_ECONOMIC_COMPONENT_BYTES_V1:
            raise ValueError("durable activation component is outside the byte bound")
        component_end = cursor + component_size
        if component_end > len(bundle_bytes):
            raise ValueError("durable activation bundle component is truncated")
        components.append(
            DurableEconomicComponentV1(kind, bundle_bytes[cursor:component_end])
        )
        cursor = component_end
    if cursor != len(bundle_bytes):
        raise ValueError("durable activation bundle has trailing bytes")
    bundle = DurableEconomicInitialStateBundleV1(record, tuple(components))
    if bundle.canonical_bytes != bundle_bytes:
        raise ValueError("durable activation bundle encoding is not canonical")
    return bundle


__all__ = [
    "DURABLE_ECONOMIC_ACTIVATION_SCHEMA_V1",
    "MAX_DURABLE_ECONOMIC_BUNDLE_BYTES_V1",
    "MAX_DURABLE_ECONOMIC_COMPONENT_BYTES_V1",
    "DurableEconomicActivationRecordV1",
    "DurableEconomicComponentCommitmentV1",
    "DurableEconomicComponentKindV1",
    "DurableEconomicComponentV1",
    "DurableEconomicHeadV1",
    "DurableEconomicInitialStateBundleV1",
    "decode_durable_economic_initial_state_bundle_v1",
    "prepare_durable_economic_initial_state_bundle_v1",
]

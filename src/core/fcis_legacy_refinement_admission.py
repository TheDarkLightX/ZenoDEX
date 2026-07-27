"""Strict bytes-to-owned admission for unmounted M5-P4B0 evidence."""

from __future__ import annotations

import json
from enum import Enum
from typing import NoReturn, cast

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.owned_collections import OwnedMapV1
from ..state.owned_json import JsonProjectionV1, JsonSourceValueV1
from ..state.snapshot_combinators import (
    AdmitCode,
    AdmitOk,
    AdmitReject,
    ValidatedAdmissionLimitsV1,
    _admit_with_registry_v1,
    build_admission_limits_v1,
    build_admission_registry_v1,
)
from .fcis_legacy_refinement_policy import (
    is_known_command_kind_v1,
    lookup_version_delta_v1,
)
from .fcis_legacy_refinement_schema import (
    MAX_REFINEMENT_BYTES_V1,
    MAX_REFINEMENT_DEPTH_V1,
    OBSERVATION_PAIR_SCHEMA_ID_V1,
    REFINEMENT_ADMISSION_LIMITS_RAW_V1,
    REFINEMENT_SCHEMA_REGISTRATIONS_V1,
    REFINEMENT_SCHEMA_REVISION_V1,
    RefinementEnumTagV1,
    RefinementRecordTagV1,
)
from .fcis_legacy_refinement_values import (
    BoundObservationV1,
    CanonicalBytesFieldV1,
    CanonicalDigestFieldV1,
    CanonicalIdentitiesFieldV1,
    CanonicalParseCodeV1,
    CanonicalParseRejectV1,
    EvidenceFieldStatusV1,
    InputBindingV1,
    InvalidEvidenceV1,
    ObservationPairV1,
    ObservationResultKindV1,
    ObservationValueV1,
    OutboxIdentityValueV1,
    RejectionValueV1,
)
from .fcis_step_evaluation_values import FCISFeeAllocationV1

REQUIRED_ANCESTOR_V1 = "09bd121f3c0194f0bead2eb8b1230657b74e2ae6"
PACKET_COMMIT_V1 = "c19b98db55ea4170204a98372be27335a9fa4284"
PACKET_TREE_HASH_V1 = "60eecabb7928b07483abe3f4a8e2a454044895ec"
BASELINE_ARTIFACT_HASH_V1 = "0xf64a101969e46c55db8421e5d3dc2accb082d13631e7336b315779e20d30636d"
DIFFERENTIAL_ARTIFACT_HASH_V1 = "0x11473d470a81046caac39b8c45449c303ba5d100a031a2650d35bf9d0b8b3910"
_UNAVAILABLE_LITERAL_V1 = "UNAVAILABLE_IN_LEGACY_V1"


class _CanonicalJsonSignal(Exception):
    def __init__(self, code: CanonicalParseCodeV1) -> None:
        super().__init__(code.value)
        self.code = code


class _DomainConstructionError(Exception):
    def __init__(self, code: str, path: tuple[str | int, ...]) -> None:
        super().__init__(code)
        self.code = code
        self.path = path


def _reject_duplicate_keys(
    pairs: list[tuple[str, JsonSourceValueV1]],
) -> dict[str, JsonSourceValueV1]:
    result: dict[str, JsonSourceValueV1] = {}
    for key, value in pairs:
        if key in result:
            raise _CanonicalJsonSignal(CanonicalParseCodeV1.DUPLICATE_KEY)
        result[key] = value
    return result


def _reject_float(_value: str) -> NoReturn:
    raise _CanonicalJsonSignal(CanonicalParseCodeV1.FLOAT_FORBIDDEN)


def _reject_nonfinite(_value: str) -> NoReturn:
    raise _CanonicalJsonSignal(CanonicalParseCodeV1.NONFINITE_FORBIDDEN)


def _json_depth_exceeds_limit(raw: bytes) -> bool:
    depth = 0
    in_string = False
    escaped = False
    for byte in raw:
        if in_string:
            if escaped:
                escaped = False
            elif byte == ord("\\"):
                escaped = True
            elif byte == ord('"'):
                in_string = False
            continue
        if byte == ord('"'):
            in_string = True
        elif byte in (ord("{"), ord("[")):
            depth += 1
            if depth > MAX_REFINEMENT_DEPTH_V1:
                return True
        elif byte in (ord("}"), ord("]")):
            depth -= 1
    return False


def decode_canonical_json_bytes_v1(
    raw: bytes,
) -> JsonSourceValueV1 | CanonicalParseRejectV1:
    """Decode one bounded canonical JSON value with complete consumption."""

    if type(raw) is not bytes:
        return CanonicalParseRejectV1(CanonicalParseCodeV1.WRONG_EXACT_TYPE)
    if not raw:
        return CanonicalParseRejectV1(CanonicalParseCodeV1.EMPTY_INPUT)
    if len(raw) > MAX_REFINEMENT_BYTES_V1:
        return CanonicalParseRejectV1(CanonicalParseCodeV1.BYTE_LIMIT)
    if raw.startswith(b"\xef\xbb\xbf"):
        return CanonicalParseRejectV1(CanonicalParseCodeV1.BOM)
    if _json_depth_exceeds_limit(raw):
        return CanonicalParseRejectV1(CanonicalParseCodeV1.DEPTH_LIMIT)
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError:
        return CanonicalParseRejectV1(CanonicalParseCodeV1.INVALID_UTF8)
    try:
        decoded = cast(
            JsonSourceValueV1,
            json.loads(
                text,
                object_pairs_hook=_reject_duplicate_keys,
                parse_float=_reject_float,
                parse_constant=_reject_nonfinite,
            ),
        )
    except _CanonicalJsonSignal as signal:
        return CanonicalParseRejectV1(signal.code)
    except (json.JSONDecodeError, RecursionError, ValueError):
        return CanonicalParseRejectV1(CanonicalParseCodeV1.INVALID_JSON)
    try:
        reencoded = canonical_json_bytes(decoded)
    except (TypeError, UnicodeEncodeError):
        return CanonicalParseRejectV1(CanonicalParseCodeV1.INVALID_UTF8)
    if reencoded != raw:
        return CanonicalParseRejectV1(CanonicalParseCodeV1.NONCANONICAL_JSON)
    return decoded


def _no_record_construction(
    _tag: Enum,
    _values: tuple[tuple[str, object], ...],
) -> object:
    raise TypeError("P4B0 evidence schemas contain no record constructors")


def _project_admitted(value: object) -> JsonProjectionV1:
    if value is None or type(value) in (bool, int, str):
        return cast(None | bool | int | str, value)
    if type(value) is tuple:
        admitted_tuple = cast(tuple[object, ...], value)
        return [_project_admitted(item) for item in admitted_tuple]
    if type(value) is OwnedMapV1:
        admitted_map = cast(OwnedMapV1[str, object], value)
        return {key: _project_admitted(item) for key, item in admitted_map.entries}
    raise TypeError("P4B0 admitted value has an unsupported exact type")


def _encode_admitted(_schema_id: str, value: object) -> bytes:
    return canonical_json_bytes(_project_admitted(value))


_LIMITS_RESULT_V1 = build_admission_limits_v1(REFINEMENT_ADMISSION_LIMITS_RAW_V1)
if type(_LIMITS_RESULT_V1) is not ValidatedAdmissionLimitsV1:
    raise RuntimeError("P4B0 admission limits are invalid")
REFINEMENT_ADMISSION_LIMITS_V1 = _LIMITS_RESULT_V1

_REGISTRY_V1 = build_admission_registry_v1(
    schema_revision=REFINEMENT_SCHEMA_REVISION_V1,
    enum_tag_type=RefinementEnumTagV1,
    record_tag_type=RefinementRecordTagV1,
    enum_registrations=(),
    record_registrations=(),
    schema_registrations=REFINEMENT_SCHEMA_REGISTRATIONS_V1,
)


def _admit_pair_source(source: JsonSourceValueV1) -> AdmitOk[object] | AdmitReject:
    return _admit_with_registry_v1(
        _REGISTRY_V1,
        REFINEMENT_SCHEMA_REVISION_V1,
        OBSERVATION_PAIR_SCHEMA_ID_V1,
        REFINEMENT_ADMISSION_LIMITS_V1,
        source,
        _no_record_construction,
        _encode_admitted,
    )


def _owned_map(
    value: object, schema_id: str, path: tuple[str | int, ...]
) -> OwnedMapV1[str, object]:
    if type(value) is not OwnedMapV1:
        raise _DomainConstructionError("owned_map_expected", path)
    result = cast(OwnedMapV1[str, object], value)
    if result.schema_id != schema_id:
        raise _DomainConstructionError("owned_map_schema_mismatch", path)
    return result


def _field(value: OwnedMapV1[str, object], name: str) -> object:
    try:
        return value[name]
    except KeyError as exc:
        raise _DomainConstructionError("admitted_field_missing", (name,)) from exc


def _string(value: object, path: tuple[str | int, ...]) -> str:
    if type(value) is not str:
        raise _DomainConstructionError("admitted_string_expected", path)
    return value


def _integer(value: object, path: tuple[str | int, ...]) -> int:
    if type(value) is not int:
        raise _DomainConstructionError("admitted_int_expected", path)
    return value


def _optional_string(value: object, path: tuple[str | int, ...]) -> str | None:
    if value is None:
        return None
    return _string(value, path)


def _optional_integer(value: object, path: tuple[str | int, ...]) -> int | None:
    if value is None:
        return None
    return _integer(value, path)


def _string_tuple(value: object, path: tuple[str | int, ...]) -> tuple[str, ...]:
    if type(value) is not tuple or any(type(item) is not str for item in value):
        raise _DomainConstructionError("admitted_string_tuple_expected", path)
    return cast(tuple[str, ...], value)


def _decode_hex(value: str, path: tuple[str | int, ...]) -> bytes:
    try:
        decoded = bytes.fromhex(value)
    except ValueError as exc:
        raise _DomainConstructionError("admitted_hex_invalid", path) from exc
    if not decoded:
        raise _DomainConstructionError("admitted_hex_empty", path)
    return decoded


def _optional_hex(value: object, path: tuple[str | int, ...]) -> bytes | None:
    text = _optional_string(value, path)
    return None if text is None else _decode_hex(text, path)


def _legacy_status(value: object, path: tuple[str | int, ...]) -> EvidenceFieldStatusV1:
    if value is None:
        return EvidenceFieldStatusV1.ABSENT
    marker = _owned_map(value, "zenodex/fcis-m5-p4b0/unavailable/v1", path)
    if _string(_field(marker, "status"), path + ("status",)) != _UNAVAILABLE_LITERAL_V1:
        raise _DomainConstructionError("unavailable_marker_mismatch", path)
    return EvidenceFieldStatusV1.UNAVAILABLE


def _legacy_bytes_field(value: object, path: tuple[str | int, ...]) -> CanonicalBytesFieldV1:
    return CanonicalBytesFieldV1(_legacy_status(value, path), None)


def _legacy_digest_field(value: object, path: tuple[str | int, ...]) -> CanonicalDigestFieldV1:
    return CanonicalDigestFieldV1(_legacy_status(value, path), None)


def _legacy_identities_field(
    value: object,
    path: tuple[str | int, ...],
) -> CanonicalIdentitiesFieldV1:
    return CanonicalIdentitiesFieldV1(_legacy_status(value, path), None)


def _exact_bytes_field(value: object, path: tuple[str | int, ...]) -> CanonicalBytesFieldV1:
    if value is None:
        return CanonicalBytesFieldV1(EvidenceFieldStatusV1.ABSENT, None)
    return CanonicalBytesFieldV1(
        EvidenceFieldStatusV1.PRESENT,
        _decode_hex(_string(value, path), path),
    )


def _exact_digest_field(value: object, path: tuple[str | int, ...]) -> CanonicalDigestFieldV1:
    if value is None:
        return CanonicalDigestFieldV1(EvidenceFieldStatusV1.ABSENT, None)
    return CanonicalDigestFieldV1(EvidenceFieldStatusV1.PRESENT, _string(value, path))


def _exact_identities_field(
    value: object,
    path: tuple[str | int, ...],
) -> CanonicalIdentitiesFieldV1:
    if value is None:
        return CanonicalIdentitiesFieldV1(EvidenceFieldStatusV1.ABSENT, None)
    if type(value) is not tuple:
        raise _DomainConstructionError("admitted_identity_tuple_expected", path)
    identities = tuple(
        _build_outbox_identity(identity, path + (index,))
        for index, identity in enumerate(cast(tuple[object, ...], value))
    )
    return CanonicalIdentitiesFieldV1(
        EvidenceFieldStatusV1.PRESENT,
        identities,
    )


def _build_outbox_identity(
    value: object,
    path: tuple[str | int, ...],
) -> OutboxIdentityValueV1:
    admitted = _owned_map(value, "zenodex/fcis-m5-p4b0/outbox-identity/v1", path)
    return OutboxIdentityValueV1(
        effect_identity=_string(
            _field(admitted, "effect_identity"),
            path + ("effect_identity",),
        ),
        effect_index=_integer(
            _field(admitted, "effect_index"),
            path + ("effect_index",),
        ),
        idempotency_key=_string(
            _field(admitted, "idempotency_key"),
            path + ("idempotency_key",),
        ),
    )


def _build_rejection(value: object, path: tuple[str | int, ...]) -> RejectionValueV1 | None:
    if value is None:
        return None
    admitted = _owned_map(value, "zenodex/fcis-m5-p4b0/rejection/v1", path)
    return RejectionValueV1(
        code=_string(_field(admitted, "code"), path + ("code",)),
        path=_string_tuple(_field(admitted, "path"), path + ("path",)),
        precedence=_string(_field(admitted, "precedence"), path + ("precedence",)),
        public_reason=_string(_field(admitted, "public_reason"), path + ("public_reason",)),
        unavailable_fields=_string_tuple(
            _field(admitted, "unavailable_fields"),
            path + ("unavailable_fields",),
        ),
    )


def _build_fee_allocation(
    value: object,
    path: tuple[str | int, ...],
) -> FCISFeeAllocationV1 | None:
    if value is None:
        return None
    admitted = _owned_map(value, "zenodex/fcis-m5-p4b0/fee-allocation/v1", path)
    return FCISFeeAllocationV1(
        buyback_amount=_integer(_field(admitted, "buyback_amount"), path + ("buyback_amount",)),
        treasury_amount=_integer(
            _field(admitted, "treasury_amount"),
            path + ("treasury_amount",),
        ),
        rewards_amount=_integer(_field(admitted, "rewards_amount"), path + ("rewards_amount",)),
        dust_carried=_integer(_field(admitted, "dust_carried"), path + ("dust_carried",)),
    )


def _result_kind(value: object, path: tuple[str | int, ...]) -> ObservationResultKindV1:
    text = _string(value, path)
    if text == ObservationResultKindV1.ACCEPT.value:
        return ObservationResultKindV1.ACCEPT
    if text == ObservationResultKindV1.REJECT.value:
        return ObservationResultKindV1.REJECT
    raise _DomainConstructionError("unknown_result_kind", path)


def _build_input_binding(value: object, path: tuple[str | int, ...]) -> InputBindingV1:
    admitted = _owned_map(value, "zenodex/fcis-m5-p4b0/input-binding/v1", path)
    command_hex = _string_tuple(_field(admitted, "command_bytes"), path + ("command_bytes",))
    command_bytes = tuple(
        _decode_hex(item, path + ("command_bytes", index)) for index, item in enumerate(command_hex)
    )
    binding = InputBindingV1(
        baseline_artifact_hash=_string(
            _field(admitted, "baseline_artifact_hash"),
            path + ("baseline_artifact_hash",),
        ),
        differential_artifact_hash=_string(
            _field(admitted, "differential_artifact_hash"),
            path + ("differential_artifact_hash",),
        ),
        reviewed_start_sha=_string(
            _field(admitted, "reviewed_start_sha"),
            path + ("reviewed_start_sha",),
        ),
        packet_commit=_string(_field(admitted, "packet_commit"), path + ("packet_commit",)),
        packet_tree_hash=_string(
            _field(admitted, "packet_tree_hash"),
            path + ("packet_tree_hash",),
        ),
        fixture_id=_string(_field(admitted, "fixture_id"), path + ("fixture_id",)),
        command_kind=_string(_field(admitted, "command_kind"), path + ("command_kind",)),
        command_bytes=command_bytes,
        command_hash=_string(_field(admitted, "command_hash"), path + ("command_hash",)),
        pre_state_bytes=_decode_hex(
            _string(_field(admitted, "pre_state_bytes"), path + ("pre_state_bytes",)),
            path + ("pre_state_bytes",),
        ),
        pre_state_root=_string(_field(admitted, "pre_state_root"), path + ("pre_state_root",)),
        context_bytes=_decode_hex(
            _string(_field(admitted, "context_bytes"), path + ("context_bytes",)),
            path + ("context_bytes",),
        ),
        context_hash=_string(_field(admitted, "context_hash"), path + ("context_hash",)),
    )
    expected_provenance = (
        BASELINE_ARTIFACT_HASH_V1,
        DIFFERENTIAL_ARTIFACT_HASH_V1,
        REQUIRED_ANCESTOR_V1,
        PACKET_COMMIT_V1,
        PACKET_TREE_HASH_V1,
    )
    observed_provenance = (
        binding.baseline_artifact_hash,
        binding.differential_artifact_hash,
        binding.reviewed_start_sha,
        binding.packet_commit,
        binding.packet_tree_hash,
    )
    if observed_provenance != expected_provenance:
        raise _DomainConstructionError("source_provenance_mismatch", path)
    if not is_known_command_kind_v1(binding.command_kind):
        raise _DomainConstructionError("unknown_command_kind", path + ("command_kind",))
    if sha256_hex(b"".join(binding.command_bytes)) != binding.command_hash:
        raise _DomainConstructionError("command_hash_mismatch", path + ("command_hash",))
    expected_context_hash = sha256_hex(
        domain_sep_bytes("fcis_p4a_execution_context", version=1) + binding.context_bytes
    )
    if expected_context_hash != binding.context_hash:
        raise _DomainConstructionError("context_hash_mismatch", path + ("context_hash",))
    return binding


def _common_observation(
    admitted: OwnedMapV1[str, object],
    path: tuple[str | int, ...],
    *,
    bundle_bytes: CanonicalBytesFieldV1,
    bundle_root: CanonicalDigestFieldV1,
    commit_plan_bytes: CanonicalBytesFieldV1,
    effects_bytes: CanonicalBytesFieldV1,
    outbox_bytes: CanonicalBytesFieldV1,
    outbox_identities: CanonicalIdentitiesFieldV1,
    patch_bytes: CanonicalBytesFieldV1,
    receipt_bytes: CanonicalBytesFieldV1,
    receipt_root: CanonicalDigestFieldV1,
    replay_bytes: CanonicalBytesFieldV1,
) -> ObservationValueV1:
    return ObservationValueV1(
        algorithm_id=_string(_field(admitted, "algorithm_id"), path + ("algorithm_id",)),
        algorithm_version=_integer(
            _field(admitted, "algorithm_version"),
            path + ("algorithm_version",),
        ),
        codec_version=_integer(_field(admitted, "codec_version"), path + ("codec_version",)),
        schema_version=_integer(_field(admitted, "schema_version"), path + ("schema_version",)),
        snapshot_version=_optional_integer(
            _field(admitted, "snapshot_version"),
            path + ("snapshot_version",),
        ),
        support_root_version=_optional_integer(
            _field(admitted, "support_root_version"),
            path + ("support_root_version",),
        ),
        result_kind=_result_kind(_field(admitted, "result_kind"), path + ("result_kind",)),
        rejection=_build_rejection(_field(admitted, "rejection"), path + ("rejection",)),
        next_state_snapshot_bytes=_optional_hex(
            _field(admitted, "next_state_snapshot_bytes"),
            path + ("next_state_snapshot_bytes",),
        ),
        next_state_snapshot_root=_optional_string(
            _field(admitted, "next_state_snapshot_root"),
            path + ("next_state_snapshot_root",),
        ),
        next_nonce_table_hash=_optional_string(
            _field(admitted, "next_nonce_table_hash"),
            path + ("next_nonce_table_hash",),
        ),
        settlement_bytes=_optional_hex(
            _field(admitted, "settlement_bytes"),
            path + ("settlement_bytes",),
        ),
        support_root=_optional_string(_field(admitted, "support_root"), path + ("support_root",)),
        total_swap_fees=_optional_integer(
            _field(admitted, "total_swap_fees"),
            path + ("total_swap_fees",),
        ),
        fee_allocation=_build_fee_allocation(
            _field(admitted, "fee_allocation"),
            path + ("fee_allocation",),
        ),
        bundle_bytes=bundle_bytes,
        bundle_root=bundle_root,
        commit_plan_bytes=commit_plan_bytes,
        effects_bytes=effects_bytes,
        outbox_bytes=outbox_bytes,
        outbox_identities=outbox_identities,
        patch_bytes=patch_bytes,
        receipt_bytes=receipt_bytes,
        receipt_root=receipt_root,
        replay_bytes=replay_bytes,
    )


def _build_legacy_observation(value: object, path: tuple[str | int, ...]) -> ObservationValueV1:
    admitted = _owned_map(value, "zenodex/fcis-m5-p4b0/legacy-observation/v1", path)
    return _common_observation(
        admitted,
        path,
        bundle_bytes=_legacy_bytes_field(
            _field(admitted, "bundle_bytes"), path + ("bundle_bytes",)
        ),
        bundle_root=_legacy_digest_field(_field(admitted, "bundle_root"), path + ("bundle_root",)),
        commit_plan_bytes=_legacy_bytes_field(
            _field(admitted, "commit_plan_bytes"),
            path + ("commit_plan_bytes",),
        ),
        effects_bytes=_legacy_bytes_field(
            _field(admitted, "effects_bytes"), path + ("effects_bytes",)
        ),
        outbox_bytes=_legacy_bytes_field(
            _field(admitted, "outbox_bytes"), path + ("outbox_bytes",)
        ),
        outbox_identities=_legacy_identities_field(
            _field(admitted, "outbox_identities"),
            path + ("outbox_identities",),
        ),
        patch_bytes=_legacy_bytes_field(_field(admitted, "patch_bytes"), path + ("patch_bytes",)),
        receipt_bytes=_legacy_bytes_field(
            _field(admitted, "receipt_bytes"),
            path + ("receipt_bytes",),
        ),
        receipt_root=_legacy_digest_field(
            _field(admitted, "receipt_root"), path + ("receipt_root",)
        ),
        replay_bytes=_legacy_bytes_field(
            _field(admitted, "replay_bytes"), path + ("replay_bytes",)
        ),
    )


def _build_exact_observation(value: object, path: tuple[str | int, ...]) -> ObservationValueV1:
    admitted = _owned_map(value, "zenodex/fcis-m5-p4b0/exact-observation/v1", path)
    return _common_observation(
        admitted,
        path,
        bundle_bytes=_exact_bytes_field(_field(admitted, "bundle_bytes"), path + ("bundle_bytes",)),
        bundle_root=_exact_digest_field(_field(admitted, "bundle_root"), path + ("bundle_root",)),
        commit_plan_bytes=_exact_bytes_field(
            _field(admitted, "commit_plan_bytes"),
            path + ("commit_plan_bytes",),
        ),
        effects_bytes=_exact_bytes_field(
            _field(admitted, "effects_bytes"), path + ("effects_bytes",)
        ),
        outbox_bytes=_exact_bytes_field(_field(admitted, "outbox_bytes"), path + ("outbox_bytes",)),
        outbox_identities=_exact_identities_field(
            _field(admitted, "outbox_identities"),
            path + ("outbox_identities",),
        ),
        patch_bytes=_exact_bytes_field(_field(admitted, "patch_bytes"), path + ("patch_bytes",)),
        receipt_bytes=_exact_bytes_field(
            _field(admitted, "receipt_bytes"), path + ("receipt_bytes",)
        ),
        receipt_root=_exact_digest_field(
            _field(admitted, "receipt_root"), path + ("receipt_root",)
        ),
        replay_bytes=_exact_bytes_field(_field(admitted, "replay_bytes"), path + ("replay_bytes",)),
    )


def _build_bound_observation(
    value: object,
    *,
    exact: bool,
    path: tuple[str | int, ...],
) -> BoundObservationV1:
    schema_id = (
        "zenodex/fcis-m5-p4b0/exact-bound/v1" if exact else "zenodex/fcis-m5-p4b0/legacy-bound/v1"
    )
    admitted = _owned_map(value, schema_id, path)
    observation_source = _field(admitted, "observation")
    observation = (
        _build_exact_observation(observation_source, path + ("observation",))
        if exact
        else _build_legacy_observation(observation_source, path + ("observation",))
    )
    return BoundObservationV1(
        binding=_build_input_binding(_field(admitted, "binding"), path + ("binding",)),
        observation=observation,
    )


def _scalar_version(value: str | int | None) -> str:
    if value is None:
        return "none"
    if type(value) is int:
        return str(value)
    return cast(str, value)


def _validate_pair_semantics(pair: ObservationPairV1) -> None:
    legacy_binding = pair.legacy.binding
    exact_binding = pair.exact.binding
    binding_fields = (
        "baseline_artifact_hash",
        "differential_artifact_hash",
        "reviewed_start_sha",
        "packet_commit",
        "packet_tree_hash",
        "fixture_id",
        "command_kind",
        "command_bytes",
        "command_hash",
        "pre_state_bytes",
        "pre_state_root",
        "context_bytes",
        "context_hash",
    )
    for field_name in binding_fields:
        if getattr(legacy_binding, field_name) != getattr(exact_binding, field_name):
            raise _DomainConstructionError("same_input_mismatch", (field_name,))

    legacy = pair.legacy.observation
    exact = pair.exact.observation
    result_kind = legacy.result_kind
    version_fields = (
        ("algorithm_id", legacy.algorithm_id, exact.algorithm_id),
        ("algorithm_version", legacy.algorithm_version, exact.algorithm_version),
        ("codec_version", legacy.codec_version, exact.codec_version),
        ("schema_version", legacy.schema_version, exact.schema_version),
        ("snapshot_version", legacy.snapshot_version, exact.snapshot_version),
        ("support_root_version", legacy.support_root_version, exact.support_root_version),
    )
    for field_name, legacy_value, exact_value in version_fields:
        if (
            lookup_version_delta_v1(
                field_name,
                _scalar_version(legacy_value),
                _scalar_version(exact_value),
                result_kind,
            )
            is None
        ):
            raise _DomainConstructionError("unknown_version_delta", (field_name,))


def _build_pair(admitted: object, raw: bytes) -> ObservationPairV1:
    pair_map = _owned_map(admitted, OBSERVATION_PAIR_SCHEMA_ID_V1, ())
    pair = ObservationPairV1(
        legacy=_build_bound_observation(_field(pair_map, "legacy"), exact=False, path=("legacy",)),
        exact=_build_bound_observation(_field(pair_map, "exact"), exact=True, path=("exact",)),
        canonical_source_bytes=raw,
        canonical_source_hash=sha256_hex(raw),
    )
    _validate_pair_semantics(pair)
    return pair


def admit_observation_pair_bytes_v1(raw: bytes) -> ObservationPairV1 | InvalidEvidenceV1:
    """Admit one source-bound pair from exact canonical bytes."""

    decoded = decode_canonical_json_bytes_v1(raw)
    if type(decoded) is CanonicalParseRejectV1:
        return InvalidEvidenceV1(f"parse_{decoded.code.value}", decoded.path)
    admitted = _admit_pair_source(decoded)
    if type(admitted) is AdmitReject:
        return InvalidEvidenceV1(f"admit_{admitted.code.value}", admitted.path)
    if type(admitted) is not AdmitOk:
        return InvalidEvidenceV1("admit_impossible_result", ())
    try:
        return _build_pair(admitted.value, raw)
    except _DomainConstructionError as error:
        return InvalidEvidenceV1(error.code, error.path)
    except (TypeError, ValueError, KeyError):
        return InvalidEvidenceV1(AdmitCode.DOMAIN_INVARIANT.value, ())


def _marker_source(status: EvidenceFieldStatusV1, *, legacy: bool) -> JsonProjectionV1:
    if type(status) is not EvidenceFieldStatusV1:
        raise TypeError("evidence field status was mutated")
    if status is EvidenceFieldStatusV1.ABSENT:
        return None
    if status is EvidenceFieldStatusV1.UNAVAILABLE and legacy:
        return {"status": _UNAVAILABLE_LITERAL_V1}
    raise TypeError("evidence field status is invalid for its observation side")


def _bytes_field_source(field: CanonicalBytesFieldV1, *, legacy: bool) -> JsonProjectionV1:
    if type(field) is not CanonicalBytesFieldV1:
        raise TypeError("canonical byte field was mutated")
    if field.status is EvidenceFieldStatusV1.PRESENT and not legacy:
        if type(field.value) is not bytes or not field.value:
            raise TypeError("present canonical byte field was mutated")
        return field.value.hex()
    if field.value is not None:
        raise TypeError("non-present canonical byte field retained a value")
    return _marker_source(field.status, legacy=legacy)


def _digest_field_source(field: CanonicalDigestFieldV1, *, legacy: bool) -> JsonProjectionV1:
    if type(field) is not CanonicalDigestFieldV1:
        raise TypeError("canonical digest field was mutated")
    if field.status is EvidenceFieldStatusV1.PRESENT and not legacy:
        if type(field.value) is not str:
            raise TypeError("present canonical digest field was mutated")
        return field.value
    if field.value is not None:
        raise TypeError("non-present canonical digest field retained a value")
    return _marker_source(field.status, legacy=legacy)


def _identities_field_source(
    field: CanonicalIdentitiesFieldV1,
    *,
    legacy: bool,
) -> JsonProjectionV1:
    if type(field) is not CanonicalIdentitiesFieldV1:
        raise TypeError("canonical identities field was mutated")
    if field.status is EvidenceFieldStatusV1.PRESENT and not legacy:
        if type(field.value) is not tuple or any(
            type(value) is not OutboxIdentityValueV1 for value in field.value
        ):
            raise TypeError("present canonical identities field was mutated")
        return [
            {
                "effect_identity": value.effect_identity,
                "effect_index": value.effect_index,
                "idempotency_key": value.idempotency_key,
            }
            for value in field.value
        ]
    if field.value is not None:
        raise TypeError("non-present canonical identities field retained a value")
    return _marker_source(field.status, legacy=legacy)


def _rejection_source(value: RejectionValueV1 | None) -> JsonProjectionV1:
    if value is None:
        return None
    if type(value) is not RejectionValueV1:
        raise TypeError("rejection value was mutated")
    return {
        "code": value.code,
        "path": list(value.path),
        "precedence": value.precedence,
        "public_reason": value.public_reason,
        "unavailable_fields": list(value.unavailable_fields),
    }


def _fee_source(value: FCISFeeAllocationV1 | None) -> JsonProjectionV1:
    if value is None:
        return None
    if type(value) is not FCISFeeAllocationV1:
        raise TypeError("fee allocation was mutated")
    return {
        "buyback_amount": value.buyback_amount,
        "dust_carried": value.dust_carried,
        "rewards_amount": value.rewards_amount,
        "treasury_amount": value.treasury_amount,
    }


def _binding_source(binding: InputBindingV1) -> JsonProjectionV1:
    if type(binding) is not InputBindingV1:
        raise TypeError("input binding was mutated")
    return {
        "baseline_artifact_hash": binding.baseline_artifact_hash,
        "command_bytes": [value.hex() for value in binding.command_bytes],
        "command_hash": binding.command_hash,
        "command_kind": binding.command_kind,
        "context_bytes": binding.context_bytes.hex(),
        "context_hash": binding.context_hash,
        "differential_artifact_hash": binding.differential_artifact_hash,
        "fixture_id": binding.fixture_id,
        "packet_commit": binding.packet_commit,
        "packet_tree_hash": binding.packet_tree_hash,
        "pre_state_bytes": binding.pre_state_bytes.hex(),
        "pre_state_root": binding.pre_state_root,
        "reviewed_start_sha": binding.reviewed_start_sha,
    }


def _observation_source(value: ObservationValueV1, *, legacy: bool) -> JsonProjectionV1:
    if (
        type(value) is not ObservationValueV1
        or type(value.result_kind) is not ObservationResultKindV1
    ):
        raise TypeError("observation value was mutated")
    return {
        "algorithm_id": value.algorithm_id,
        "algorithm_version": value.algorithm_version,
        "bundle_bytes": _bytes_field_source(value.bundle_bytes, legacy=legacy),
        "bundle_root": _digest_field_source(value.bundle_root, legacy=legacy),
        "codec_version": value.codec_version,
        "commit_plan_bytes": _bytes_field_source(value.commit_plan_bytes, legacy=legacy),
        "effects_bytes": _bytes_field_source(value.effects_bytes, legacy=legacy),
        "fee_allocation": _fee_source(value.fee_allocation),
        "next_nonce_table_hash": value.next_nonce_table_hash,
        "next_state_snapshot_bytes": (
            None
            if value.next_state_snapshot_bytes is None
            else value.next_state_snapshot_bytes.hex()
        ),
        "next_state_snapshot_root": value.next_state_snapshot_root,
        "outbox_bytes": _bytes_field_source(value.outbox_bytes, legacy=legacy),
        "outbox_identities": _identities_field_source(value.outbox_identities, legacy=legacy),
        "patch_bytes": _bytes_field_source(value.patch_bytes, legacy=legacy),
        "receipt_bytes": _bytes_field_source(value.receipt_bytes, legacy=legacy),
        "receipt_root": _digest_field_source(value.receipt_root, legacy=legacy),
        "rejection": _rejection_source(value.rejection),
        "replay_bytes": _bytes_field_source(value.replay_bytes, legacy=legacy),
        "result_kind": value.result_kind.value,
        "schema_version": value.schema_version,
        "settlement_bytes": None
        if value.settlement_bytes is None
        else value.settlement_bytes.hex(),
        "snapshot_version": value.snapshot_version,
        "support_root": value.support_root,
        "support_root_version": value.support_root_version,
        "total_swap_fees": value.total_swap_fees,
    }


def _pair_source(pair: ObservationPairV1) -> JsonProjectionV1:
    if type(pair) is not ObservationPairV1:
        raise TypeError("observation pair was mutated")
    return {
        "exact": {
            "binding": _binding_source(pair.exact.binding),
            "observation": _observation_source(pair.exact.observation, legacy=False),
        },
        "legacy": {
            "binding": _binding_source(pair.legacy.binding),
            "observation": _observation_source(pair.legacy.observation, legacy=True),
        },
    }


def revalidate_observation_pair_v1(
    source: object,
) -> ObservationPairV1 | InvalidEvidenceV1:
    """Detect nested hostile mutation against retained canonical source bytes."""

    if type(source) is not ObservationPairV1:
        return InvalidEvidenceV1("pair_exact_type_mismatch", ())
    pair = source
    try:
        projected = canonical_json_bytes(_pair_source(pair))
    except (TypeError, ValueError, AttributeError):
        return InvalidEvidenceV1("pair_projection_invalid", ())
    if projected != pair.canonical_source_bytes:
        return InvalidEvidenceV1("pair_source_bytes_mismatch", ())
    if sha256_hex(projected) != pair.canonical_source_hash:
        return InvalidEvidenceV1("pair_source_hash_mismatch", ())
    rebuilt = admit_observation_pair_bytes_v1(projected)
    if type(rebuilt) is InvalidEvidenceV1:
        return rebuilt
    if rebuilt != pair:
        return InvalidEvidenceV1("pair_rebuild_mismatch", ())
    return pair


def encode_observation_pair_v1(pair: ObservationPairV1) -> bytes | InvalidEvidenceV1:
    validated = revalidate_observation_pair_v1(pair)
    if type(validated) is InvalidEvidenceV1:
        return validated
    return validated.canonical_source_bytes


__all__ = (
    "BASELINE_ARTIFACT_HASH_V1",
    "DIFFERENTIAL_ARTIFACT_HASH_V1",
    "PACKET_COMMIT_V1",
    "PACKET_TREE_HASH_V1",
    "REFINEMENT_ADMISSION_LIMITS_V1",
    "REQUIRED_ANCESTOR_V1",
    "admit_observation_pair_bytes_v1",
    "decode_canonical_json_bytes_v1",
    "encode_observation_pair_v1",
    "revalidate_observation_pair_v1",
)

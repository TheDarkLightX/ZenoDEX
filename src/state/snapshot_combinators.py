"""Bounded closed admission algebra for authority-bearing snapshots.

Registries are trusted configuration values. Authority inputs never select a
constructor, callback, source type, or encoder outside a closed registry.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from dataclasses import fields as dataclass_fields
from enum import Enum, EnumType
from types import FunctionType, MappingProxyType
from typing import Callable, Generic, TypeVar, cast, final

from typing_extensions import TypeIs

from .owned_collections import (
    OwnedEnumV1,
    OwnedMapV1,
    _owned_enum_from_admitted,
    _owned_map_from_admitted,
)

PathPart = str | int
FieldPath = tuple[PathPart, ...]
T = TypeVar("T")
_MAPPING_PROXY_TYPE: type[object] = type(MappingProxyType({}))


def _has_exact_type(value: object, expected_type: type[T]) -> TypeIs[T]:
    return type(value) is expected_type


MAX_ADMISSION_DEPTH_V1 = 64
MAX_ADMISSION_NODES_V1 = 200_000
MAX_CANONICAL_BYTES_V1 = 4_000_000
MAX_COLLECTION_ITEMS_V1 = 200_000
MAX_SORTABLE_KEY_INTEGER_BITS_V1 = 256


class AdmitCode(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    NONCANONICAL_SCALAR = "noncanonical_scalar"
    OUT_OF_RANGE = "out_of_range"
    WRONG_CONTAINER = "wrong_container"
    WRONG_KEY_TYPE = "wrong_key_type"
    UNKNOWN_FIELD = "unknown_field"
    MISSING_FIELD = "missing_field"
    UNSUPPORTED_VARIANT = "unsupported_variant"
    REGISTRY_DRIFT = "registry_drift"
    CYCLE = "cycle"
    DEPTH_LIMIT = "depth_limit"
    ITEM_LIMIT = "item_limit"
    BYTE_LIMIT = "byte_limit"
    DOMAIN_INVARIANT = "domain_invariant"


@dataclass(frozen=True, slots=True)
class AdmitReject:
    code: AdmitCode
    path: FieldPath


@dataclass(frozen=True, slots=True)
class AdmitOk(Generic[T]):
    value: T


class LimitProfileCode(Enum):
    INVALID_LIMIT_PROFILE = "invalid_limit_profile"


@dataclass(frozen=True, slots=True)
class LimitProfileReject:
    code: LimitProfileCode
    path: FieldPath


@dataclass(frozen=True, slots=True)
class AdmissionLimitsV1:
    """Raw trusted configuration; it is not accepted by ``admit``."""

    max_depth: int
    max_nodes: int
    max_canonical_bytes: int
    max_collection_items: int


_VALIDATED_LIMITS_TOKEN = object()


@final
@dataclass(frozen=True, slots=True, init=False)
class ValidatedAdmissionLimitsV1:
    max_depth: int
    max_nodes: int
    max_canonical_bytes: int
    max_collection_items: int

    def __init__(
        self,
        max_depth: int,
        max_nodes: int,
        max_canonical_bytes: int,
        max_collection_items: int,
        *,
        _construction_token: object = None,
    ) -> None:
        try:
            object.__getattribute__(self, "max_depth")
        except AttributeError:
            pass
        else:
            raise TypeError("ValidatedAdmissionLimitsV1 is already initialized")
        if _construction_token is not _VALIDATED_LIMITS_TOKEN:
            raise TypeError("ValidatedAdmissionLimitsV1 requires its builder")
        object.__setattr__(self, "max_depth", max_depth)
        object.__setattr__(self, "max_nodes", max_nodes)
        object.__setattr__(self, "max_canonical_bytes", max_canonical_bytes)
        object.__setattr__(self, "max_collection_items", max_collection_items)


def build_admission_limits_v1(
    raw: AdmissionLimitsV1,
) -> ValidatedAdmissionLimitsV1 | LimitProfileReject:
    """Validate a resource profile without inspecting an authority value."""

    if type(raw) is not AdmissionLimitsV1:
        return LimitProfileReject(LimitProfileCode.INVALID_LIMIT_PROFILE, ())

    values = (
        ("max_depth", raw.max_depth, MAX_ADMISSION_DEPTH_V1),
        ("max_nodes", raw.max_nodes, MAX_ADMISSION_NODES_V1),
        (
            "max_canonical_bytes",
            raw.max_canonical_bytes,
            MAX_CANONICAL_BYTES_V1,
        ),
        (
            "max_collection_items",
            raw.max_collection_items,
            MAX_COLLECTION_ITEMS_V1,
        ),
    )
    for name, value, policy_maximum in values:
        if type(value) is not int or value <= 0 or value > policy_maximum:
            return LimitProfileReject(
                LimitProfileCode.INVALID_LIMIT_PROFILE,
                (name,),
            )
    if raw.max_collection_items > raw.max_nodes:
        return LimitProfileReject(
            LimitProfileCode.INVALID_LIMIT_PROFILE,
            ("max_collection_items",),
        )
    return ValidatedAdmissionLimitsV1(
        raw.max_depth,
        raw.max_nodes,
        raw.max_canonical_bytes,
        raw.max_collection_items,
        _construction_token=_VALIDATED_LIMITS_TOKEN,
    )


def _validated_limits_are_within_policy(limits: ValidatedAdmissionLimitsV1) -> bool:
    values = (
        (limits.max_depth, MAX_ADMISSION_DEPTH_V1),
        (limits.max_nodes, MAX_ADMISSION_NODES_V1),
        (limits.max_canonical_bytes, MAX_CANONICAL_BYTES_V1),
        (limits.max_collection_items, MAX_COLLECTION_ITEMS_V1),
    )
    return (
        all(type(value) is int and 0 < value <= policy_maximum for value, policy_maximum in values)
        and limits.max_collection_items <= limits.max_nodes
    )


def _resolver_is_source_bound(resolver: object) -> bool:
    return (
        type(resolver) is FunctionType
        and resolver.__closure__ is None
        and resolver.__name__ != "<lambda>"
        and "<locals>" not in resolver.__qualname__
    )


class StringRuleV1(Enum):
    EXACT_TEXT = "exact_text"
    NON_EMPTY = "non_empty"
    LOWERCASE_HEX = "lowercase_hex"
    EXACT_LITERAL = "exact_literal"


class SequenceSourceKind(Enum):
    EXACT_LIST = "exact_list"
    EXACT_TUPLE = "exact_tuple"


@dataclass(frozen=True, slots=True)
class ExactInt:
    minimum: int
    maximum: int | None


@dataclass(frozen=True, slots=True)
class ExactBool:
    pass


@dataclass(frozen=True, slots=True)
class ExactString:
    string_rule: StringRuleV1
    max_utf8_bytes: int
    exact_literal: str | None = None
    exact_utf8_bytes: int | None = None
    max_characters: int | None = None


@dataclass(frozen=True, slots=True)
class ExactBytes:
    exact_length: int | None
    max_length: int


@dataclass(frozen=True, slots=True)
class ExactEnum:
    enum_tag: Enum


@dataclass(frozen=True, slots=True)
class OptionalValue:
    inner: SchemaV1


@dataclass(frozen=True, slots=True)
class SequenceOf:
    accepted_source_kinds: tuple[SequenceSourceKind, ...]
    inner: SchemaV1
    minimum_items: int
    maximum_items: int


@dataclass(frozen=True, slots=True)
class ExactPair:
    left: SchemaV1
    right: SchemaV1


@dataclass(frozen=True, slots=True)
class MapOf:
    key_schema: SchemaV1
    value_schema: SchemaV1
    maximum_items: int
    map_schema_id: str


@dataclass(frozen=True, slots=True)
class ExactKeyedMap:
    """A closed exact-string-key map with one schema per declared key."""

    declared_fields: tuple[DeclaredFieldV1, ...]
    map_schema_id: str


@dataclass(frozen=True, slots=True)
class DeclaredFieldV1:
    name: str
    schema: SchemaV1


@dataclass(frozen=True, slots=True)
class RecordOf:
    record_tag: Enum
    declared_fields: tuple[DeclaredFieldV1, ...]


@dataclass(frozen=True, slots=True)
class RecordUnionOf:
    variants: tuple[RecordOf, ...]


@dataclass(frozen=True, slots=True)
class TaggedVariantV1:
    discriminant: Enum
    declared_fields: tuple[DeclaredFieldV1, ...]


@dataclass(frozen=True, slots=True)
class TaggedRecordOf:
    record_tag: Enum
    discriminant_field: str
    discriminant_enum_tag: Enum
    variants: tuple[TaggedVariantV1, ...]


SchemaV1 = (
    ExactInt
    | ExactBool
    | ExactString
    | ExactBytes
    | ExactEnum
    | OptionalValue
    | SequenceOf
    | ExactPair
    | MapOf
    | ExactKeyedMap
    | RecordOf
    | RecordUnionOf
    | TaggedRecordOf
)

KeySortValue = int | str | bytes | tuple["KeySortValue", ...]

CanonicalEncoderResolverV1 = Callable[[str, object], bytes]
RecordConstructionResolverV1 = Callable[
    [Enum, tuple[tuple[str, object], ...]],
    object,
]
# The profile resolver performs both named construction and the record's
# semantic postcondition. A returned wrong exact type is registry drift.


@dataclass(frozen=True, slots=True)
class EnumRegistrationV1:
    tag: Enum
    enum_type: type[Enum]


@dataclass(frozen=True, slots=True)
class RecordRegistrationV1:
    tag: Enum
    source_type: type[object]
    owned_type: type[object]


@dataclass(frozen=True, slots=True)
class SchemaRegistrationV1:
    schema_id: str
    schema: SchemaV1


_ADMISSION_REGISTRY_TOKEN = object()


@final
@dataclass(frozen=True, slots=True, init=False)
class AdmissionRegistryV1:
    schema_revision: str
    enum_tag_type: type[Enum]
    record_tag_type: type[Enum]
    enum_registrations: tuple[EnumRegistrationV1, ...]
    record_registrations: tuple[RecordRegistrationV1, ...]
    schema_registrations: tuple[SchemaRegistrationV1, ...]

    def __init__(
        self,
        schema_revision: str,
        enum_tag_type: type[Enum],
        record_tag_type: type[Enum],
        enum_registrations: tuple[EnumRegistrationV1, ...],
        record_registrations: tuple[RecordRegistrationV1, ...],
        schema_registrations: tuple[SchemaRegistrationV1, ...],
        *,
        _construction_token: object = None,
    ) -> None:
        try:
            object.__getattribute__(self, "schema_revision")
        except AttributeError:
            pass
        else:
            raise TypeError("AdmissionRegistryV1 is already initialized")
        if _construction_token is not _ADMISSION_REGISTRY_TOKEN:
            raise TypeError("AdmissionRegistryV1 requires its builder")
        object.__setattr__(self, "schema_revision", schema_revision)
        object.__setattr__(self, "enum_tag_type", enum_tag_type)
        object.__setattr__(self, "record_tag_type", record_tag_type)
        object.__setattr__(self, "enum_registrations", enum_registrations)
        object.__setattr__(self, "record_registrations", record_registrations)
        object.__setattr__(self, "schema_registrations", schema_registrations)

    @property
    def schema_ids(self) -> tuple[str, ...]:
        return tuple(registration.schema_id for registration in self.schema_registrations)

    def _schema_registration(self, schema_id: str) -> SchemaRegistrationV1 | None:
        for registration in self.schema_registrations:
            if registration.schema_id == schema_id:
                return registration
        return None

    def _enum_registration(self, tag: Enum) -> EnumRegistrationV1 | None:
        for registration in self.enum_registrations:
            if registration.tag is tag:
                return registration
        return None

    def _enum_registration_index(self, tag: Enum) -> int | None:
        for index, registration in enumerate(self.enum_registrations):
            if registration.tag is tag:
                return index
        return None

    def _record_registration(self, tag: Enum) -> RecordRegistrationV1 | None:
        for registration in self.record_registrations:
            if registration.tag is tag:
                return registration
        return None


def _enum_class_is_closed(enum_type: type[Enum]) -> bool:
    return (
        type(enum_type) is EnumType
        and int not in enum_type.__mro__
        and all(name == member.name for name, member in enum_type.__members__.items())
    )


def _validate_enum_registrations(
    enum_tag_type: type[Enum],
    registrations: tuple[EnumRegistrationV1, ...],
) -> None:
    if type(registrations) is not tuple:
        raise TypeError("enum registrations must be an exact tuple")
    tags: list[Enum] = []
    for registration in registrations:
        if type(registration) is not EnumRegistrationV1:
            raise TypeError("invalid enum registration")
        if type(registration.tag) is not enum_tag_type:
            raise ValueError("enum registration tag drift")
        if not _enum_class_is_closed(registration.enum_type):
            raise TypeError("registered enum must be a closed non-IntEnum")
        tags.append(registration.tag)
    declared_tags = (*enum_tag_type,)
    if (*tags,) != declared_tags:
        raise ValueError("enum registry is not exhaustive and ordered")


def _validate_record_registrations(
    record_tag_type: type[Enum],
    registrations: tuple[RecordRegistrationV1, ...],
) -> None:
    if type(registrations) is not tuple:
        raise TypeError("record registrations must be an exact tuple")
    tags: list[Enum] = []
    source_types: list[type[object]] = []
    owned_types: list[type[object]] = []
    for registration in registrations:
        if type(registration) is not RecordRegistrationV1:
            raise TypeError("invalid record registration")
        if type(registration.tag) is not record_tag_type:
            raise ValueError("record registration tag drift")
        if type(registration.source_type) is not type or type(registration.owned_type) is not type:
            raise TypeError("registered records must be exact classes")
        try:
            dataclass_fields(registration.source_type)  # type: ignore[arg-type]
            dataclass_fields(registration.owned_type)  # type: ignore[arg-type]
        except TypeError as exc:
            raise TypeError("registered records must be dataclasses") from exc
        owned_parameters = getattr(registration.owned_type, "__dataclass_params__", None)
        owned_field_names = {
            item.name
            for item in dataclass_fields(
                registration.owned_type  # type: ignore[arg-type]
            )
        }
        hidden_slots = {
            slot_name
            for base in registration.owned_type.__mro__[:-1]
            for slot_name in base.__dict__.get("__slots__", ())
            if slot_name not in owned_field_names and slot_name != "__weakref__"
        }
        if (
            owned_parameters is None
            or owned_parameters.frozen is not True
            or getattr(registration.owned_type, "__final__", False) is not True
            or getattr(registration.owned_type, "__dictoffset__", -1) != 0
            or type(getattr(registration.owned_type, "__slots__", None)) is not tuple
            or bool(hidden_slots)
        ):
            # Authority invariant: admitted records cannot retain a mutable object API.
            raise TypeError("registered owned records must be frozen slotted final dataclasses")
        tags.append(registration.tag)
        source_types.append(registration.source_type)
        owned_types.append(registration.owned_type)
    declared_tags = (*record_tag_type,)
    if (*tags,) != declared_tags:
        raise ValueError("record registry is not exhaustive and ordered")
    if len(source_types) != len(set(source_types)):
        raise ValueError("record source types must be unique")
    if len(owned_types) != len(set(owned_types)):
        raise ValueError("record owned types must be unique")
    if len((*source_types, *owned_types)) != len(set((*source_types, *owned_types))):
        raise ValueError("record source and owned types must be pairwise distinct")


def _validate_exact_int_schema(schema: ExactInt) -> None:
    if type(schema.minimum) is not int:
        raise TypeError("ExactInt minimum must be exact int")
    if schema.maximum is not None and type(schema.maximum) is not int:
        raise TypeError("ExactInt maximum must be exact int or None")
    if schema.maximum is not None and schema.maximum < schema.minimum:
        raise ValueError("ExactInt bounds are inverted")


def _validate_exact_string_schema(schema: ExactString) -> None:
    if type(schema.string_rule) is not StringRuleV1:
        raise TypeError("unknown string rule")
    if (
        type(schema.max_utf8_bytes) is not int
        or schema.max_utf8_bytes <= 0
        or schema.max_utf8_bytes > MAX_CANONICAL_BYTES_V1
    ):
        raise ValueError("invalid string byte bound")
    if schema.exact_utf8_bytes is not None and (
        type(schema.exact_utf8_bytes) is not int
        or schema.exact_utf8_bytes <= 0
        or schema.exact_utf8_bytes > schema.max_utf8_bytes
    ):
        raise ValueError("invalid exact string byte width")
    if schema.max_characters is not None and (
        type(schema.max_characters) is not int
        or schema.max_characters <= 0
        or schema.max_characters > MAX_CANONICAL_BYTES_V1
    ):
        raise ValueError("invalid string character bound")
    if schema.string_rule is StringRuleV1.EXACT_LITERAL:
        if type(schema.exact_literal) is not str:
            raise TypeError("exact literal rule requires an exact string")
        try:
            literal_bytes = schema.exact_literal.encode("utf-8")
        except UnicodeEncodeError as exc:
            raise ValueError("exact literal must be valid UTF-8") from exc
        if len(literal_bytes) > schema.max_utf8_bytes or (
            schema.exact_utf8_bytes is not None and len(literal_bytes) != schema.exact_utf8_bytes
        ):
            raise ValueError("exact literal violates its byte bounds")
        if schema.max_characters is not None and len(schema.exact_literal) > schema.max_characters:
            raise ValueError("exact literal violates its character bound")
    elif schema.exact_literal is not None:
        raise ValueError("literal data requires the exact literal rule")


def _validate_exact_bytes_schema(schema: ExactBytes) -> None:
    if (
        type(schema.max_length) is not int
        or schema.max_length < 0
        or schema.max_length > MAX_CANONICAL_BYTES_V1
    ):
        raise ValueError("invalid bytes maximum")
    if schema.exact_length is not None and (
        type(schema.exact_length) is not int
        or schema.exact_length < 0
        or schema.exact_length > schema.max_length
    ):
        raise ValueError("invalid exact bytes length")


def _validate_sequence_schema(
    schema: SequenceOf,
    enum_tag_type: type[Enum],
    record_tag_type: type[Enum],
    active_schema_ids: set[int],
) -> None:
    if type(schema.accepted_source_kinds) is not tuple or not schema.accepted_source_kinds:
        raise ValueError("sequence source kinds must be a nonempty exact tuple")
    if any(type(kind) is not SequenceSourceKind for kind in schema.accepted_source_kinds):
        raise TypeError("unknown sequence source kind")
    if len(schema.accepted_source_kinds) != len(tuple(dict.fromkeys(schema.accepted_source_kinds))):
        raise ValueError("duplicate sequence source kind")
    _validate_item_bounds(schema.minimum_items, schema.maximum_items)
    _validate_schema(schema.inner, enum_tag_type, record_tag_type, active_schema_ids)


def _validate_pair_schema(
    schema: ExactPair,
    enum_tag_type: type[Enum],
    record_tag_type: type[Enum],
    active_schema_ids: set[int],
) -> None:
    _validate_schema(schema.left, enum_tag_type, record_tag_type, active_schema_ids)
    _validate_schema(schema.right, enum_tag_type, record_tag_type, active_schema_ids)


def _validate_map_schema(
    schema: MapOf,
    enum_tag_type: type[Enum],
    record_tag_type: type[Enum],
    active_schema_ids: set[int],
) -> None:
    if type(schema.map_schema_id) is not str or not schema.map_schema_id:
        raise ValueError("map schema ID must be an exact nonempty string")
    if not _schema_is_valid_map_key(schema.key_schema):
        raise TypeError("map key schema has no canonical total order")
    _validate_map_key_sort_bounds(schema.key_schema)
    _validate_item_bounds(0, schema.maximum_items)
    _validate_schema(schema.key_schema, enum_tag_type, record_tag_type, active_schema_ids)
    _validate_schema(schema.value_schema, enum_tag_type, record_tag_type, active_schema_ids)


def _validate_map_key_sort_bounds(schema: SchemaV1) -> None:
    if _has_exact_type(schema, ExactInt):
        if schema.maximum is None:
            raise ValueError("integer map keys require a finite maximum")
        if (
            abs(schema.minimum).bit_length() > MAX_SORTABLE_KEY_INTEGER_BITS_V1
            or abs(schema.maximum).bit_length() > MAX_SORTABLE_KEY_INTEGER_BITS_V1
        ):
            raise ValueError("integer map-key bounds exceed the sortable width")
        return
    if _has_exact_type(schema, ExactPair):
        _validate_map_key_sort_bounds(schema.left)
        _validate_map_key_sort_bounds(schema.right)


def _validate_exact_keyed_map_schema(
    schema: ExactKeyedMap,
    enum_tag_type: type[Enum],
    record_tag_type: type[Enum],
    active_schema_ids: set[int],
) -> None:
    if type(schema.map_schema_id) is not str or not schema.map_schema_id:
        raise ValueError("map schema ID must be an exact nonempty string")
    _validate_declared_fields(
        schema.declared_fields,
        enum_tag_type,
        record_tag_type,
        active_schema_ids,
    )
    _validate_item_bounds(len(schema.declared_fields), len(schema.declared_fields))


def _schema_is_valid_map_key(schema: SchemaV1) -> bool:
    if type(schema) in {ExactInt, ExactBool, ExactString, ExactBytes, ExactEnum}:
        return True
    if _has_exact_type(schema, ExactPair):
        return _schema_is_valid_map_key(schema.left) and _schema_is_valid_map_key(schema.right)
    return False


def _validate_record_schema(
    schema: RecordOf,
    enum_tag_type: type[Enum],
    record_tag_type: type[Enum],
    active_schema_ids: set[int],
) -> None:
    if type(schema.record_tag) is not record_tag_type:
        raise ValueError("record schema tag drift")
    _validate_declared_fields(
        schema.declared_fields,
        enum_tag_type,
        record_tag_type,
        active_schema_ids,
    )


def _validate_record_union_schema(
    schema: RecordUnionOf,
    enum_tag_type: type[Enum],
    record_tag_type: type[Enum],
    active_schema_ids: set[int],
) -> None:
    if type(schema.variants) is not tuple or not schema.variants:
        raise ValueError("record union variants must be a nonempty exact tuple")
    record_tags: list[Enum] = []
    for variant in schema.variants:
        if type(variant) is not RecordOf:
            raise TypeError("record union variants must be exact RecordOf values")
        _validate_record_schema(
            variant,
            enum_tag_type,
            record_tag_type,
            active_schema_ids,
        )
        record_tags.append(variant.record_tag)
    if len(record_tags) != len(set(record_tags)):
        raise ValueError("record union tags must be unique")


def _validate_tagged_record_schema(
    schema: TaggedRecordOf,
    enum_tag_type: type[Enum],
    record_tag_type: type[Enum],
    active_schema_ids: set[int],
) -> None:
    if type(schema.record_tag) is not record_tag_type:
        raise ValueError("tagged record schema tag drift")
    if type(schema.discriminant_field) is not str or not schema.discriminant_field:
        raise ValueError("invalid discriminant field")
    if type(schema.discriminant_enum_tag) is not enum_tag_type:
        raise ValueError("discriminant enum tag drift")
    if type(schema.variants) is not tuple:
        raise TypeError("tagged variants must be an exact tuple")
    for variant in schema.variants:
        if type(variant) is not TaggedVariantV1:
            raise TypeError("invalid tagged variant")
        _validate_declared_fields(
            variant.declared_fields,
            enum_tag_type,
            record_tag_type,
            active_schema_ids,
        )


def _validate_schema_variant(
    schema: SchemaV1,
    enum_tag_type: type[Enum],
    record_tag_type: type[Enum],
    active_schema_ids: set[int],
) -> None:
    if _has_exact_type(schema, ExactInt):
        _validate_exact_int_schema(schema)
    elif _has_exact_type(schema, ExactBool):
        return
    elif _has_exact_type(schema, ExactString):
        _validate_exact_string_schema(schema)
    elif _has_exact_type(schema, ExactBytes):
        _validate_exact_bytes_schema(schema)
    elif _has_exact_type(schema, ExactEnum):
        if type(schema.enum_tag) is not enum_tag_type:
            raise ValueError("enum schema tag drift")
    elif _has_exact_type(schema, OptionalValue):
        _validate_schema(schema.inner, enum_tag_type, record_tag_type, active_schema_ids)
    elif _has_exact_type(schema, SequenceOf):
        _validate_sequence_schema(schema, enum_tag_type, record_tag_type, active_schema_ids)
    elif _has_exact_type(schema, ExactPair):
        _validate_pair_schema(schema, enum_tag_type, record_tag_type, active_schema_ids)
    elif _has_exact_type(schema, MapOf):
        _validate_map_schema(schema, enum_tag_type, record_tag_type, active_schema_ids)
    elif _has_exact_type(schema, ExactKeyedMap):
        _validate_exact_keyed_map_schema(
            schema,
            enum_tag_type,
            record_tag_type,
            active_schema_ids,
        )
    elif _has_exact_type(schema, RecordOf):
        _validate_record_schema(schema, enum_tag_type, record_tag_type, active_schema_ids)
    elif _has_exact_type(schema, RecordUnionOf):
        _validate_record_union_schema(
            schema,
            enum_tag_type,
            record_tag_type,
            active_schema_ids,
        )
    elif _has_exact_type(schema, TaggedRecordOf):
        _validate_tagged_record_schema(
            schema,
            enum_tag_type,
            record_tag_type,
            active_schema_ids,
        )
    else:
        raise TypeError("unsupported schema value")


def _validate_schema(
    schema: SchemaV1,
    enum_tag_type: type[Enum],
    record_tag_type: type[Enum],
    active_schema_ids: set[int],
) -> None:
    schema_object_id = id(schema)
    if schema_object_id in active_schema_ids:
        raise ValueError("cyclic schema values are forbidden")
    active_schema_ids.add(schema_object_id)
    try:
        _validate_schema_variant(
            schema,
            enum_tag_type,
            record_tag_type,
            active_schema_ids,
        )
    finally:
        active_schema_ids.remove(schema_object_id)


def _validate_item_bounds(minimum_items: int, maximum_items: int) -> None:
    if type(minimum_items) is not int or type(maximum_items) is not int:
        raise TypeError("collection bounds must be exact integers")
    if minimum_items < 0 or maximum_items < minimum_items:
        raise ValueError("collection bounds are invalid")
    if maximum_items > MAX_COLLECTION_ITEMS_V1:
        raise ValueError("collection bound exceeds the mounted policy")


def _validate_declared_fields(
    declared_fields: tuple[DeclaredFieldV1, ...],
    enum_tag_type: type[Enum],
    record_tag_type: type[Enum],
    active_schema_ids: set[int],
) -> None:
    if type(declared_fields) is not tuple:
        raise TypeError("declared fields must be an exact tuple")
    names: list[str] = []
    for declared_field in declared_fields:
        if type(declared_field) is not DeclaredFieldV1:
            raise TypeError("invalid declared field")
        if type(declared_field.name) is not str or not declared_field.name:
            raise ValueError("declared field name must be an exact nonempty string")
        if _bounded_utf8_length(declared_field.name, MAX_CANONICAL_BYTES_V1) is None:
            raise ValueError("declared field name must be valid UTF-8")
        names.append(declared_field.name)
        _validate_schema(
            declared_field.schema,
            enum_tag_type,
            record_tag_type,
            active_schema_ids,
        )
    if len(names) != len(tuple(dict.fromkeys(names))):
        raise ValueError("duplicate declared field")


def build_admission_registry_v1(
    *,
    schema_revision: str,
    enum_tag_type: type[Enum],
    record_tag_type: type[Enum],
    enum_registrations: tuple[EnumRegistrationV1, ...],
    record_registrations: tuple[RecordRegistrationV1, ...],
    schema_registrations: tuple[SchemaRegistrationV1, ...],
) -> AdmissionRegistryV1:
    """Build the immutable declarative schema and exact-type registry."""

    if type(schema_revision) is not str or not schema_revision:
        raise ValueError("schema revision must be an exact nonempty string")
    if not _enum_class_is_closed(enum_tag_type) or not _enum_class_is_closed(record_tag_type):
        raise TypeError("registry tag types must be closed non-IntEnum values")
    _validate_enum_registrations(enum_tag_type, enum_registrations)
    _validate_record_registrations(record_tag_type, record_registrations)
    if type(schema_registrations) is not tuple or not schema_registrations:
        raise ValueError("schema registrations must be a nonempty exact tuple")
    schema_ids: list[str] = []
    for registration in schema_registrations:
        if type(registration) is not SchemaRegistrationV1:
            raise TypeError("invalid schema registration")
        if type(registration.schema_id) is not str or not registration.schema_id:
            raise ValueError("schema ID must be an exact nonempty string")
        _validate_schema(registration.schema, enum_tag_type, record_tag_type, set())
        schema_ids.append(registration.schema_id)
    if len(schema_ids) != len(tuple(dict.fromkeys(schema_ids))):
        raise ValueError("duplicate schema ID")
    return AdmissionRegistryV1(
        schema_revision,
        enum_tag_type,
        record_tag_type,
        enum_registrations,
        record_registrations,
        schema_registrations,
        _construction_token=_ADMISSION_REGISTRY_TOKEN,
    )


@dataclass(frozen=True, slots=True)
class _AdmissionState:
    limits: ValidatedAdmissionLimitsV1
    record_construction_resolver: RecordConstructionResolverV1
    nodes_used: int = 0
    trusted_scalar_bytes_used: int = 0
    active_container_ids: tuple[int, ...] = ()


@dataclass(frozen=True, slots=True)
class _AdmitProgress(Generic[T]):
    """An admitted value paired with the next immutable evaluation state."""

    value: T
    state: _AdmissionState


def _reject(code: AdmitCode, path: FieldPath) -> AdmitReject:
    return AdmitReject(code, path)


def _check_depth(
    state: _AdmissionState,
    depth: int,
    path: FieldPath,
) -> AdmitReject | None:
    if depth > state.limits.max_depth:
        return _reject(AdmitCode.DEPTH_LIMIT, path)
    return None


def _consume_node(
    state: _AdmissionState,
    path: FieldPath,
) -> _AdmissionState | AdmitReject:
    if state.nodes_used >= state.limits.max_nodes:
        return _reject(AdmitCode.ITEM_LIMIT, path)
    return _AdmissionState(
        state.limits,
        state.record_construction_resolver,
        state.nodes_used + 1,
        state.trusted_scalar_bytes_used,
        state.active_container_ids,
    )


def _consume_trusted_scalar_bytes(
    state: _AdmissionState,
    byte_count: int,
    path: FieldPath,
) -> _AdmissionState | AdmitReject:
    remaining = state.limits.max_canonical_bytes - state.trusted_scalar_bytes_used
    if byte_count > remaining:
        return _reject(AdmitCode.BYTE_LIMIT, path)
    return _AdmissionState(
        state.limits,
        state.record_construction_resolver,
        state.nodes_used,
        state.trusted_scalar_bytes_used + byte_count,
        state.active_container_ids,
    )


def _enter_active(
    state: _AdmissionState,
    source: object,
    path: FieldPath,
) -> _AdmissionState | AdmitReject:
    source_id = id(source)
    if source_id in state.active_container_ids:
        return _reject(AdmitCode.CYCLE, path)
    return _AdmissionState(
        state.limits,
        state.record_construction_resolver,
        state.nodes_used,
        state.trusted_scalar_bytes_used,
        state.active_container_ids + (source_id,),
    )


def _leave_active(state: _AdmissionState, source: object) -> _AdmissionState:
    return _AdmissionState(
        state.limits,
        state.record_construction_resolver,
        state.nodes_used,
        state.trusted_scalar_bytes_used,
        tuple(item for item in state.active_container_ids if item != id(source)),
    )


def _bounded_utf8_length(source: str, maximum: int) -> int | None:
    byte_count = 0
    for character in source:
        codepoint = ord(character)
        if 0xD800 <= codepoint <= 0xDFFF:
            return None
        if codepoint <= 0x7F:
            byte_count += 1
        elif codepoint <= 0x7FF:
            byte_count += 2
        elif codepoint <= 0xFFFF:
            byte_count += 3
        else:
            byte_count += 4
        if byte_count > maximum:
            return byte_count
    return byte_count


def _string_is_canonical(
    schema: ExactString,
    source: str,
    utf8_bytes: int,
) -> bool:
    if schema.exact_utf8_bytes is not None and utf8_bytes != schema.exact_utf8_bytes:
        return False
    if schema.string_rule is StringRuleV1.EXACT_TEXT:
        return True
    if schema.string_rule is StringRuleV1.NON_EMPTY:
        return bool(source)
    if schema.string_rule is StringRuleV1.LOWERCASE_HEX:
        return bool(source) and all(character in "0123456789abcdef" for character in source)
    if schema.string_rule is StringRuleV1.EXACT_LITERAL:
        return source == schema.exact_literal


def _admit_exact_int(
    schema: ExactInt,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
) -> _AdmitProgress[object] | AdmitReject:
    if not _has_exact_type(source, int):
        return _reject(AdmitCode.WRONG_EXACT_TYPE, path)
    next_state = _consume_node(state, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    if source < schema.minimum or (schema.maximum is not None and source > schema.maximum):
        return _reject(AdmitCode.OUT_OF_RANGE, path)
    return _AdmitProgress(source, next_state)


def _admit_exact_bool(
    source: object,
    state: _AdmissionState,
    path: FieldPath,
) -> _AdmitProgress[object] | AdmitReject:
    if not _has_exact_type(source, bool):
        return _reject(AdmitCode.WRONG_EXACT_TYPE, path)
    next_state = _consume_node(state, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    return _AdmitProgress(source, next_state)


def _admit_exact_string(
    schema: ExactString,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
) -> _AdmitProgress[object] | AdmitReject:
    if not _has_exact_type(source, str):
        return _reject(AdmitCode.WRONG_EXACT_TYPE, path)
    next_state = _consume_node(state, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    if schema.max_characters is not None and len(source) > schema.max_characters:
        return _reject(AdmitCode.BYTE_LIMIT, path)
    utf8_bytes = _bounded_utf8_length(source, schema.max_utf8_bytes)
    if utf8_bytes is None:
        # Authority invariant: every exact string has one valid UTF-8 representation.
        return _reject(AdmitCode.NONCANONICAL_SCALAR, path)
    if utf8_bytes > schema.max_utf8_bytes:
        return _reject(AdmitCode.BYTE_LIMIT, path)
    if not _string_is_canonical(schema, source, utf8_bytes):
        return _reject(AdmitCode.NONCANONICAL_SCALAR, path)
    next_state = _consume_trusted_scalar_bytes(next_state, utf8_bytes, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    return _AdmitProgress(source, next_state)


def _admit_exact_bytes(
    schema: ExactBytes,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
) -> _AdmitProgress[object] | AdmitReject:
    if not _has_exact_type(source, bytes):
        return _reject(AdmitCode.WRONG_EXACT_TYPE, path)
    next_state = _consume_node(state, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    if len(source) > schema.max_length:
        return _reject(AdmitCode.BYTE_LIMIT, path)
    if schema.exact_length is not None and len(source) != schema.exact_length:
        return _reject(AdmitCode.OUT_OF_RANGE, path)
    next_state = _consume_trusted_scalar_bytes(next_state, len(source), path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    return _AdmitProgress(source, next_state)


def _admit_scalar(
    schema: SchemaV1,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
) -> _AdmitProgress[object] | AdmitReject | None:
    if _has_exact_type(schema, ExactInt):
        return _admit_exact_int(schema, source, state, path)
    if _has_exact_type(schema, ExactBool):
        return _admit_exact_bool(source, state, path)
    if _has_exact_type(schema, ExactString):
        return _admit_exact_string(schema, source, state, path)
    if _has_exact_type(schema, ExactBytes):
        return _admit_exact_bytes(schema, source, state, path)
    return None


def _admit_enum(
    schema: ExactEnum,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
    registry: AdmissionRegistryV1,
    schema_revision: str,
) -> _AdmitProgress[object] | AdmitReject:
    registration = registry._enum_registration(schema.enum_tag)
    tag_ordinal = registry._enum_registration_index(schema.enum_tag)
    if registration is None or tag_ordinal is None:
        return _reject(AdmitCode.UNSUPPORTED_VARIANT, path)
    member_ordinal: int | None = None
    if type(source) is registration.enum_type:
        for index, member in enumerate(registration.enum_type):
            if member is source:
                member_ordinal = index
                break
    elif type(source) is OwnedEnumV1:
        metadata = _owned_enum_metadata(source)
        if metadata is None:
            return _reject(AdmitCode.REGISTRY_DRIFT, path)
        owned_revision, owned_tag_ordinal, owned_member_ordinal = metadata
        if owned_revision != schema_revision or owned_tag_ordinal != tag_ordinal:
            return _reject(AdmitCode.WRONG_EXACT_TYPE, path)
        if owned_member_ordinal >= len(registration.enum_type):
            return _reject(AdmitCode.REGISTRY_DRIFT, path)
        member_ordinal = owned_member_ordinal
    else:
        return _reject(AdmitCode.WRONG_EXACT_TYPE, path)
    if member_ordinal is None:
        return _reject(AdmitCode.UNSUPPORTED_VARIANT, path)
    next_state = _consume_node(state, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    # Authority invariant: a mutable Enum singleton never enters committed state.
    return _AdmitProgress(
        _owned_enum_from_admitted(
            schema_revision,
            tag_ordinal,
            member_ordinal,
        ),
        next_state,
    )


def _owned_enum_metadata(source: OwnedEnumV1) -> tuple[str, int, int] | None:
    try:
        schema_revision = object.__getattribute__(source, "_schema_revision")
        enum_tag_ordinal = object.__getattribute__(source, "_enum_tag_ordinal")
        member_ordinal = object.__getattribute__(source, "_member_ordinal")
    except AttributeError:
        return None
    if (
        type(schema_revision) is not str
        or type(enum_tag_ordinal) is not int
        or type(member_ordinal) is not int
        or enum_tag_ordinal < 0
        or member_ordinal < 0
    ):
        return None
    return schema_revision, enum_tag_ordinal, member_ordinal


def _source_kind_matches(
    source: object,
    accepted_source_kinds: tuple[SequenceSourceKind, ...],
) -> bool:
    source_type = type(source)
    for kind in accepted_source_kinds:
        if kind is SequenceSourceKind.EXACT_LIST and source_type is list:
            return True
        if kind is SequenceSourceKind.EXACT_TUPLE and source_type is tuple:
            return True
    return False


def _admit_sequence(
    schema: SequenceOf,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
    depth: int,
    registry: AdmissionRegistryV1,
    schema_revision: str,
) -> _AdmitProgress[object] | AdmitReject:
    if not _source_kind_matches(source, schema.accepted_source_kinds):
        return _reject(AdmitCode.WRONG_CONTAINER, path)
    owned_source = cast(list[object] | tuple[object, ...], source)
    item_count = len(owned_source)
    if (
        item_count < schema.minimum_items
        or item_count > schema.maximum_items
        or item_count > state.limits.max_collection_items
    ):
        return _reject(AdmitCode.ITEM_LIMIT, path)
    next_state = _consume_node(state, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    next_state = _enter_active(next_state, source, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    owned_items: list[object] = []
    for index in range(item_count):
        result = _admit_value(
            schema.inner,
            owned_source[index],
            next_state,
            path + (index,),
            depth + 1,
            registry,
            schema_revision,
        )
        if _has_exact_type(result, AdmitReject):
            return result
        admitted = result
        owned_items.append(admitted.value)
        next_state = admitted.state
    return _AdmitProgress(tuple(owned_items), _leave_active(next_state, source))


def _admit_pair(
    schema: ExactPair,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
    depth: int,
    registry: AdmissionRegistryV1,
    schema_revision: str,
) -> _AdmitProgress[object] | AdmitReject:
    if not _has_exact_type(source, tuple) or len(source) != 2:
        return _reject(AdmitCode.WRONG_CONTAINER, path)
    owned_source = cast(tuple[object, object], source)
    next_state = _consume_node(state, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    next_state = _enter_active(next_state, source, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    left = _admit_value(
        schema.left,
        owned_source[0],
        next_state,
        path + (0,),
        depth + 1,
        registry,
        schema_revision,
    )
    if _has_exact_type(left, AdmitReject):
        return left
    admitted_left = left
    right = _admit_value(
        schema.right,
        owned_source[1],
        admitted_left.state,
        path + (1,),
        depth + 1,
        registry,
        schema_revision,
    )
    if _has_exact_type(right, AdmitReject):
        return right
    admitted_right = right
    return _AdmitProgress(
        (admitted_left.value, admitted_right.value),
        _leave_active(admitted_right.state, source),
    )


def _key_has_exact_shape(
    schema: SchemaV1,
    source: object,
    registry: AdmissionRegistryV1,
) -> bool:
    if _has_exact_type(schema, ExactInt):
        return type(source) is int
    if _has_exact_type(schema, ExactBool):
        return type(source) is bool
    if _has_exact_type(schema, ExactString):
        return type(source) is str
    if _has_exact_type(schema, ExactBytes):
        return type(source) is bytes
    if _has_exact_type(schema, ExactEnum):
        registration = registry._enum_registration(schema.enum_tag)
        return registration is not None and type(source) in {
            registration.enum_type,
            OwnedEnumV1,
        }
    if _has_exact_type(schema, ExactPair):
        return (
            _has_exact_type(source, tuple)
            and len(source) == 2
            and _key_has_exact_shape(schema.left, source[0], registry)
            and _key_has_exact_shape(schema.right, source[1], registry)
        )
    return False


def _key_canonical_reject(
    schema: SchemaV1,
    source: object,
    path: FieldPath,
    registry: AdmissionRegistryV1,
    schema_revision: str,
) -> AdmitReject | None:
    if _has_exact_type(schema, ExactInt):
        key_int = cast(int, source)
        if key_int < schema.minimum or (schema.maximum is not None and key_int > schema.maximum):
            return _reject(AdmitCode.OUT_OF_RANGE, path)
    elif _has_exact_type(schema, ExactString):
        key_string = cast(str, source)
        if schema.max_characters is not None and len(key_string) > schema.max_characters:
            return _reject(AdmitCode.BYTE_LIMIT, path)
        utf8_bytes = _bounded_utf8_length(key_string, schema.max_utf8_bytes)
        if utf8_bytes is None:
            return _reject(AdmitCode.NONCANONICAL_SCALAR, path)
        if utf8_bytes > schema.max_utf8_bytes:
            return _reject(AdmitCode.BYTE_LIMIT, path)
        if not _string_is_canonical(schema, key_string, utf8_bytes):
            return _reject(AdmitCode.NONCANONICAL_SCALAR, path)
    elif _has_exact_type(schema, ExactBytes):
        key_bytes = cast(bytes, source)
        if len(key_bytes) > schema.max_length:
            return _reject(AdmitCode.BYTE_LIMIT, path)
        if schema.exact_length is not None and len(key_bytes) != schema.exact_length:
            return _reject(AdmitCode.OUT_OF_RANGE, path)
    elif _has_exact_type(schema, ExactEnum):
        registration = registry._enum_registration(schema.enum_tag)
        tag_ordinal = registry._enum_registration_index(schema.enum_tag)
        if registration is None or tag_ordinal is None:
            return _reject(AdmitCode.UNSUPPORTED_VARIANT, path)
        if type(source) is registration.enum_type:
            if not any(member is source for member in registration.enum_type):
                return _reject(AdmitCode.UNSUPPORTED_VARIANT, path)
        else:
            owned_source = cast(OwnedEnumV1, source)
            metadata = _owned_enum_metadata(owned_source)
            if metadata is None:
                return _reject(AdmitCode.REGISTRY_DRIFT, path)
            owned_revision, owned_tag_ordinal, owned_member_ordinal = metadata
            if owned_revision != schema_revision or owned_tag_ordinal != tag_ordinal:
                return _reject(AdmitCode.WRONG_EXACT_TYPE, path)
            if owned_member_ordinal >= len(registration.enum_type):
                return _reject(AdmitCode.REGISTRY_DRIFT, path)
    elif _has_exact_type(schema, ExactPair):
        key_pair = cast(tuple[object, object], source)
        left_reject = _key_canonical_reject(
            schema.left,
            key_pair[0],
            path,
            registry,
            schema_revision,
        )
        if left_reject is not None:
            return left_reject
        return _key_canonical_reject(
            schema.right,
            key_pair[1],
            path,
            registry,
            schema_revision,
        )
    return None


def _key_sort_value(
    schema: SchemaV1,
    source: object,
    registry: AdmissionRegistryV1,
) -> KeySortValue:
    if _has_exact_type(schema, ExactInt):
        key_int = cast(int, source)
        if key_int < schema.minimum:
            return (0, 0)
        if schema.maximum is not None and key_int > schema.maximum:
            return (2, 0)
        return (1, key_int)
    if _has_exact_type(schema, ExactBool):
        return cast(bool, source)
    if _has_exact_type(schema, ExactString):
        return cast(str, source)
    if _has_exact_type(schema, ExactBytes):
        return cast(bytes, source)
    if _has_exact_type(schema, ExactPair):
        key = cast(tuple[object, object], source)
        return (
            _key_sort_value(schema.left, key[0], registry),
            _key_sort_value(schema.right, key[1], registry),
        )
    if _has_exact_type(schema, ExactEnum):
        registration = registry._enum_registration(schema.enum_tag)
        tag_ordinal = registry._enum_registration_index(schema.enum_tag)
        if registration is None or tag_ordinal is None:
            return (-1, 0)
        if type(source) is OwnedEnumV1:
            metadata = _owned_enum_metadata(source)
            if metadata is None:
                return (0, 0)
            owned_revision, owned_tag_ordinal, owned_member_ordinal = metadata
            if (
                len(owned_revision) != len(registry.schema_revision)
                or owned_revision != registry.schema_revision
                or owned_tag_ordinal != tag_ordinal
            ):
                return (0, 1)
            if owned_member_ordinal >= len(registration.enum_type):
                return (2, 0)
            return (1, owned_member_ordinal)
        for index, member in enumerate(registration.enum_type):
            if member is source:
                return (1, index)
        return (-1, 1)
    return 0


def _preflight_key_sort_bytes(
    schema: SchemaV1,
    source: object,
    remaining_bytes: int,
    path: FieldPath,
) -> int | AdmitReject:
    """Bound string/bytes comparison work before deriving raw sort values."""

    if _has_exact_type(schema, ExactString):
        key_string = cast(str, source)
        if schema.max_characters is not None and len(key_string) > schema.max_characters:
            return _reject(AdmitCode.BYTE_LIMIT, path)
        # Every Unicode code point occupies at least one UTF-8 byte. The exact
        # length check therefore rejects huge keys before scanning their prefix.
        if len(key_string) > min(schema.max_utf8_bytes, remaining_bytes):
            return _reject(AdmitCode.BYTE_LIMIT, path)
        utf8_bytes = _bounded_utf8_length(key_string, schema.max_utf8_bytes)
        if utf8_bytes is None:
            # A bounded surrogate-containing key is safe to order as text and
            # receives NONCANONICAL_SCALAR in canonical key order later.
            return len(key_string)
        if utf8_bytes > schema.max_utf8_bytes or utf8_bytes > remaining_bytes:
            return _reject(AdmitCode.BYTE_LIMIT, path)
        return utf8_bytes
    if _has_exact_type(schema, ExactBytes):
        byte_count = len(cast(bytes, source))
        if byte_count > schema.max_length or byte_count > remaining_bytes:
            return _reject(AdmitCode.BYTE_LIMIT, path)
        return byte_count
    if _has_exact_type(schema, ExactPair):
        key_pair = cast(tuple[object, object], source)
        left = _preflight_key_sort_bytes(
            schema.left,
            key_pair[0],
            remaining_bytes,
            path,
        )
        if _has_exact_type(left, AdmitReject):
            return left
        left_bytes = left
        right = _preflight_key_sort_bytes(
            schema.right,
            key_pair[1],
            remaining_bytes - left_bytes,
            path,
        )
        if _has_exact_type(right, AdmitReject):
            return right
        return left_bytes + right
    return 0


def _preflight_map_key_sort_bytes(
    schema: MapOf,
    entries: tuple[tuple[object, object], ...],
    state: _AdmissionState,
    path: FieldPath,
) -> AdmitReject | None:
    remaining_bytes = state.limits.max_canonical_bytes - state.trusted_scalar_bytes_used
    for key, _value in entries:
        key_bytes = _preflight_key_sort_bytes(
            schema.key_schema,
            key,
            remaining_bytes,
            path,
        )
        if _has_exact_type(key_bytes, AdmitReject):
            return key_bytes
        remaining_bytes -= key_bytes
    return None


def _admit_owned_key(
    schema: SchemaV1,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
    depth: int,
    registry: AdmissionRegistryV1,
    schema_revision: str,
) -> _AdmitProgress[object] | AdmitReject:
    depth_reject = _check_depth(state, depth, path)
    if depth_reject is not None:
        return depth_reject
    next_state = _consume_node(state, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    if _has_exact_type(schema, ExactString):
        key_string = cast(str, source)
        utf8_bytes = _bounded_utf8_length(key_string, schema.max_utf8_bytes)
        if utf8_bytes is None:
            return _reject(AdmitCode.NONCANONICAL_SCALAR, path)
        next_state = _consume_trusted_scalar_bytes(
            next_state,
            utf8_bytes,
            path,
        )
        if _has_exact_type(next_state, AdmitReject):
            return next_state
        return _AdmitProgress(source, next_state)
    if _has_exact_type(schema, ExactBytes):
        next_state = _consume_trusted_scalar_bytes(
            next_state,
            len(cast(bytes, source)),
            path,
        )
        if _has_exact_type(next_state, AdmitReject):
            return next_state
        return _AdmitProgress(source, next_state)
    if _has_exact_type(schema, ExactEnum):
        registration = registry._enum_registration(schema.enum_tag)
        tag_ordinal = registry._enum_registration_index(schema.enum_tag)
        if registration is None or tag_ordinal is None:
            return _reject(AdmitCode.UNSUPPORTED_VARIANT, path)
        if type(source) is OwnedEnumV1:
            metadata = _owned_enum_metadata(source)
            if metadata is None:
                return _reject(AdmitCode.REGISTRY_DRIFT, path)
            member_ordinal = metadata[2]
        else:
            member_ordinal = next(
                (index for index, member in enumerate(registration.enum_type) if member is source),
                -1,
            )
        if member_ordinal < 0:
            return _reject(AdmitCode.UNSUPPORTED_VARIANT, path)
        return _AdmitProgress(
            _owned_enum_from_admitted(
                schema_revision,
                tag_ordinal,
                member_ordinal,
            ),
            next_state,
        )
    if _has_exact_type(schema, ExactPair):
        key = cast(tuple[object, object], source)
        left_result = _admit_owned_key(
            schema.left,
            key[0],
            next_state,
            path,
            depth + 1,
            registry,
            schema_revision,
        )
        if _has_exact_type(left_result, AdmitReject):
            return left_result
        right_result = _admit_owned_key(
            schema.right,
            key[1],
            left_result.state,
            path,
            depth + 1,
            registry,
            schema_revision,
        )
        if _has_exact_type(right_result, AdmitReject):
            return right_result
        owned_left = left_result
        owned_right = right_result
        return _AdmitProgress((owned_left.value, owned_right.value), owned_right.state)
    return _AdmitProgress(source, next_state)


def _map_source_entries(
    source: object,
    schema_revision: str,
    map_schema_id: str,
    maximum_items: int,
) -> tuple[tuple[object, object], ...] | AdmitReject:
    if _has_exact_type(source, dict):
        if dict.__len__(source) > maximum_items:
            # Authority invariant: reject oversized maps before allocating a copy.
            return _reject(AdmitCode.ITEM_LIMIT, ())
        return tuple(dict.items(source))
    if _has_exact_type(source, OwnedMapV1):
        try:
            owned_revision = object.__getattribute__(source, "_schema_revision")
            owned_schema_id = object.__getattribute__(source, "_schema_id")
            entries = object.__getattribute__(source, "_entries")
            owned_index = object.__getattribute__(source, "_index")
        except AttributeError:
            return _reject(AdmitCode.REGISTRY_DRIFT, ())
        if (
            type(owned_revision) is not str
            or type(owned_schema_id) is not str
            or type(entries) is not tuple
            or type(owned_index) is not _MAPPING_PROXY_TYPE
        ):
            # Authority invariant: corrupt internals reject before behavior is invoked.
            return _reject(AdmitCode.REGISTRY_DRIFT, ())
        if owned_revision != schema_revision or owned_schema_id != map_schema_id:
            return _reject(AdmitCode.WRONG_CONTAINER, ())
        if len(entries) > maximum_items:
            return _reject(AdmitCode.ITEM_LIMIT, ())
        for entry in entries:
            if type(entry) is not tuple or len(entry) != 2:
                return _reject(AdmitCode.REGISTRY_DRIFT, ())
        return entries
    return _reject(AdmitCode.WRONG_CONTAINER, ())


def _owned_map_index_matches_entries(
    source: object,
    entries: tuple[tuple[object, object], ...],
) -> bool:
    if type(source) is not OwnedMapV1:
        return True
    index = object.__getattribute__(source, "_index")
    if type(index) is not _MAPPING_PROXY_TYPE:
        return False
    trusted_index = cast(Mapping[object, object], index)
    if len(trusted_index) != len(entries):
        return False
    # Inspect the exact built-in mapping proxy without hashing or comparing a
    # potentially corrupt stored key. The private identity index contains only
    # builtin integer IDs and never escapes this pure validation call.
    index_entries = tuple(trusted_index.items())
    by_identity = {id(key): (key, value) for key, value in index_entries}
    if len(by_identity) != len(entries):
        return False
    return all(
        id(key) in by_identity
        and by_identity[id(key)][0] is key
        and by_identity[id(key)][1] is value
        for key, value in entries
    )


def _map_value_path(path: FieldPath, key: object) -> FieldPath:
    if type(key) is str or type(key) is int:
        return path + (key,)
    return path


def _admit_map(
    schema: MapOf,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
    depth: int,
    registry: AdmissionRegistryV1,
    schema_revision: str,
) -> _AdmitProgress[object] | AdmitReject:
    maximum_items = min(schema.maximum_items, state.limits.max_collection_items)
    source_entries = _map_source_entries(
        source,
        schema_revision,
        schema.map_schema_id,
        maximum_items,
    )
    if _has_exact_type(source_entries, AdmitReject):
        return AdmitReject(source_entries.code, path)
    entries = source_entries
    item_count = len(entries)
    if item_count > maximum_items:
        return _reject(AdmitCode.ITEM_LIMIT, path)
    next_state = _consume_node(state, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    next_state = _enter_active(next_state, source, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    for key, _value in entries:
        if not _key_has_exact_shape(schema.key_schema, key, registry):
            return _reject(AdmitCode.WRONG_KEY_TYPE, path)
    key_resource_reject = _preflight_map_key_sort_bytes(
        schema,
        entries,
        next_state,
        path,
    )
    if key_resource_reject is not None:
        return key_resource_reject
    # Authority invariant: key errors are selected by canonical key order,
    # so rejected output cannot depend on caller dictionary insertion order.
    # Raw integers and enum ordinals are reduced to bounded tagged values.
    sorted_entries_with_keys = tuple(
        sorted(
            (
                (
                    _key_sort_value(schema.key_schema, key, registry),
                    key,
                    value,
                )
                for key, value in entries
            ),
            key=lambda entry: entry[0],
        )
    )
    sorted_entries = tuple((key, value) for _sort_key, key, value in sorted_entries_with_keys)

    for key, _value in sorted_entries:
        canonical_reject = _key_canonical_reject(
            schema.key_schema,
            key,
            path,
            registry,
            schema_revision,
        )
        if canonical_reject is not None:
            return canonical_reject
    for index in range(1, len(sorted_entries_with_keys)):
        if sorted_entries_with_keys[index - 1][0] == sorted_entries_with_keys[index][0]:
            return _reject(AdmitCode.REGISTRY_DRIFT, path)
    if type(source) is OwnedMapV1 and entries != sorted_entries:
        return _reject(AdmitCode.REGISTRY_DRIFT, path)
    if not _owned_map_index_matches_entries(source, sorted_entries):
        return _reject(AdmitCode.REGISTRY_DRIFT, path)

    owned_entries: list[tuple[object, object]] = []
    for key, value in sorted_entries:
        key_result = _admit_owned_key(
            schema.key_schema,
            key,
            next_state,
            path,
            depth + 1,
            registry,
            schema_revision,
        )
        if _has_exact_type(key_result, AdmitReject):
            return key_result
        admitted_key = key_result
        value_path = _map_value_path(path, key)
        result = _admit_value(
            schema.value_schema,
            value,
            admitted_key.state,
            value_path,
            depth + 1,
            registry,
            schema_revision,
        )
        if _has_exact_type(result, AdmitReject):
            return result
        admitted = result
        owned_entries.append((admitted_key.value, admitted.value))
        next_state = admitted.state
    return _AdmitProgress(
        _owned_map_from_admitted(
            tuple(owned_entries),
            schema_revision,
            schema.map_schema_id,
        ),
        _leave_active(next_state, source),
    )


def _admit_exact_keyed_map(
    schema: ExactKeyedMap,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
    depth: int,
    registry: AdmissionRegistryV1,
    schema_revision: str,
) -> _AdmitProgress[object] | AdmitReject:
    declared_count = len(schema.declared_fields)
    maximum_items = min(declared_count, state.limits.max_collection_items)
    source_entries = _map_source_entries(
        source,
        schema_revision,
        schema.map_schema_id,
        maximum_items,
    )
    if _has_exact_type(source_entries, AdmitReject):
        return AdmitReject(source_entries.code, path)
    if len(source_entries) != declared_count:
        return _reject(AdmitCode.ITEM_LIMIT, path)

    next_state = _consume_node(state, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    next_state = _enter_active(next_state, source, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state

    for key, _value in source_entries:
        if type(key) is not str:
            return _reject(AdmitCode.WRONG_KEY_TYPE, path)
    string_keyed_entries = tuple((cast(str, key), value) for key, value in source_entries)
    remaining_bytes = next_state.limits.max_canonical_bytes - next_state.trusted_scalar_bytes_used
    for key, _value in string_keyed_entries:
        key_length = _bounded_utf8_length(key, remaining_bytes)
        if key_length is None:
            return _reject(AdmitCode.NONCANONICAL_SCALAR, path)
        if key_length > remaining_bytes:
            return _reject(AdmitCode.BYTE_LIMIT, path)
        remaining_bytes -= key_length

    declared_names = tuple(field.name for field in schema.declared_fields)
    source_names = tuple(sorted(key for key, _value in string_keyed_entries))
    for source_name in source_names:
        if source_name not in declared_names:
            return _reject(AdmitCode.UNKNOWN_FIELD, path + (source_name,))
    for declared_name in declared_names:
        if declared_name not in source_names:
            return _reject(AdmitCode.MISSING_FIELD, path + (declared_name,))

    value_by_name = {key: value for key, value in string_keyed_entries}
    ordered_source_entries = tuple((name, value_by_name[name]) for name in declared_names)
    if type(source) is OwnedMapV1 and source_entries != ordered_source_entries:
        return _reject(AdmitCode.REGISTRY_DRIFT, path)
    if not _owned_map_index_matches_entries(source, ordered_source_entries):
        return _reject(AdmitCode.REGISTRY_DRIFT, path)

    owned_entries: list[tuple[object, object]] = []
    for declared_field in schema.declared_fields:
        field_path = path + (declared_field.name,)
        next_state = _consume_node(next_state, field_path)
        if _has_exact_type(next_state, AdmitReject):
            return next_state
        key_length = _bounded_utf8_length(
            declared_field.name,
            next_state.limits.max_canonical_bytes,
        )
        if key_length is None:  # pragma: no cover - registry validation excludes this
            return _reject(AdmitCode.REGISTRY_DRIFT, field_path)
        next_state = _consume_trusted_scalar_bytes(next_state, key_length, field_path)
        if _has_exact_type(next_state, AdmitReject):
            return next_state
        value_result = _admit_value(
            declared_field.schema,
            value_by_name[declared_field.name],
            next_state,
            field_path,
            depth + 1,
            registry,
            schema_revision,
        )
        if _has_exact_type(value_result, AdmitReject):
            return value_result
        owned_entries.append((declared_field.name, value_result.value))
        next_state = value_result.state

    return _AdmitProgress(
        _owned_map_from_admitted(
            tuple(owned_entries),
            schema_revision,
            schema.map_schema_id,
        ),
        _leave_active(next_state, source),
    )


def _registered_record_fields(registration: RecordRegistrationV1) -> tuple[str, ...]:
    return tuple(
        record_field.name
        for record_field in dataclass_fields(
            registration.source_type  # type: ignore[arg-type]
        )
    )


def _owned_record_fields(registration: RecordRegistrationV1) -> tuple[str, ...]:
    return tuple(
        record_field.name
        for record_field in dataclass_fields(
            registration.owned_type  # type: ignore[arg-type]
        )
    )


def _record_instance_field_reject(
    source: object,
    declared_names: tuple[str, ...],
    path: FieldPath,
) -> AdmitReject | None:
    try:
        instance_fields = object.__getattribute__(source, "__dict__")
    except AttributeError:
        return None
    if type(instance_fields) is not dict:
        return _reject(AdmitCode.REGISTRY_DRIFT, path)
    # Authority invariant: exact source types still cannot smuggle undeclared
    # attributes or inherit a class default through a malformed __dict__.
    observed_names: list[str] = []
    for field_name in dict.keys(instance_fields):
        if type(field_name) is not str or field_name not in declared_names:
            return _reject(AdmitCode.UNKNOWN_FIELD, path)
        observed_names.append(field_name)
    for field_name in declared_names:
        if field_name not in observed_names:
            return _reject(AdmitCode.MISSING_FIELD, path + (field_name,))
    return None


def _construct_owned_record(
    registration: RecordRegistrationV1,
    values: tuple[tuple[str, object], ...],
    state: _AdmissionState,
    path: FieldPath,
) -> _AdmitProgress[object] | AdmitReject:
    try:
        # Authority invariant: the profile owns construction and semantic checks;
        # declarative registry data never becomes executable constructor behavior.
        owned = state.record_construction_resolver(
            registration.tag,
            values,
        )
    except Exception:
        # Authority invariant: trusted resolver faults produce no partial output.
        return _reject(AdmitCode.DOMAIN_INVARIANT, path)
    if type(owned) is not registration.owned_type:
        return _reject(AdmitCode.REGISTRY_DRIFT, path)
    for field_name, admitted_value in values:
        try:
            owned_value = object.__getattribute__(owned, field_name)
        except AttributeError:
            return _reject(AdmitCode.REGISTRY_DRIFT, path)
        if owned_value is not admitted_value:
            # Authority invariant: the trusted resolver validates and packages
            # admitted children; it cannot normalize or replace their meaning.
            return _reject(AdmitCode.REGISTRY_DRIFT, path)
    return _AdmitProgress(owned, state)


def _admit_declared_record_fields(
    source: object,
    declared_fields: tuple[DeclaredFieldV1, ...],
    state: _AdmissionState,
    path: FieldPath,
    depth: int,
    registry: AdmissionRegistryV1,
    schema_revision: str,
) -> _AdmitProgress[tuple[tuple[str, object], ...]] | AdmitReject:
    values: list[tuple[str, object]] = []
    next_state = state
    for declared_field in declared_fields:
        field_path = path + (declared_field.name,)
        try:
            raw_value = object.__getattribute__(source, declared_field.name)
        except AttributeError:
            return _reject(AdmitCode.MISSING_FIELD, field_path)
        result = _admit_value(
            declared_field.schema,
            raw_value,
            next_state,
            field_path,
            depth + 1,
            registry,
            schema_revision,
        )
        if _has_exact_type(result, AdmitReject):
            return result
        admitted = result
        values.append((declared_field.name, admitted.value))
        next_state = admitted.state
    return _AdmitProgress(tuple(values), next_state)


def _admit_record(
    schema: RecordOf,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
    depth: int,
    registry: AdmissionRegistryV1,
    schema_revision: str,
) -> _AdmitProgress[object] | AdmitReject:
    registration = registry._record_registration(schema.record_tag)
    if registration is None:
        return _reject(AdmitCode.UNSUPPORTED_VARIANT, path)
    if type(source) not in {registration.source_type, registration.owned_type}:
        return _reject(AdmitCode.WRONG_EXACT_TYPE, path)
    declared_names = tuple(item.name for item in schema.declared_fields)
    if (
        _registered_record_fields(registration) != declared_names
        or _owned_record_fields(registration) != declared_names
    ):
        return _reject(AdmitCode.REGISTRY_DRIFT, path)
    unknown_field_reject = _record_instance_field_reject(
        source,
        declared_names,
        path,
    )
    if unknown_field_reject is not None:
        return unknown_field_reject
    next_state = _consume_node(state, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    next_state = _enter_active(next_state, source, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    values = _admit_declared_record_fields(
        source,
        schema.declared_fields,
        next_state,
        path,
        depth,
        registry,
        schema_revision,
    )
    if _has_exact_type(values, AdmitReject):
        return values
    admitted_values = values
    result = _construct_owned_record(
        registration,
        admitted_values.value,
        admitted_values.state,
        path,
    )
    if _has_exact_type(result, AdmitReject):
        return result
    admitted_record = result
    return _AdmitProgress(
        admitted_record.value,
        _leave_active(admitted_record.state, source),
    )


def _admit_record_union(
    schema: RecordUnionOf,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
    depth: int,
    registry: AdmissionRegistryV1,
    schema_revision: str,
) -> _AdmitProgress[object] | AdmitReject:
    source_type = type(source)
    for variant in schema.variants:
        registration = registry._record_registration(variant.record_tag)
        if registration is None:
            return _reject(AdmitCode.UNSUPPORTED_VARIANT, path)
        if source_type in {registration.source_type, registration.owned_type}:
            return _admit_record(
                variant,
                source,
                state,
                path,
                depth,
                registry,
                schema_revision,
            )
    return _reject(AdmitCode.WRONG_EXACT_TYPE, path)


def _tagged_registry_drift(
    schema: TaggedRecordOf,
    registration: RecordRegistrationV1,
    enum_registration: EnumRegistrationV1,
) -> bool:
    discriminants = tuple(variant.discriminant for variant in schema.variants)
    if discriminants != tuple(enum_registration.enum_type):
        return True
    registered = _registered_record_fields(registration)
    owned = _owned_record_fields(registration)
    if registered != owned:
        return True
    for variant in schema.variants:
        if type(variant.discriminant) is not enum_registration.enum_type:
            return True
        if not variant.declared_fields:
            return True
        field_names = tuple(field.name for field in variant.declared_fields)
        if field_names != registered:
            return True
        discriminant_schema = variant.declared_fields[0]
        if (
            discriminant_schema.name != schema.discriminant_field
            or not _has_exact_type(discriminant_schema.schema, ExactEnum)
            or discriminant_schema.schema.enum_tag is not schema.discriminant_enum_tag
        ):
            return True
    return False


def _admit_tagged_record(
    schema: TaggedRecordOf,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
    depth: int,
    registry: AdmissionRegistryV1,
    schema_revision: str,
) -> _AdmitProgress[object] | AdmitReject:
    registration = registry._record_registration(schema.record_tag)
    if registration is None:
        return _reject(AdmitCode.UNSUPPORTED_VARIANT, path)
    if type(source) not in {registration.source_type, registration.owned_type}:
        return _reject(AdmitCode.WRONG_EXACT_TYPE, path)
    enum_registration = registry._enum_registration(schema.discriminant_enum_tag)
    if enum_registration is None:
        return _reject(AdmitCode.UNSUPPORTED_VARIANT, path)
    if _tagged_registry_drift(schema, registration, enum_registration):
        return _reject(AdmitCode.REGISTRY_DRIFT, path)
    instance_field_reject = _record_instance_field_reject(
        source,
        _registered_record_fields(registration),
        path,
    )
    if instance_field_reject is not None:
        return instance_field_reject

    discriminant_path = path + (schema.discriminant_field,)
    try:
        discriminant = object.__getattribute__(source, schema.discriminant_field)
    except AttributeError:
        return _reject(AdmitCode.MISSING_FIELD, discriminant_path)
    member_ordinal: int | None = None
    if type(discriminant) is enum_registration.enum_type:
        for index, variant in enumerate(schema.variants):
            if variant.discriminant is discriminant:
                member_ordinal = index
                break
    elif type(discriminant) is OwnedEnumV1:
        tag_ordinal = registry._enum_registration_index(schema.discriminant_enum_tag)
        metadata = _owned_enum_metadata(discriminant)
        if metadata is None:
            return _reject(AdmitCode.REGISTRY_DRIFT, discriminant_path)
        owned_revision, owned_tag_ordinal, owned_member_ordinal = metadata
        if owned_revision != schema_revision or owned_tag_ordinal != tag_ordinal:
            return _reject(AdmitCode.WRONG_EXACT_TYPE, discriminant_path)
        member_ordinal = owned_member_ordinal
    else:
        return _reject(AdmitCode.WRONG_EXACT_TYPE, discriminant_path)
    if member_ordinal is None or member_ordinal >= len(schema.variants):
        return _reject(AdmitCode.UNSUPPORTED_VARIANT, discriminant_path)
    selected = schema.variants[member_ordinal]

    next_state = _consume_node(state, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    next_state = _enter_active(next_state, source, path)
    if _has_exact_type(next_state, AdmitReject):
        return next_state
    values = _admit_declared_record_fields(
        source,
        selected.declared_fields,
        next_state,
        path,
        depth,
        registry,
        schema_revision,
    )
    if _has_exact_type(values, AdmitReject):
        return values
    admitted_values = values
    result = _construct_owned_record(
        registration,
        admitted_values.value,
        admitted_values.state,
        path,
    )
    if _has_exact_type(result, AdmitReject):
        return result
    admitted_record = result
    return _AdmitProgress(
        admitted_record.value,
        _leave_active(admitted_record.state, source),
    )


def _admit_value(
    schema: SchemaV1,
    source: object,
    state: _AdmissionState,
    path: FieldPath,
    depth: int,
    registry: AdmissionRegistryV1,
    schema_revision: str,
) -> _AdmitProgress[object] | AdmitReject:
    depth_reject = _check_depth(state, depth, path)
    if depth_reject is not None:
        return depth_reject
    scalar_result = _admit_scalar(schema, source, state, path)
    if scalar_result is not None:
        return scalar_result
    if _has_exact_type(schema, ExactEnum):
        return _admit_enum(
            schema,
            source,
            state,
            path,
            registry,
            schema_revision,
        )
    if _has_exact_type(schema, OptionalValue):
        if source is None:
            next_state = _consume_node(state, path)
            if _has_exact_type(next_state, AdmitReject):
                return next_state
            return _AdmitProgress(None, next_state)
        return _admit_value(
            schema.inner,
            source,
            state,
            path,
            depth,
            registry,
            schema_revision,
        )
    if _has_exact_type(schema, SequenceOf):
        return _admit_sequence(
            schema,
            source,
            state,
            path,
            depth,
            registry,
            schema_revision,
        )
    if _has_exact_type(schema, ExactPair):
        return _admit_pair(
            schema,
            source,
            state,
            path,
            depth,
            registry,
            schema_revision,
        )
    if _has_exact_type(schema, MapOf):
        return _admit_map(
            schema,
            source,
            state,
            path,
            depth,
            registry,
            schema_revision,
        )
    if _has_exact_type(schema, ExactKeyedMap):
        return _admit_exact_keyed_map(
            schema,
            source,
            state,
            path,
            depth,
            registry,
            schema_revision,
        )
    if _has_exact_type(schema, RecordOf):
        return _admit_record(
            schema,
            source,
            state,
            path,
            depth,
            registry,
            schema_revision,
        )
    if _has_exact_type(schema, RecordUnionOf):
        return _admit_record_union(
            schema,
            source,
            state,
            path,
            depth,
            registry,
            schema_revision,
        )
    if _has_exact_type(schema, TaggedRecordOf):
        return _admit_tagged_record(
            schema,
            source,
            state,
            path,
            depth,
            registry,
            schema_revision,
        )
    return _reject(AdmitCode.UNSUPPORTED_VARIANT, path)


def _admit_with_registry_v1(
    registry: AdmissionRegistryV1,
    schema_revision: str,
    schema_id: str,
    validated_limits: ValidatedAdmissionLimitsV1,
    source: object,
    record_construction_resolver: RecordConstructionResolverV1,
    canonical_encoder_resolver: CanonicalEncoderResolverV1,
) -> AdmitOk[object] | AdmitReject:
    """Internal engine used by one source-pinned, four-argument profile facade.

    The mounted authority API must bind both resolvers in its own module. A
    transaction or caller never supplies registry or resolver behavior.
    """

    if type(registry) is not AdmissionRegistryV1:
        raise TypeError("admit requires an exact closed registry")
    if type(validated_limits) is not ValidatedAdmissionLimitsV1:
        raise TypeError("admit requires exact validated limits")
    if not _validated_limits_are_within_policy(validated_limits):
        # Authority invariant: source inspection starts only under a valid work budget.
        raise TypeError("admit requires validated limits within policy")
    if not _resolver_is_source_bound(record_construction_resolver) or not _resolver_is_source_bound(
        canonical_encoder_resolver
    ):
        raise TypeError("internal admission resolvers must be source-bound functions")
    if type(schema_revision) is not str or type(schema_id) is not str:
        return _reject(AdmitCode.UNSUPPORTED_VARIANT, ())
    if schema_revision != registry.schema_revision:
        return _reject(AdmitCode.UNSUPPORTED_VARIANT, ())
    registration = registry._schema_registration(schema_id)
    if registration is None:
        return _reject(AdmitCode.UNSUPPORTED_VARIANT, ())

    initial_state = _AdmissionState(validated_limits, record_construction_resolver)
    result = _admit_value(
        registration.schema,
        source,
        initial_state,
        (),
        0,
        registry,
        schema_revision,
    )
    if _has_exact_type(result, AdmitReject):
        return result
    try:
        admitted = result
        canonical_bytes = canonical_encoder_resolver(schema_id, admitted.value)
    except Exception:
        # Authority invariant: encoding faults never authorize an unbounded value.
        return _reject(AdmitCode.DOMAIN_INVARIANT, ())
    if type(canonical_bytes) is not bytes:
        return _reject(AdmitCode.REGISTRY_DRIFT, ())
    if len(canonical_bytes) > validated_limits.max_canonical_bytes:
        return _reject(AdmitCode.BYTE_LIMIT, ())
    return AdmitOk(admitted.value)


def format_admit_path(path: FieldPath) -> str:
    """Render a trusted stable path without rejected-object diagnostics."""

    rendered = "$"
    for part in path:
        if _has_exact_type(part, int):
            rendered += f"[{part}]"
        else:
            text_part = part
            escaped = text_part.replace("\\", "\\\\").replace('"', '\\"')
            rendered += f'["{escaped}"]'
    return rendered

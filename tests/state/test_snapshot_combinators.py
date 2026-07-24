from __future__ import annotations

import tracemalloc
from dataclasses import dataclass
from dataclasses import fields as dataclass_fields
from enum import Enum, IntEnum
from itertools import permutations
from types import MappingProxyType
from typing import cast, final

import pytest

from src.state.owned_collections import OwnedEnumV1, OwnedMapV1
from src.state.snapshot_combinators import (
    AdmissionLimitsV1,
    AdmissionRegistryV1,
    AdmitCode,
    AdmitOk,
    AdmitReject,
    BoundedJsonValue,
    DeclaredFieldV1,
    EnumRegistrationV1,
    ExactBool,
    ExactBytes,
    ExactEnum,
    ExactInt,
    ExactKeyedMap,
    ExactPair,
    ExactString,
    KeySortValue,
    LimitProfileCode,
    LimitProfileReject,
    MapOf,
    OptionalValue,
    RecordOf,
    RecordRegistrationV1,
    RecordUnionOf,
    SchemaRegistrationV1,
    SchemaV1,
    SequenceOf,
    SequenceSourceKind,
    StringRuleV1,
    TaggedRecordOf,
    TaggedVariantV1,
    ValidatedAdmissionLimitsV1,
    _admit_with_registry_v1,
    build_admission_limits_v1,
    build_admission_registry_v1,
    format_admit_path,
)


class _EnumTag(Enum):
    COLOR = "color"
    KIND = "kind"


class _RecordTag(Enum):
    POINT = "point"
    TAGGED = "tagged"


class _UnionEnumTag(Enum):
    pass


class _UnionRecordTag(Enum):
    LEFT = "left"
    RIGHT = "right"


class _Color(Enum):
    RED = "red"
    BLUE = "blue"


class _Kind(Enum):
    LEFT = "left"
    RIGHT = "right"


class _ForeignColor(Enum):
    RED = "red"


class _NumericColor(IntEnum):
    RED = 1


@dataclass
class _SourcePoint:
    x: int
    label: str


@final
@dataclass(frozen=True, slots=True)
class _OwnedPoint:
    x: int
    label: str


@dataclass
class _SourceTagged:
    kind: _Kind
    left: int | None = None
    right: str | None = None


@final
@dataclass(frozen=True, slots=True)
class _OwnedTagged:
    kind: OwnedEnumV1
    left: int | None = None
    right: str | None = None


@dataclass
class _SourceUnionLeft:
    amount: int


@final
@dataclass(frozen=True, slots=True)
class _OwnedUnionLeft:
    amount: int


@dataclass
class _SourceUnionRight:
    label: str


@final
@dataclass(frozen=True, slots=True)
class _OwnedUnionRight:
    label: str


def _canonical_bytes(_schema_id: str, value: object) -> bytes:
    if type(value) is OwnedMapV1:
        return repr(value.entries).encode("utf-8")
    return repr(value).encode("utf-8")


def _construct_record(
    tag: Enum,
    fields: tuple[tuple[str, object], ...],
) -> object:
    values = dict(fields)
    if tag is _RecordTag.POINT:
        return _OwnedPoint(
            cast(int, values["x"]),
            cast(str, values["label"]),
        )
    if tag is _RecordTag.TAGGED:
        return _OwnedTagged(
            cast(OwnedEnumV1, values["kind"]),
            cast(int | None, values["left"]),
            cast(str | None, values["right"]),
        )
    raise ValueError("unknown test record tag")


def _construct_union_record(
    tag: Enum,
    fields: tuple[tuple[str, object], ...],
) -> object:
    values = dict(fields)
    if tag is _UnionRecordTag.LEFT:
        return _OwnedUnionLeft(cast(int, values["amount"]))
    if tag is _UnionRecordTag.RIGHT:
        return _OwnedUnionRight(cast(str, values["label"]))
    raise ValueError("unknown union record tag")


def _five_canonical_bytes(_schema_id: str, _value: object) -> bytes:
    return b"12345"


def _empty_canonical_bytes(_schema_id: str, _value: object) -> bytes:
    return b""


def _bounded_json_schema(
    *,
    maximum_container_items: int = 8,
    maximum_integer_bits: int = 256,
    max_string_characters: int = 4_096,
    max_string_utf8_bytes: int = 16_384,
) -> BoundedJsonValue:
    return BoundedJsonValue(
        "test/json-object/v1",
        maximum_container_items,
        maximum_integer_bits,
        max_string_characters,
        max_string_utf8_bytes,
    )


def _construct_wrong_point(
    tag: Enum,
    fields: tuple[tuple[str, object], ...],
) -> object:
    if tag is not _RecordTag.POINT:
        raise ValueError("wrong test record tag")
    values = dict(fields)
    return _OwnedPoint(
        cast(int, values["x"]) + 1,
        cast(str, values["label"]),
    )


def _registry(schema: object):
    return build_admission_registry_v1(
        schema_revision="test-v1",
        enum_tag_type=_EnumTag,
        record_tag_type=_RecordTag,
        enum_registrations=(
            EnumRegistrationV1(_EnumTag.COLOR, _Color),
            EnumRegistrationV1(_EnumTag.KIND, _Kind),
        ),
        record_registrations=(
            RecordRegistrationV1(
                _RecordTag.POINT,
                _SourcePoint,
                _OwnedPoint,
            ),
            RecordRegistrationV1(
                _RecordTag.TAGGED,
                _SourceTagged,
                _OwnedTagged,
            ),
        ),
        schema_registrations=(SchemaRegistrationV1("test/root/v1", schema),),
    )


def _limits(
    *,
    max_depth: int = 16,
    max_nodes: int = 100,
    max_canonical_bytes: int = 10_000,
    max_collection_items: int = 100,
) -> ValidatedAdmissionLimitsV1:
    result = build_admission_limits_v1(
        AdmissionLimitsV1(
            max_depth=max_depth,
            max_nodes=max_nodes,
            max_canonical_bytes=max_canonical_bytes,
            max_collection_items=max_collection_items,
        )
    )
    assert type(result) is ValidatedAdmissionLimitsV1
    return result


def _admit(schema: object, source: object, *, limits=None, encoder=_canonical_bytes):
    # Test-only synthetic profiles exercise the private engine directly. Production
    # callers must use the source-pinned four-argument facade in state_admission_profile.
    return _admit_with_registry_v1(
        _registry(schema),
        "test-v1",
        "test/root/v1",
        _limits() if limits is None else limits,
        source,
        _construct_record,
        encoder,
    )


def _admit_union(schema: object, source: object):
    registry = build_admission_registry_v1(
        schema_revision="test-union-v1",
        enum_tag_type=_UnionEnumTag,
        record_tag_type=_UnionRecordTag,
        enum_registrations=(),
        record_registrations=(
            RecordRegistrationV1(
                _UnionRecordTag.LEFT,
                _SourceUnionLeft,
                _OwnedUnionLeft,
            ),
            RecordRegistrationV1(
                _UnionRecordTag.RIGHT,
                _SourceUnionRight,
                _OwnedUnionRight,
            ),
        ),
        schema_registrations=(SchemaRegistrationV1("test/union/v1", schema),),
    )
    return _admit_with_registry_v1(
        registry,
        "test-union-v1",
        "test/union/v1",
        _limits(),
        source,
        _construct_union_record,
        _canonical_bytes,
    )


def test_exact_int_bounds_and_bool_subclass_rejection() -> None:
    schema = ExactInt(-2, 2)
    assert _admit(schema, -2) == AdmitOk(-2)
    assert _admit(schema, 2) == AdmitOk(2)
    assert _admit(schema, -3) == AdmitReject(AdmitCode.OUT_OF_RANGE, ())
    assert _admit(schema, 3) == AdmitReject(AdmitCode.OUT_OF_RANGE, ())
    assert _admit(schema, True) == AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ())

    class _IntSubclass(int):
        pass

    assert _admit(schema, _IntSubclass(1)) == AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ())


def test_exact_int_open_endpoints_preserve_unbounded_mounted_domains() -> None:
    assert _admit(ExactInt(None, None), -(1 << 4096)) == AdmitOk(-(1 << 4096))
    assert _admit(ExactInt(None, 2), -3) == AdmitOk(-3)
    assert _admit(ExactInt(-2, None), 1 << 4096) == AdmitOk(1 << 4096)
    assert _admit(ExactInt(None, 2), 3) == AdmitReject(AdmitCode.OUT_OF_RANGE, ())
    assert _admit(ExactInt(-2, None), -3) == AdmitReject(AdmitCode.OUT_OF_RANGE, ())


def test_exact_int_rejects_before_integer_conversion_hook() -> None:
    class _IntegerLike:
        called = False

        def __int__(self) -> int:
            self.called = True
            raise AssertionError("must not execute")

    source = _IntegerLike()
    assert _admit(ExactInt(0, 2), source) == AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ())
    assert source.called is False


@pytest.mark.parametrize("source", [0, 1, object()])
def test_exact_bool_accepts_only_exact_bool(source: object) -> None:
    assert _admit(ExactBool(), source) == AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ())
    assert _admit(ExactBool(), True) == AdmitOk(True)
    assert _admit(ExactBool(), False) == AdmitOk(False)


def test_string_and_bytes_are_exact_bounded_builtins() -> None:
    string_schema = ExactString(StringRuleV1.NON_EMPTY, 3)
    assert _admit(string_schema, "abc") == AdmitOk("abc")
    assert _admit(string_schema, "") == AdmitReject(AdmitCode.NONCANONICAL_SCALAR, ())
    assert _admit(string_schema, "four") == AdmitReject(AdmitCode.BYTE_LIMIT, ())
    multibyte_schema = ExactString(StringRuleV1.NON_EMPTY, 4)
    assert _admit(multibyte_schema, "éé") == AdmitOk("éé")
    assert _admit(multibyte_schema, "ééé") == AdmitReject(
        AdmitCode.BYTE_LIMIT,
        (),
    )


def test_string_character_and_utf8_work_bounds_are_independent() -> None:
    four_characters = ExactString(
        StringRuleV1.NON_EMPTY,
        max_utf8_bytes=16,
        max_characters=4,
    )
    assert _admit(four_characters, "éééé") == AdmitOk("éééé")
    assert _admit(four_characters, "𐍈𐍈𐍈𐍈") == AdmitOk("𐍈𐍈𐍈𐍈")
    assert _admit(four_characters, "abcde") == AdmitReject(AdmitCode.BYTE_LIMIT, ())

    seven_bytes = ExactString(
        StringRuleV1.NON_EMPTY,
        max_utf8_bytes=7,
        max_characters=4,
    )
    assert _admit(seven_bytes, "éééé") == AdmitReject(AdmitCode.BYTE_LIMIT, ())

    map_schema = MapOf(
        four_characters,
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    assert type(_admit(map_schema, {"éééé": 1})) is AdmitOk
    assert _admit(map_schema, {"abcde": 1}) == AdmitReject(AdmitCode.BYTE_LIMIT, ())


def test_invalid_utf8_scalar_and_map_key_return_typed_rejection() -> None:
    surrogate = "\ud800"
    string_schema = ExactString(StringRuleV1.EXACT_TEXT, 8)
    assert _admit(string_schema, surrogate) == AdmitReject(
        AdmitCode.NONCANONICAL_SCALAR,
        (),
    )

    map_schema = MapOf(string_schema, ExactInt(0, 9), 4, "test/map/v1")
    assert _admit(map_schema, {surrogate: 1}) == AdmitReject(
        AdmitCode.NONCANONICAL_SCALAR,
        (),
    )

    class _StringSubclass(str):
        pass

    assert _admit(string_schema, _StringSubclass("abc")) == AdmitReject(
        AdmitCode.WRONG_EXACT_TYPE, ()
    )

    bytes_schema = ExactBytes(exact_length=None, max_length=3)
    assert _admit(bytes_schema, b"abc") == AdmitOk(b"abc")
    assert _admit(bytes_schema, bytearray(b"abc")) == AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ())
    assert _admit(bytes_schema, b"four") == AdmitReject(AdmitCode.BYTE_LIMIT, ())


def test_exact_literal_is_data_not_a_callback() -> None:
    schema = ExactString(
        StringRuleV1.EXACT_LITERAL,
        8,
        exact_literal="literal",
    )
    assert _admit(schema, "literal") == AdmitOk("literal")
    assert _admit(schema, "LITERAL") == AdmitReject(AdmitCode.NONCANONICAL_SCALAR, ())


def test_lowercase_prefixed_hex_has_one_exact_spelling() -> None:
    schema = ExactString(
        StringRuleV1.LOWERCASE_0X_HEX,
        6,
        exact_utf8_bytes=6,
    )
    assert _admit(schema, "0x01af") == AdmitOk("0x01af")
    for source in ("01af", "0X01af", "0x01AF", "0x", "0x1af"):
        assert _admit(schema, source) == AdmitReject(
            AdmitCode.NONCANONICAL_SCALAR,
            (),
        )
    assert _admit(schema, " 0x01af") == AdmitReject(AdmitCode.BYTE_LIMIT, ())


@pytest.mark.parametrize(
    "source",
    [_ForeignColor.RED, _NumericColor.RED, 1, "red"],
)
def test_exact_enum_accepts_only_registered_exact_enum(source: object) -> None:
    schema = ExactEnum(_EnumTag.COLOR)
    accepted = _admit(schema, _Color.RED)
    assert type(accepted) is AdmitOk
    assert type(accepted.value) is OwnedEnumV1
    assert accepted.value.schema_revision == "test-v1"
    assert accepted.value.enum_tag_ordinal == 0
    assert accepted.value.member_ordinal == 0
    assert _admit(schema, source) == AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ())


def test_exact_enum_detaches_mutable_member_value_alias() -> None:
    payload: list[int] = []

    class _MutableColor(Enum):
        RED = payload

    registry = build_admission_registry_v1(
        schema_revision="test-v1",
        enum_tag_type=_EnumTag,
        record_tag_type=_RecordTag,
        enum_registrations=(
            EnumRegistrationV1(_EnumTag.COLOR, _MutableColor),
            EnumRegistrationV1(_EnumTag.KIND, _Kind),
        ),
        record_registrations=(
            RecordRegistrationV1(_RecordTag.POINT, _SourcePoint, _OwnedPoint),
            RecordRegistrationV1(_RecordTag.TAGGED, _SourceTagged, _OwnedTagged),
        ),
        schema_registrations=(SchemaRegistrationV1("test/root/v1", ExactEnum(_EnumTag.COLOR)),),
    )
    accepted = _admit_with_registry_v1(
        registry,
        "test-v1",
        "test/root/v1",
        _limits(),
        _MutableColor.RED,
        _construct_record,
        _canonical_bytes,
    )
    assert type(accepted) is AdmitOk
    assert type(accepted.value) is OwnedEnumV1
    before = repr(accepted.value)

    payload.append(7)

    assert repr(accepted.value) == before
    assert not hasattr(accepted.value, "__dict__")


def test_owned_enum_cannot_be_publicly_constructed_or_reinitialized() -> None:
    accepted = _admit(ExactEnum(_EnumTag.COLOR), _Color.RED)
    assert type(accepted) is AdmitOk
    owned = cast(OwnedEnumV1, accepted.value)

    with pytest.raises(TypeError):
        OwnedEnumV1("test-v1", 0, 0)
    with pytest.raises(TypeError, match="already initialized"):
        OwnedEnumV1.__init__(owned, "test-v1", 0, 1)


def test_owned_enum_is_revalidated_and_reconstructed() -> None:
    first = _admit(ExactEnum(_EnumTag.COLOR), _Color.BLUE)
    assert type(first) is AdmitOk

    second = _admit(ExactEnum(_EnumTag.COLOR), first.value)

    assert second == first
    assert type(second) is AdmitOk
    assert second.value is not first.value


def test_corrupted_owned_enum_rejects_before_hostile_metadata_behavior() -> None:
    class _HostileOrdinal:
        calls = 0

        def __index__(self) -> int:
            type(self).calls += 1
            raise AssertionError("must not coerce")

    first = _admit(ExactEnum(_EnumTag.COLOR), _Color.RED)
    assert type(first) is AdmitOk
    object.__setattr__(first.value, "_member_ordinal", _HostileOrdinal())

    assert _admit(ExactEnum(_EnumTag.COLOR), first.value) == AdmitReject(
        AdmitCode.REGISTRY_DRIFT,
        (),
    )
    assert _HostileOrdinal.calls == 0


def test_sequence_accepts_only_declared_exact_source_kinds() -> None:
    list_schema = SequenceOf(
        (SequenceSourceKind.EXACT_LIST,),
        ExactInt(0, 9),
        0,
        3,
    )
    assert _admit(list_schema, [1, 2]) == AdmitOk((1, 2))
    assert _admit(list_schema, (1, 2)) == AdmitReject(AdmitCode.WRONG_CONTAINER, ())

    class _ListSubclass(list[int]):
        pass

    class _HostileIterable:
        called = False

        def __iter__(self):
            self.called = True
            raise AssertionError("must not iterate")

    hostile = _HostileIterable()
    for source in (_ListSubclass([1]), hostile, {1}, frozenset({1}), (x for x in [1])):
        assert _admit(list_schema, source) == AdmitReject(AdmitCode.WRONG_CONTAINER, ())
    assert hostile.called is False


def test_exact_pair_owns_children_in_order() -> None:
    schema = ExactPair(ExactInt(0, 9), ExactString(StringRuleV1.NON_EMPTY, 4))
    assert _admit(schema, (2, "ok")) == AdmitOk((2, "ok"))
    assert _admit(schema, [2, "ok"]) == AdmitReject(AdmitCode.WRONG_CONTAINER, ())


def test_map_rejects_broad_or_subclass_sources_without_hooks() -> None:
    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )

    class _DictSubclass(dict[str, int]):
        called = False

        def items(self):
            self.called = True
            raise AssertionError("must not call items")

    source = _DictSubclass({"a": 1})
    assert _admit(schema, source) == AdmitReject(AdmitCode.WRONG_CONTAINER, ())
    assert source.called is False


def test_map_is_owned_and_canonically_ordered() -> None:
    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    source = {"b": 2, "a": 1}
    result = _admit(schema, source)
    assert type(result) is AdmitOk
    owned = result.value
    assert type(owned) is OwnedMapV1
    assert owned.entries == (("a", 1), ("b", 2))
    permuted = _admit(schema, {"a": 1, "b": 2})
    assert type(permuted) is AdmitOk
    assert permuted.value == owned
    source["a"] = 9
    assert owned["a"] == 1


def test_exact_keyed_map_uses_declared_order_and_per_key_schema() -> None:
    schema = ExactKeyedMap(
        (
            DeclaredFieldV1("count", ExactInt(0, 9)),
            DeclaredFieldV1("enabled", ExactBool()),
        ),
        "test/keyed-map/v1",
    )
    first = _admit(schema, {"enabled": True, "count": 2})
    second = _admit(schema, {"count": 2, "enabled": True})
    assert type(first) is AdmitOk
    assert type(second) is AdmitOk
    assert type(first.value) is OwnedMapV1
    assert first.value.entries == (("count", 2), ("enabled", True))
    assert second.value == first.value

    revalidated = _admit(schema, first.value)
    assert type(revalidated) is AdmitOk
    assert revalidated.value == first.value
    assert revalidated.value is not first.value

    assert _admit(schema, {"count": 2, "enabled": 1}) == AdmitReject(
        AdmitCode.WRONG_EXACT_TYPE,
        ("enabled",),
    )
    assert _admit(schema, {"count": 2, "extra": True}) == AdmitReject(
        AdmitCode.UNKNOWN_FIELD,
        ("extra",),
    )


def test_exact_keyed_map_cardinality_rejects_before_field_inspection() -> None:
    schema = ExactKeyedMap(
        (DeclaredFieldV1("required", ExactInt(0, 9)),),
        "test/keyed-map/v1",
    )
    assert _admit(schema, {}) == AdmitReject(AdmitCode.ITEM_LIMIT, ())
    assert _admit(schema, {"required": 1, "extra": object()}) == AdmitReject(
        AdmitCode.ITEM_LIMIT,
        (),
    )


def test_exact_keyed_map_declares_optional_members_without_adapter_logic() -> None:
    schema = ExactKeyedMap(
        (
            DeclaredFieldV1("required", ExactInt(0, 9)),
            DeclaredFieldV1("optional", OptionalValue(ExactInt(0, 9))),
        ),
        "test/optional-keyed-map/v1",
        ("required",),
    )
    absent = _admit(schema, {"required": 2})
    explicit_none = _admit(schema, {"optional": None, "required": 2})
    assert type(absent) is AdmitOk
    assert type(explicit_none) is AdmitOk
    assert cast(OwnedMapV1[object, object], absent.value).entries == (
        ("required", 2),
    )
    assert cast(OwnedMapV1[object, object], explicit_none.value).entries == (
        ("required", 2),
        ("optional", None),
    )
    assert absent.value != explicit_none.value

    revalidated = _admit(schema, explicit_none.value)
    assert revalidated == explicit_none
    assert type(revalidated) is AdmitOk
    assert revalidated.value is not explicit_none.value

    assert _admit(schema, {"optional": 1}) == AdmitReject(
        AdmitCode.MISSING_FIELD,
        ("required",),
    )
    assert _admit(schema, {"extra": 1}) == AdmitReject(
        AdmitCode.UNKNOWN_FIELD,
        ("extra",),
    )


@pytest.mark.parametrize(
    "required_names, error_type, message",
    [
        (["first"], TypeError, "exact tuple"),
        (("first", "first"), ValueError, "unique"),
        (("unknown",), ValueError, "not declared"),
        (("second", "first"), ValueError, "declared order"),
        ((1,), TypeError, "exact strings"),
    ],
)
def test_registry_rejects_invalid_exact_keyed_map_required_sets(
    required_names: object,
    error_type: type[Exception],
    message: str,
) -> None:
    schema = ExactKeyedMap(
        (
            DeclaredFieldV1("first", ExactInt(0, 9)),
            DeclaredFieldV1("second", ExactInt(0, 9)),
        ),
        "test/optional-keyed-map/v1",
        cast(tuple[str, ...], required_names),
    )
    with pytest.raises(error_type, match=message):
        _registry(schema)


def test_bounded_json_recursively_owns_and_canonically_orders_values() -> None:
    schema = _bounded_json_schema()
    inner = {"beta": "ok"}
    items = [None, True, 7]
    source: dict[str, object] = {"z": items, "a": inner}

    first = _admit(schema, source)
    second = _admit(schema, {"a": {"beta": "ok"}, "z": [None, True, 7]})
    assert type(first) is AdmitOk
    assert type(second) is AdmitOk
    assert type(first.value) is OwnedMapV1
    owned = cast(OwnedMapV1[str, object], first.value)
    assert owned.entries[0][0] == "a"
    assert owned.entries[1] == ("z", (None, True, 7))
    assert type(owned["a"]) is OwnedMapV1
    assert cast(OwnedMapV1[str, object], owned["a"]).entries == (("beta", "ok"),)
    assert second.value == first.value

    inner["beta"] = "changed"
    items.append(9)
    source["new"] = False
    assert cast(OwnedMapV1[str, object], owned["a"])["beta"] == "ok"
    assert owned["z"] == (None, True, 7)
    assert "new" not in owned

    revalidated = _admit(schema, owned)
    assert revalidated == first
    assert type(revalidated) is AdmitOk
    assert revalidated.value is not owned
    rebuilt = cast(OwnedMapV1[str, object], revalidated.value)
    assert rebuilt["a"] is not owned["a"]


def test_bounded_json_rejects_unsupported_exact_types_without_hooks() -> None:
    class _DictSubclass(dict[str, object]):
        called = False

        def items(self):
            self.called = True
            raise AssertionError("must not call")

    class _Hostile:
        called = False

        def __iter__(self):
            self.called = True
            raise AssertionError("must not iterate")

    schema = _bounded_json_schema()
    subclass = _DictSubclass({"a": 1})
    hostile = _Hostile()
    for source in (1.0, b"bytes", subclass, hostile):
        assert _admit(schema, source) == AdmitReject(
            AdmitCode.WRONG_EXACT_TYPE,
            (),
        )
    assert subclass.called is False
    assert hostile.called is False


def test_bounded_json_enforces_integer_and_string_bounds() -> None:
    integer_schema = _bounded_json_schema(maximum_integer_bits=4)
    assert _admit(integer_schema, 15) == AdmitOk(15)
    assert _admit(integer_schema, -15) == AdmitOk(-15)
    assert _admit(integer_schema, 16) == AdmitReject(AdmitCode.OUT_OF_RANGE, ())
    assert _admit(integer_schema, -16) == AdmitReject(AdmitCode.OUT_OF_RANGE, ())

    string_schema = _bounded_json_schema(
        max_string_characters=2,
        max_string_utf8_bytes=4,
    )
    assert _admit(string_schema, "éé") == AdmitOk("éé")
    assert _admit(string_schema, "abc") == AdmitReject(AdmitCode.BYTE_LIMIT, ())
    assert _admit(string_schema, "𐍈x") == AdmitReject(AdmitCode.BYTE_LIMIT, ())


def test_bounded_json_uses_shared_cycle_depth_node_item_and_byte_budgets() -> None:
    schema = _bounded_json_schema(maximum_container_items=2)
    direct: list[object] = []
    direct.append(direct)
    assert _admit(schema, direct) == AdmitReject(AdmitCode.CYCLE, (0,))

    mapping: dict[str, object] = {}
    mapping["self"] = mapping
    assert _admit(schema, mapping) == AdmitReject(AdmitCode.CYCLE, ("self",))

    assert _admit(schema, [[]], limits=_limits(max_depth=1)) == AdmitOk(((),))
    assert _admit(schema, [[None]], limits=_limits(max_depth=1)) == AdmitReject(
        AdmitCode.DEPTH_LIMIT,
        (0, 0),
    )
    assert _admit(
        schema,
        [None],
        limits=_limits(max_nodes=2, max_collection_items=2),
    ) == AdmitOk((None,))
    assert _admit(
        schema,
        [None, None],
        limits=_limits(max_nodes=2, max_collection_items=2),
    ) == AdmitReject(AdmitCode.ITEM_LIMIT, (1,))
    assert _admit(schema, [1, 2, 3]) == AdmitReject(AdmitCode.ITEM_LIMIT, ())
    assert _admit(
        schema,
        {"a": "éé"},
        limits=_limits(max_canonical_bytes=4),
        encoder=_empty_canonical_bytes,
    ) == AdmitReject(AdmitCode.BYTE_LIMIT, ("a",))


def test_bounded_json_rejects_corrupted_owned_map_order() -> None:
    schema = _bounded_json_schema()
    accepted = _admit(schema, {"a": 1, "b": 2})
    assert type(accepted) is AdmitOk
    owned = cast(OwnedMapV1[str, object], accepted.value)
    object.__setattr__(owned, "_entries", tuple(reversed(owned.entries)))

    assert _admit(schema, owned) == AdmitReject(AdmitCode.REGISTRY_DRIFT, ())


def test_enum_map_keys_are_copied_into_owned_ordinals() -> None:
    schema = MapOf(
        ExactEnum(_EnumTag.COLOR),
        ExactInt(0, 9),
        4,
        "test/enum-map/v1",
    )
    result = _admit(schema, {_Color.BLUE: 2, _Color.RED: 1})
    assert type(result) is AdmitOk
    owned = cast(OwnedMapV1[OwnedEnumV1, int], result.value)
    assert tuple(key.member_ordinal for key in owned) == (0, 1)
    assert all(type(key) is OwnedEnumV1 for key in owned)

    revalidated = _admit(schema, owned)
    assert type(revalidated) is AdmitOk
    assert revalidated.value == owned
    assert revalidated.value is not owned


def test_map_wrong_key_type_rejects_before_hash_or_ordering() -> None:
    class _HostileKey:
        calls = 0

        def __hash__(self) -> int:
            type(self).calls += 1
            return 1

        def __lt__(self, _other: object) -> bool:
            type(self).calls += 1
            raise AssertionError("must not order")

    key = _HostileKey()
    source = {key: 1}
    _HostileKey.calls = 0
    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    assert _admit(schema, source) == AdmitReject(AdmitCode.WRONG_KEY_TYPE, ())
    assert _HostileKey.calls == 0


def test_record_accepts_only_registered_exact_source() -> None:
    schema = RecordOf(
        _RecordTag.POINT,
        (
            DeclaredFieldV1("x", ExactInt(0, 9)),
            DeclaredFieldV1("label", ExactString(StringRuleV1.NON_EMPTY, 8)),
        ),
    )
    assert _admit(schema, _SourcePoint(3, "p")) == AdmitOk(_OwnedPoint(3, "p"))
    assert _admit(schema, _OwnedPoint(3, "p")) == AdmitOk(_OwnedPoint(3, "p"))

    @dataclass
    class _Lookalike:
        x: int
        label: str

    class _PointSubclass(_SourcePoint):
        pass

    for source in (_Lookalike(3, "p"), _PointSubclass(3, "p"), {"x": 3}):
        assert _admit(schema, source) == AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ())


def test_record_union_dispatches_only_by_registered_exact_source_type() -> None:
    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        RecordUnionOf(
            (
                RecordOf(
                    _UnionRecordTag.LEFT,
                    (DeclaredFieldV1("amount", ExactInt(0, 9)),),
                ),
                RecordOf(
                    _UnionRecordTag.RIGHT,
                    (
                        DeclaredFieldV1(
                            "label",
                            ExactString(StringRuleV1.NON_EMPTY, 8),
                        ),
                    ),
                ),
            )
        ),
        4,
        "test/union-map/v1",
    )
    result = _admit_union(
        schema,
        {
            "left": _SourceUnionLeft(3),
            "right": _SourceUnionRight("r"),
        },
    )
    assert type(result) is AdmitOk
    assert type(result.value) is OwnedMapV1
    assert result.value["left"] == _OwnedUnionLeft(3)
    assert result.value["right"] == _OwnedUnionRight("r")

    class _HostileLeft(_SourceUnionLeft):
        inspected = False

        def __getattribute__(self, name: str):
            if name not in {"inspected", "__class__"}:
                type(self).inspected = True
                raise AssertionError("record union must reject before field access")
            return object.__getattribute__(self, name)

    @dataclass
    class _LookalikeLeft:
        amount: int

    _HostileLeft.inspected = False
    assert _admit_union(schema, {"bad": _HostileLeft(3)}) == AdmitReject(
        AdmitCode.WRONG_EXACT_TYPE,
        ("bad",),
    )
    assert _HostileLeft.inspected is False
    assert _admit_union(schema, {"bad": _LookalikeLeft(3)}) == AdmitReject(
        AdmitCode.WRONG_EXACT_TYPE,
        ("bad",),
    )


@pytest.mark.parametrize(
    "registrations, message",
    [
        (
            (
                RecordRegistrationV1(
                    _UnionRecordTag.LEFT,
                    _SourceUnionLeft,
                    _OwnedUnionLeft,
                ),
                RecordRegistrationV1(
                    _UnionRecordTag.RIGHT,
                    _SourceUnionLeft,
                    _OwnedUnionRight,
                ),
            ),
            "source types must be unique",
        ),
        (
            (
                RecordRegistrationV1(
                    _UnionRecordTag.LEFT,
                    _SourceUnionLeft,
                    _OwnedUnionLeft,
                ),
                RecordRegistrationV1(
                    _UnionRecordTag.RIGHT,
                    _SourceUnionRight,
                    _OwnedUnionLeft,
                ),
            ),
            "owned types must be unique",
        ),
    ],
)
def test_record_registry_rejects_ambiguous_union_types(
    registrations: tuple[RecordRegistrationV1, ...],
    message: str,
) -> None:
    with pytest.raises(ValueError, match=message):
        build_admission_registry_v1(
            schema_revision="test-union-v1",
            enum_tag_type=_UnionEnumTag,
            record_tag_type=_UnionRecordTag,
            enum_registrations=(),
            record_registrations=registrations,
            schema_registrations=(SchemaRegistrationV1("test/union/v1", ExactInt(0, 1)),),
        )


def test_record_registry_field_drift_fails_closed() -> None:
    schema = RecordOf(
        _RecordTag.POINT,
        (DeclaredFieldV1("x", ExactInt(0, 9)),),
    )
    assert _admit(schema, _SourcePoint(3, "p")) == AdmitReject(AdmitCode.REGISTRY_DRIFT, ())


def test_record_rejects_instance_fields_outside_closed_schema() -> None:
    schema = RecordOf(
        _RecordTag.POINT,
        (
            DeclaredFieldV1("x", ExactInt(0, 9)),
            DeclaredFieldV1("label", ExactString(StringRuleV1.NON_EMPTY, 8)),
        ),
    )
    source = _SourcePoint(3, "p")
    source.unregistered = 7

    assert _admit(schema, source) == AdmitReject(AdmitCode.UNKNOWN_FIELD, ())


def test_record_rejects_deleted_instance_field_instead_of_using_class_default() -> None:
    @dataclass
    class _DefaultSourcePoint:
        x: int = 5
        label: str = "default"

    schema = RecordOf(
        _RecordTag.POINT,
        (
            DeclaredFieldV1("x", ExactInt(0, 9)),
            DeclaredFieldV1("label", ExactString(StringRuleV1.NON_EMPTY, 8)),
        ),
    )
    registry = build_admission_registry_v1(
        schema_revision="test-v1",
        enum_tag_type=_EnumTag,
        record_tag_type=_RecordTag,
        enum_registrations=(
            EnumRegistrationV1(_EnumTag.COLOR, _Color),
            EnumRegistrationV1(_EnumTag.KIND, _Kind),
        ),
        record_registrations=(
            RecordRegistrationV1(
                _RecordTag.POINT,
                _DefaultSourcePoint,
                _OwnedPoint,
            ),
            RecordRegistrationV1(
                _RecordTag.TAGGED,
                _SourceTagged,
                _OwnedTagged,
            ),
        ),
        schema_registrations=(SchemaRegistrationV1("test/root/v1", schema),),
    )
    source = _DefaultSourcePoint()
    del source.x

    result = _admit_with_registry_v1(
        registry,
        "test-v1",
        "test/root/v1",
        _limits(),
        source,
        _construct_record,
        _canonical_bytes,
    )

    assert result == AdmitReject(AdmitCode.MISSING_FIELD, ("x",))


def test_record_resolver_cannot_replace_an_admitted_child() -> None:
    schema = RecordOf(
        _RecordTag.POINT,
        (
            DeclaredFieldV1("x", ExactInt(0, 9)),
            DeclaredFieldV1("label", ExactString(StringRuleV1.NON_EMPTY, 8)),
        ),
    )
    result = _admit_with_registry_v1(
        _registry(schema),
        "test-v1",
        "test/root/v1",
        _limits(),
        _SourcePoint(3, "p"),
        _construct_wrong_point,
        _canonical_bytes,
    )
    assert result == AdmitReject(AdmitCode.REGISTRY_DRIFT, ())


def test_registry_rejects_mutable_owned_record_before_admission() -> None:
    @dataclass
    class _MutableOwnedPoint:
        x: int
        label: str

    with pytest.raises(TypeError, match="frozen slotted final"):
        build_admission_registry_v1(
            schema_revision="test-v1",
            enum_tag_type=_EnumTag,
            record_tag_type=_RecordTag,
            enum_registrations=(
                EnumRegistrationV1(_EnumTag.COLOR, _Color),
                EnumRegistrationV1(_EnumTag.KIND, _Kind),
            ),
            record_registrations=(
                RecordRegistrationV1(
                    _RecordTag.POINT,
                    _SourcePoint,
                    _MutableOwnedPoint,
                ),
                RecordRegistrationV1(
                    _RecordTag.TAGGED,
                    _SourceTagged,
                    _OwnedTagged,
                ),
            ),
            schema_registrations=(SchemaRegistrationV1("test/root/v1", ExactInt(0, 1)),),
        )


def test_registry_rejects_owned_record_with_hidden_mutable_slot() -> None:
    class _HiddenMutableBase:
        __slots__ = ("hidden",)

    @final
    @dataclass(frozen=True, slots=True)
    class _OwnedWithHiddenSlot(_HiddenMutableBase):
        x: int
        label: str

        def __post_init__(self) -> None:
            object.__setattr__(self, "hidden", [])

    with pytest.raises(TypeError, match="frozen slotted final"):
        build_admission_registry_v1(
            schema_revision="test-v1",
            enum_tag_type=_EnumTag,
            record_tag_type=_RecordTag,
            enum_registrations=(
                EnumRegistrationV1(_EnumTag.COLOR, _Color),
                EnumRegistrationV1(_EnumTag.KIND, _Kind),
            ),
            record_registrations=(
                RecordRegistrationV1(
                    _RecordTag.POINT,
                    _SourcePoint,
                    _OwnedWithHiddenSlot,
                ),
                RecordRegistrationV1(
                    _RecordTag.TAGGED,
                    _SourceTagged,
                    _OwnedTagged,
                ),
            ),
            schema_registrations=(SchemaRegistrationV1("test/root/v1", ExactInt(0, 1)),),
        )


def test_registry_rejects_enum_aliases() -> None:
    class _AliasedColor(Enum):
        RED = "red"
        ALSO_RED = "red"

    with pytest.raises(TypeError, match="closed non-IntEnum"):
        build_admission_registry_v1(
            schema_revision="test-v1",
            enum_tag_type=_EnumTag,
            record_tag_type=_RecordTag,
            enum_registrations=(
                EnumRegistrationV1(_EnumTag.COLOR, _AliasedColor),
                EnumRegistrationV1(_EnumTag.KIND, _Kind),
            ),
            record_registrations=(
                RecordRegistrationV1(_RecordTag.POINT, _SourcePoint, _OwnedPoint),
                RecordRegistrationV1(
                    _RecordTag.TAGGED,
                    _SourceTagged,
                    _OwnedTagged,
                ),
            ),
            schema_registrations=(SchemaRegistrationV1("test/root/v1", ExactInt(0, 1)),),
        )


def test_registry_rejects_map_key_schema_without_total_order() -> None:
    invalid_key = SequenceOf(
        (SequenceSourceKind.EXACT_TUPLE,),
        ExactInt(0, 1),
        0,
        1,
    )
    with pytest.raises(TypeError, match="canonical total order"):
        _registry(MapOf(invalid_key, ExactInt(0, 1), 1, "test/map/v1"))


@pytest.mark.parametrize(
    "key_schema",
    [
        ExactInt(None, 1),
        ExactInt(0, None),
        ExactInt(0, 1 << 256),
        ExactPair(ExactString(StringRuleV1.NON_EMPTY, 8), ExactInt(-(1 << 256), 1)),
    ],
)
def test_registry_rejects_unbounded_integer_map_key_sort_work(
    key_schema: object,
) -> None:
    with pytest.raises(ValueError, match="integer map key|sortable width"):
        _registry(MapOf(key_schema, ExactInt(0, 1), 1, "test/map/v1"))


@pytest.mark.parametrize(
    "schema",
    [
        ExactString(StringRuleV1.EXACT_TEXT, 4_000_001),
        ExactBytes(exact_length=None, max_length=4_000_001),
        ExactString(StringRuleV1.EXACT_TEXT, 8, max_characters=0),
        ExactString(StringRuleV1.EXACT_TEXT, 8, max_characters=True),
        ExactString(
            StringRuleV1.EXACT_LITERAL,
            2,
            exact_literal="three",
        ),
        ExactString(
            StringRuleV1.EXACT_LITERAL,
            8,
            exact_literal="three",
            max_characters=4,
        ),
    ],
)
def test_registry_rejects_scalar_schema_bounds_outside_policy(schema: object) -> None:
    with pytest.raises(ValueError):
        _registry(schema)


@pytest.mark.parametrize(
    "schema, error_type",
    [
        (BoundedJsonValue("", 1, 1, 1, 1), ValueError),
        (BoundedJsonValue("json", -1, 1, 1, 1), ValueError),
        (BoundedJsonValue("json", 1, 0, 1, 1), ValueError),
        (BoundedJsonValue("json", 1, 257, 1, 1), ValueError),
        (BoundedJsonValue("json", 1, True, 1, 1), ValueError),
        (BoundedJsonValue("json", 1, 1, 0, 1), ValueError),
        (BoundedJsonValue("json", 1, 1, 1, 0), ValueError),
    ],
)
def test_registry_rejects_bounded_json_schema_outside_policy(
    schema: BoundedJsonValue,
    error_type: type[Exception],
) -> None:
    with pytest.raises(error_type):
        _registry(schema)


def test_registry_rejects_empty_or_duplicate_record_union() -> None:
    left = RecordOf(
        _UnionRecordTag.LEFT,
        (DeclaredFieldV1("amount", ExactInt(0, 9)),),
    )
    with pytest.raises(ValueError, match="nonempty exact tuple"):
        _admit_union(RecordUnionOf(()), _SourceUnionLeft(1))
    with pytest.raises(ValueError, match="tags must be unique"):
        _admit_union(RecordUnionOf((left, left)), _SourceUnionLeft(1))


def test_tagged_record_requires_exhaustive_variant_registry() -> None:
    complete = TaggedRecordOf(
        _RecordTag.TAGGED,
        "kind",
        _EnumTag.KIND,
        (
            TaggedVariantV1(
                _Kind.LEFT,
                (
                    DeclaredFieldV1("kind", ExactEnum(_EnumTag.KIND)),
                    DeclaredFieldV1("left", OptionalValue(ExactInt(0, 9))),
                    DeclaredFieldV1(
                        "right",
                        OptionalValue(ExactString(StringRuleV1.NON_EMPTY, 8)),
                    ),
                ),
            ),
            TaggedVariantV1(
                _Kind.RIGHT,
                (
                    DeclaredFieldV1("kind", ExactEnum(_EnumTag.KIND)),
                    DeclaredFieldV1("left", OptionalValue(ExactInt(0, 9))),
                    DeclaredFieldV1(
                        "right",
                        OptionalValue(ExactString(StringRuleV1.NON_EMPTY, 8)),
                    ),
                ),
            ),
        ),
    )
    admitted = _admit(complete, _SourceTagged(_Kind.LEFT, left=2))
    assert type(admitted) is AdmitOk
    assert type(admitted.value) is _OwnedTagged
    assert type(admitted.value.kind) is OwnedEnumV1
    assert admitted.value.kind.member_ordinal == 0
    assert admitted.value.left == 2
    assert admitted.value.right is None

    incomplete = TaggedRecordOf(
        _RecordTag.TAGGED,
        "kind",
        _EnumTag.KIND,
        (complete.variants[0],),
    )
    assert _admit(incomplete, _SourceTagged(_Kind.LEFT, left=2)) == AdmitReject(
        AdmitCode.REGISTRY_DRIFT, ()
    )


def test_tagged_record_rejects_variant_that_relies_on_constructor_defaults() -> None:
    schema = TaggedRecordOf(
        _RecordTag.TAGGED,
        "kind",
        _EnumTag.KIND,
        (
            TaggedVariantV1(
                _Kind.LEFT,
                (
                    DeclaredFieldV1("kind", ExactEnum(_EnumTag.KIND)),
                    DeclaredFieldV1("left", OptionalValue(ExactInt(0, 9))),
                ),
            ),
            TaggedVariantV1(
                _Kind.RIGHT,
                (
                    DeclaredFieldV1("kind", ExactEnum(_EnumTag.KIND)),
                    DeclaredFieldV1(
                        "right",
                        OptionalValue(ExactString(StringRuleV1.NON_EMPTY, 8)),
                    ),
                ),
            ),
        ),
    )
    assert _admit(schema, _SourceTagged(_Kind.LEFT, left=2)) == AdmitReject(
        AdmitCode.REGISTRY_DRIFT,
        (),
    )


def test_unknown_schema_id_is_stable_and_does_not_inspect_source() -> None:
    class _Hostile:
        called = False

        def __getattribute__(self, name: str):
            if name != "called":
                object.__setattr__(self, "called", True)
                raise AssertionError("must not inspect")
            return object.__getattribute__(self, name)

    source = _Hostile()
    result = _admit_with_registry_v1(
        _registry(ExactInt(0, 1)),
        "test-v1",
        "unknown",
        _limits(),
        source,
        _construct_record,
        _canonical_bytes,
    )
    assert result == AdmitReject(AdmitCode.UNSUPPORTED_VARIANT, ())
    assert source.called is False


def test_direct_and_indirect_cycles_return_stable_reject() -> None:
    inner = SequenceOf(
        (SequenceSourceKind.EXACT_LIST,),
        ExactInt(0, 9),
        0,
        4,
    )
    schema = SequenceOf((SequenceSourceKind.EXACT_LIST,), inner, 0, 4)
    direct: list[object] = []
    direct.append(direct)
    assert _admit(schema, direct) == AdmitReject(AdmitCode.CYCLE, (0,))

    outer = SequenceOf((SequenceSourceKind.EXACT_LIST,), schema, 0, 4)
    left: list[object] = []
    right: list[object] = [left]
    left.append(right)
    assert _admit(outer, left) == AdmitReject(AdmitCode.CYCLE, (0, 0))


def test_shared_acyclic_child_is_counted_per_occurrence_and_accepted() -> None:
    child_schema = SequenceOf(
        (SequenceSourceKind.EXACT_LIST,),
        ExactInt(0, 9),
        0,
        4,
    )
    schema = SequenceOf(
        (SequenceSourceKind.EXACT_TUPLE,),
        child_schema,
        0,
        4,
    )
    child = [1]
    assert _admit(schema, (child, child)) == AdmitOk(((1,), (1,)))


def test_depth_limit_accepts_boundary_and_rejects_next_level() -> None:
    child_schema = SequenceOf(
        (SequenceSourceKind.EXACT_LIST,),
        ExactInt(0, 9),
        0,
        4,
    )
    schema = SequenceOf(
        (SequenceSourceKind.EXACT_LIST,),
        child_schema,
        0,
        4,
    )
    assert _admit(schema, [[]], limits=_limits(max_depth=1)) == AdmitOk(((),))
    assert _admit(schema, [[1]], limits=_limits(max_depth=1)) == AdmitReject(
        AdmitCode.DEPTH_LIMIT, (0, 0)
    )


def test_node_item_string_bytes_and_final_byte_limits() -> None:
    pair_schema = SequenceOf(
        (SequenceSourceKind.EXACT_LIST,),
        ExactInt(0, 9),
        0,
        2,
    )
    assert _admit(
        pair_schema,
        [1],
        limits=_limits(max_nodes=2, max_collection_items=2),
    ) == AdmitOk((1,))
    assert _admit(
        pair_schema,
        [1, 2],
        limits=_limits(max_nodes=2, max_collection_items=2),
    ) == AdmitReject(AdmitCode.ITEM_LIMIT, (1,))
    assert _admit(pair_schema, [1, 2, 3]) == AdmitReject(AdmitCode.ITEM_LIMIT, ())

    exact = ExactBytes(exact_length=3, max_length=3)
    assert _admit(exact, b"abc") == AdmitOk(b"abc")
    assert _admit(exact, b"ab") == AdmitReject(AdmitCode.OUT_OF_RANGE, ())

    assert _admit(
        ExactInt(0, 9),
        1,
        limits=_limits(max_canonical_bytes=4),
        encoder=_five_canonical_bytes,
    ) == AdmitReject(AdmitCode.BYTE_LIMIT, ())


def test_oversized_map_rejects_before_entry_tuple_allocation() -> None:
    schema = MapOf(ExactInt(0, 100_000), ExactInt(0, 100_000), 100_000, "m")
    registry = _registry(schema)
    limits = _limits(max_nodes=2, max_collection_items=1)
    source = {index: index for index in range(50_000)}

    tracemalloc.start()
    try:
        result = _admit_with_registry_v1(
            registry,
            "test-v1",
            "test/root/v1",
            limits,
            source,
            _construct_record,
            _canonical_bytes,
        )
        _current, peak = tracemalloc.get_traced_memory()
    finally:
        tracemalloc.stop()

    assert result == AdmitReject(AdmitCode.ITEM_LIMIT, ())
    # The rejected path may allocate diagnostics, never an O(len(source)) tuple.
    assert peak < 500_000


def test_oversized_map_key_rejects_before_sort_value_derivation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import src.state.snapshot_combinators as combinators

    def forbidden_sort_value(*_args: object) -> object:
        raise AssertionError("oversized key reached sort-value derivation")

    monkeypatch.setattr(combinators, "_key_sort_value", forbidden_sort_value)
    schema = MapOf(
        ExactString(StringRuleV1.EXACT_TEXT, 8),
        ExactInt(0, 9),
        2,
        "test/map/v1",
    )
    assert _admit(schema, {"x" * 1_000_000: 1}) == AdmitReject(
        AdmitCode.BYTE_LIMIT,
        (),
    )


def test_aggregate_map_key_bytes_reject_before_sort_value_derivation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import src.state.snapshot_combinators as combinators

    def forbidden_sort_value(*_args: object) -> object:
        raise AssertionError("aggregate key overflow reached sort-value derivation")

    monkeypatch.setattr(combinators, "_key_sort_value", forbidden_sort_value)
    schema = MapOf(
        ExactPair(
            ExactString(StringRuleV1.EXACT_TEXT, 4),
            ExactBytes(exact_length=None, max_length=4),
        ),
        ExactInt(0, 9),
        2,
        "test/map/v1",
    )
    limits = _limits(max_canonical_bytes=7)
    source = {("abc", b"x"): 1, ("def", b"y"): 2}
    assert _admit(schema, source, limits=limits) == AdmitReject(
        AdmitCode.BYTE_LIMIT,
        (),
    )


def test_out_of_range_integer_map_key_uses_bounded_sort_value() -> None:
    import src.state.snapshot_combinators as combinators

    schema = MapOf(ExactInt(0, 9), ExactInt(0, 9), 2, "test/map/v1")
    source = {1 << 1_000_000: 1}

    assert combinators._key_sort_value(
        schema.key_schema,
        next(iter(source)),
        _registry(schema),
    ) == (2, 0)
    assert _admit(schema, source) == AdmitReject(AdmitCode.OUT_OF_RANGE, ())


def test_out_of_range_integer_key_rejects_before_sort_value_derivation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import src.state.snapshot_combinators as combinators

    def forbidden_sort_value(*_args: object) -> object:
        raise AssertionError("out-of-range integer reached sort-value derivation")

    monkeypatch.setattr(combinators, "_key_sort_value", forbidden_sort_value)
    schema = MapOf(ExactInt(0, 9), ExactInt(0, 9), 1, "test/map/v1")

    assert _admit(schema, {1 << 1_000_000: 1}) == AdmitReject(
        AdmitCode.OUT_OF_RANGE,
        (),
    )


def test_corrupted_enum_map_key_uses_bounded_sort_value() -> None:
    import src.state.snapshot_combinators as combinators

    accepted = _admit(ExactEnum(_EnumTag.COLOR), _Color.RED)
    assert type(accepted) is AdmitOk
    owned = cast(OwnedEnumV1, accepted.value)
    object.__setattr__(owned, "_member_ordinal", 1 << 1_000_000)

    schema = MapOf(
        ExactEnum(_EnumTag.COLOR),
        ExactInt(0, 9),
        2,
        "test/map/v1",
    )
    assert combinators._key_sort_value(
        schema.key_schema,
        owned,
        _registry(schema),
    ) == (2, 0)
    assert _admit(schema, {owned: 1}) == AdmitReject(
        AdmitCode.REGISTRY_DRIFT,
        (),
    )


def test_corrupted_nested_enum_key_rejects_before_sort_value_derivation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import src.state.snapshot_combinators as combinators

    accepted = _admit(ExactEnum(_EnumTag.COLOR), _Color.RED)
    assert type(accepted) is AdmitOk
    owned = cast(OwnedEnumV1, accepted.value)
    object.__setattr__(owned, "_member_ordinal", 1 << 1_000_000)
    original_sort_value = combinators._key_sort_value

    def reject_corrupt_enum_sort(
        schema: SchemaV1,
        source: object,
        registry: AdmissionRegistryV1,
    ) -> KeySortValue:
        if type(source) is OwnedEnumV1:
            raise AssertionError("corrupt enum ordinal reached sort-value derivation")
        return original_sort_value(schema, source, registry)

    monkeypatch.setattr(combinators, "_key_sort_value", reject_corrupt_enum_sort)
    schema = MapOf(
        ExactPair(ExactInt(0, 9), ExactEnum(_EnumTag.COLOR)),
        ExactInt(0, 9),
        1,
        "test/map/v1",
    )

    assert _admit(schema, {(1, owned): 1}) == AdmitReject(
        AdmitCode.REGISTRY_DRIFT,
        (),
    )


def test_pair_key_domain_preflight_is_insertion_order_independent() -> None:
    schema = MapOf(
        ExactPair(ExactInt(0, 9), ExactEnum(_EnumTag.COLOR)),
        ExactInt(0, 9),
        2,
        "test/map/v1",
    )
    accepted = _admit(ExactEnum(_EnumTag.COLOR), _Color.RED)
    assert type(accepted) is AdmitOk
    owned = cast(OwnedEnumV1, accepted.value)
    object.__setattr__(owned, "_member_ordinal", 1 << 1_000_000)
    first = {(10, _Color.RED): 1, (1, owned): 2}
    second = {(1, owned): 2, (10, _Color.RED): 1}

    expected = AdmitReject(AdmitCode.REGISTRY_DRIFT, ())
    assert _admit(schema, first) == expected
    assert _admit(schema, second) == expected


def test_trusted_scalar_bytes_use_one_graph_wide_pre_encoding_budget() -> None:
    sequence_schema = SequenceOf(
        (SequenceSourceKind.EXACT_LIST,),
        ExactString(StringRuleV1.NON_EMPTY, 3),
        0,
        2,
    )
    assert _admit(
        sequence_schema,
        ["abc", "def"],
        limits=_limits(max_canonical_bytes=5),
    ) == AdmitReject(AdmitCode.BYTE_LIMIT, (1,))

    map_schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 3),
        ExactBytes(exact_length=3, max_length=3),
        1,
        "test/map/v1",
    )
    assert _admit(
        map_schema,
        {"abc": b"def"},
        limits=_limits(max_canonical_bytes=5),
    ) == AdmitReject(AdmitCode.BYTE_LIMIT, ("abc",))


def test_map_rejection_is_independent_of_insertion_order() -> None:
    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    first = {"b": 10, "a": True}
    second = {"a": True, "b": 10}
    expected = AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ("a",))
    assert _admit(schema, first) == expected
    assert _admit(schema, second) == expected


def test_noncanonical_pair_key_rejection_is_independent_of_insertion_order() -> None:
    schema = MapOf(
        ExactPair(
            ExactInt(0, 1),
            ExactString(StringRuleV1.LOWERCASE_HEX, 8),
        ),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    entries = (((2, "a"), 1), ((0, "G"), 2))
    first = _admit(schema, dict(entries))
    second = _admit(schema, dict(reversed(entries)))
    assert first == second == AdmitReject(AdmitCode.NONCANONICAL_SCALAR, ())


@pytest.mark.parametrize("key", ["AA", "0xAA"])
def test_noncanonical_map_keys_are_never_normalized(key: str) -> None:
    schema = MapOf(
        ExactString(StringRuleV1.LOWERCASE_HEX, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    assert _admit(schema, {key: 1}) == AdmitReject(AdmitCode.NONCANONICAL_SCALAR, ())


def test_hostile_protocol_hooks_are_not_executed() -> None:
    class _Hostile:
        calls = 0

        def _called(self):
            type(self).calls += 1
            raise AssertionError("hostile protocol executed")

        __copy__ = _called
        __deepcopy__ = _called
        __reduce__ = _called
        __reduce_ex__ = _called
        __getstate__ = _called
        __hash__ = _called
        __int__ = _called
        __str__ = _called

        def __eq__(self, _other: object) -> bool:
            return self._called()

        def __lt__(self, _other: object) -> bool:
            return self._called()

        def __iter__(self):
            return self._called()

    source = _Hostile()
    assert _admit(ExactInt(0, 1), source) == AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ())
    assert _Hostile.calls == 0


def test_rejection_rendering_is_stable_and_uses_only_code_and_path() -> None:
    for code in AdmitCode:
        left = AdmitReject(code, ("safe", 2))
        right = AdmitReject(code, ("safe", 2))
        assert left == right
        assert format_admit_path(left.path) == '$["safe"][2]'


def test_successful_nested_result_uses_only_declared_owned_values() -> None:
    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        SequenceOf(
            (SequenceSourceKind.EXACT_LIST,),
            ExactInt(0, 9),
            0,
            4,
        ),
        4,
        "test/map/v1",
    )
    result = _admit(schema, {"a": [1, 2]})
    assert type(result) is AdmitOk
    assert type(result.value) is OwnedMapV1
    assert type(result.value["a"]) is tuple
    assert all(type(value) is int for value in result.value["a"])


@pytest.mark.parametrize(
    "raw",
    [
        AdmissionLimitsV1(0, 10, 100, 10),
        AdmissionLimitsV1(-1, 10, 100, 10),
        AdmissionLimitsV1(True, 10, 100, 10),
        AdmissionLimitsV1(1, 0, 100, 10),
        AdmissionLimitsV1(1, 10, 0, 10),
        AdmissionLimitsV1(1, 10, 100, 0),
        AdmissionLimitsV1(1, 10, 100, 11),
        AdmissionLimitsV1(65, 10, 100, 10),
        AdmissionLimitsV1(1, 200_001, 100, 10),
        AdmissionLimitsV1(1, 10, 4_000_001, 10),
    ],
)
def test_limit_builder_rejects_invalid_profiles_before_admission(raw) -> None:
    result = build_admission_limits_v1(raw)
    assert type(result) is LimitProfileReject
    assert result.code is LimitProfileCode.INVALID_LIMIT_PROFILE


def test_limit_builder_rejects_subclassed_integer_field() -> None:
    class _IntSubclass(int):
        pass

    result = build_admission_limits_v1(AdmissionLimitsV1(_IntSubclass(1), 10, 100, 10))
    assert result == LimitProfileReject(
        LimitProfileCode.INVALID_LIMIT_PROFILE,
        ("max_depth",),
    )


def test_admit_requires_exact_validated_limits_before_source_inspection() -> None:
    class _ValidatedSubclass(ValidatedAdmissionLimitsV1):
        pass

    class _Hostile:
        inspected = False

        def __getattribute__(self, name: str):
            if name != "inspected":
                object.__setattr__(self, "inspected", True)
                raise AssertionError("must not inspect")
            return object.__getattribute__(self, name)

    forged = object.__new__(_ValidatedSubclass)
    source = _Hostile()
    with pytest.raises(TypeError, match="validated limits"):
        _admit_with_registry_v1(
            _registry(ExactInt(0, 1)),
            "test-v1",
            "test/root/v1",
            forged,
            source,
            _construct_record,
            _canonical_bytes,
        )
    assert source.inspected is False


def test_corrupted_exact_validated_limits_reject_before_source_inspection() -> None:
    class _Hostile:
        inspected = False

        def __getattribute__(self, name: str):
            if name != "inspected":
                object.__setattr__(self, "inspected", True)
                raise AssertionError("must not inspect")
            return object.__getattribute__(self, name)

    limits = _limits()
    object.__setattr__(limits, "max_nodes", 1_000_000_000)
    source = _Hostile()
    with pytest.raises(TypeError, match="validated limits"):
        _admit_with_registry_v1(
            _registry(ExactInt(0, 1)),
            "test-v1",
            "test/root/v1",
            limits,
            source,
            _construct_record,
            _canonical_bytes,
        )
    assert source.inspected is False


def test_validated_limits_has_no_unchecked_factory_or_reinitialization_path() -> None:
    limits = _limits()
    before = (
        limits.max_depth,
        limits.max_nodes,
        limits.max_canonical_bytes,
        limits.max_collection_items,
    )
    assert not hasattr(ValidatedAdmissionLimitsV1, "_from_validated_values")
    with pytest.raises(TypeError, match="already initialized|requires its builder"):
        ValidatedAdmissionLimitsV1.__init__(limits, 1, 1, 1, 1)
    assert (
        limits.max_depth,
        limits.max_nodes,
        limits.max_canonical_bytes,
        limits.max_collection_items,
    ) == before


def test_registry_is_closed_owned_and_rejects_reassignment() -> None:
    registry = _registry(ExactInt(0, 1))
    assert registry.schema_revision == "test-v1"
    assert registry.schema_ids == ("test/root/v1",)
    assert not hasattr(registry, "__dict__")
    with pytest.raises((AttributeError, TypeError)):
        registry.schema_revision = "other"  # type: ignore[misc]


def test_registry_records_are_declarative_and_carry_no_behavior() -> None:
    assert tuple(field.name for field in dataclass_fields(RecordRegistrationV1)) == (
        "tag",
        "source_type",
        "owned_type",
    )
    assert tuple(field.name for field in dataclass_fields(SchemaRegistrationV1)) == (
        "schema_id",
        "schema",
    )


def test_internal_engine_rejects_dynamic_resolver_before_source_inspection() -> None:
    class _Hostile:
        inspected = False

        def __getattribute__(self, name: str):
            if name != "inspected":
                object.__setattr__(self, "inspected", True)
                raise AssertionError("must not inspect")
            return object.__getattribute__(self, name)

    suffix = b"x"

    def _closure_encoder(_schema_id: str, _value: object) -> bytes:
        return suffix

    source = _Hostile()
    with pytest.raises(TypeError, match="source-bound"):
        _admit_with_registry_v1(
            _registry(ExactInt(0, 1)),
            "test-v1",
            "test/root/v1",
            _limits(),
            source,
            _construct_record,
            _closure_encoder,
        )
    assert source.inspected is False


def test_owned_map_cannot_be_publicly_constructed_or_reinitialized() -> None:
    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    result = _admit(schema, {"a": 1})
    assert type(result) is AdmitOk
    owned = result.value
    assert type(owned) is OwnedMapV1
    before = owned.entries

    with pytest.raises(TypeError):
        OwnedMapV1((("a", 2),), "test-v1", "test/map/v1")
    with pytest.raises(TypeError, match="already initialized"):
        OwnedMapV1.__init__(owned, (("a", 2),), "test-v1", "test/map/v1")
    assert owned.entries == before


def test_owned_map_has_no_mutable_base_or_exposed_backing_dict() -> None:
    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    result = _admit(schema, {"a": 1})
    assert type(result) is AdmitOk
    owned = result.value
    assert dict not in type(owned).__mro__
    assert not hasattr(owned, "__dict__")
    assert not hasattr(owned, "update")
    assert not hasattr(owned, "_data")
    assert type(owned.entries) is tuple


def test_owned_map_revalidation_requires_matching_schema_metadata() -> None:
    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    first = _admit(schema, {"a": 1})
    assert type(first) is AdmitOk
    second = _admit(schema, first.value)
    assert type(second) is AdmitOk
    assert second.value == first.value
    assert second.value is not first.value


def test_corrupted_owned_map_entry_order_is_not_silently_repaired() -> None:
    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    first = _admit(schema, {"a": 1, "b": 2})
    assert type(first) is AdmitOk
    object.__setattr__(first.value, "_entries", (("b", 2), ("a", 1)))

    assert _admit(schema, first.value) == AdmitReject(AdmitCode.REGISTRY_DRIFT, ())


def test_corrupted_owned_map_metadata_rejects_without_behavior_hooks() -> None:
    class _HostileMetadata:
        calls = 0

        def __eq__(self, _other: object) -> bool:
            type(self).calls += 1
            raise RuntimeError("hostile equality executed")

    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    first = _admit(schema, {"a": 1})
    assert type(first) is AdmitOk
    object.__setattr__(first.value, "_schema_revision", _HostileMetadata())

    assert _admit(schema, first.value) == AdmitReject(AdmitCode.REGISTRY_DRIFT, ())
    assert _HostileMetadata.calls == 0


def test_corrupted_owned_map_index_rejects_without_behavior_hooks() -> None:
    class _HostileIndex:
        calls = 0

        def __len__(self) -> int:
            type(self).calls += 1
            raise RuntimeError("hostile length executed")

        def __getitem__(self, _key: object) -> object:
            type(self).calls += 1
            raise RuntimeError("hostile lookup executed")

    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    first = _admit(schema, {"a": 1})
    assert type(first) is AdmitOk
    object.__setattr__(first.value, "_index", _HostileIndex())

    assert _admit(schema, first.value) == AdmitReject(AdmitCode.REGISTRY_DRIFT, ())
    assert _HostileIndex.calls == 0


def test_corrupted_owned_map_exact_index_is_not_silently_repaired() -> None:
    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    first = _admit(schema, {"a": 1})
    assert type(first) is AdmitOk
    object.__setattr__(first.value, "_index", MappingProxyType({"a": 2}))

    assert _admit(schema, first.value) == AdmitReject(AdmitCode.REGISTRY_DRIFT, ())


def test_exact_keyed_map_revalidates_under_equal_reconstructed_field_names() -> None:
    first_name = bytes.fromhex("62616c616e6365").decode("ascii")
    second_name = bytearray.fromhex("62616c616e6365").decode("ascii")
    assert first_name == second_name
    assert first_name is not second_name
    first_schema = ExactKeyedMap(
        (DeclaredFieldV1(first_name, ExactInt(0, 9)),),
        "test/exact-map/v1",
    )
    second_schema = ExactKeyedMap(
        (DeclaredFieldV1(second_name, ExactInt(0, 9)),),
        "test/exact-map/v1",
    )

    first = _admit(first_schema, {first_name: 7})
    assert type(first) is AdmitOk
    assert type(first.value) is OwnedMapV1
    second = _admit(second_schema, first.value)

    assert type(second) is AdmitOk
    assert type(second.value) is OwnedMapV1
    assert second.value.entries == ((second_name, 7),)
    assert second.value.entries[0][0] is second_name


def test_owned_map_all_insertion_permutations_have_identical_order_and_bytes() -> None:
    schema = MapOf(
        ExactString(StringRuleV1.NON_EMPTY, 8),
        ExactInt(0, 9),
        4,
        "test/map/v1",
    )
    entries = (("c", 3), ("a", 1), ("b", 2))
    admitted = [_admit(schema, dict(order)) for order in permutations(entries)]
    assert all(type(result) is AdmitOk for result in admitted)
    owned_values = [result.value for result in admitted if type(result) is AdmitOk]
    assert {owned.entries for owned in owned_values} == {(("a", 1), ("b", 2), ("c", 3))}
    assert {_canonical_bytes("test/root/v1", owned) for owned in owned_values} == {
        b"(('a', 1), ('b', 2), ('c', 3))"
    }

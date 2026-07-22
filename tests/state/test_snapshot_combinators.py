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
    AdmitCode,
    AdmitOk,
    AdmitReject,
    DeclaredFieldV1,
    EnumRegistrationV1,
    ExactBool,
    ExactBytes,
    ExactEnum,
    ExactInt,
    ExactPair,
    ExactString,
    LimitProfileCode,
    LimitProfileReject,
    MapOf,
    OptionalValue,
    RecordOf,
    RecordRegistrationV1,
    SchemaRegistrationV1,
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


def _five_canonical_bytes(_schema_id: str, _value: object) -> bytes:
    return b"12345"


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

    @dataclass
    class _Lookalike:
        x: int
        label: str

    class _PointSubclass(_SourcePoint):
        pass

    for source in (_Lookalike(3, "p"), _PointSubclass(3, "p"), {"x": 3}):
        assert _admit(schema, source) == AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ())


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
    "schema",
    [
        ExactString(StringRuleV1.EXACT_TEXT, 4_000_001),
        ExactBytes(exact_length=None, max_length=4_000_001),
        ExactString(
            StringRuleV1.EXACT_LITERAL,
            2,
            exact_literal="three",
        ),
    ],
)
def test_registry_rejects_scalar_schema_bounds_outside_policy(schema: object) -> None:
    with pytest.raises(ValueError):
        _registry(schema)


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

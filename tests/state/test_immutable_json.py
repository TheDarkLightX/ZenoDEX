from __future__ import annotations

import copy

import pytest

from src.state.canonical import canonical_json_bytes
from src.state.immutable_json import FrozenDict, FrozenList, freeze_json_mapping


def test_freeze_json_mapping_detaches_and_recursively_freezes() -> None:
    source = {
        "outer": {
            "items": [
                {"amount": 9},
                {"labels": ["a", "b"]},
            ]
        }
    }
    frozen = freeze_json_mapping(source, name="test")
    encoded = canonical_json_bytes(frozen)

    source["outer"]["items"][0]["amount"] = 8
    source["outer"]["items"].append({"amount": 7})

    assert isinstance(frozen, FrozenDict)
    assert isinstance(frozen["outer"], FrozenDict)
    assert isinstance(frozen["outer"]["items"], FrozenList)
    assert frozen["outer"]["items"][0]["amount"] == 9
    assert canonical_json_bytes(frozen) == encoded

    with pytest.raises(TypeError):
        frozen["outer"] = {}  # type: ignore[index]
    with pytest.raises(TypeError):
        frozen["outer"]["items"].append({"amount": 6})
    with pytest.raises(TypeError):
        frozen["outer"]["items"][0]["amount"] = 6


def test_frozen_json_has_no_mutable_builtin_descriptor_bypass() -> None:
    frozen = freeze_json_mapping({"items": [{"amount": 9}]})
    items = frozen["items"]
    encoded = canonical_json_bytes(frozen)

    assert not isinstance(frozen, dict)
    assert not isinstance(items, list)

    with pytest.raises(TypeError):
        dict.__setitem__(frozen, "evil", True)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        list.append(items, {"amount": 8})  # type: ignore[arg-type]

    assert "evil" not in frozen
    assert frozen["items"] == [{"amount": 9}]
    assert canonical_json_bytes(frozen) == encoded


def test_shallow_copy_preserves_authority_and_deepcopy_thaws_builder() -> None:
    frozen = freeze_json_mapping({"items": [{"amount": 1}, {"amount": 2}]})

    assert copy.copy(frozen) is frozen

    builder = copy.deepcopy(frozen)
    assert type(builder) is dict
    assert type(builder["items"]) is list
    assert type(builder["items"][0]) is dict

    builder["items"][0]["amount"] = 9
    builder["items"].append({"amount": 3})

    assert frozen["items"] == [{"amount": 1}, {"amount": 2}]
    assert builder == {"items": [{"amount": 9}, {"amount": 2}, {"amount": 3}]}


def test_non_json_values_fail_closed() -> None:
    with pytest.raises(TypeError, match="floats"):
        freeze_json_mapping({"amount": 1.5})
    with pytest.raises(TypeError, match="keys must be strings"):
        freeze_json_mapping({1: "bad"})  # type: ignore[dict-item]
    with pytest.raises(TypeError, match="unsupported type"):
        freeze_json_mapping({"payload": b"bytes"})


def test_canonical_encoder_rejects_behavior_changing_container_subclasses() -> None:
    class BehaviorChangingDict(dict[str, object]):
        def items(self):  # type: ignore[no-untyped-def]
            raise AssertionError("behavior-changing mapping executed")

    class BehaviorChangingList(list[object]):
        def __iter__(self):  # type: ignore[no-untyped-def]
            raise AssertionError("behavior-changing sequence executed")

    with pytest.raises(TypeError, match="mapping subclasses"):
        canonical_json_bytes(BehaviorChangingDict({"amount": 1}))
    with pytest.raises(TypeError, match="sequence subclasses"):
        canonical_json_bytes(BehaviorChangingList([1]))


def test_freeze_json_mapping_rejects_subclass_before_executing_behavior() -> None:
    class BehaviorChangingDict(dict[str, object]):
        def items(self):  # type: ignore[no-untyped-def]
            raise AssertionError("behavior-changing mapping executed")

    with pytest.raises(TypeError, match="exact owned mapping"):
        freeze_json_mapping(BehaviorChangingDict({"amount": 1}))

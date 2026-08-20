from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from tools.check_global_economic_delta_v2 import (
    I128_MAX,
    MAX_EVENTS_V2,
    MAX_INPUT_BYTES_V2,
    SCHEMA_V2,
    DeltaRejectCodeV2,
    DeltaValidationErrorV2,
    decode_delta_plan_bytes_v2,
    validate_plan_v2,
)

VECTOR_PATH = Path(__file__).parent / "data/global_economic_delta_v2_plan.json"
VECTOR_ROOT = "sha256:0a7e960b474fd446a834a590ecf2abe6c208adabb704c794a702f9d41894f18a"
MAX_AMOUNT_VECTOR_ROOT = (
    "sha256:68a13c2c92e55244dc3cae9b4f13114dbf85977a9b18a29f32b5f3819f8d6f4f"
)


def _plan() -> dict[str, object]:
    value = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _event(index: int) -> dict[str, object]:
    events = _plan()["events"]
    assert isinstance(events, list)
    event = events[index]
    assert isinstance(event, dict)
    return event


def _plan_for_events(*events: dict[str, object]) -> dict[str, object]:
    source_fields = {
        "external_in": "source_effect",
        "external_out": "ancestor_claim_event",
        "refund": "source_event",
    }
    required_roots = {
        event[field]
        for event in events
        if (field := source_fields.get(event["delta_class"])) is not None
    }
    bindings = _plan()["source_bindings"]
    assert isinstance(bindings, list)
    return {
        "events": list(events),
        "schema": SCHEMA_V2,
        "source_bindings": [
            copy.deepcopy(binding)
            for binding in bindings
            if isinstance(binding, dict) and binding["source_root"] in required_roots
        ],
    }


def _assert_reject(
    plan: object,
    expected_code: DeltaRejectCodeV2,
) -> None:
    with pytest.raises(DeltaValidationErrorV2) as captured:
        validate_plan_v2(plan)
    assert captured.value.code is expected_code


def test_all_eight_delta_classes_form_one_canonical_owned_plan() -> None:
    # Arrange
    plan = _plan()

    # Act
    validated = validate_plan_v2(plan)

    # Assert
    assert tuple(event["delta_class"] for event in validated.events) == (
        "internal_transfer",
        "mint",
        "burn",
        "liability",
        "external_in",
        "external_out",
        "refund",
        "slash",
    )
    assert validated.root.startswith("sha256:")
    assert validated.canonical_bytes.endswith(b"\n")


def test_checked_in_vector_is_canonical_and_root_bound() -> None:
    # Arrange
    raw = VECTOR_PATH.read_bytes()
    value = json.loads(raw)

    # Act
    validated = validate_plan_v2(value)

    # Assert
    assert validated.canonical_bytes == raw
    assert validated.root == VECTOR_ROOT


def test_empty_plan_rejects_before_any_candidate_exists() -> None:
    # Arrange
    plan = {"schema": SCHEMA_V2, "events": [], "source_bindings": []}

    # Act / Assert
    _assert_reject(plan, DeltaRejectCodeV2.EMPTY_PLAN)


def test_event_count_bva_accepts_64_and_rejects_65() -> None:
    # Arrange
    template = _event(0)

    def events(count: int) -> list[dict[str, object]]:
        return [
            dict(template, economic_event=f"sha256:{index + 1:064x}")
            for index in range(count)
        ]

    # Act / Assert
    accepted = _plan_for_events(*events(MAX_EVENTS_V2))
    rejected = _plan_for_events(*events(MAX_EVENTS_V2 + 1))
    assert len(validate_plan_v2(accepted).events) == MAX_EVENTS_V2
    _assert_reject(rejected, DeltaRejectCodeV2.EVENT_COUNT_OUT_OF_RANGE)


@pytest.mark.parametrize(
    ("amount_atoms", "accepted", "reject_code"),
    [
        (0, False, DeltaRejectCodeV2.AMOUNT_OUT_OF_RANGE),
        (1, True, None),
        (I128_MAX, True, None),
        (I128_MAX + 1, False, DeltaRejectCodeV2.AMOUNT_OUT_OF_RANGE),
    ],
)
def test_amount_atoms_bva_is_one_through_i128_max(
    amount_atoms: int,
    accepted: bool,
    reject_code: DeltaRejectCodeV2 | None,
) -> None:
    # Arrange
    plan = _plan_for_events(dict(_event(0), amount_atoms=amount_atoms))

    # Act / Assert
    if accepted:
        assert validate_plan_v2(plan).events[0]["amount_atoms"] == amount_atoms
    else:
        assert reject_code is not None
        _assert_reject(plan, reject_code)


def test_i128_max_has_a_fixed_cross_language_canonical_root() -> None:
    # Arrange
    plan = _plan_for_events(dict(_event(0), amount_atoms=I128_MAX))

    # Act
    validated = validate_plan_v2(plan)

    # Assert
    assert validated.root == MAX_AMOUNT_VECTOR_ROOT


def test_boolean_amount_does_not_alias_integer_one() -> None:
    # Arrange
    plan = _plan_for_events(dict(_event(0), amount_atoms=True))

    # Act / Assert
    _assert_reject(plan, DeltaRejectCodeV2.AMOUNT_TYPE_INVALID)


def test_unknown_event_field_rejects_closed_variant() -> None:
    # Arrange
    event = dict(_event(0), hidden_authority="mallory")
    plan = _plan_for_events(event)

    # Act / Assert
    _assert_reject(plan, DeltaRejectCodeV2.EVENT_FIELDS_INVALID)


def test_duplicate_economic_event_rejects_instead_of_double_applying() -> None:
    # Arrange
    first = _event(0)
    second = dict(_event(1), economic_event=first["economic_event"])
    plan = _plan_for_events(first, second)

    # Act / Assert
    _assert_reject(plan, DeltaRejectCodeV2.DUPLICATE_EVENT)


def test_reordered_events_reject_noncanonical_plan() -> None:
    # Arrange
    events = [_event(0), _event(1)]
    plan = _plan_for_events(*reversed(events))

    # Act / Assert
    _assert_reject(plan, DeltaRejectCodeV2.NONCANONICAL_EVENT_ORDER)


def test_internal_transfer_cannot_name_the_same_owned_allocation_twice() -> None:
    # Arrange
    event = dict(
        _event(0),
        destination_owner="alice",
        destination_ledger_allocation="account:alice",
    )
    plan = _plan_for_events(event)

    # Act / Assert
    _assert_reject(plan, DeltaRejectCodeV2.SOURCE_EQUALS_DESTINATION)


def test_liability_relation_requires_exact_nonzero_before_after_delta() -> None:
    # Arrange
    no_change = dict(_event(3), amount_atoms=1, pre_atoms=7, post_atoms=7)
    wrong_direction = dict(_event(3), direction="decrease")

    # Act / Assert
    _assert_reject(
        _plan_for_events(no_change),
        DeltaRejectCodeV2.LIABILITY_RELATION_INVALID,
    )
    _assert_reject(
        _plan_for_events(wrong_direction),
        DeltaRejectCodeV2.LIABILITY_RELATION_INVALID,
    )


def test_slash_partition_must_assign_every_atom_once() -> None:
    # Arrange
    event = dict(_event(7), residue_atoms=2)
    plan = _plan_for_events(event)

    # Act / Assert -- kills a mutant that omits the partition equality.
    _assert_reject(plan, DeltaRejectCodeV2.SLASH_PARTITION_MISMATCH)


@pytest.mark.parametrize(
    ("event_index", "field"),
    [
        (4, "source_effect"),
        (5, "ancestor_claim_event"),
        (5, "destination_effect"),
        (6, "source_event"),
    ],
)
def test_event_cannot_reference_itself_as_ancestry_or_effect(
    event_index: int,
    field: str,
) -> None:
    # Arrange
    event = _event(event_index)
    event[field] = event["economic_event"]
    plan = _plan_for_events(event)

    # Act / Assert
    _assert_reject(plan, DeltaRejectCodeV2.SELF_REFERENTIAL_EVENT)


def test_external_out_ancestor_and_destination_effect_must_differ() -> None:
    # Arrange
    event = _event(5)
    event["destination_effect"] = event["ancestor_claim_event"]
    plan = _plan_for_events(event)

    # Act / Assert
    _assert_reject(plan, DeltaRejectCodeV2.SELF_REFERENTIAL_EVENT)


def test_canonical_bytes_ignore_mapping_insertion_history() -> None:
    # Arrange
    plan = _plan()
    reordered_events = []
    for event in plan["events"]:
        assert isinstance(event, dict)
        reordered_events.append(dict(reversed(tuple(event.items()))))
    source_bindings = plan["source_bindings"]
    assert isinstance(source_bindings, list)
    reordered_bindings = [
        dict(reversed(tuple(binding.items())))
        for binding in source_bindings
        if isinstance(binding, dict)
    ]
    reordered_plan = dict(
        (
            ("source_bindings", reordered_bindings),
            ("events", reordered_events),
            ("schema", plan["schema"]),
        )
    )

    # Act
    ordinary = validate_plan_v2(copy.deepcopy(plan))
    reordered = validate_plan_v2(reordered_plan)

    # Assert
    assert reordered.canonical_bytes == ordinary.canonical_bytes
    assert reordered.root == ordinary.root


def test_validated_plan_owns_inputs_and_exposes_read_only_events() -> None:
    # Arrange
    plan = _plan()
    validated = validate_plan_v2(plan)
    original_bytes = validated.canonical_bytes
    original_root = validated.root

    # Act
    events = plan["events"]
    assert isinstance(events, list)
    first = events[0]
    assert isinstance(first, dict)
    first["amount_atoms"] = 99
    events.clear()

    # Assert
    assert validated.canonical_bytes == original_bytes
    assert validated.root == original_root
    with pytest.raises(TypeError):
        validated.events[0]["amount_atoms"] = 99  # type: ignore[index]


def test_hostile_schema_value_cannot_forge_exact_schema_equality() -> None:
    # Arrange
    class AlwaysEqual:
        def __ne__(self, _other: object) -> bool:
            return False

    plan = _plan()
    plan["schema"] = AlwaysEqual()

    # Act / Assert -- kills duck-typed equality at the schema boundary.
    _assert_reject(plan, DeltaRejectCodeV2.SCHEMA_TYPE_INVALID)


def test_reference_must_have_one_exact_compatible_source_binding() -> None:
    # Arrange
    event = _event(6)
    missing = _plan_for_events(event)
    missing["source_bindings"] = []
    wrong_amount = _plan_for_events(event)
    bindings = wrong_amount["source_bindings"]
    assert isinstance(bindings, list) and isinstance(bindings[0], dict)
    bindings[0]["amount_atoms"] = 8

    # Act / Assert
    _assert_reject(missing, DeltaRejectCodeV2.SOURCE_REFERENCE_INVALID)
    _assert_reject(wrong_amount, DeltaRejectCodeV2.SOURCE_REFERENCE_INVALID)


def test_reference_cycles_and_double_consumption_are_closed() -> None:
    # Arrange
    first = dict(
        _event(6),
        economic_event="sha256:0707070707070707070707070707070707070707070707070707070707070707",
        source_event="sha256:0808080808080808080808080808080808080808080808080808080808080808",
    )
    second = dict(
        _event(6),
        economic_event="sha256:0808080808080808080808080808080808080808080808080808080808080808",
        source_event="sha256:0707070707070707070707070707070707070707070707070707070707070707",
    )
    cycle = {"events": [first, second], "schema": SCHEMA_V2, "source_bindings": []}
    repeated = _plan_for_events(_event(6), dict(_event(6), economic_event="sha256:0909090909090909090909090909090909090909090909090909090909090909"))

    # Act / Assert
    _assert_reject(cycle, DeltaRejectCodeV2.REFERENCE_ROOT_CONFLICT)
    _assert_reject(repeated, DeltaRejectCodeV2.SOURCE_REFERENCE_REUSED)


def test_reject_code_is_independent_of_event_mapping_order() -> None:
    # Arrange
    event = dict(_event(0), asset="UPPER", economic_event="bad-root")
    ordinary = _plan_for_events(event)
    reversed_event = dict(reversed(tuple(event.items())))
    reordered = _plan_for_events(reversed_event)

    # Act / Assert
    for plan in (ordinary, reordered):
        _assert_reject(plan, DeltaRejectCodeV2.ROOT_INVALID)


def test_python_byte_decoder_enforces_exact_input_bva() -> None:
    # Arrange
    raw = VECTOR_PATH.read_bytes()
    exact = raw + b" " * (MAX_INPUT_BYTES_V2 - len(raw))
    above = exact + b" "

    # Act / Assert
    assert decode_delta_plan_bytes_v2(exact).root == VECTOR_ROOT
    with pytest.raises(DeltaValidationErrorV2) as captured:
        decode_delta_plan_bytes_v2(above)
    assert captured.value.code is DeltaRejectCodeV2.INPUT_TOO_LARGE


@pytest.mark.parametrize("field", ["pre_atoms", "post_atoms"])
def test_liability_balance_atoms_reject_above_i128_max(field: str) -> None:
    # Arrange
    event = dict(_event(3), **{field: I128_MAX + 1})

    # Act / Assert
    _assert_reject(_plan_for_events(event), DeltaRejectCodeV2.AMOUNT_OUT_OF_RANGE)


def test_exact_byte_decoder_collapses_malformed_values_to_shared_code() -> None:
    # Arrange
    plan = _plan_for_events(dict(_event(0), amount_atoms=True))
    raw = json.dumps(plan, separators=(",", ":"), sort_keys=True).encode("ascii")

    # Act / Assert
    with pytest.raises(DeltaValidationErrorV2) as captured:
        decode_delta_plan_bytes_v2(raw)
    assert captured.value.code is DeltaRejectCodeV2.DECODE_INVALID


def test_identifier_and_root_bva_are_closed() -> None:
    # Arrange
    accepted_id = _plan_for_events(dict(_event(0), asset="a" * 128))
    long_id = _plan_for_events(dict(_event(0), asset="a" * 129))
    short_root = _plan_for_events(dict(_event(0), economic_event="sha256:" + "1" * 63))
    zero_root = _plan_for_events(dict(_event(0), economic_event="sha256:" + "0" * 64))

    # Act / Assert
    assert validate_plan_v2(accepted_id).events[0]["asset"] == "a" * 128
    _assert_reject(long_id, DeltaRejectCodeV2.IDENTIFIER_INVALID)
    _assert_reject(short_root, DeltaRejectCodeV2.ROOT_INVALID)
    _assert_reject(zero_root, DeltaRejectCodeV2.ROOT_INVALID)


@pytest.mark.parametrize("amount_atoms", [0, I128_MAX + 1])
def test_source_binding_amount_bva_rejects_outside_positive_i128(
    amount_atoms: int,
) -> None:
    # Arrange
    plan = _plan_for_events(_event(4))
    bindings = plan["source_bindings"]
    assert isinstance(bindings, list) and isinstance(bindings[0], dict)
    bindings[0]["amount_atoms"] = amount_atoms

    # Act / Assert
    _assert_reject(plan, DeltaRejectCodeV2.AMOUNT_OUT_OF_RANGE)


def test_zero_is_allowed_only_for_balance_side_atom_fields() -> None:
    # Arrange
    liability = dict(_event(3), amount_atoms=4, pre_atoms=0, post_atoms=4)
    slash = dict(_event(7), beneficiary_atoms=0, residue_atoms=8)

    # Act / Assert
    assert validate_plan_v2(_plan_for_events(liability)).events[0]["pre_atoms"] == 0
    assert validate_plan_v2(_plan_for_events(slash)).events[0]["beneficiary_atoms"] == 0


def test_deep_json_nesting_is_a_typed_decode_reject() -> None:
    # Arrange
    raw = b"[" * 2_000 + b"0" + b"]" * 2_000

    # Act / Assert
    with pytest.raises(DeltaValidationErrorV2) as captured:
        decode_delta_plan_bytes_v2(raw)
    assert captured.value.code is DeltaRejectCodeV2.DECODE_INVALID


def test_malformed_byte_corpus_matches_the_rust_rejection_abi() -> None:
    # Arrange
    raw = VECTOR_PATH.read_bytes()
    malformed = (
        b"\xef\xbb\xbf" + raw,
        raw.decode("ascii").encode("utf-16"),
        raw.replace(b'"amount_atoms":1', b'"amount_atoms":1.5', 1),
        raw.replace(
            b'"schema":"zenodex/global-economic-delta-plan/v2"',
            b'"schema":7',
            1,
        ),
    )

    # Act / Assert
    for candidate in malformed:
        with pytest.raises(DeltaValidationErrorV2) as captured:
            decode_delta_plan_bytes_v2(candidate)
        assert captured.value.code is DeltaRejectCodeV2.DECODE_INVALID

    wrong_schema = raw.replace(
        b"zenodex/global-economic-delta-plan/v2",
        b"zenodex/global-economic-delta-plan/v3",
        1,
    )
    with pytest.raises(DeltaValidationErrorV2) as captured:
        decode_delta_plan_bytes_v2(wrong_schema)
    assert captured.value.code is DeltaRejectCodeV2.SCHEMA_MISMATCH

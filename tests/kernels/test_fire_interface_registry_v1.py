from __future__ import annotations

from src.fire.runtime.interface_registry_v1 import (
    build_fire_interface_terms,
    get_fire_interface_entry,
    list_fire_interface_entries,
    verify_fire_interface_to_object_composition,
)


def test_list_fire_interface_entries_exposes_index_object_ids() -> None:
    object_ids = {entry.object_id for entry in list_fire_interface_entries()}
    assert object_ids == {"burn_index_v1", "fee_index_v1", "reward_index_v1", "hodl_value_v1", "lp_value_v1"}


def test_burn_index_interface_builds_output_guarantee() -> None:
    spec = get_fire_interface_entry("burn_index_v1")
    terms = build_fire_interface_terms("burn_index_v1", {"burn_final": 7})

    outputs = spec.build_output_guarantees(terms)

    assert len(outputs) == 1
    assert outputs[0].name == "burn_final"
    assert outputs[0].unit == "Index"
    assert outputs[0].lower == 7
    assert outputs[0].upper == 7


def test_verify_fire_interface_to_object_composition_accepts_burn_index_into_burn_note() -> None:
    ok, err = verify_fire_interface_to_object_composition(
        interface_object_id="burn_index_v1",
        interface_raw_terms={"burn_final": 7},
        consumer_object_id="burn_boost_call_v1",
        consumer_raw_terms={
            "n_notional": 10,
            "strike_index": 4,
            "cap_index": 3,
            "source_upper": 9,
        },
        bindings={"burn_final": "burn_final"},
    )

    assert ok is True
    assert err is None


def test_verify_fire_interface_to_object_composition_rejects_fee_bound_mismatch() -> None:
    ok, err = verify_fire_interface_to_object_composition(
        interface_object_id="fee_index_v1",
        interface_raw_terms={"fee_final": 7},
        consumer_object_id="fee_note_v1",
        consumer_raw_terms={
            "n_notional": 10,
            "cap_index": 4,
            "source_upper": 2,
        },
        bindings={"fee_final": "fee_final"},
    )

    assert ok is False
    assert err == "composition_bound_mismatch:fee_final:fee_final"


def test_hodl_value_interface_builds_interval_output_guarantee() -> None:
    spec = get_fire_interface_entry("hodl_value_v1")
    terms = build_fire_interface_terms("hodl_value_v1", {"hodl_lower": 10, "hodl_upper": 20})

    outputs = spec.build_output_guarantees(terms)

    assert len(outputs) == 1
    assert outputs[0].name == "hodl_final"
    assert outputs[0].unit == "Amount[zUSD]"
    assert outputs[0].lower == 10
    assert outputs[0].upper == 20


def test_verify_fire_interface_to_object_composition_accepts_hodl_value_into_lp_loss_cover() -> None:
    ok, err = verify_fire_interface_to_object_composition(
        interface_object_id="hodl_value_v1",
        interface_raw_terms={"hodl_lower": 10, "hodl_upper": 20},
        consumer_object_id="lp_loss_cover_v1",
        consumer_raw_terms={
            "n_notional": 2,
            "deductible": 5,
            "cap_amount": 40,
            "hodl_lower": 10,
            "hodl_upper": 25,
            "lpv_lower": 10,
            "lpv_upper": 60,
        },
        bindings={"hodl_final": "hodl_final"},
    )

    assert ok is True
    assert err is None


def test_verify_fire_interface_to_object_composition_rejects_lp_value_bound_mismatch() -> None:
    ok, err = verify_fire_interface_to_object_composition(
        interface_object_id="lp_value_v1",
        interface_raw_terms={"lpv_lower": 5, "lpv_upper": 65},
        consumer_object_id="lp_loss_cover_v1",
        consumer_raw_terms={
            "n_notional": 2,
            "deductible": 5,
            "cap_amount": 40,
            "hodl_lower": 10,
            "hodl_upper": 25,
            "lpv_lower": 10,
            "lpv_upper": 60,
        },
        bindings={"lpv_final": "lpv_final"},
    )

    assert ok is False
    assert err == "composition_bound_mismatch:lpv_final:lpv_final"

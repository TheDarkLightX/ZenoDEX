"""Fixed-vector evidence for the offline Tau economic qualification oracle."""

from __future__ import annotations

from collections import Counter
from dataclasses import FrozenInstanceError

import pytest

from experiments.tau_economic_qualification_v1.reference import (
    SPEC_IDS,
    UINT32_MAX,
    QualificationCase,
    corpus,
    evaluate,
    stateful_histories,
)

TRUTH_PARTITION_PREFIX = "zusd_transfer_truth_partition_"

EXACT_VECTORS = {
    "nonce_replay_initial_accept": (
        "nonce_replay_guard_v1",
        (1, 0, 1),
        (1, 1, 1, 1),
    ),
    "nonce_replay_stale_caller_state_reaccepts_pointwise": (
        "nonce_replay_guard_v1",
        (1, 0, 1),
        (1, 1, 1, 1),
    ),
    "nonce_replay_zero_rejected": (
        "nonce_replay_guard_v1",
        (0, 0, 1),
        (1, 0, 0, 0),
    ),
    "nonce_replay_all_predicates_fail": (
        "nonce_replay_guard_v1",
        (0, 0, 2),
        (0, 0, 0, 0),
    ),
    "nonce_replay_expected_mismatch_with_same_nonce": (
        "nonce_replay_guard_v1",
        (0, 0, 0),
        (0, 0, 1, 0),
    ),
    "nonce_replay_fresh_wrong_expected": (
        "nonce_replay_guard_v1",
        (1, 0, 0),
        (0, 1, 0, 0),
    ),
    "nonce_replay_fresh_not_sequential": (
        "nonce_replay_guard_v1",
        (2, 0, 1),
        (1, 1, 0, 0),
    ),
    "nonce_replay_fresh_sequential_but_params_fail": (
        "nonce_replay_guard_v1",
        (2, 0, 2),
        (0, 1, 1, 0),
    ),
    "nonce_replay_wrap_params_and_sequence_not_fresh": (
        "nonce_replay_guard_v1",
        (0, UINT32_MAX, 0),
        (1, 0, 1, 0),
    ),
    "nonce_replay_max_neighbor_accept": (
        "nonce_replay_guard_v1",
        (UINT32_MAX, UINT32_MAX - 1, UINT32_MAX),
        (1, 1, 1, 1),
    ),
    "nonce_replay_unsigned_signed_seam_accept": (
        "nonce_replay_guard_v1",
        (0x80000000, 0x7FFFFFFF, 0x80000000),
        (1, 1, 1, 1),
    ),
    "nonce_manager_zero_replay": ("nonce_manager_v1", (0, 0), (0,)),
    "nonce_manager_gap_999_accept": ("nonce_manager_v1", (999, 0), (1,)),
    "nonce_manager_unsigned_signed_seam_accept": (
        "nonce_manager_v1",
        (0x80000000, 0x7FFFFFFF),
        (1,),
    ),
    "nonce_manager_history_replay_then_later_valid_step_1": (
        "nonce_manager_v1",
        (1, 0),
        (1,),
    ),
    "nonce_manager_history_replay_then_later_valid_step_2_replay": (
        "nonce_manager_v1",
        (1, 1),
        (0,),
    ),
    "nonce_manager_history_replay_then_later_valid_step_3_later_valid": (
        "nonce_manager_v1",
        (2, 1),
        (1,),
    ),
    "nonce_manager_history_gap_boundary_step_1_gap_1000": (
        "nonce_manager_v1",
        (1000, 0),
        (1,),
    ),
    "nonce_manager_history_gap_boundary_step_2_gap_1001_rejected": (
        "nonce_manager_v1",
        (2001, 1000),
        (0,),
    ),
    "nonce_manager_history_gap_boundary_step_3_later_gap_1000": (
        "nonce_manager_v1",
        (2000, 1000),
        (1,),
    ),
    "nonce_manager_history_exhaustion_step_1_accept_max": (
        "nonce_manager_v1",
        (UINT32_MAX, UINT32_MAX - 1),
        (1,),
    ),
    "nonce_manager_history_exhaustion_step_2_wrap_rejected": (
        "nonce_manager_v1",
        (0, UINT32_MAX),
        (0,),
    ),
    "nonce_manager_history_exhaustion_step_3_replay_rejected": (
        "nonce_manager_v1",
        (UINT32_MAX, UINT32_MAX),
        (0,),
    ),
    "transfer_hook_zero_amount_dust_allowed": (
        "transfer_hook_guard_v1",
        (0, 0, 0, 0, 0, 1),
        (1, 1, 1, 1),
    ),
    "transfer_hook_valid_one_atom": (
        "transfer_hook_guard_v1",
        (10, 9, 3, 4, 1, 1),
        (1, 1, 1, 1),
    ),
    "transfer_hook_conserved_but_wrong_deltas": (
        "transfer_hook_guard_v1",
        (10, 9, 4, 5, 2, 1),
        (1, 0, 1, 0),
    ),
    "transfer_hook_conserved_wrong_deltas_rejected_hook": (
        "transfer_hook_guard_v1",
        (10, 9, 4, 5, 2, 0),
        (1, 0, 0, 0),
    ),
    "transfer_hook_rejected_hook": (
        "transfer_hook_guard_v1",
        (10, 9, 3, 4, 1, 0),
        (1, 1, 0, 0),
    ),
    "transfer_hook_modular_sum_wrap_with_valid_deltas": (
        "transfer_hook_guard_v1",
        (UINT32_MAX, UINT32_MAX - 1, 1, 2, 1, 1),
        (1, 1, 1, 1),
    ),
    "transfer_hook_sender_underflow_keeps_o2_true": (
        "transfer_hook_guard_v1",
        (0, UINT32_MAX, 10, 11, 1, 1),
        (0, 1, 1, 0),
    ),
    "transfer_hook_sender_underflow_rejected_hook": (
        "transfer_hook_guard_v1",
        (0, UINT32_MAX, 10, 11, 1, 0),
        (0, 1, 0, 0),
    ),
    "transfer_hook_receiver_wrap_keeps_o2_true": (
        "transfer_hook_guard_v1",
        (10, 9, UINT32_MAX, 0, 1, 1),
        (0, 1, 1, 0),
    ),
    "transfer_hook_direction_and_delta_fail_approved": (
        "transfer_hook_guard_v1",
        (0, 1, 0, 0, 1, 1),
        (0, 0, 1, 0),
    ),
    "transfer_hook_direction_and_delta_fail_rejected_hook": (
        "transfer_hook_guard_v1",
        (0, 1, 0, 0, 1, 0),
        (0, 0, 0, 0),
    ),
    "zusd_transfer_allowed": ("zusd_transfer_guard_v1", (1, 1, 1, 1, 1, 0), (1, 1, 1, 1)),
    "zusd_transfer_zero_amount_flag": (
        "zusd_transfer_guard_v1",
        (0, 1, 1, 1, 1, 0),
        (0, 1, 0, 0),
    ),
    "zusd_transfer_missing_balance": (
        "zusd_transfer_guard_v1",
        (1, 0, 1, 1, 1, 0),
        (0, 1, 0, 0),
    ),
    "zusd_transfer_delta_mismatch": (
        "zusd_transfer_guard_v1",
        (1, 1, 0, 1, 1, 0),
        (0, 1, 0, 0),
    ),
    "zusd_transfer_unauthorized": (
        "zusd_transfer_guard_v1",
        (1, 1, 1, 0, 1, 0),
        (1, 0, 0, 0),
    ),
    "zusd_transfer_invalid_recipient": (
        "zusd_transfer_guard_v1",
        (1, 1, 1, 1, 0, 0),
        (1, 0, 0, 0),
    ),
    "zusd_transfer_paused": (
        "zusd_transfer_guard_v1",
        (1, 1, 1, 1, 1, 1),
        (1, 0, 0, 0),
    ),
    "zusd_transfer_pause_then_unpause_paused": (
        "zusd_transfer_guard_v1",
        (1, 1, 1, 1, 1, 1),
        (1, 0, 0, 0),
    ),
    "zusd_transfer_pause_then_unpause_unpaused": (
        "zusd_transfer_guard_v1",
        (1, 1, 1, 1, 1, 0),
        (1, 1, 1, 1),
    ),
}


def _cases_by_name() -> dict[str, QualificationCase]:
    return {case.name: case for case in corpus()}


def _zusd_partition_expected(inputs: tuple[int, ...]) -> tuple[int, ...]:
    encoded = sum(bit << index for index, bit in enumerate(inputs))
    structural_ok = (encoded & 0b000111) == 0b000111
    policy_ok = (encoded & 0b111000) == 0b011000
    transfer_ok = structural_ok and policy_ok
    return (int(structural_ok), int(policy_ok), int(transfer_ok), int(transfer_ok))


def test_fixed_vectors_cover_complete_outputs_with_an_independent_integer_oracle() -> None:
    observed = {
        case.name: (case.spec_id, case.inputs, case.expected_outputs)
        for case in corpus()
        if not case.name.startswith(TRUTH_PARTITION_PREFIX)
    }
    assert observed == EXACT_VECTORS
    assert len(observed) == len(corpus()) - 64
    for spec_id, inputs, expected_outputs in EXACT_VECTORS.values():
        assert evaluate(spec_id, inputs) == expected_outputs


def test_exhaustive_zusd_binary_truth_partition_is_frozen_and_independently_checked() -> None:
    generated_cases = tuple(
        case for case in corpus() if case.name.startswith(TRUTH_PARTITION_PREFIX)
    )
    assert len(generated_cases) == 64
    assert {case.inputs for case in generated_cases} == {
        tuple((encoded >> index) & 1 for index in range(6)) for encoded in range(64)
    }
    assert Counter(case.expected_outputs for case in generated_cases) == Counter(
        {
            (0, 0, 0, 0): 49,
            (0, 1, 0, 0): 7,
            (1, 0, 0, 0): 7,
            (1, 1, 1, 1): 1,
        }
    )
    for case in generated_cases:
        expected_outputs = _zusd_partition_expected(case.inputs)
        assert case.spec_id == "zusd_transfer_guard_v1"
        assert case.expected_outputs == expected_outputs
        assert evaluate(case.spec_id, case.inputs) == expected_outputs


def test_closed_registry_and_tuple_shapes_keep_the_corpus_deterministic() -> None:
    assert SPEC_IDS == (
        "nonce_replay_guard_v1",
        "nonce_manager_v1",
        "transfer_hook_guard_v1",
        "zusd_transfer_guard_v1",
    )
    assert len(corpus()) == 107
    assert corpus() == corpus()
    assert set(case.spec_id for case in corpus()) == set(SPEC_IDS)
    assert all(type(case.inputs) is tuple for case in corpus())
    assert all(type(case.expected_outputs) is tuple for case in corpus())
    assert all(value in (0, 1) for case in corpus() for value in case.expected_outputs)
    assert {
        case.expected_outputs for case in corpus() if case.spec_id == "nonce_replay_guard_v1"
    } == {
        (0, 0, 0, 0),
        (0, 0, 1, 0),
        (0, 1, 0, 0),
        (0, 1, 1, 0),
        (1, 0, 0, 0),
        (1, 0, 1, 0),
        (1, 1, 0, 0),
        (1, 1, 1, 1),
    }


def test_uint32_and_sbf_boundary_validation_rejects_booleans_and_out_of_domain_values() -> None:
    with pytest.raises(TypeError, match="not a boolean"):
        evaluate("nonce_replay_guard_v1", (True, 0, 1))
    with pytest.raises(TypeError, match="not a boolean"):
        evaluate("nonce_manager_v1", (1, False))
    with pytest.raises(TypeError, match="not a boolean"):
        evaluate("transfer_hook_guard_v1", (5, 5, 7, 7, True, 1))
    with pytest.raises(TypeError, match="not a boolean"):
        evaluate("zusd_transfer_guard_v1", (1, 1, 1, True, 1, 0))
    with pytest.raises(ValueError, match="unsigned 32-bit"):
        evaluate("nonce_manager_v1", (UINT32_MAX + 1, 0))
    with pytest.raises(ValueError, match="unsigned 32-bit"):
        evaluate("transfer_hook_guard_v1", (0, -1, 0, 0, 0, 1))
    with pytest.raises(ValueError, match="zero or one"):
        evaluate("transfer_hook_guard_v1", (0, 0, 0, 0, 0, 2))
    with pytest.raises(ValueError, match="zero or one"):
        evaluate("zusd_transfer_guard_v1", (1, 1, 1, 1, 1, -1))
    with pytest.raises(TypeError, match="immutable tuple"):
        evaluate("nonce_replay_guard_v1", [1, 0, 1])  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="unsupported"):
        evaluate("unknown_guard", (0,))


def test_sbf_positions_in_every_fixed_row_are_closed_to_zero_or_one() -> None:
    sbf_indexes = {
        "transfer_hook_guard_v1": (5,),
        "zusd_transfer_guard_v1": (0, 1, 2, 3, 4, 5),
    }
    for case in corpus():
        for index in sbf_indexes.get(case.spec_id, ()):
            assert case.inputs[index] in (0, 1)


def test_immutable_records_do_not_allow_row_or_history_alias_mutation() -> None:
    case = corpus()[0]
    history = stateful_histories()[0]
    with pytest.raises(FrozenInstanceError):
        case.name = "mutated"  # type: ignore[misc]
    with pytest.raises(FrozenInstanceError):
        case.expected_outputs += (0,)  # type: ignore[misc]
    with pytest.raises(FrozenInstanceError):
        history.final_last_nonce = 0  # type: ignore[misc]
    assert type(history.cases) is tuple


def test_modular_transfer_vectors_preserve_each_source_output_independently() -> None:
    cases = _cases_by_name()
    assert evaluate(
        cases["transfer_hook_modular_sum_wrap_with_valid_deltas"].spec_id,
        cases["transfer_hook_modular_sum_wrap_with_valid_deltas"].inputs,
    ) == (1, 1, 1, 1)
    assert evaluate(
        cases["transfer_hook_sender_underflow_keeps_o2_true"].spec_id,
        cases["transfer_hook_sender_underflow_keeps_o2_true"].inputs,
    ) == (0, 1, 1, 0)
    assert evaluate(
        cases["transfer_hook_receiver_wrap_keeps_o2_true"].spec_id,
        cases["transfer_hook_receiver_wrap_keeps_o2_true"].inputs,
    ) == (0, 1, 1, 0)
    assert evaluate(
        cases["transfer_hook_zero_amount_dust_allowed"].spec_id,
        cases["transfer_hook_zero_amount_dust_allowed"].inputs,
    ) == (1, 1, 1, 1)


def test_transfer_direction_delta_and_hook_partitions_cover_every_output_class() -> None:
    transfer_cases = tuple(
        case for case in corpus() if case.spec_id == "transfer_hook_guard_v1"
    )
    assert {
        (case.expected_outputs[0], case.expected_outputs[1], case.expected_outputs[2])
        for case in transfer_cases
    } == {
        (directions_ok, deltas_ok, hook_ok)
        for directions_ok in (0, 1)
        for deltas_ok in (0, 1)
        for hook_ok in (0, 1)
    }
    assert all(
        case.expected_outputs[3] == int(all(case.expected_outputs[:3]))
        for case in transfer_cases
    )


def test_nonce_wrap_and_gap_edges_are_exact_unsigned_vectors() -> None:
    cases = _cases_by_name()
    assert evaluate(
        cases["nonce_replay_wrap_params_and_sequence_not_fresh"].spec_id,
        cases["nonce_replay_wrap_params_and_sequence_not_fresh"].inputs,
    ) == (1, 0, 1, 0)
    assert evaluate(
        cases["nonce_manager_gap_999_accept"].spec_id,
        cases["nonce_manager_gap_999_accept"].inputs,
    ) == (1,)
    assert evaluate(
        cases["nonce_manager_history_gap_boundary_step_1_gap_1000"].spec_id,
        cases["nonce_manager_history_gap_boundary_step_1_gap_1000"].inputs,
    ) == (1,)
    assert evaluate(
        cases["nonce_manager_history_gap_boundary_step_2_gap_1001_rejected"].spec_id,
        cases["nonce_manager_history_gap_boundary_step_2_gap_1001_rejected"].inputs,
    ) == (0,)
    assert evaluate(
        cases["nonce_replay_unsigned_signed_seam_accept"].spec_id,
        cases["nonce_replay_unsigned_signed_seam_accept"].inputs,
    ) == (1, 1, 1, 1)
    assert evaluate(
        cases["nonce_manager_unsigned_signed_seam_accept"].spec_id,
        cases["nonce_manager_unsigned_signed_seam_accept"].inputs,
    ) == (1,)


def test_stale_caller_state_is_only_a_pointwise_observation() -> None:
    cases = _cases_by_name()
    stale_row = cases["nonce_replay_stale_caller_state_reaccepts_pointwise"]
    assert evaluate(stale_row.spec_id, stale_row.inputs) == (1, 1, 1, 1)
    assert stale_row.inputs == cases["nonce_replay_initial_accept"].inputs


def test_pause_then_unpause_rows_are_contiguous_independent_inputs() -> None:
    cases = corpus()
    paused_index = next(
        index for index, case in enumerate(cases) if case.name == "zusd_transfer_pause_then_unpause_paused"
    )
    paused = cases[paused_index]
    unpaused = cases[paused_index + 1]
    assert unpaused.name == "zusd_transfer_pause_then_unpause_unpaused"
    assert paused.inputs[:5] == unpaused.inputs[:5] == (1, 1, 1, 1, 1)
    assert paused.inputs[5] == 1
    assert unpaused.inputs[5] == 0
    assert paused.expected_outputs == (1, 0, 0, 0)
    assert unpaused.expected_outputs == (1, 1, 1, 1)


def test_nonce_histories_advance_external_caller_state_only_after_acceptance() -> None:
    histories = {history.name: history for history in stateful_histories()}
    assert set(histories) == {"replay_then_later_valid", "gap_boundaries", "exhaustion"}
    for history in histories.values():
        assert len(history.cases) <= 8
        last_nonce = history.initial_last_nonce
        for case in history.cases:
            assert case.inputs[1] == last_nonce
            result = evaluate(case.spec_id, case.inputs)
            assert result == case.expected_outputs
            if result == (1,):
                last_nonce = case.inputs[0]
        assert last_nonce == history.final_last_nonce

    replay_history = histories["replay_then_later_valid"]
    assert replay_history.cases[2].inputs[1] == replay_history.cases[1].inputs[1]
    gap_history = histories["gap_boundaries"]
    assert gap_history.cases[2].inputs[1] == gap_history.cases[1].inputs[1]
    exhaustion_history = histories["exhaustion"]
    assert exhaustion_history.cases[2].inputs[1] == exhaustion_history.cases[1].inputs[1]

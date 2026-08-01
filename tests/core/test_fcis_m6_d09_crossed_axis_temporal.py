from __future__ import annotations

from typing import cast

from experiments.fcis_m6_d09_crossed_axis_temporal_check import (
    _build_transitions,
    run_checks,
)
from src.core.fcis_m6_d08_combined_anf import (
    D08CombinedANFAcceptV1,
    verify_combined_anf_v1,
)


def test_d09_uses_two_distinct_valid_d08_transitions() -> None:
    first, second = _build_transitions()
    first_result = verify_combined_anf_v1(first)
    second_result = verify_combined_anf_v1(second)
    assert type(first_result) is D08CombinedANFAcceptV1
    assert type(second_result) is D08CombinedANFAcceptV1
    assert first_result.anf_root != second_result.anf_root
    assert first.base_bundle.bundle_root != second.base_bundle.bundle_root


def test_d09_kills_all_crossed_axis_and_temporal_mutants() -> None:
    payload = run_checks()
    assert payload["mutants_killed"] == 8
    cases = cast(dict[str, object], payload["cases"])
    assert set(cases) == {
        "semantic_transition_1_receipt_transition_2",
        "receipt_transition_1_bundle_transition_2",
        "bundle_transition_1_outbox_transition_2",
        "tcg_receipt_foreign_topology",
        "dra_atom_foreign_authority_epoch",
        "same_semantic_different_lineage",
        "stutter_hiding_new_commit",
        "stutter_hiding_migration",
    }


def test_d09_temporal_mutants_remain_forbidden_operation_rejections() -> None:
    payload = run_checks()
    cases = cast(dict[str, object], payload["cases"])
    assert cases["stutter_hiding_new_commit"] == "forbidden_operation"
    assert cases["stutter_hiding_migration"] == "forbidden_operation"

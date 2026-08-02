"""Focused E06 independent-connection concurrency tests."""

from __future__ import annotations

from experiments.fcis_m6_e06_concurrency import run_campaign


def test_required_races_have_one_linearized_outcome_and_no_partial_rows() -> None:
    observations = run_campaign()

    assert tuple(observation.name for observation in observations) == (
        "same_command_retry",
        "same_sender_nonce_different_command",
        "same_commit_id_different_fingerprint",
        "commit_racing_quiescence",
        "commit_racing_authority_switch",
    )
    for observation in observations[:3]:
        assert observation.result_kinds == ("committed", "rejected")
        assert observation.reject_codes == ("stale_snapshot_cas",)
        assert observation.publication_count == 1
        assert observation.nullifier_count == 1
        assert observation.effect_count == 1
        assert observation.final_authority_epoch_index == 3
    for observation in observations[3:]:
        assert observation.result_kinds == ("head_changed", "rejected")
        assert observation.reject_codes == ("stale_authority_cas",)
        assert observation.publication_count == 0
        assert observation.nullifier_count == 0
        assert observation.effect_count == 0
        assert observation.final_authority_epoch_index == 4


def test_race_summary_is_repeatable() -> None:
    first = tuple(item.to_wire() for item in run_campaign())
    second = tuple(item.to_wire() for item in run_campaign())

    assert first == second

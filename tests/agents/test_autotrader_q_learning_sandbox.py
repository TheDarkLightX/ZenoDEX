from __future__ import annotations

import pytest

from src.agents.autotrader_q_learning_sandbox import (
    AutoTraderQLAction,
    AutoTraderQLConfig,
    AutoTraderQLRewardProfile,
    AutoTraderQLState,
    compare_autotrader_q_reward_profiles,
    coarse_krr_action_for_state,
    recommend_autotrader_q_action,
    train_autotrader_q_table,
)


def test_train_autotrader_q_table_is_deterministic_for_fixed_seed() -> None:
    config = AutoTraderQLConfig(episodes=24, seed=19)
    left = train_autotrader_q_table(config)
    right = train_autotrader_q_table(config)

    assert left.greedy_policy == right.greedy_policy
    assert left.policy_action_counts == right.policy_action_counts
    assert left.oracle_match_ratio == right.oracle_match_ratio
    assert left.average_episode_reward == pytest.approx(right.average_episode_reward)


def test_train_autotrader_q_table_recovers_expected_probe_actions() -> None:
    result = train_autotrader_q_table(AutoTraderQLConfig(episodes=64, seed=7))

    assert (
        recommend_autotrader_q_action(
            result.q_table,
            AutoTraderQLState(0, 0, 2, 0, 0, 0),
        )
        is AutoTraderQLAction.SUBMIT
    )
    assert (
        recommend_autotrader_q_action(
            result.q_table,
            AutoTraderQLState(0, 2, 2, 0, 0, 0),
        )
        is AutoTraderQLAction.SKIP
    )
    assert (
        recommend_autotrader_q_action(
            result.q_table,
            AutoTraderQLState(1, 0, 1, 1, 0, 0),
        )
        is AutoTraderQLAction.WAIT
    )


def test_train_autotrader_q_table_stays_close_to_oracle_policy() -> None:
    result = train_autotrader_q_table(AutoTraderQLConfig(episodes=64, seed=11))

    assert result.oracle_match_ratio >= 0.85
    assert result.coarse_krr_match_ratio >= 0.75
    assert result.policy_action_counts[AutoTraderQLAction.SUBMIT.value] > 0
    assert result.policy_action_counts[AutoTraderQLAction.WAIT.value] > 0
    assert result.policy_action_counts[AutoTraderQLAction.SKIP.value] > 0


def test_coarse_krr_action_for_state_recovers_expected_posture() -> None:
    assert coarse_krr_action_for_state(AutoTraderQLState(0, 0, 2, 0, 0, 0)) is AutoTraderQLAction.SUBMIT
    assert coarse_krr_action_for_state(AutoTraderQLState(0, 2, 2, 0, 0, 0)) is AutoTraderQLAction.WAIT
    assert coarse_krr_action_for_state(AutoTraderQLState(0, 0, 0, 1, 0, 0)) is AutoTraderQLAction.SKIP


def test_train_autotrader_q_table_reward_profiles_shift_action_posture() -> None:
    throughput = train_autotrader_q_table(
        AutoTraderQLConfig(
            episodes=64,
            seed=7,
            reward_profile=AutoTraderQLRewardProfile.THROUGHPUT_BIAS,
        )
    )
    preservation = train_autotrader_q_table(
        AutoTraderQLConfig(
            episodes=64,
            seed=7,
            reward_profile=AutoTraderQLRewardProfile.CAPITAL_PRESERVATION,
        )
    )

    assert throughput.config.reward_profile is AutoTraderQLRewardProfile.THROUGHPUT_BIAS
    assert preservation.config.reward_profile is AutoTraderQLRewardProfile.CAPITAL_PRESERVATION
    assert throughput.policy_action_counts[AutoTraderQLAction.SUBMIT.value] > preservation.policy_action_counts[
        AutoTraderQLAction.SUBMIT.value
    ]
    assert preservation.policy_action_counts[AutoTraderQLAction.WAIT.value] > throughput.policy_action_counts[
        AutoTraderQLAction.WAIT.value
    ]


def test_compare_autotrader_q_reward_profiles_reports_pairwise_deltas() -> None:
    comparison = compare_autotrader_q_reward_profiles(AutoTraderQLConfig(episodes=64, seed=7))
    payload = comparison.to_dict()

    assert payload["schema"] == "zenodex/autotrader-tabular-q-profile-compare/v1"
    assert payload["baseline_profile"] == "balanced"
    assert payload["profile_summaries"]["throughput_bias"]["policy_action_counts"]["submit"] > payload[
        "profile_summaries"
    ]["capital_preservation"]["policy_action_counts"]["submit"]
    assert payload["pairwise_deltas"]["throughput_bias"]["submit_delta"] > 0
    assert payload["pairwise_deltas"]["capital_preservation"]["wait_delta"] > 0
    flip_map = {entry["name"]: entry for entry in payload["probe_flip_states"]}
    assert flip_map["wait_for_spacing"]["flipped_profiles"] == ["throughput_bias"]
    assert flip_map["wait_for_spacing"]["profile_actions"]["throughput_bias"] == "submit"
    assert flip_map["skip_for_stale_oracle"]["flipped_profiles"] == ["execution_safety"]
    assert flip_map["skip_for_stale_oracle"]["profile_actions"]["execution_safety"] == "wait"
    summary = payload["policy_flip_summary"]
    assert summary["state_count"] == 324
    assert summary["unstable_state_count"] > 0
    assert summary["stable_state_count"] < 324
    assert summary["action_variant_histogram"]["wait|skip"] > 0
    assert summary["action_variant_histogram"]["submit|wait"] > 0
    top_state = summary["top_unstable_states"][0]
    assert top_state["flip_count"] >= 1
    assert len(top_state["action_variants"]) >= 2
    coarse_krr_alignment = payload["coarse_krr_alignment"]
    assert coarse_krr_alignment["policy_action_counts"]["wait"] > coarse_krr_alignment["policy_action_counts"]["submit"]
    assert coarse_krr_alignment["best_aligned_profile"] == "balanced"
    assert coarse_krr_alignment["worst_aligned_profile"] == "capital_preservation"
    assert coarse_krr_alignment["profile_match_ratios"]["balanced"] > coarse_krr_alignment["profile_match_ratios"]["throughput_bias"]
    assert coarse_krr_alignment["match_ratio_deltas_vs_baseline"]["throughput_bias"] < 0


def test_train_autotrader_q_table_rejects_invalid_config() -> None:
    with pytest.raises(ValueError, match="episodes must be positive"):
        train_autotrader_q_table(AutoTraderQLConfig(episodes=0))

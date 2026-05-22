"""Deterministic, advisory-only tabular Q-learning sandbox for auto-trader research."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from itertools import product
from random import Random
from typing import Any

AUTOTRADER_TABULAR_Q_SCHEMA = "zenodex/autotrader-tabular-q-sandbox/v1"
AUTOTRADER_TABULAR_Q_COMPARE_SCHEMA = "zenodex/autotrader-tabular-q-profile-compare/v1"


class AutoTraderQLAction(StrEnum):
    SUBMIT = "submit"
    WAIT = "wait"
    SKIP = "skip"


class AutoTraderQLRewardProfile(StrEnum):
    BALANCED = "balanced"
    EXECUTION_SAFETY = "execution_safety"
    CAPITAL_PRESERVATION = "capital_preservation"
    THROUGHPUT_BIAS = "throughput_bias"


_ACTION_ORDER: tuple[AutoTraderQLAction, ...] = (
    AutoTraderQLAction.SUBMIT,
    AutoTraderQLAction.WAIT,
    AutoTraderQLAction.SKIP,
)

_PROFILE_ORDER: tuple[AutoTraderQLRewardProfile, ...] = (
    AutoTraderQLRewardProfile.BALANCED,
    AutoTraderQLRewardProfile.EXECUTION_SAFETY,
    AutoTraderQLRewardProfile.CAPITAL_PRESERVATION,
    AutoTraderQLRewardProfile.THROUGHPUT_BIAS,
)


@dataclass(frozen=True)
class AutoTraderQLState:
    slippage_bucket: int
    oracle_bucket: int
    trust_bucket: int
    route_risk_bucket: int
    spacing_bucket: int
    budget_bucket: int

    def key(self) -> str:
        return (
            f"{self.slippage_bucket}|{self.oracle_bucket}|{self.trust_bucket}|"
            f"{self.route_risk_bucket}|{self.spacing_bucket}|{self.budget_bucket}"
        )

    def to_dict(self) -> dict[str, int]:
        return {
            "slippage_bucket": self.slippage_bucket,
            "oracle_bucket": self.oracle_bucket,
            "trust_bucket": self.trust_bucket,
            "route_risk_bucket": self.route_risk_bucket,
            "spacing_bucket": self.spacing_bucket,
            "budget_bucket": self.budget_bucket,
        }

    @classmethod
    def from_key(cls, raw: str) -> "AutoTraderQLState":
        parts = raw.split("|")
        if len(parts) != 6:
            raise ValueError(f"invalid state key: {raw!r}")
        try:
            values = tuple(int(part) for part in parts)
        except ValueError as exc:
            raise ValueError(f"invalid state key: {raw!r}") from exc
        state = cls(*values)
        _validate_state(state)
        return state


@dataclass(frozen=True)
class AutoTraderQLConfig:
    episodes: int = 48
    alpha: float = 0.30
    gamma: float = 0.90
    epsilon: float = 0.15
    seed: int = 7
    reward_profile: AutoTraderQLRewardProfile = AutoTraderQLRewardProfile.BALANCED

    def to_dict(self) -> dict[str, float | int | str]:
        return {
            "episodes": self.episodes,
            "alpha": self.alpha,
            "gamma": self.gamma,
            "epsilon": self.epsilon,
            "seed": self.seed,
            "reward_profile": self.reward_profile.value,
        }


@dataclass(frozen=True)
class AutoTraderQLTrainingResult:
    config: AutoTraderQLConfig
    q_table: dict[str, dict[str, float]]
    greedy_policy: dict[str, str]
    oracle_policy: dict[str, str]
    state_visit_counts: dict[str, int]
    average_episode_reward: float
    policy_action_counts: dict[str, int]
    oracle_match_ratio: float
    coarse_krr_match_ratio: float
    coarse_krr_policy_action_counts: dict[str, int]

    def to_dict(self, *, include_q_table: bool = True) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "schema": AUTOTRADER_TABULAR_Q_SCHEMA,
            "advisory_only": True,
            "training_config": self.config.to_dict(),
            "state_count": len(self.greedy_policy),
            "action_space": [action.value for action in _ACTION_ORDER],
            "greedy_policy": dict(self.greedy_policy),
            "oracle_policy": dict(self.oracle_policy),
            "state_visit_counts": dict(self.state_visit_counts),
            "average_episode_reward": round(self.average_episode_reward, 6),
            "policy_action_counts": dict(self.policy_action_counts),
            "oracle_match_ratio": round(self.oracle_match_ratio, 6),
            "coarse_krr_match_ratio": round(self.coarse_krr_match_ratio, 6),
            "coarse_krr_policy_action_counts": dict(self.coarse_krr_policy_action_counts),
            "probe_states": default_autotrader_q_probe_states(self),
        }
        if include_q_table:
            payload["q_table"] = {
                state_key: {action: round(value, 6) for action, value in row.items()}
                for state_key, row in sorted(self.q_table.items())
            }
        return payload


@dataclass(frozen=True)
class AutoTraderQLProfileComparison:
    base_config: AutoTraderQLConfig
    baseline_profile: AutoTraderQLRewardProfile
    profile_summaries: dict[str, dict[str, Any]]
    pairwise_deltas: dict[str, dict[str, float | int]]
    probe_flip_states: list[dict[str, Any]]
    policy_flip_summary: dict[str, Any]
    coarse_krr_alignment: dict[str, Any]

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": AUTOTRADER_TABULAR_Q_COMPARE_SCHEMA,
            "advisory_only": True,
            "base_training_config": self.base_config.to_dict(),
            "baseline_profile": self.baseline_profile.value,
            "profile_summaries": self.profile_summaries,
            "pairwise_deltas": self.pairwise_deltas,
            "probe_flip_states": self.probe_flip_states,
            "policy_flip_summary": self.policy_flip_summary,
            "coarse_krr_alignment": self.coarse_krr_alignment,
        }


def _validate_state(state: AutoTraderQLState) -> None:
    for name, value, upper in (
        ("slippage_bucket", state.slippage_bucket, 2),
        ("oracle_bucket", state.oracle_bucket, 2),
        ("trust_bucket", state.trust_bucket, 2),
        ("route_risk_bucket", state.route_risk_bucket, 1),
        ("spacing_bucket", state.spacing_bucket, 1),
        ("budget_bucket", state.budget_bucket, 2),
    ):
        if not isinstance(value, int) or value < 0 or value > upper:
            raise ValueError(f"{name} out of range: {value!r}")


def iter_autotrader_q_states() -> tuple[AutoTraderQLState, ...]:
    return tuple(
        AutoTraderQLState(*values)
        for values in product(range(3), range(3), range(3), range(2), range(2), range(3))
    )


def oracle_action_for_state(state: AutoTraderQLState) -> AutoTraderQLAction:
    _validate_state(state)
    if state.oracle_bucket == 2 or state.budget_bucket == 2:
        return AutoTraderQLAction.SKIP
    if state.spacing_bucket == 1:
        return AutoTraderQLAction.WAIT
    if state.slippage_bucket == 2 and state.trust_bucket <= 1:
        return AutoTraderQLAction.SKIP
    if state.route_risk_bucket == 1 and state.trust_bucket == 0:
        return AutoTraderQLAction.SKIP
    if state.oracle_bucket == 1 and state.trust_bucket <= 1:
        return AutoTraderQLAction.WAIT
    if state.slippage_bucket == 2 or state.route_risk_bucket == 1 or state.trust_bucket == 0:
        return AutoTraderQLAction.WAIT
    return AutoTraderQLAction.SUBMIT


def coarse_krr_action_for_state(state: AutoTraderQLState) -> AutoTraderQLAction:
    _validate_state(state)
    if state.budget_bucket == 2:
        return AutoTraderQLAction.SKIP
    if state.oracle_bucket == 2:
        if state.trust_bucket == 2 and state.route_risk_bucket == 0:
            return AutoTraderQLAction.WAIT
        return AutoTraderQLAction.SKIP
    if state.spacing_bucket == 1:
        return AutoTraderQLAction.WAIT
    if state.route_risk_bucket == 1 and state.trust_bucket <= 1:
        return AutoTraderQLAction.SKIP
    if state.slippage_bucket == 2:
        if state.trust_bucket == 2 and state.route_risk_bucket == 0 and state.oracle_bucket == 0:
            return AutoTraderQLAction.WAIT
        return AutoTraderQLAction.SKIP
    if state.oracle_bucket == 1:
        return AutoTraderQLAction.WAIT
    if state.trust_bucket == 0:
        if state.route_risk_bucket == 0 and state.slippage_bucket <= 1:
            return AutoTraderQLAction.WAIT
        return AutoTraderQLAction.SKIP
    if state.route_risk_bucket == 1:
        return AutoTraderQLAction.WAIT
    return AutoTraderQLAction.SUBMIT


def _reward_profile_settings(profile: AutoTraderQLRewardProfile) -> dict[str, Any]:
    if profile is AutoTraderQLRewardProfile.EXECUTION_SAFETY:
        return {
            "matrix": {
                AutoTraderQLAction.SUBMIT: {
                    AutoTraderQLAction.SUBMIT: 1.35,
                    AutoTraderQLAction.WAIT: -0.20,
                    AutoTraderQLAction.SKIP: -0.55,
                },
                AutoTraderQLAction.WAIT: {
                    AutoTraderQLAction.SUBMIT: -0.95,
                    AutoTraderQLAction.WAIT: 1.20,
                    AutoTraderQLAction.SKIP: 0.35,
                },
                AutoTraderQLAction.SKIP: {
                    AutoTraderQLAction.SUBMIT: -2.50,
                    AutoTraderQLAction.WAIT: -0.25,
                    AutoTraderQLAction.SKIP: 1.40,
                },
            },
            "submit": {"trust": 0.24, "slippage": 0.34, "oracle": 0.32, "route": 0.28, "budget": 0.20},
            "wait": {"spacing": 0.28, "oracle": 0.18, "trust": 0.05},
            "skip": {"oracle": 0.24, "budget": 0.22, "route": 0.18, "trust": 0.06},
        }
    if profile is AutoTraderQLRewardProfile.CAPITAL_PRESERVATION:
        return {
            "matrix": {
                AutoTraderQLAction.SUBMIT: {
                    AutoTraderQLAction.SUBMIT: 1.10,
                    AutoTraderQLAction.WAIT: -0.15,
                    AutoTraderQLAction.SKIP: 0.05,
                },
                AutoTraderQLAction.WAIT: {
                    AutoTraderQLAction.SUBMIT: -1.05,
                    AutoTraderQLAction.WAIT: 1.05,
                    AutoTraderQLAction.SKIP: 0.50,
                },
                AutoTraderQLAction.SKIP: {
                    AutoTraderQLAction.SUBMIT: -2.80,
                    AutoTraderQLAction.WAIT: -0.10,
                    AutoTraderQLAction.SKIP: 1.75,
                },
            },
            "submit": {"trust": 0.20, "slippage": 0.38, "oracle": 0.36, "route": 0.32, "budget": 0.26},
            "wait": {"spacing": 0.18, "oracle": 0.14, "trust": 0.04},
            "skip": {"oracle": 0.32, "budget": 0.34, "route": 0.20, "trust": 0.02},
        }
    if profile is AutoTraderQLRewardProfile.THROUGHPUT_BIAS:
        return {
            "matrix": {
                AutoTraderQLAction.SUBMIT: {
                    AutoTraderQLAction.SUBMIT: 1.95,
                    AutoTraderQLAction.WAIT: -0.60,
                    AutoTraderQLAction.SKIP: -1.20,
                },
                AutoTraderQLAction.WAIT: {
                    AutoTraderQLAction.SUBMIT: -0.45,
                    AutoTraderQLAction.WAIT: 0.85,
                    AutoTraderQLAction.SKIP: 0.10,
                },
                AutoTraderQLAction.SKIP: {
                    AutoTraderQLAction.SUBMIT: -1.60,
                    AutoTraderQLAction.WAIT: -0.70,
                    AutoTraderQLAction.SKIP: 0.90,
                },
            },
            "submit": {"trust": 0.36, "slippage": 0.15, "oracle": 0.12, "route": 0.10, "budget": 0.08},
            "wait": {"spacing": 0.18, "oracle": 0.06, "trust": 0.12},
            "skip": {"oracle": 0.10, "budget": 0.10, "route": 0.06, "trust": 0.16},
        }
    return {
        "matrix": {
            AutoTraderQLAction.SUBMIT: {
                AutoTraderQLAction.SUBMIT: 1.60,
                AutoTraderQLAction.WAIT: -0.40,
                AutoTraderQLAction.SKIP: -0.90,
            },
            AutoTraderQLAction.WAIT: {
                AutoTraderQLAction.SUBMIT: -0.70,
                AutoTraderQLAction.WAIT: 1.00,
                AutoTraderQLAction.SKIP: 0.25,
            },
            AutoTraderQLAction.SKIP: {
                AutoTraderQLAction.SUBMIT: -2.10,
                AutoTraderQLAction.WAIT: -0.50,
                AutoTraderQLAction.SKIP: 1.25,
            },
        },
        "submit": {"trust": 0.30, "slippage": 0.22, "oracle": 0.18, "route": 0.15, "budget": 0.12},
        "wait": {"spacing": 0.20, "oracle": 0.10, "trust": 0.08},
        "skip": {"oracle": 0.18, "budget": 0.16, "route": 0.10, "trust": 0.12},
    }


def _reward_for_action(
    state: AutoTraderQLState,
    action: AutoTraderQLAction,
    profile: AutoTraderQLRewardProfile,
) -> float:
    oracle_action = oracle_action_for_state(state)
    settings = _reward_profile_settings(profile)
    reward_matrix: dict[AutoTraderQLAction, dict[AutoTraderQLAction, float]] = settings["matrix"]
    reward = reward_matrix[oracle_action][action]
    if action is AutoTraderQLAction.SUBMIT:
        coeffs = settings["submit"]
        reward += coeffs["trust"] * state.trust_bucket
        reward -= coeffs["slippage"] * state.slippage_bucket
        reward -= coeffs["oracle"] * state.oracle_bucket
        reward -= coeffs["route"] * state.route_risk_bucket
        reward -= coeffs["budget"] * state.budget_bucket
    elif action is AutoTraderQLAction.WAIT:
        coeffs = settings["wait"]
        reward += coeffs["spacing"] * state.spacing_bucket
        reward += coeffs["oracle"] * state.oracle_bucket
        reward -= coeffs["trust"] * state.trust_bucket
    else:
        coeffs = settings["skip"]
        reward += coeffs["oracle"] * state.oracle_bucket
        reward += coeffs["budget"] * state.budget_bucket
        reward += coeffs["route"] * state.route_risk_bucket
        reward -= coeffs["trust"] * state.trust_bucket
    return reward


def _best_action_from_row(row: dict[str, float]) -> AutoTraderQLAction:
    return min(
        _ACTION_ORDER,
        key=lambda action: (-float(row[action.value]), _ACTION_ORDER.index(action)),
    )


def recommend_autotrader_q_action(
    q_table: dict[str, dict[str, float]],
    state: AutoTraderQLState,
) -> AutoTraderQLAction:
    _validate_state(state)
    row = q_table.get(state.key())
    if row is None:
        return oracle_action_for_state(state)
    return _best_action_from_row(row)


def train_autotrader_q_table(config: AutoTraderQLConfig) -> AutoTraderQLTrainingResult:
    if config.episodes <= 0:
        raise ValueError("episodes must be positive")
    if not 0.0 < config.alpha <= 1.0:
        raise ValueError("alpha must be in (0, 1]")
    if not 0.0 <= config.gamma <= 1.0:
        raise ValueError("gamma must be in [0, 1]")
    if not 0.0 <= config.epsilon <= 1.0:
        raise ValueError("epsilon must be in [0, 1]")

    rng = Random(config.seed)
    states = list(iter_autotrader_q_states())
    q_table = {
        state.key(): {action.value: 0.0 for action in _ACTION_ORDER}
        for state in states
    }
    state_visit_counts = {state.key(): 0 for state in states}
    episode_rewards: list[float] = []

    for _episode in range(config.episodes):
        order = list(states)
        rng.shuffle(order)
        total_reward = 0.0
        for index, state in enumerate(order):
            key = state.key()
            state_visit_counts[key] += 1
            if rng.random() < config.epsilon:
                action = rng.choice(_ACTION_ORDER)
            else:
                action = _best_action_from_row(q_table[key])
            reward = _reward_for_action(state, action, config.reward_profile)
            next_state = order[(index + 1) % len(order)]
            next_key = next_state.key()
            next_best = q_table[next_key][_best_action_from_row(q_table[next_key]).value]
            current_q = q_table[key][action.value]
            target = reward + config.gamma * next_best
            q_table[key][action.value] = current_q + config.alpha * (target - current_q)
            total_reward += reward
        episode_rewards.append(total_reward / float(len(order)))

    greedy_policy = {
        state.key(): recommend_autotrader_q_action(q_table, state).value for state in states
    }
    oracle_policy = {state.key(): oracle_action_for_state(state).value for state in states}
    policy_action_counts = {action.value: 0 for action in _ACTION_ORDER}
    coarse_krr_policy_action_counts = {action.value: 0 for action in _ACTION_ORDER}
    oracle_matches = 0
    coarse_krr_matches = 0
    for state in states:
        state_key = state.key()
        action_name = greedy_policy[state_key]
        policy_action_counts[action_name] += 1
        if action_name == oracle_policy[state_key]:
            oracle_matches += 1
        coarse_krr_action = coarse_krr_action_for_state(state).value
        coarse_krr_policy_action_counts[coarse_krr_action] += 1
        if action_name == coarse_krr_action:
            coarse_krr_matches += 1
    average_episode_reward = sum(episode_rewards) / float(len(episode_rewards))
    oracle_match_ratio = oracle_matches / float(len(states))
    coarse_krr_match_ratio = coarse_krr_matches / float(len(states))
    return AutoTraderQLTrainingResult(
        config=config,
        q_table=q_table,
        greedy_policy=greedy_policy,
        oracle_policy=oracle_policy,
        state_visit_counts=state_visit_counts,
        average_episode_reward=average_episode_reward,
        policy_action_counts=policy_action_counts,
        oracle_match_ratio=oracle_match_ratio,
        coarse_krr_match_ratio=coarse_krr_match_ratio,
        coarse_krr_policy_action_counts=coarse_krr_policy_action_counts,
    )


def _profile_summary(result: AutoTraderQLTrainingResult) -> dict[str, Any]:
    return {
        "reward_profile": result.config.reward_profile.value,
        "average_episode_reward": round(result.average_episode_reward, 6),
        "oracle_match_ratio": round(result.oracle_match_ratio, 6),
        "coarse_krr_match_ratio": round(result.coarse_krr_match_ratio, 6),
        "policy_action_counts": dict(result.policy_action_counts),
        "probe_states": default_autotrader_q_probe_states(result),
    }


def compare_autotrader_q_reward_profiles(
    base_config: AutoTraderQLConfig,
    *,
    baseline_profile: AutoTraderQLRewardProfile = AutoTraderQLRewardProfile.BALANCED,
    profiles: tuple[AutoTraderQLRewardProfile, ...] = _PROFILE_ORDER,
) -> AutoTraderQLProfileComparison:
    if baseline_profile not in profiles:
        raise ValueError("baseline_profile must be included in profiles")
    summaries: dict[str, dict[str, Any]] = {}
    raw_results: dict[AutoTraderQLRewardProfile, AutoTraderQLTrainingResult] = {}
    for profile in profiles:
        result = train_autotrader_q_table(
            AutoTraderQLConfig(
                episodes=base_config.episodes,
                alpha=base_config.alpha,
                gamma=base_config.gamma,
                epsilon=base_config.epsilon,
                seed=base_config.seed,
                reward_profile=profile,
            )
        )
        raw_results[profile] = result
        summaries[profile.value] = _profile_summary(result)

    baseline = raw_results[baseline_profile]
    pairwise_deltas: dict[str, dict[str, float | int]] = {}
    for profile, result in raw_results.items():
        if profile is baseline_profile:
            continue
        pairwise_deltas[profile.value] = {
            "submit_delta": result.policy_action_counts[AutoTraderQLAction.SUBMIT.value]
            - baseline.policy_action_counts[AutoTraderQLAction.SUBMIT.value],
            "wait_delta": result.policy_action_counts[AutoTraderQLAction.WAIT.value]
            - baseline.policy_action_counts[AutoTraderQLAction.WAIT.value],
            "skip_delta": result.policy_action_counts[AutoTraderQLAction.SKIP.value]
            - baseline.policy_action_counts[AutoTraderQLAction.SKIP.value],
            "oracle_match_ratio_delta": round(result.oracle_match_ratio - baseline.oracle_match_ratio, 6),
            "average_episode_reward_delta": round(
                result.average_episode_reward - baseline.average_episode_reward,
                6,
            ),
        }

    baseline_probes = {
        probe["name"]: probe for probe in summaries[baseline_profile.value]["probe_states"]
    }
    probe_flip_states: list[dict[str, Any]] = []
    for probe_name, baseline_probe in baseline_probes.items():
        profile_actions = {
            profile.value: next(
                probe["greedy_action"]
                for probe in summaries[profile.value]["probe_states"]
                if probe["name"] == probe_name
            )
            for profile in profiles
        }
        flipped_profiles = [
            profile_name
            for profile_name, action_name in profile_actions.items()
            if action_name != baseline_probe["greedy_action"]
        ]
        if not flipped_profiles:
            continue
        probe_flip_states.append(
            {
                "name": probe_name,
                "state_key": baseline_probe["state_key"],
                "state": baseline_probe["state"],
                "oracle_action": baseline_probe["oracle_action"],
                "baseline_action": baseline_probe["greedy_action"],
                "profile_actions": profile_actions,
                "flipped_profiles": flipped_profiles,
                "flip_count": len(flipped_profiles),
            }
        )

    unstable_states: list[dict[str, Any]] = []
    action_variant_histogram: dict[str, int] = {}
    for state in iter_autotrader_q_states():
        state_key = state.key()
        baseline_action = raw_results[baseline_profile].greedy_policy[state_key]
        profile_actions = {
            profile.value: raw_results[profile].greedy_policy[state_key]
            for profile in profiles
        }
        action_variants = sorted(
            set(profile_actions.values()),
            key=lambda action_name: _ACTION_ORDER.index(AutoTraderQLAction(action_name)),
        )
        if len(action_variants) <= 1:
            continue
        flipped_profiles = [
            profile_name
            for profile_name, action_name in profile_actions.items()
            if action_name != baseline_action
        ]
        variant_key = "|".join(action_variants)
        action_variant_histogram[variant_key] = action_variant_histogram.get(variant_key, 0) + 1
        unstable_states.append(
            {
                "state_key": state_key,
                "state": state.to_dict(),
                "oracle_action": oracle_action_for_state(state).value,
                "baseline_action": baseline_action,
                "action_variants": action_variants,
                "profile_actions": profile_actions,
                "flipped_profiles": flipped_profiles,
                "flip_count": len(flipped_profiles),
            }
        )

    unstable_states.sort(key=lambda entry: (-int(entry["flip_count"]), str(entry["state_key"])))
    state_count = len(tuple(iter_autotrader_q_states()))
    policy_flip_summary = {
        "state_count": state_count,
        "unstable_state_count": len(unstable_states),
        "stable_state_count": state_count - len(unstable_states),
        "max_flip_count": max((int(entry["flip_count"]) for entry in unstable_states), default=0),
        "action_variant_histogram": dict(sorted(action_variant_histogram.items())),
        "top_unstable_states": unstable_states[:10],
    }

    profile_match_ratios = {
        profile.value: round(raw_results[profile].coarse_krr_match_ratio, 6)
        for profile in profiles
    }
    coarse_krr_policy_action_counts = {action.value: 0 for action in _ACTION_ORDER}
    for state in iter_autotrader_q_states():
        coarse_krr_policy_action_counts[coarse_krr_action_for_state(state).value] += 1
    ordered_profiles = list(profiles)
    best_aligned_profile = max(
        ordered_profiles,
        key=lambda profile: (raw_results[profile].coarse_krr_match_ratio, -ordered_profiles.index(profile)),
    )
    worst_aligned_profile = min(
        ordered_profiles,
        key=lambda profile: (raw_results[profile].coarse_krr_match_ratio, ordered_profiles.index(profile)),
    )
    coarse_krr_alignment = {
        "policy_action_counts": coarse_krr_policy_action_counts,
        "profile_match_ratios": profile_match_ratios,
        "best_aligned_profile": best_aligned_profile.value,
        "worst_aligned_profile": worst_aligned_profile.value,
        "match_ratio_deltas_vs_baseline": {
            profile.value: round(
                raw_results[profile].coarse_krr_match_ratio - raw_results[baseline_profile].coarse_krr_match_ratio,
                6,
            )
            for profile in ordered_profiles
            if profile is not baseline_profile
        },
    }

    return AutoTraderQLProfileComparison(
        base_config=base_config,
        baseline_profile=baseline_profile,
        profile_summaries=summaries,
        pairwise_deltas=pairwise_deltas,
        probe_flip_states=probe_flip_states,
        policy_flip_summary=policy_flip_summary,
        coarse_krr_alignment=coarse_krr_alignment,
    )


def default_autotrader_q_probe_states(
    result: AutoTraderQLTrainingResult,
) -> list[dict[str, Any]]:
    probes = (
        ("favorable_submit", AutoTraderQLState(0, 0, 2, 0, 0, 0)),
        ("wait_for_spacing", AutoTraderQLState(0, 0, 2, 0, 1, 0)),
        ("wait_for_route_risk", AutoTraderQLState(1, 0, 1, 1, 0, 0)),
        ("skip_for_stale_oracle", AutoTraderQLState(0, 2, 2, 0, 0, 0)),
        ("skip_for_budget_exhaustion", AutoTraderQLState(0, 0, 2, 0, 0, 2)),
    )
    out: list[dict[str, Any]] = []
    for name, state in probes:
        key = state.key()
        row = result.q_table[key]
        greedy_action = result.greedy_policy[key]
        oracle_action = result.oracle_policy[key]
        out.append(
            {
                "name": name,
                "state": state.to_dict(),
                "state_key": key,
                "greedy_action": greedy_action,
                "oracle_action": oracle_action,
                "q_values": {action: round(value, 6) for action, value in row.items()},
                "oracle_match": greedy_action == oracle_action,
            }
        )
    return out

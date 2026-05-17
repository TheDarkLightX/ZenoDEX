"""Deterministic hand-coded UPBA v2 advisory energy."""

from __future__ import annotations

from typing import Mapping, Sequence

from src.core.uniform_batch_clearing import UniformBatchCertificateV1
from src.energy.upba_v2_features import UpbaV2FeatureRecord, extract_upba_v2_feature_record
from src.state.balances import BalanceTable
from src.state.intents import Intent
from src.state.pools import PoolState

HARD_BARRIER_COMPONENTS = frozenset(
    {
        "invalid_balance",
        "limit_price_violation",
        "negative_reserve",
        "cpmm_invariant_violation",
        "noncanonical_fill_vector",
        "schema_policy_mismatch",
        "price_ratio_unreduced",
        "price_objective_violation",
        "output_mismatch",
        "fill_coverage_violation",
        "duplicate_fill_id",
        "unknown_fill_id",
        "executed_input_over_amount",
        "output_without_input",
        "zero_net_input",
    }
)


def hand_energy_breakdown_from_record(record: UpbaV2FeatureRecord) -> dict[str, float]:
    """Return named hand-energy components for failure localization."""

    raw = record.raw
    total_amount_in = max(1, int(raw.get("total_amount_in", 1)))
    normalized_executed_volume = max(0.0, min(1.0, int(raw.get("volume", 0)) / total_amount_in))
    normalized_surplus = max(-1.0, min(1.0, int(raw.get("surplus", 0)) / total_amount_in))

    return {
        "invalid_balance": 1_000_000.0 * int(raw.get("balance_violation_count", 0)),
        "limit_price_violation": 1_000_000.0 * int(raw.get("limit_violation_count", 0)),
        "negative_reserve": 1_000_000.0 * int(raw.get("negative_reserve_flag", 0)),
        "cpmm_invariant_violation": 1_000_000.0 * int(raw.get("invariant_violation_flag", 0)),
        "noncanonical_fill_vector": 100_000.0 * int(raw.get("noncanonical_fill_vector_flag", 0)),
        "schema_policy_mismatch": 100_000.0 * int(raw.get("schema_policy_mismatch_flag", 0)),
        "price_ratio_unreduced": 50_000.0 * int(raw.get("price_ratio_unreduced_flag", 0)),
        "price_objective_violation": 100_000.0 * int(raw.get("price_objective_violation_flag", 0)),
        "output_mismatch": 100_000.0 * int(raw.get("output_mismatch_count", 0)),
        "fill_coverage_violation": 100_000.0 * int(raw.get("fill_coverage_violation_flag", 0)),
        "duplicate_fill_id": 100_000.0 * int(raw.get("duplicate_fill_id_flag", 0)),
        "unknown_fill_id": 100_000.0 * int(raw.get("unknown_fill_id_count", 0)),
        "executed_input_over_amount": 100_000.0
        * int(raw.get("executed_input_over_amount_count", 0)),
        "output_without_input": 100_000.0 * int(raw.get("output_without_input_count", 0)),
        "zero_net_input": 10_000.0 * int(raw.get("zero_net_input_count", 0)),
        "dust": 100.0 * int(raw.get("dust_penalty", 0)),
        "imbalance": 10.0 * float(raw.get("imbalance_penalty", 0.0)),
        "executed_volume_reward": -10.0 * normalized_executed_volume,
        "surplus_reward": -1.0 * normalized_surplus,
    }


def hand_energy_from_record(record: UpbaV2FeatureRecord) -> float:
    """Return lower-is-better deterministic hand energy for a feature record."""

    return sum(hand_energy_breakdown_from_record(record).values())


def hard_barrier_energy_from_record(record: UpbaV2FeatureRecord) -> float:
    """Return the deterministic hard-violation part of the hand energy."""

    breakdown = hand_energy_breakdown_from_record(record)
    return sum(value for name, value in breakdown.items() if name in HARD_BARRIER_COMPONENTS)


def primary_energy_failure_from_record(record: UpbaV2FeatureRecord) -> str | None:
    """Return the largest positive hand-energy component, if any."""

    penalties = {
        name: value
        for name, value in hand_energy_breakdown_from_record(record).items()
        if value > 0.0
    }
    if not penalties:
        return None
    return max(penalties, key=lambda name: (penalties[name], name))


def score_upba_v2_hand_energy(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    candidate: UniformBatchCertificateV1 | Mapping[str, object],
) -> float:
    """Extract features and score a candidate with the hand-coded energy."""

    return hand_energy_from_record(
        extract_upba_v2_feature_record(
            pool=pool,
            intents=intents,
            balances=balances,
            candidate=candidate,
            include_verifier_label=False,
        )
    )

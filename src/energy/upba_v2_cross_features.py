"""Crossed UPBA v2 features for advisory energy rankers.

This module turns the reserved tail of the fixed UPBA v2 feature vector into
deterministic interaction terms. The crossed vector is still advisory-only:
it may guide candidate ordering, but deterministic UPBA verification remains
the acceptance authority.
"""

from __future__ import annotations

from math import log1p
from typing import Any, Sequence

from src.core.uniform_batch_clearing import UniformBatchCertificateV1
from src.energy.upba_v2_features import FEATURE_NAMES, extract_upba_v2_feature_record
from src.state.balances import BalanceTable
from src.state.intents import Intent
from src.state.pools import PoolState


FIRST_RESERVED_INDEX = FEATURE_NAMES.index("reserved_00")

GEMINI_CROSS_NAMES: tuple[str, ...] = (
    "gemini_volume_x_surplus",
    "gemini_volume_x_imbalance",
    "gemini_surplus_x_imbalance",
    "gemini_volume_x_price_violation",
    "gemini_volume_x_invariant_violation",
    "gemini_volume_x_limit_violation",
    "gemini_volume_x_balance_violation",
    "gemini_volume_squared",
    "gemini_surplus_squared",
    "gemini_vol_surp_imb_triple",
    "gemini_vol_x_spot_price",
    "gemini_surp_x_fee_bps",
    "gemini_inv_v_x_price_v",
    "gemini_lim_v_x_bal_v",
)

GEMINI_FEATURE_NAMES: tuple[str, ...] = (
    FEATURE_NAMES[:FIRST_RESERVED_INDEX]
    + GEMINI_CROSS_NAMES
    + FEATURE_NAMES[FIRST_RESERVED_INDEX + len(GEMINI_CROSS_NAMES) :]
)

UPBA_V2_CROSSED_FEATURE_NAMES = GEMINI_FEATURE_NAMES

_FEATURE_INDEX = {name: index for index, name in enumerate(FEATURE_NAMES)}


def extract_gemini_features(base_features: Sequence[float]) -> tuple[float, ...]:
    """Compatibility wrapper for Gemini's crossed-feature checkpoint."""

    return extract_upba_v2_crossed_features(base_features)


def extract_upba_v2_crossed_features(base_features: Sequence[float]) -> tuple[float, ...]:
    """Return a 96-dimensional feature vector with deterministic interactions."""

    if len(base_features) != len(FEATURE_NAMES):
        raise ValueError(f"expected {len(FEATURE_NAMES)} base features, got {len(base_features)}")

    values = tuple(float(value) for value in base_features)
    volume = _value(values, "candidate_normalized_executed_volume")
    surplus = _value(values, "candidate_normalized_surplus")
    imbalance = _value(values, "candidate_imbalance_penalty")
    price_violation = _value(values, "candidate_price_objective_violation_flag")
    invariant_violation = _value(values, "candidate_invariant_violation_flag")
    limit_violation = _value(values, "candidate_limit_violation_count_norm")
    balance_violation = _value(values, "candidate_balance_violation_count_norm")
    spot_price = _value(values, "pool_spot_price_ratio")
    fee_bps = _value(values, "pool_fee_bps_norm")

    crosses = (
        _log_cross(volume, surplus),
        _log_cross(volume, imbalance),
        _log_cross(surplus, imbalance),
        volume * price_violation,
        volume * invariant_violation,
        volume * limit_violation,
        volume * balance_violation,
        volume * volume,
        surplus * surplus,
        _log_cross(volume * surplus, imbalance),
        _log_cross(volume, spot_price),
        _log_cross(surplus, fee_bps),
        invariant_violation * price_violation,
        limit_violation * balance_violation,
    )
    return values[:FIRST_RESERVED_INDEX] + crosses + values[FIRST_RESERVED_INDEX + len(crosses) :]


def feature_values_for_energy_model(model: Any, base_features: Sequence[float]) -> tuple[float, ...]:
    """Select the feature block expected by a loaded advisory model."""

    feature_names = tuple(getattr(model, "feature_names", ()))
    if feature_names == FEATURE_NAMES:
        return tuple(float(value) for value in base_features)
    if feature_names == GEMINI_FEATURE_NAMES:
        return extract_upba_v2_crossed_features(base_features)
    raise ValueError("unsupported UPBA v2 feature schema for advisory model")


def bind_upba_v2_cross_feature_scorer(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    model: Any,
) -> "UpbaV2CrossFeatureScorerBound":
    """Bind a crossed-feature model to one batch context."""

    return UpbaV2CrossFeatureScorerBound(pool=pool, intents=intents, balances=balances, model=model)


class UpbaV2CrossFeatureScorerBound:
    """Callable advisory scorer for a single UPBA v2 batch context."""

    def __init__(
        self,
        *,
        pool: PoolState,
        intents: Sequence[Intent],
        balances: BalanceTable,
        model: Any,
    ) -> None:
        self.pool = pool
        self.intents = tuple(intents)
        self.balances = balances
        self.model = model

    def __call__(self, candidate: UniformBatchCertificateV1) -> float:
        record = extract_upba_v2_feature_record(
            pool=self.pool,
            intents=self.intents,
            balances=self.balances,
            candidate=candidate,
            include_verifier_label=False,
        )
        return float(self.model.energy(feature_values_for_energy_model(self.model, record.values)))


def _value(values: Sequence[float], name: str) -> float:
    return float(values[_FEATURE_INDEX[name]])


def _log_cross(left: float, right: float) -> float:
    return log1p(max(0.0, left * right) * 10.0) / 4.0

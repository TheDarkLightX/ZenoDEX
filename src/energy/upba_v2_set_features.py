"""Permutation-invariant set features for advisory UPBA v2 ranking.

The base UPBA v2 feature schema compresses intents into fixed summary fields.
This module adds a small Deep-Sets-style feature block over intent/fill pairs.
It remains advisory: it does not call the deterministic verifier and it does not
produce validity labels.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import log1p, sqrt
from typing import Any, Mapping, Sequence

from src.core.cpmm import compute_fee_total
from src.core.uniform_batch_clearing import UniformBatchCertificateV1, UniformBatchFillV1
from src.energy.upba_v2_features import FEATURE_NAMES, extract_upba_v2_feature_record
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState

SET_FEATURE_NAMES: tuple[str, ...] = (
    "set_size_norm",
    "set_amount_in_log_mean",
    "set_amount_in_log_min",
    "set_amount_in_log_max",
    "set_amount_in_log_std",
    "set_min_out_log_mean",
    "set_min_out_log_min",
    "set_min_out_log_max",
    "set_min_out_log_std",
    "set_min_out_to_amount_ratio_mean",
    "set_min_out_to_amount_ratio_max",
    "set_min_out_to_amount_ratio_std",
    "set_balance_to_amount_ratio_min",
    "set_balance_to_amount_ratio_mean",
    "set_insufficient_balance_mean",
    "set_insufficient_balance_max",
    "set_base_to_quote_fill_fraction_mean",
    "set_quote_to_base_fill_fraction_mean",
    "set_direction_fill_fraction_gap_abs",
    "set_fill_fraction_min",
    "set_fill_fraction_mean",
    "set_fill_fraction_max",
    "set_fill_fraction_std",
    "set_positive_fill_mean",
    "set_zero_fill_mean",
    "set_partial_fill_mean",
    "set_overfill_mean",
    "set_overfill_max",
    "set_output_to_min_required_ratio_min",
    "set_output_to_min_required_ratio_mean",
    "set_output_to_min_required_ratio_max",
    "set_surplus_ratio_min",
    "set_surplus_ratio_mean",
    "set_surplus_ratio_max",
    "set_surplus_ratio_std",
    "set_expected_out_ratio_min",
    "set_expected_out_ratio_mean",
    "set_expected_out_ratio_max",
    "set_expected_out_ratio_std",
    "set_limit_violation_mean",
    "set_limit_violation_max",
    "set_balance_violation_mean",
    "set_balance_violation_max",
    "set_output_mismatch_mean",
    "set_output_mismatch_max",
    "set_dust_fill_mean",
    "set_dust_fill_max",
    "set_zero_net_input_mean",
    "set_zero_net_input_max",
    "set_fee_fraction_mean",
    "set_fee_fraction_max",
)

SET_FEATURE_DIM = len(SET_FEATURE_NAMES)
SET_AWARE_FEATURE_NAMES: tuple[str, ...] = tuple(
    f"aggregate::{name}" for name in FEATURE_NAMES
) + tuple(f"set::{name}" for name in SET_FEATURE_NAMES)
SET_AWARE_FEATURE_DIM = len(SET_AWARE_FEATURE_NAMES)


@dataclass(frozen=True)
class UpbaV2SetFeatureRecord:
    """Fixed-width permutation-invariant set feature vector."""

    feature_names: tuple[str, ...]
    values: tuple[float, ...]
    raw: dict[str, Any]

    def feature_dict(self) -> dict[str, float]:
        return dict(zip(self.feature_names, self.values, strict=True))


def extract_upba_v2_set_feature_record(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    candidate: UniformBatchCertificateV1 | Mapping[str, Any],
) -> UpbaV2SetFeatureRecord:
    """Extract deterministic set features over intent/fill pairs."""

    parsed_candidate = _parse_candidate_lossy(candidate)
    parsed_intents = tuple(sorted(intents, key=lambda intent: intent.intent_id))
    intent_ids = {intent.intent_id for intent in parsed_intents}
    fills_by_id: dict[str, list[UniformBatchFillV1]] = {}
    for fill in parsed_candidate.fills:
        fills_by_id.setdefault(fill.intent_id, []).append(fill)

    per_intent = [
        _intent_fill_features(
            pool=pool,
            balances=balances,
            candidate=parsed_candidate,
            intent=intent,
            fills=fills_by_id.get(intent.intent_id, []),
        )
        for intent in parsed_intents
    ]
    values_by_name = _aggregate_per_intent_features(per_intent)
    values = tuple(float(values_by_name.get(name, 0.0)) for name in SET_FEATURE_NAMES)
    return UpbaV2SetFeatureRecord(
        feature_names=SET_FEATURE_NAMES,
        values=values,
        raw={
            "feature_schema": "zenodex/energy/upba_v2_set_features/v1",
            "feature_dim": SET_FEATURE_DIM,
            "intent_count": len(parsed_intents),
            "candidate_fill_count": len(parsed_candidate.fills),
            "unknown_fill_id_count": sum(
                1 for fill in parsed_candidate.fills if fill.intent_id not in intent_ids
            ),
        },
    )


def extract_upba_v2_set_aware_feature_record(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    candidate: UniformBatchCertificateV1 | Mapping[str, Any],
) -> UpbaV2SetFeatureRecord:
    """Return the aggregate 96-feature block plus the set-aware block."""

    aggregate = extract_upba_v2_feature_record(
        pool=pool,
        intents=intents,
        balances=balances,
        candidate=candidate,
        include_verifier_label=False,
    )
    set_record = extract_upba_v2_set_feature_record(
        pool=pool,
        intents=intents,
        balances=balances,
        candidate=candidate,
    )
    return UpbaV2SetFeatureRecord(
        feature_names=SET_AWARE_FEATURE_NAMES,
        values=tuple(aggregate.values) + tuple(set_record.values),
        raw={
            "feature_schema": "zenodex/energy/upba_v2_set_aware_features/v1",
            "feature_dim": SET_AWARE_FEATURE_DIM,
            "aggregate_feature_dim": len(aggregate.values),
            "set_feature_dim": len(set_record.values),
        },
    )


def _parse_candidate_lossy(candidate: UniformBatchCertificateV1 | Mapping[str, Any]) -> UniformBatchCertificateV1:
    if isinstance(candidate, UniformBatchCertificateV1):
        return candidate
    return UniformBatchCertificateV1.from_obj(candidate)


def _intent_fill_features(
    *,
    pool: PoolState,
    balances: BalanceTable,
    candidate: UniformBatchCertificateV1,
    intent: Intent,
    fills: Sequence[UniformBatchFillV1],
) -> dict[str, float]:
    amount_in = _nonnegative_int(intent.get_field("amount_in")) if intent.kind == IntentKind.SWAP_EXACT_IN else 0
    min_out = _nonnegative_int(intent.get_field("min_amount_out")) if intent.kind == IntentKind.SWAP_EXACT_IN else 0
    asset_in = str(intent.get_field("asset_in")) if intent.kind == IntentKind.SWAP_EXACT_IN else ""
    asset_out = str(intent.get_field("asset_out")) if intent.kind == IntentKind.SWAP_EXACT_IN else ""
    balance = balances.get(intent.sender_pubkey, asset_in) if asset_in else 0
    executed_in = sum(max(0, int(fill.executed_in)) for fill in fills)
    executed_out = sum(max(0, int(fill.executed_out)) for fill in fills)
    fee = _safe_fee(executed_in, pool.fee_bps)
    net_in = max(0, executed_in - fee)
    required_min_out = _ceil_div(min_out * executed_in, max(1, amount_in)) if amount_in > 0 else 0
    expected_out = _expected_uniform_out(
        pool=pool,
        candidate=candidate,
        asset_in=asset_in,
        asset_out=asset_out,
        net_in=net_in,
    )
    fill_fraction = _ratio2_norm(executed_in, max(1, amount_in))
    output_to_min_required = _ratio2_norm(executed_out, max(1, required_min_out))
    expected_out_ratio = _ratio2_norm(executed_out, max(1, expected_out))
    surplus_ratio = _signed_ratio(executed_out - required_min_out, max(1, min_out, amount_in))
    is_base_to_quote = (
        intent.kind == IntentKind.SWAP_EXACT_IN
        and asset_in == pool.asset0
        and asset_out == pool.asset1
    )
    is_quote_to_base = (
        intent.kind == IntentKind.SWAP_EXACT_IN
        and asset_in == pool.asset1
        and asset_out == pool.asset0
    )
    return {
        "amount_in_log": _log_norm(amount_in),
        "min_out_log": _log_norm(min_out),
        "min_out_to_amount_ratio": _clip01(min_out / max(1, amount_in)),
        "balance_to_amount_ratio": _ratio2_norm(balance, max(1, amount_in)),
        "insufficient_balance": float(balance < executed_in),
        "base_to_quote_fill_fraction": fill_fraction if is_base_to_quote else 0.0,
        "quote_to_base_fill_fraction": fill_fraction if is_quote_to_base else 0.0,
        "fill_fraction": fill_fraction,
        "positive_fill": float(executed_in > 0),
        "zero_fill": float(executed_in == 0),
        "partial_fill": float(0 < executed_in < amount_in),
        "overfill": float(executed_in > amount_in),
        "output_to_min_required_ratio": output_to_min_required,
        "surplus_ratio": surplus_ratio,
        "expected_out_ratio": expected_out_ratio,
        "limit_violation": float(executed_out < required_min_out),
        "balance_violation": float(balance < executed_in),
        "output_mismatch": float(expected_out != executed_out),
        "dust_fill": float(0 < executed_in <= 2 or 0 < executed_out <= 2),
        "zero_net_input": float(executed_in > 0 and net_in <= 0),
        "fee_fraction": _clip01(fee / max(1, executed_in)),
    }


def _aggregate_per_intent_features(rows: Sequence[dict[str, float]]) -> dict[str, float]:
    count = max(1, len(rows))

    def series(name: str) -> list[float]:
        return [float(row.get(name, 0.0)) for row in rows] or [0.0]

    fill_gap = abs(
        _mean(series("base_to_quote_fill_fraction"))
        - _mean(series("quote_to_base_fill_fraction"))
    )
    return {
        "set_size_norm": _clip01(len(rows) / 256),
        **_moments("set_amount_in_log", series("amount_in_log")),
        **_moments("set_min_out_log", series("min_out_log")),
        "set_min_out_to_amount_ratio_mean": _mean(series("min_out_to_amount_ratio")),
        "set_min_out_to_amount_ratio_max": max(series("min_out_to_amount_ratio")),
        "set_min_out_to_amount_ratio_std": _std(series("min_out_to_amount_ratio")),
        "set_balance_to_amount_ratio_min": min(series("balance_to_amount_ratio")),
        "set_balance_to_amount_ratio_mean": _mean(series("balance_to_amount_ratio")),
        "set_insufficient_balance_mean": sum(series("insufficient_balance")) / count,
        "set_insufficient_balance_max": max(series("insufficient_balance")),
        "set_base_to_quote_fill_fraction_mean": _mean(series("base_to_quote_fill_fraction")),
        "set_quote_to_base_fill_fraction_mean": _mean(series("quote_to_base_fill_fraction")),
        "set_direction_fill_fraction_gap_abs": fill_gap,
        **_moments("set_fill_fraction", series("fill_fraction")),
        "set_positive_fill_mean": _mean(series("positive_fill")),
        "set_zero_fill_mean": _mean(series("zero_fill")),
        "set_partial_fill_mean": _mean(series("partial_fill")),
        "set_overfill_mean": _mean(series("overfill")),
        "set_overfill_max": max(series("overfill")),
        "set_output_to_min_required_ratio_min": min(series("output_to_min_required_ratio")),
        "set_output_to_min_required_ratio_mean": _mean(series("output_to_min_required_ratio")),
        "set_output_to_min_required_ratio_max": max(series("output_to_min_required_ratio")),
        **_moments("set_surplus_ratio", series("surplus_ratio")),
        **_moments("set_expected_out_ratio", series("expected_out_ratio")),
        "set_limit_violation_mean": _mean(series("limit_violation")),
        "set_limit_violation_max": max(series("limit_violation")),
        "set_balance_violation_mean": _mean(series("balance_violation")),
        "set_balance_violation_max": max(series("balance_violation")),
        "set_output_mismatch_mean": _mean(series("output_mismatch")),
        "set_output_mismatch_max": max(series("output_mismatch")),
        "set_dust_fill_mean": _mean(series("dust_fill")),
        "set_dust_fill_max": max(series("dust_fill")),
        "set_zero_net_input_mean": _mean(series("zero_net_input")),
        "set_zero_net_input_max": max(series("zero_net_input")),
        "set_fee_fraction_mean": _mean(series("fee_fraction")),
        "set_fee_fraction_max": max(series("fee_fraction")),
    }


def _expected_uniform_out(
    *,
    pool: PoolState,
    candidate: UniformBatchCertificateV1,
    asset_in: str,
    asset_out: str,
    net_in: int,
) -> int:
    if net_in <= 0 or candidate.price_num <= 0 or candidate.price_den <= 0:
        return 0
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return (net_in * candidate.price_num) // candidate.price_den
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return (net_in * candidate.price_den) // candidate.price_num
    return 0


def _moments(prefix: str, values: Sequence[float]) -> dict[str, float]:
    vals = list(values) or [0.0]
    return {
        f"{prefix}_mean": _mean(vals),
        f"{prefix}_min": min(vals),
        f"{prefix}_max": max(vals),
        f"{prefix}_std": _std(vals),
    }


def _safe_fee(executed_in: int, fee_bps: int) -> int:
    try:
        return compute_fee_total(executed_in, fee_bps)
    except (TypeError, ValueError):
        return max(0, (executed_in * fee_bps + 9_999) // 10_000)


def _ceil_div(numerator: int, denominator: int) -> int:
    return (int(numerator) + int(denominator) - 1) // int(denominator)


def _nonnegative_int(value: Any) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        return 0
    return max(0, int(value))


def _log_norm(value: int) -> float:
    return _clip(log1p(max(0, int(value))) / 32.0, 0.0, 1.0)


def _ratio2_norm(numerator: int, denominator: int) -> float:
    return _clip(float(numerator) / float(max(1, denominator)), 0.0, 2.0) / 2.0


def _signed_ratio(numerator: int, denominator: int) -> float:
    return _clip(float(numerator) / float(max(1, denominator)), -1.0, 1.0)


def _mean(values: Sequence[float]) -> float:
    return sum(values) / max(1, len(values))


def _std(values: Sequence[float]) -> float:
    if not values:
        return 0.0
    avg = _mean(values)
    return sqrt(sum((value - avg) ** 2 for value in values) / len(values))


def _clip01(value: float) -> float:
    return _clip(value, 0.0, 1.0)


def _clip(value: float, lower: float, upper: float) -> float:
    return max(lower, min(upper, value))

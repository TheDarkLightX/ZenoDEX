"""Feature extraction for advisory UPBA v2 energy ranking.

The extractor is intentionally downstream of the deterministic UPBA verifier.
It computes normalized numeric features and explicit violation diagnostics for
candidate certificates. The feature vector is suitable for hand-coded energy,
linear rankers, and tiny MLP experiments.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd, log1p
from typing import Any, Mapping, Sequence

from src.core.cpmm import compute_fee_total
from src.core.uniform_batch_clearing import (
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    UNIFORM_BATCH_POLICY_V2_ID,
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    verify_uniform_batch_certificate_v1,
)
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState

FEATURE_DIM = 96

_BASE_FEATURE_NAMES: tuple[str, ...] = (
    "pool_reserve0_log1p",
    "pool_reserve1_log1p",
    "pool_fee_bps_norm",
    "pool_k_before_log1p",
    "pool_spot_price_ratio",
    "pool_spot_price_inverse_ratio",
    "intent_n_norm",
    "intent_base_to_quote_count_norm",
    "intent_quote_to_base_count_norm",
    "intent_total_base_to_quote_amount_in_log1p",
    "intent_total_quote_to_base_amount_in_log1p",
    "intent_min_out_min_log1p",
    "intent_min_out_max_log1p",
    "intent_min_out_mean_log1p",
    "intent_amount_in_min_log1p",
    "intent_amount_in_max_log1p",
    "intent_amount_in_mean_log1p",
    "intent_sender_count_norm",
    "intent_insufficient_balance_count_norm",
    "candidate_price_num_log1p",
    "candidate_price_den_log1p",
    "candidate_price_ratio_vs_spot",
    "candidate_positive_fill_count_norm",
    "candidate_zero_fill_count_norm",
    "candidate_partial_fill_count_norm",
    "candidate_executed_base_in_log1p",
    "candidate_executed_quote_in_log1p",
    "candidate_executed_base_out_log1p",
    "candidate_executed_quote_out_log1p",
    "candidate_net_base_in_log1p",
    "candidate_net_quote_in_log1p",
    "candidate_total_fee_log1p",
    "candidate_volume_log1p",
    "candidate_surplus_signed",
    "candidate_reserve0_after_log1p",
    "candidate_reserve1_after_log1p",
    "candidate_k_after_log1p",
    "candidate_k_margin_signed",
    "candidate_negative_reserve_flag",
    "candidate_invariant_violation_flag",
    "candidate_limit_violation_count_norm",
    "candidate_balance_violation_count_norm",
    "candidate_noncanonical_fill_vector_flag",
    "candidate_zero_net_input_count_norm",
    "candidate_dust_penalty_norm",
    "candidate_imbalance_penalty",
    "candidate_price_objective_violation_flag",
    "candidate_output_mismatch_count_norm",
    "candidate_all_zero_fill_vector_flag",
    "candidate_schema_policy_mismatch_flag",
    "candidate_price_ratio_unreduced_flag",
    "candidate_fill_coverage_violation_flag",
    "candidate_duplicate_fill_id_flag",
    "candidate_unknown_fill_id_count_norm",
    "candidate_executed_input_over_amount_count_norm",
    "candidate_output_without_input_count_norm",
    "candidate_normalized_executed_volume",
    "candidate_normalized_surplus",
)

if len(_BASE_FEATURE_NAMES) > FEATURE_DIM:  # pragma: no cover - import-time guard
    raise RuntimeError("base UPBA feature schema exceeds fixed feature dimension")

FEATURE_NAMES: tuple[str, ...] = _BASE_FEATURE_NAMES + tuple(
    f"reserved_{index:02d}" for index in range(FEATURE_DIM - len(_BASE_FEATURE_NAMES))
)


@dataclass(frozen=True)
class UpbaV2FeatureRecord:
    """Normalized feature vector plus raw diagnostics for one UPBA v2 candidate."""

    feature_names: tuple[str, ...]
    values: tuple[float, ...]
    raw: dict[str, Any]

    def feature_dict(self) -> dict[str, float]:
        return dict(zip(self.feature_names, self.values, strict=True))


def extract_upba_v2_feature_record(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    candidate: UniformBatchCertificateV1 | Mapping[str, Any],
    include_verifier_label: bool = False,
) -> UpbaV2FeatureRecord:
    """Extract a fixed-width advisory feature record for a v2 candidate."""

    parsed_candidate = _parse_candidate_lossy(candidate)
    parsed_intents = tuple(intents)
    intents_by_id = {intent.intent_id: intent for intent in parsed_intents}
    expected_fill_ids = sorted(intents_by_id)
    fills = tuple(parsed_candidate.fills)

    intent_summary = _summarize_intents(pool=pool, intents=parsed_intents, balances=balances)
    candidate_summary = _summarize_candidate(
        pool=pool,
        intents_by_id=intents_by_id,
        balances=balances,
        candidate=parsed_candidate,
        fills=fills,
        expected_fill_ids=expected_fill_ids,
    )

    verifier_result = (
        verify_uniform_batch_certificate_v1(
            intents=parsed_intents,
            pool=pool,
            balances=balances,
            certificate=parsed_candidate,
        )
        if include_verifier_label
        else None
    )
    valid_objective_volume = 0
    valid_objective_surplus = 0
    if verifier_result is not None and verifier_result.ok:
        valid_objective_volume = max(0, candidate_summary["volume"])
        valid_objective_surplus = max(0, candidate_summary["surplus"])

    total_intents = max(1, len(parsed_intents))
    total_amount_in = max(1, intent_summary["total_amount_in"])
    k_before = pool.reserve0 * pool.reserve1
    k_after = candidate_summary["k_after"]
    spot_num = max(1, pool.reserve1)
    spot_den = max(1, pool.reserve0)

    raw: dict[str, Any] = {
        **intent_summary,
        **candidate_summary,
        "verifier_ok": bool(verifier_result.ok) if verifier_result is not None else None,
        "verifier_error": verifier_result.error if verifier_result is not None else None,
        "valid_objective_volume": int(valid_objective_volume),
        "valid_objective_surplus": int(valid_objective_surplus),
        "feature_schema": "zenodex/energy/upba_v2_features/v1",
        "feature_dim": FEATURE_DIM,
    }

    feature_values = {
        "pool_reserve0_log1p": _log_norm(pool.reserve0),
        "pool_reserve1_log1p": _log_norm(pool.reserve1),
        "pool_fee_bps_norm": _clip01(pool.fee_bps / 10_000),
        "pool_k_before_log1p": _log_norm(k_before),
        "pool_spot_price_ratio": _bounded_ratio(spot_num, spot_den),
        "pool_spot_price_inverse_ratio": _bounded_ratio(spot_den, spot_num),
        "intent_n_norm": _clip01(len(parsed_intents) / 256),
        "intent_base_to_quote_count_norm": _clip01(intent_summary["base_to_quote_count"] / total_intents),
        "intent_quote_to_base_count_norm": _clip01(intent_summary["quote_to_base_count"] / total_intents),
        "intent_total_base_to_quote_amount_in_log1p": _log_norm(
            intent_summary["total_base_to_quote_amount_in"]
        ),
        "intent_total_quote_to_base_amount_in_log1p": _log_norm(
            intent_summary["total_quote_to_base_amount_in"]
        ),
        "intent_min_out_min_log1p": _log_norm(intent_summary["min_out_min"]),
        "intent_min_out_max_log1p": _log_norm(intent_summary["min_out_max"]),
        "intent_min_out_mean_log1p": _log_norm(intent_summary["min_out_mean"]),
        "intent_amount_in_min_log1p": _log_norm(intent_summary["amount_in_min"]),
        "intent_amount_in_max_log1p": _log_norm(intent_summary["amount_in_max"]),
        "intent_amount_in_mean_log1p": _log_norm(intent_summary["amount_in_mean"]),
        "intent_sender_count_norm": _clip01(intent_summary["sender_count"] / total_intents),
        "intent_insufficient_balance_count_norm": _clip01(
            intent_summary["insufficient_balance_count"] / total_intents
        ),
        "candidate_price_num_log1p": _log_norm(parsed_candidate.price_num),
        "candidate_price_den_log1p": _log_norm(parsed_candidate.price_den),
        "candidate_price_ratio_vs_spot": _bounded_ratio(
            parsed_candidate.price_num * spot_den,
            max(1, parsed_candidate.price_den * spot_num),
        ),
        "candidate_positive_fill_count_norm": _clip01(
            candidate_summary["positive_fill_count"] / total_intents
        ),
        "candidate_zero_fill_count_norm": _clip01(candidate_summary["zero_fill_count"] / total_intents),
        "candidate_partial_fill_count_norm": _clip01(
            candidate_summary["partial_fill_count"] / total_intents
        ),
        "candidate_executed_base_in_log1p": _log_norm(candidate_summary["executed_base_in"]),
        "candidate_executed_quote_in_log1p": _log_norm(candidate_summary["executed_quote_in"]),
        "candidate_executed_base_out_log1p": _log_norm(candidate_summary["executed_base_out"]),
        "candidate_executed_quote_out_log1p": _log_norm(candidate_summary["executed_quote_out"]),
        "candidate_net_base_in_log1p": _log_norm(candidate_summary["net_base_in"]),
        "candidate_net_quote_in_log1p": _log_norm(candidate_summary["net_quote_in"]),
        "candidate_total_fee_log1p": _log_norm(candidate_summary["total_fee"]),
        "candidate_volume_log1p": _log_norm(max(0, candidate_summary["volume"])),
        "candidate_surplus_signed": _signed_log_norm(candidate_summary["surplus"]),
        "candidate_reserve0_after_log1p": _log_norm(max(0, candidate_summary["reserve0_after"])),
        "candidate_reserve1_after_log1p": _log_norm(max(0, candidate_summary["reserve1_after"])),
        "candidate_k_after_log1p": _log_norm(max(0, k_after)),
        "candidate_k_margin_signed": _signed_ratio(k_after - k_before, max(1, k_before)),
        "candidate_negative_reserve_flag": float(candidate_summary["negative_reserve_flag"]),
        "candidate_invariant_violation_flag": float(candidate_summary["invariant_violation_flag"]),
        "candidate_limit_violation_count_norm": _clip01(
            candidate_summary["limit_violation_count"] / total_intents
        ),
        "candidate_balance_violation_count_norm": _clip01(
            candidate_summary["balance_violation_count"] / total_intents
        ),
        "candidate_noncanonical_fill_vector_flag": float(
            candidate_summary["noncanonical_fill_vector_flag"]
        ),
        "candidate_zero_net_input_count_norm": _clip01(
            candidate_summary["zero_net_input_count"] / total_intents
        ),
        "candidate_dust_penalty_norm": _clip01(candidate_summary["dust_penalty"] / total_intents),
        "candidate_imbalance_penalty": candidate_summary["imbalance_penalty"],
        "candidate_price_objective_violation_flag": float(
            candidate_summary["price_objective_violation_flag"]
        ),
        "candidate_output_mismatch_count_norm": _clip01(
            candidate_summary["output_mismatch_count"] / total_intents
        ),
        "candidate_all_zero_fill_vector_flag": float(candidate_summary["all_zero_fill_vector_flag"]),
        "candidate_schema_policy_mismatch_flag": float(
            candidate_summary["schema_policy_mismatch_flag"]
        ),
        "candidate_price_ratio_unreduced_flag": float(
            candidate_summary["price_ratio_unreduced_flag"]
        ),
        "candidate_fill_coverage_violation_flag": float(
            candidate_summary["fill_coverage_violation_flag"]
        ),
        "candidate_duplicate_fill_id_flag": float(candidate_summary["duplicate_fill_id_flag"]),
        "candidate_unknown_fill_id_count_norm": _clip01(
            candidate_summary["unknown_fill_id_count"] / total_intents
        ),
        "candidate_executed_input_over_amount_count_norm": _clip01(
            candidate_summary["executed_input_over_amount_count"] / total_intents
        ),
        "candidate_output_without_input_count_norm": _clip01(
            candidate_summary["output_without_input_count"] / total_intents
        ),
        "candidate_normalized_executed_volume": _clip01(
            max(0, candidate_summary["volume"]) / total_amount_in
        ),
        "candidate_normalized_surplus": _signed_ratio(
            candidate_summary["surplus"],
            max(1, intent_summary["min_out_max"], total_amount_in),
        ),
    }
    values = tuple(float(feature_values.get(name, 0.0)) for name in FEATURE_NAMES)
    return UpbaV2FeatureRecord(feature_names=FEATURE_NAMES, values=values, raw=raw)


def feature_dict_from_record(record: UpbaV2FeatureRecord) -> dict[str, float]:
    return record.feature_dict()


def _parse_candidate_lossy(candidate: UniformBatchCertificateV1 | Mapping[str, Any]) -> UniformBatchCertificateV1:
    if isinstance(candidate, UniformBatchCertificateV1):
        return candidate
    return UniformBatchCertificateV1.from_obj(candidate)


def _summarize_intents(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
) -> dict[str, int]:
    amounts: list[int] = []
    min_outs: list[int] = []
    senders: set[str] = set()
    base_to_quote_count = 0
    quote_to_base_count = 0
    total_base_to_quote_amount_in = 0
    total_quote_to_base_amount_in = 0
    insufficient_balance_count = 0

    for intent in intents:
        senders.add(str(intent.sender_pubkey))
        if intent.kind != IntentKind.SWAP_EXACT_IN:
            continue
        amount_in = _nonnegative_int(intent.get_field("amount_in"))
        min_amount_out = _nonnegative_int(intent.get_field("min_amount_out"))
        amounts.append(amount_in)
        min_outs.append(min_amount_out)
        asset_in = str(intent.get_field("asset_in"))
        asset_out = str(intent.get_field("asset_out"))
        if balances.get(intent.sender_pubkey, asset_in) < amount_in:
            insufficient_balance_count += 1
        if asset_in == pool.asset0 and asset_out == pool.asset1:
            base_to_quote_count += 1
            total_base_to_quote_amount_in += amount_in
        elif asset_in == pool.asset1 and asset_out == pool.asset0:
            quote_to_base_count += 1
            total_quote_to_base_amount_in += amount_in

    return {
        "n_intents": len(intents),
        "base_to_quote_count": base_to_quote_count,
        "quote_to_base_count": quote_to_base_count,
        "total_base_to_quote_amount_in": total_base_to_quote_amount_in,
        "total_quote_to_base_amount_in": total_quote_to_base_amount_in,
        "total_amount_in": sum(amounts),
        "min_out_min": min(min_outs) if min_outs else 0,
        "min_out_max": max(min_outs) if min_outs else 0,
        "min_out_mean": sum(min_outs) // max(1, len(min_outs)),
        "amount_in_min": min(amounts) if amounts else 0,
        "amount_in_max": max(amounts) if amounts else 0,
        "amount_in_mean": sum(amounts) // max(1, len(amounts)),
        "sender_count": len(senders),
        "insufficient_balance_count": insufficient_balance_count,
    }


def _summarize_candidate(
    *,
    pool: PoolState,
    intents_by_id: Mapping[str, Intent],
    balances: BalanceTable,
    candidate: UniformBatchCertificateV1,
    fills: Sequence[UniformBatchFillV1],
    expected_fill_ids: Sequence[str],
) -> dict[str, Any]:
    fill_ids = [fill.intent_id for fill in fills]
    duplicate_fill_id_flag = len(fill_ids) != len(set(fill_ids))
    fill_coverage_violation_flag = fill_ids != list(expected_fill_ids)
    schema_policy_mismatch_flag = (
        candidate.schema != UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2
        or candidate.policy_id != UNIFORM_BATCH_POLICY_V2_ID
    )
    price_ratio_unreduced_flag = gcd(max(1, candidate.price_num), max(1, candidate.price_den)) != 1

    balance_consumed: dict[tuple[str, str], int] = {}
    reserve_net = {pool.asset0: 0, pool.asset1: 0}
    executed_base_in = 0
    executed_quote_in = 0
    executed_base_out = 0
    executed_quote_out = 0
    net_base_in = 0
    net_quote_in = 0
    total_fee = 0
    volume = 0
    surplus = 0
    positive_fill_count = 0
    zero_fill_count = 0
    partial_fill_count = 0
    limit_violation_count = 0
    zero_net_input_count = 0
    output_mismatch_count = 0
    unknown_fill_id_count = 0
    executed_input_over_amount_count = 0
    output_without_input_count = 0
    dust_penalty = 0

    base_to_quote_net_for_price = 0
    quote_to_base_net_for_price = 0

    for fill in fills:
        intent = intents_by_id.get(fill.intent_id)
        executed_in = int(fill.executed_in)
        executed_out = int(fill.executed_out)
        if executed_in == 0:
            zero_fill_count += 1
            if executed_out > 0:
                output_without_input_count += 1
            if intent is None:
                unknown_fill_id_count += 1
            continue
        positive_fill_count += 1
        if executed_in <= 2 or executed_out <= 2:
            dust_penalty += 1
        if intent is None:
            unknown_fill_id_count += 1
            continue
        if intent.kind != IntentKind.SWAP_EXACT_IN:
            output_mismatch_count += 1
            continue
        amount_in = _nonnegative_int(intent.get_field("amount_in"))
        min_out = _nonnegative_int(intent.get_field("min_amount_out"))
        if executed_in < amount_in:
            partial_fill_count += 1
        if executed_in > amount_in:
            executed_input_over_amount_count += 1
        if executed_out * amount_in < min_out * executed_in:
            limit_violation_count += 1
        required_min_out = _ceil_div(min_out * executed_in, max(1, amount_in))
        surplus += executed_out - required_min_out
        fee_paid = _safe_fee(executed_in, pool.fee_bps)
        total_fee += fee_paid
        net_in = executed_in - fee_paid
        if net_in <= 0:
            zero_net_input_count += 1
        asset_in = str(intent.get_field("asset_in"))
        asset_out = str(intent.get_field("asset_out"))
        balance_key = (intent.sender_pubkey, asset_in)
        balance_consumed[balance_key] = balance_consumed.get(balance_key, 0) + max(0, executed_in)
        reserve_net[asset_in] = reserve_net.get(asset_in, 0) + executed_in
        reserve_net[asset_out] = reserve_net.get(asset_out, 0) - executed_out
        volume += executed_out
        if asset_in == pool.asset0 and asset_out == pool.asset1:
            executed_base_in += executed_in
            executed_quote_out += executed_out
            net_base_in += max(0, net_in)
            base_to_quote_net_for_price += max(0, net_in)
            expected_out = _uniform_price_out(
                net_in=max(0, net_in),
                direction="base_to_quote",
                price_num=candidate.price_num,
                price_den=candidate.price_den,
            )
        elif asset_in == pool.asset1 and asset_out == pool.asset0:
            executed_quote_in += executed_in
            executed_base_out += executed_out
            net_quote_in += max(0, net_in)
            quote_to_base_net_for_price += max(0, net_in)
            expected_out = _uniform_price_out(
                net_in=max(0, net_in),
                direction="quote_to_base",
                price_num=candidate.price_num,
                price_den=candidate.price_den,
            )
        else:
            output_mismatch_count += 1
            continue
        if executed_out != expected_out:
            output_mismatch_count += 1

    balance_violation_count = sum(
        1 for (sender, asset), spent in balance_consumed.items() if balances.get(sender, asset) < spent
    )
    reserve0_after = pool.reserve0 + reserve_net.get(pool.asset0, 0)
    reserve1_after = pool.reserve1 + reserve_net.get(pool.asset1, 0)
    negative_reserve_flag = reserve0_after < 0 or reserve1_after < 0
    k_before = pool.reserve0 * pool.reserve1
    k_after = reserve0_after * reserve1_after
    invariant_violation_flag = bool(negative_reserve_flag or k_after < k_before)
    expected_price = _canonical_price_ratio_lossy(
        pool=pool,
        base_to_quote_net=base_to_quote_net_for_price,
        quote_to_base_net=quote_to_base_net_for_price,
    )
    price_objective_violation_flag = expected_price != (candidate.price_num, candidate.price_den)
    all_zero_fill_vector_flag = positive_fill_count == 0
    noncanonical_fill_vector_flag = bool(
        fill_coverage_violation_flag
        or duplicate_fill_id_flag
        or output_mismatch_count
        or all_zero_fill_vector_flag
        or price_objective_violation_flag
        or executed_input_over_amount_count
        or output_without_input_count
    )
    imbalance_penalty = _clip01(
        abs(base_to_quote_net_for_price - quote_to_base_net_for_price)
        / max(1, base_to_quote_net_for_price + quote_to_base_net_for_price)
    )

    return {
        "positive_fill_count": positive_fill_count,
        "zero_fill_count": zero_fill_count,
        "partial_fill_count": partial_fill_count,
        "executed_base_in": executed_base_in,
        "executed_quote_in": executed_quote_in,
        "executed_base_out": executed_base_out,
        "executed_quote_out": executed_quote_out,
        "net_base_in": net_base_in,
        "net_quote_in": net_quote_in,
        "total_fee": total_fee,
        "volume": volume,
        "surplus": surplus,
        "reserve0_after": reserve0_after,
        "reserve1_after": reserve1_after,
        "k_after": k_after,
        "negative_reserve_flag": int(negative_reserve_flag),
        "invariant_violation_flag": int(invariant_violation_flag),
        "limit_violation_count": limit_violation_count,
        "balance_violation_count": balance_violation_count,
        "noncanonical_fill_vector_flag": int(noncanonical_fill_vector_flag),
        "zero_net_input_count": zero_net_input_count,
        "dust_penalty": dust_penalty,
        "imbalance_penalty": imbalance_penalty,
        "price_objective_violation_flag": int(price_objective_violation_flag),
        "output_mismatch_count": output_mismatch_count,
        "all_zero_fill_vector_flag": int(all_zero_fill_vector_flag),
        "schema_policy_mismatch_flag": int(schema_policy_mismatch_flag),
        "price_ratio_unreduced_flag": int(price_ratio_unreduced_flag),
        "fill_coverage_violation_flag": int(fill_coverage_violation_flag),
        "duplicate_fill_id_flag": int(duplicate_fill_id_flag),
        "unknown_fill_id_count": unknown_fill_id_count,
        "executed_input_over_amount_count": executed_input_over_amount_count,
        "output_without_input_count": output_without_input_count,
    }


def _canonical_price_ratio_lossy(
    *,
    pool: PoolState,
    base_to_quote_net: int,
    quote_to_base_net: int,
) -> tuple[int, int]:
    if base_to_quote_net > 0 and quote_to_base_net > 0:
        divisor = gcd(base_to_quote_net, quote_to_base_net)
        return quote_to_base_net // divisor, base_to_quote_net // divisor
    divisor = gcd(pool.reserve1, pool.reserve0)
    return pool.reserve1 // divisor, pool.reserve0 // divisor


def _safe_fee(executed_in: int, fee_bps: int) -> int:
    try:
        return compute_fee_total(executed_in, fee_bps)
    except (TypeError, ValueError):
        return max(0, (executed_in * fee_bps + 9_999) // 10_000)


def _uniform_price_out(*, net_in: int, direction: str, price_num: int, price_den: int) -> int:
    if net_in <= 0 or price_num <= 0 or price_den <= 0:
        return 0
    if direction == "base_to_quote":
        return (net_in * price_num) // price_den
    return (net_in * price_den) // price_num


def _ceil_div(numerator: int, denominator: int) -> int:
    return (int(numerator) + int(denominator) - 1) // int(denominator)


def _nonnegative_int(value: Any) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        return 0
    return max(0, int(value))


def _log_norm(value: int) -> float:
    return _clip(log1p(max(0, int(value))) / 32.0, 0.0, 1.0)


def _signed_log_norm(value: int) -> float:
    sign = -1.0 if value < 0 else 1.0
    return sign * _clip(log1p(abs(int(value))) / 32.0, 0.0, 1.0)


def _bounded_ratio(numerator: int, denominator: int) -> float:
    return _clip(float(numerator) / float(max(1, denominator)), 0.0, 10.0) / 10.0


def _signed_ratio(numerator: int, denominator: int) -> float:
    return _clip(float(numerator) / float(max(1, denominator)), -1.0, 1.0)


def _clip01(value: float) -> float:
    return _clip(value, 0.0, 1.0)


def _clip(value: float, lower: float, upper: float) -> float:
    return max(lower, min(upper, value))

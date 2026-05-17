#!/usr/bin/env python3
"""Generate synthetic UPBA v2 energy-ranking datasets."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from hashlib import sha256
from math import gcd
from pathlib import Path
from random import Random
from typing import Iterable, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.cpmm import compute_fee_total
from src.core.uniform_batch_clearing import (
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V1,
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    UNIFORM_BATCH_POLICY_V2_ID,
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    uniform_batch_intent_set_hash,
    uniform_batch_pool_state_hash,
    verify_uniform_batch_certificate_v1,
)
from src.energy.upba_v2_features import FEATURE_NAMES, extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import hand_energy_from_record
from src.energy.upba_v2_ranker import advisory_candidate_hash
from src.state.balances import BalanceTable
from src.state.canonical import canonical_json_bytes
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus


@dataclass(frozen=True)
class SyntheticCandidate:
    candidate: UniformBatchCertificateV1
    candidate_type: str


@dataclass(frozen=True)
class SyntheticBatch:
    batch_id: str
    pool: PoolState
    intents: tuple[Intent, ...]
    balances: BalanceTable
    candidates: tuple[SyntheticCandidate, ...]


def generate_synthetic_batch(
    *,
    rng: Random,
    batch_index: int,
    target_candidate_count: int = 24,
) -> SyntheticBatch:
    pool = PoolState(
        pool_id="pool_ab",
        asset0="A",
        asset1="B",
        reserve0=rng.randint(5_000, 50_000),
        reserve1=rng.randint(5_000, 50_000),
        fee_bps=rng.choice((0, 5, 30, 100, 300)),
        lp_supply=1_000_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    intent_count = rng.randint(2, 6)
    intents: list[Intent] = []
    balances = BalanceTable()
    for index in range(intent_count):
        direction_base_to_quote = index % 2 == 0
        sender = f"user_{batch_index}_{index}"
        asset_in = pool.asset0 if direction_base_to_quote else pool.asset1
        asset_out = pool.asset1 if direction_base_to_quote else pool.asset0
        amount_in = rng.randint(20, 600)
        min_amount_out = rng.randint(0, max(1, amount_in // 2))
        intent = _swap_intent(
            label=f"batch-{batch_index}-intent-{index}",
            sender=sender,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
            min_amount_out=min_amount_out,
        )
        intents.append(intent)
        balance = amount_in if index != intent_count - 1 else max(1, amount_in // 2)
        balances.set(sender, asset_in, balance)

    fill_vectors = _candidate_fill_vectors(rng=rng, intents=intents)
    candidates: list[SyntheticCandidate] = []
    for fill_vector in fill_vectors:
        candidate = _certificate_for_fill_vector(intents=intents, pool=pool, fills=fill_vector)
        if verify_uniform_batch_certificate_v1(
            intents=intents,
            pool=pool,
            balances=balances,
            certificate=candidate,
        ).ok:
            candidates.append(SyntheticCandidate(candidate=candidate, candidate_type="valid"))

    if not candidates:
        safe_fills = [
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=min(int(intent.get_field("amount_in")), balances.get(intent.sender_pubkey, str(intent.get_field("asset_in")))),
                executed_out=0,
            )
            for intent in intents
        ]
        safe_candidate = _certificate_for_fill_vector(
            intents=intents,
            pool=pool,
            fills=_with_uniform_outputs(pool=pool, intents=intents, fills=safe_fills),
        )
        candidates.append(SyntheticCandidate(candidate=safe_candidate, candidate_type="valid_seed"))

    valid_seed = candidates[0].candidate
    candidates.extend(
        [
            SyntheticCandidate(
                candidate=_mutate_limit_violation(valid_seed),
                candidate_type="invalid_limit_price",
            ),
            SyntheticCandidate(
                candidate=_mutate_negative_reserve(valid_seed, pool=pool),
                candidate_type="invalid_negative_reserve",
            ),
            SyntheticCandidate(
                candidate=_mutate_noncanonical_order(valid_seed),
                candidate_type="invalid_noncanonical_fill_vector",
            ),
            SyntheticCandidate(
                candidate=_all_zero_candidate(intents=intents, pool=pool),
                candidate_type="invalid_all_zero",
            ),
            SyntheticCandidate(
                candidate=_mutate_balance_violation(valid_seed, intents=intents),
                candidate_type="invalid_balance",
            ),
            SyntheticCandidate(
                candidate=_mutate_near_miss(valid_seed),
                candidate_type="near_miss_adversarial",
            ),
            SyntheticCandidate(
                candidate=_mutate_attractive_output_mismatch(valid_seed),
                candidate_type="hard_attractive_output_mismatch",
            ),
            SyntheticCandidate(
                candidate=_mutate_unreduced_price(valid_seed),
                candidate_type="hard_unreduced_price",
            ),
            SyntheticCandidate(
                candidate=_mutate_schema_policy_mismatch(valid_seed),
                candidate_type="hard_schema_policy_mismatch",
            ),
        ]
    )

    while len(candidates) < target_candidate_count:
        candidates.append(
            SyntheticCandidate(
                candidate=_random_noisy_candidate(rng=rng, intents=intents, pool=pool),
                candidate_type="random_noisy",
            )
        )

    dedup: dict[str, SyntheticCandidate] = {}
    for item in candidates:
        dedup.setdefault(advisory_candidate_hash(item.candidate), item)
    selected = tuple(dedup.values())[:target_candidate_count]
    return SyntheticBatch(
        batch_id=f"synthetic-upba-v2-{batch_index:08d}",
        pool=pool,
        intents=tuple(intents),
        balances=balances,
        candidates=selected,
    )


def rows_for_batch(batch: SyntheticBatch) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    valid_rows: list[dict[str, object]] = []
    for index, item in enumerate(batch.candidates):
        record = extract_upba_v2_feature_record(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidate=item.candidate,
            include_verifier_label=True,
        )
        candidate_hash = advisory_candidate_hash(item.candidate)
        valid = bool(record.raw["verifier_ok"])
        objective_volume = int(record.raw["valid_objective_volume"])
        objective_surplus = int(record.raw["valid_objective_surplus"])
        row: dict[str, object] = {
            "schema": "zenodex/energy/upba_v2_dataset_row/v1",
            "source": "synthetic",
            "batch_id": batch.batch_id,
            "candidate_index": index,
            "candidate_hash": candidate_hash,
            "candidate_type": item.candidate_type,
            "feature_names": list(FEATURE_NAMES),
            "features": list(record.values),
            "label": {
                "valid": valid,
                "objective_volume": objective_volume,
                "objective_surplus": objective_surplus,
                "verifier_error": record.raw["verifier_error"],
                "hand_energy": hand_energy_from_record(record),
                "target_energy": _target_energy(record),
                "is_winner": False,
            },
        }
        rows.append(row)
        if valid:
            valid_rows.append(row)
    if valid_rows:
        winner = max(
            valid_rows,
            key=lambda row: (
                int(row["label"]["objective_volume"]),  # type: ignore[index]
                int(row["label"]["objective_surplus"]),  # type: ignore[index]
                str(row["candidate_hash"]),
            ),
        )
        winner["label"]["is_winner"] = True  # type: ignore[index]
    return rows


def generate_dataset_rows(
    *,
    batches: int,
    candidates_per_batch: int,
    seed: int,
) -> Iterable[dict[str, object]]:
    rng = Random(seed)
    for batch_index in range(batches):
        batch = generate_synthetic_batch(
            rng=rng,
            batch_index=batch_index,
            target_candidate_count=candidates_per_batch,
        )
        yield from rows_for_batch(batch)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=1_000)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--seed", type=int, default=20260517)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--metadata-output", type=Path)
    args = parser.parse_args()

    if args.batches <= 0:
        raise SystemExit("--batches must be positive")
    if args.candidates_per_batch <= 1:
        raise SystemExit("--candidates-per-batch must be greater than one")

    digest = sha256()
    row_count = 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        for row in generate_dataset_rows(
            batches=args.batches,
            candidates_per_batch=args.candidates_per_batch,
            seed=args.seed,
        ):
            encoded = json.dumps(row, sort_keys=True, separators=(",", ":"))
            digest.update(encoded.encode("utf-8"))
            digest.update(b"\n")
            handle.write(encoded + "\n")
            row_count += 1
    metadata = {
        "schema": "zenodex/energy/upba_v2_dataset_metadata/v1",
        "source": "synthetic",
        "seed": args.seed,
        "batches": args.batches,
        "candidates_per_batch": args.candidates_per_batch,
        "rows": row_count,
        "sha256": "0x" + digest.hexdigest(),
        "feature_dim": len(FEATURE_NAMES),
    }
    if args.metadata_output is not None:
        args.metadata_output.parent.mkdir(parents=True, exist_ok=True)
        args.metadata_output.write_text(
            json.dumps(metadata, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    print(json.dumps(metadata, indent=2, sort_keys=True))
    return 0


def _swap_intent(
    *,
    label: str,
    sender: str,
    asset_in: str,
    asset_out: str,
    amount_in: int,
    min_amount_out: int,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + sha256(label.encode("utf-8")).hexdigest(),
        sender_pubkey=sender,
        deadline=999,
        fields={
            "pool_id": "pool_ab",
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
        },
    )


def _candidate_fill_vectors(*, rng: Random, intents: Sequence[Intent]) -> list[tuple[UniformBatchFillV1, ...]]:
    fractions = (0.25, 0.5, 0.75, 1.0)
    vectors: list[tuple[UniformBatchFillV1, ...]] = []
    for fraction in fractions:
        fills = []
        for intent in intents:
            amount_in = int(intent.get_field("amount_in"))
            fills.append(
                UniformBatchFillV1(
                    intent_id=intent.intent_id,
                    executed_in=max(0, int(amount_in * fraction)),
                    executed_out=0,
                )
            )
        vectors.append(tuple(sorted(fills, key=lambda fill: fill.intent_id)))
    for _ in range(8):
        fills = []
        for intent in intents:
            amount_in = int(intent.get_field("amount_in"))
            executed_in = rng.choice((0, rng.randint(1, amount_in)))
            fills.append(
                UniformBatchFillV1(
                    intent_id=intent.intent_id,
                    executed_in=executed_in,
                    executed_out=0,
                )
            )
        vectors.append(tuple(sorted(fills, key=lambda fill: fill.intent_id)))
    return [_with_uniform_outputs(pool=None, intents=intents, fills=fills) for fills in vectors]


def _with_uniform_outputs(
    *,
    pool: PoolState | None,
    intents: Sequence[Intent],
    fills: Sequence[UniformBatchFillV1],
) -> tuple[UniformBatchFillV1, ...]:
    if pool is None:
        pool = PoolState(
            pool_id="pool_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=1_000,
            fee_bps=0,
            lp_supply=1_000,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    fills_by_id = {fill.intent_id: fill for fill in fills}
    price_num, price_den = _canonical_price_for_fills(pool=pool, intents=intents, fills=fills)
    out: list[UniformBatchFillV1] = []
    for intent in sorted(intents, key=lambda item: item.intent_id):
        fill = fills_by_id[intent.intent_id]
        fee_paid = compute_fee_total(max(0, fill.executed_in), pool.fee_bps)
        net_in = max(0, fill.executed_in - fee_paid)
        if fill.executed_in == 0:
            executed_out = 0
        elif str(intent.get_field("asset_in")) == pool.asset0:
            executed_out = (net_in * price_num) // price_den
        else:
            executed_out = (net_in * price_den) // price_num
        out.append(
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=fill.executed_in,
                executed_out=executed_out,
            )
        )
    return tuple(out)


def _certificate_for_fill_vector(
    *,
    intents: Sequence[Intent],
    pool: PoolState,
    fills: Sequence[UniformBatchFillV1],
) -> UniformBatchCertificateV1:
    normalized_fills = _with_uniform_outputs(pool=pool, intents=intents, fills=fills)
    price_num, price_den = _canonical_price_for_fills(pool=pool, intents=intents, fills=normalized_fills)
    return UniformBatchCertificateV1(
        pool_id=pool.pool_id,
        base_asset=pool.asset0,
        quote_asset=pool.asset1,
        pool_state_hash=uniform_batch_pool_state_hash(pool),
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=price_num,
        price_den=price_den,
        fills=tuple(sorted(normalized_fills, key=lambda fill: fill.intent_id)),
        policy_id=UNIFORM_BATCH_POLICY_V2_ID,
        schema=UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    )


def _canonical_price_for_fills(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    fills: Sequence[UniformBatchFillV1],
) -> tuple[int, int]:
    intents_by_id = {intent.intent_id: intent for intent in intents}
    base_to_quote_net = 0
    quote_to_base_net = 0
    for fill in fills:
        if fill.executed_in <= 0:
            continue
        intent = intents_by_id[fill.intent_id]
        net_in = fill.executed_in - compute_fee_total(fill.executed_in, pool.fee_bps)
        if net_in <= 0:
            continue
        if str(intent.get_field("asset_in")) == pool.asset0:
            base_to_quote_net += net_in
        else:
            quote_to_base_net += net_in
    if base_to_quote_net > 0 and quote_to_base_net > 0:
        return _reduce_ratio(quote_to_base_net, base_to_quote_net)
    return _reduce_ratio(pool.reserve1, pool.reserve0)


def _reduce_ratio(numerator: int, denominator: int) -> tuple[int, int]:
    divisor = gcd(numerator, denominator)
    return numerator // divisor, denominator // divisor


def _mutate_limit_violation(candidate: UniformBatchCertificateV1) -> UniformBatchCertificateV1:
    fills = list(candidate.fills)
    first_positive = next((index for index, fill in enumerate(fills) if fill.executed_in > 0), 0)
    fill = fills[first_positive]
    fills[first_positive] = UniformBatchFillV1(
        intent_id=fill.intent_id,
        executed_in=fill.executed_in,
        executed_out=0,
    )
    return _replace_fills(candidate, fills)


def _mutate_negative_reserve(candidate: UniformBatchCertificateV1, *, pool: PoolState) -> UniformBatchCertificateV1:
    fills = list(candidate.fills)
    fill = fills[0]
    fills[0] = UniformBatchFillV1(
        intent_id=fill.intent_id,
        executed_in=max(1, fill.executed_in),
        executed_out=max(pool.reserve0, pool.reserve1) + 1,
    )
    return _replace_fills(candidate, fills)


def _mutate_noncanonical_order(candidate: UniformBatchCertificateV1) -> UniformBatchCertificateV1:
    return _replace_fills(candidate, tuple(reversed(candidate.fills)))


def _all_zero_candidate(*, intents: Sequence[Intent], pool: PoolState) -> UniformBatchCertificateV1:
    fills = tuple(
        UniformBatchFillV1(intent_id=intent.intent_id, executed_in=0, executed_out=0)
        for intent in sorted(intents, key=lambda item: item.intent_id)
    )
    price_num, price_den = _reduce_ratio(pool.reserve1, pool.reserve0)
    return UniformBatchCertificateV1(
        pool_id=pool.pool_id,
        base_asset=pool.asset0,
        quote_asset=pool.asset1,
        pool_state_hash=uniform_batch_pool_state_hash(pool),
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=price_num,
        price_den=price_den,
        fills=fills,
        policy_id=UNIFORM_BATCH_POLICY_V2_ID,
        schema=UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    )


def _mutate_balance_violation(
    candidate: UniformBatchCertificateV1,
    *,
    intents: Sequence[Intent],
) -> UniformBatchCertificateV1:
    intents_by_id = {intent.intent_id: intent for intent in intents}
    fills = list(candidate.fills)
    fill = fills[-1]
    amount_in = int(intents_by_id[fill.intent_id].get_field("amount_in"))
    fills[-1] = UniformBatchFillV1(
        intent_id=fill.intent_id,
        executed_in=amount_in,
        executed_out=fill.executed_out,
    )
    return _replace_fills(candidate, fills)


def _mutate_near_miss(candidate: UniformBatchCertificateV1) -> UniformBatchCertificateV1:
    fills = list(candidate.fills)
    fill = next((item for item in fills if item.executed_in > 0), fills[0])
    index = fills.index(fill)
    fills[index] = UniformBatchFillV1(
        intent_id=fill.intent_id,
        executed_in=fill.executed_in,
        executed_out=max(0, fill.executed_out - 1),
    )
    return _replace_fills(candidate, fills)


def _mutate_attractive_output_mismatch(candidate: UniformBatchCertificateV1) -> UniformBatchCertificateV1:
    fills = list(candidate.fills)
    fill = next((item for item in fills if item.executed_in > 0), fills[0])
    index = fills.index(fill)
    fills[index] = UniformBatchFillV1(
        intent_id=fill.intent_id,
        executed_in=fill.executed_in,
        executed_out=fill.executed_out + max(1, fill.executed_out // 4),
    )
    return _replace_fills(candidate, fills)


def _mutate_unreduced_price(candidate: UniformBatchCertificateV1) -> UniformBatchCertificateV1:
    return UniformBatchCertificateV1(
        pool_id=candidate.pool_id,
        base_asset=candidate.base_asset,
        quote_asset=candidate.quote_asset,
        pool_state_hash=candidate.pool_state_hash,
        intent_set_hash=candidate.intent_set_hash,
        price_num=candidate.price_num * 2,
        price_den=candidate.price_den * 2,
        fills=candidate.fills,
        policy_id=candidate.policy_id,
        price_objective_id=candidate.price_objective_id,
        schema=candidate.schema,
    )


def _mutate_schema_policy_mismatch(candidate: UniformBatchCertificateV1) -> UniformBatchCertificateV1:
    return UniformBatchCertificateV1(
        pool_id=candidate.pool_id,
        base_asset=candidate.base_asset,
        quote_asset=candidate.quote_asset,
        pool_state_hash=candidate.pool_state_hash,
        intent_set_hash=candidate.intent_set_hash,
        price_num=candidate.price_num,
        price_den=candidate.price_den,
        fills=candidate.fills,
        policy_id=UNIFORM_BATCH_POLICY_V2_ID,
        price_objective_id=candidate.price_objective_id,
        schema=UNIFORM_BATCH_CERTIFICATE_SCHEMA_V1,
    )


def _random_noisy_candidate(
    *,
    rng: Random,
    intents: Sequence[Intent],
    pool: PoolState,
) -> UniformBatchCertificateV1:
    fills = []
    for intent in sorted(intents, key=lambda item: item.intent_id):
        amount_in = int(intent.get_field("amount_in"))
        executed_in = rng.randint(0, amount_in + max(1, amount_in // 2))
        executed_out = rng.randint(0, max(1, amount_in * 2))
        fills.append(
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=executed_in,
                executed_out=executed_out,
            )
        )
    price_num = rng.randint(1, 8)
    price_den = rng.randint(1, 8)
    if rng.random() < 0.8:
        price_num, price_den = _reduce_ratio(price_num, price_den)
    return UniformBatchCertificateV1(
        pool_id=pool.pool_id,
        base_asset=pool.asset0,
        quote_asset=pool.asset1,
        pool_state_hash=uniform_batch_pool_state_hash(pool),
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=price_num,
        price_den=price_den,
        fills=tuple(fills),
        policy_id=UNIFORM_BATCH_POLICY_V2_ID,
        schema=UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    )


def _replace_fills(
    candidate: UniformBatchCertificateV1,
    fills: Sequence[UniformBatchFillV1],
) -> UniformBatchCertificateV1:
    return UniformBatchCertificateV1(
        pool_id=candidate.pool_id,
        base_asset=candidate.base_asset,
        quote_asset=candidate.quote_asset,
        pool_state_hash=candidate.pool_state_hash,
        intent_set_hash=candidate.intent_set_hash,
        price_num=candidate.price_num,
        price_den=candidate.price_den,
        fills=tuple(fills),
        policy_id=candidate.policy_id,
        price_objective_id=candidate.price_objective_id,
        schema=candidate.schema,
    )


def _target_energy(record: object) -> float:
    raw = record.raw  # type: ignore[attr-defined]
    invalid_penalty = 0.0 if raw["verifier_ok"] else 1_000_000.0
    total_amount_in = max(1, int(raw.get("total_amount_in", 1)))
    normalized_volume = int(raw.get("volume", 0)) / total_amount_in
    normalized_surplus = int(raw.get("surplus", 0)) / total_amount_in
    return (
        invalid_penalty
        - normalized_volume
        - normalized_surplus
        + int(raw.get("dust_penalty", 0))
        + float(raw.get("imbalance_penalty", 0.0))
    )


def dataset_checksum(rows: Sequence[dict[str, object]]) -> str:
    digest = sha256()
    for row in rows:
        digest.update(canonical_json_bytes(row))
        digest.update(b"\n")
    return "0x" + digest.hexdigest()


if __name__ == "__main__":
    raise SystemExit(main())

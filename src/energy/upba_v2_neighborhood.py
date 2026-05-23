"""Deterministic UPBA v2 neighborhood proposals for advisory search.

The functions in this module generate candidate certificates. They do not
authorize settlement. Every generated candidate must still pass deterministic
UPBA verification before it can be considered for acceptance.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from typing import Mapping, Sequence

from src.core.cpmm import compute_fee_total
from src.core.uniform_batch_clearing import (
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    UNIFORM_BATCH_POLICY_V2_ID,
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    uniform_batch_intent_set_hash,
    uniform_batch_pool_state_hash,
)
from src.energy.upba_v2_ranker import advisory_candidate_hash
from src.state.balances import BalanceTable
from src.state.intents import Intent
from src.state.pools import PoolState


@dataclass(frozen=True)
class UpbaV2NeighborhoodProposal:
    """A deterministic repair or local move around a seed candidate."""

    recipe_id: str
    source_hash: str
    candidate: UniformBatchCertificateV1
    candidate_hash: str


@dataclass(frozen=True)
class UpbaV2NeighborhoodAugmentation:
    """Result of appending unique neighborhood proposals to a candidate list."""

    candidates: tuple[UniformBatchCertificateV1, ...]
    proposals: tuple[UpbaV2NeighborhoodProposal, ...]
    original_hashes: tuple[str, ...]
    augmented_hashes: tuple[str, ...]
    original_subset_ok: bool


def propose_upba_v2_neighborhood(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    seed_candidate: UniformBatchCertificateV1,
    max_proposals: int = 16,
    step_denominator: int = 4,
) -> tuple[UpbaV2NeighborhoodProposal, ...]:
    """Generate deterministic local candidate proposals around a seed.

    The recipes are intentionally simple:
    - canonicalize, sort fills, clamp inputs to amount and balance, recompute outputs;
    - snap the whole fill vector to common fractions;
    - move one intent up or down by a bounded step;
    - try one-sided directional fills.

    The returned candidates are advisory only and may be invalid. The caller must
    verify them with the deterministic UPBA verifier before use.
    """

    if max_proposals <= 0:
        return ()
    step_denominator = max(1, int(step_denominator))
    source_hash = advisory_candidate_hash(seed_candidate)
    context = _intent_context(pool=pool, intents=intents, balances=balances)
    seed_inputs = _seed_inputs(seed_candidate=seed_candidate, context=context)
    proposals: list[UpbaV2NeighborhoodProposal] = []
    seen_hashes = {source_hash}

    def add(recipe_id: str, inputs: Mapping[str, int]) -> None:
        if len(proposals) >= max_proposals:
            return
        candidate = _candidate_from_inputs(pool=pool, intents=intents, inputs=inputs)
        candidate_hash = advisory_candidate_hash(candidate)
        if candidate_hash in seen_hashes:
            return
        seen_hashes.add(candidate_hash)
        proposals.append(
            UpbaV2NeighborhoodProposal(
                recipe_id=recipe_id,
                source_hash=source_hash,
                candidate=candidate,
                candidate_hash=candidate_hash,
            )
        )

    add("canonical_clamped", seed_inputs)

    caps = {intent_id: int(data["cap"]) for intent_id, data in context.items()}
    add("full_balance_clamped", caps)
    for numerator in (1, 2, 3):
        add(
            f"snap_fraction_{numerator}_{step_denominator}",
            {
                intent_id: (data["cap"] * numerator) // step_denominator
                for intent_id, data in context.items()
            },
        )

    for intent in sorted(intents, key=lambda item: item.intent_id):
        data = context[intent.intent_id]
        cap = int(data["cap"])
        if cap <= 0:
            continue
        current = seed_inputs.get(intent.intent_id, 0)
        amount_in = int(data["amount_in"])
        step = max(1, (amount_in + step_denominator - 1) // step_denominator)
        up_inputs = dict(seed_inputs)
        up_inputs[intent.intent_id] = min(cap, current + step)
        add(f"increase_step:{intent.intent_id}", up_inputs)
        down_inputs = dict(seed_inputs)
        down_inputs[intent.intent_id] = max(0, current - step)
        add(f"decrease_step:{intent.intent_id}", down_inputs)

    for direction in ("base_to_quote", "quote_to_base"):
        add(
            f"single_direction:{direction}",
            {
                intent_id: int(data["cap"]) if data["direction"] == direction else 0
                for intent_id, data in context.items()
            },
        )

    return tuple(proposals)


def augment_candidates_with_neighborhood(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    candidates: Sequence[UniformBatchCertificateV1],
    repair_seed_count: int = 4,
    max_proposals_per_seed: int = 8,
    step_denominator: int = 4,
) -> UpbaV2NeighborhoodAugmentation:
    """Append unique deterministic neighborhood proposals to `candidates`.

    Original candidates are retained first and are never mutated. This preserves
    the audit trail for research benchmarks that compare limited search against
    neighborhood-expanded search.
    """

    original = tuple(candidates)
    original_hashes = tuple(advisory_candidate_hash(candidate) for candidate in original)
    seen_hashes = set(original_hashes)
    augmented = list(original)
    proposals: list[UpbaV2NeighborhoodProposal] = []
    seeds = original[: max(0, repair_seed_count)]
    for seed in seeds:
        for proposal in propose_upba_v2_neighborhood(
            pool=pool,
            intents=intents,
            balances=balances,
            seed_candidate=seed,
            max_proposals=max_proposals_per_seed,
            step_denominator=step_denominator,
        ):
            if proposal.candidate_hash in seen_hashes:
                continue
            seen_hashes.add(proposal.candidate_hash)
            proposals.append(proposal)
            augmented.append(proposal.candidate)

    augmented_hashes = tuple(advisory_candidate_hash(candidate) for candidate in augmented)
    augmented_hash_set = set(augmented_hashes)
    original_subset_ok = all(candidate_hash in augmented_hash_set for candidate_hash in original_hashes)
    return UpbaV2NeighborhoodAugmentation(
        candidates=tuple(augmented),
        proposals=tuple(proposals),
        original_hashes=original_hashes,
        augmented_hashes=augmented_hashes,
        original_subset_ok=original_subset_ok,
    )


def _intent_context(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
) -> dict[str, dict[str, int | str]]:
    context: dict[str, dict[str, int | str]] = {}
    for intent in sorted(intents, key=lambda item: item.intent_id):
        asset_in = str(intent.get_field("asset_in"))
        amount_in = int(intent.get_field("amount_in"))
        balance = int(balances.get(intent.sender_pubkey, asset_in))
        direction = "base_to_quote" if asset_in == pool.asset0 else "quote_to_base"
        context[intent.intent_id] = {
            "amount_in": max(0, amount_in),
            "cap": max(0, min(amount_in, balance)),
            "direction": direction,
        }
    return context


def _seed_inputs(
    *,
    seed_candidate: UniformBatchCertificateV1,
    context: Mapping[str, Mapping[str, int | str]],
) -> dict[str, int]:
    raw_by_id: dict[str, int] = {}
    for fill in seed_candidate.fills:
        if fill.intent_id in context and fill.intent_id not in raw_by_id:
            raw_by_id[fill.intent_id] = int(fill.executed_in)
    clamped: dict[str, int] = {}
    for intent_id, data in context.items():
        cap = int(data["cap"])
        clamped[intent_id] = max(0, min(cap, raw_by_id.get(intent_id, 0)))
    return clamped


def _candidate_from_inputs(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    inputs: Mapping[str, int],
) -> UniformBatchCertificateV1:
    price_num, price_den = _canonical_price_for_inputs(pool=pool, intents=intents, inputs=inputs)
    fills: list[UniformBatchFillV1] = []
    for intent in sorted(intents, key=lambda item: item.intent_id):
        executed_in = max(0, int(inputs.get(intent.intent_id, 0)))
        fee_paid = compute_fee_total(executed_in, pool.fee_bps)
        net_in = max(0, executed_in - fee_paid)
        if executed_in == 0:
            executed_out = 0
        elif str(intent.get_field("asset_in")) == pool.asset0:
            executed_out = (net_in * price_num) // price_den
        else:
            executed_out = (net_in * price_den) // price_num
        fills.append(
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=executed_in,
                executed_out=max(0, executed_out),
            )
        )
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


def _canonical_price_for_inputs(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    inputs: Mapping[str, int],
) -> tuple[int, int]:
    base_to_quote_net = 0
    quote_to_base_net = 0
    for intent in intents:
        executed_in = max(0, int(inputs.get(intent.intent_id, 0)))
        if executed_in <= 0:
            continue
        net_in = executed_in - compute_fee_total(executed_in, pool.fee_bps)
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
    numerator = max(1, int(numerator))
    denominator = max(1, int(denominator))
    divisor = gcd(numerator, denominator)
    return numerator // divisor, denominator // divisor

"""Advisory ranking and verifier-backed search helpers for UPBA v2 candidates."""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from typing import Callable, Mapping, Sequence

from src.core.uniform_batch_clearing import (
    UniformBatchCertificateV1,
    uniform_batch_certificate_hash,
    verify_uniform_batch_certificate_v1,
)
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import hand_energy_from_record
from src.energy.upba_v2_set_features import (
    SET_AWARE_FEATURE_NAMES,
    extract_upba_v2_set_aware_feature_record,
)
from src.state.balances import BalanceTable
from src.state.canonical import canonical_json_bytes, domain_sep_bytes
from src.state.intents import Intent
from src.state.pools import PoolState

EnergyScorer = Callable[[UniformBatchCertificateV1], float]


@dataclass(frozen=True)
class RankedUpbaV2Candidate:
    candidate: UniformBatchCertificateV1
    energy: float
    original_index: int


@dataclass(frozen=True)
class VerifiedCandidateResult:
    candidate: UniformBatchCertificateV1
    certificate_hash: str
    ok: bool
    error: str | None
    volume: int
    surplus: int


@dataclass(frozen=True)
class UpbaV2SearchReport:
    best: VerifiedCandidateResult | None
    verifier_calls: int
    invalid_accept_count: int
    checked_hashes: tuple[str, ...]
    permutation_ok: bool


def rank_upba_v2_candidates(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    candidates: Sequence[UniformBatchCertificateV1],
    scorer: EnergyScorer | None = None,
) -> tuple[RankedUpbaV2Candidate, ...]:
    """Rank candidates by lower energy while preserving deterministic tie-breaks."""

    ranked: list[RankedUpbaV2Candidate] = []
    for index, candidate in enumerate(candidates):
        if scorer is None:
            record = extract_upba_v2_feature_record(
                pool=pool,
                intents=intents,
                balances=balances,
                candidate=candidate,
                include_verifier_label=False,
            )
            energy = hand_energy_from_record(record)
        else:
            energy = float(scorer(candidate))
        ranked.append(RankedUpbaV2Candidate(candidate=candidate, energy=energy, original_index=index))
    ranked.sort(key=lambda item: (item.energy, advisory_candidate_hash(item.candidate), item.original_index))
    return tuple(ranked)


def verify_candidates_in_order(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    candidates: Sequence[UniformBatchCertificateV1],
) -> tuple[VerifiedCandidateResult, ...]:
    """Run the deterministic verifier over a supplied order."""

    results: list[VerifiedCandidateResult] = []
    intents_by_id = {intent.intent_id: intent for intent in intents}
    for candidate in candidates:
        result = verify_uniform_batch_certificate_v1(
            intents=intents,
            pool=pool,
            balances=balances,
            certificate=candidate,
        )
        volume, surplus = _objective_for_candidate(candidate, intents_by_id=intents_by_id) if result.ok else (0, 0)
        results.append(
            VerifiedCandidateResult(
                candidate=candidate,
                certificate_hash=advisory_candidate_hash(candidate),
                ok=result.ok,
                error=result.error,
                volume=volume,
                surplus=surplus,
            )
        )
    return tuple(results)


def deterministic_best_verified_candidate(
    results: Sequence[VerifiedCandidateResult],
) -> VerifiedCandidateResult | None:
    """Select the verifier-accepted candidate with lexicographic volume/surplus objective."""

    accepted = [result for result in results if result.ok]
    if not accepted:
        return None
    return max(accepted, key=lambda result: (result.volume, result.surplus, result.certificate_hash))


def objective_equivalent_verified_results(
    left: VerifiedCandidateResult,
    right: VerifiedCandidateResult,
) -> bool:
    """Return whether two verified candidates occupy the same objective class."""

    return (
        left.ok
        and right.ok
        and left.volume == right.volume
        and left.surplus == right.surplus
    )


def calls_until_objective_equivalent_winner(
    *,
    ordered_results: Sequence[VerifiedCandidateResult],
    winner: VerifiedCandidateResult,
) -> int:
    """Count verifier calls until the first candidate equivalent to a benchmark winner."""

    for index, result in enumerate(ordered_results, start=1):
        if objective_equivalent_verified_results(result, winner):
            return index
    return len(ordered_results)


def objective_argmax_class_size(
    *,
    verified_results: Sequence[VerifiedCandidateResult],
    winner: VerifiedCandidateResult,
) -> int:
    """Count accepted candidates with the same objective as the benchmark winner."""

    return sum(
        1 for result in verified_results if objective_equivalent_verified_results(result, winner)
    )


def verified_result_cannot_beat(
    winner: VerifiedCandidateResult,
    other: VerifiedCandidateResult,
) -> bool:
    """Return whether a verified result cannot beat the winner objective."""

    if not other.ok:
        return True
    if other.volume < winner.volume:
        return True
    if other.volume == winner.volume and other.surplus <= winner.surplus:
        return True
    return False


def verified_checked_stop_certificate_holds(
    *,
    winner: VerifiedCandidateResult,
    checked: Sequence[VerifiedCandidateResult],
    suffix: Sequence[VerifiedCandidateResult],
) -> bool:
    """Audit a checked-stop certificate over already verified results.

    This helper is for offline evidence and deterministic receipts. A live
    early stop still needs a verifier-facing bound for the unchecked suffix.
    """

    if not winner.ok:
        return False
    if all(result.certificate_hash != winner.certificate_hash for result in checked):
        return False
    return all(verified_result_cannot_beat(winner, result) for result in (*checked, *suffix))


def search_best_with_deterministic_fallback(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    candidates: Sequence[UniformBatchCertificateV1],
    scorer: EnergyScorer | None = None,
    top_k: int | None = None,
) -> UpbaV2SearchReport:
    """Rank candidates, verify the prefix, then deterministically verify the rest.

    The model only changes order. The returned best candidate is selected from
    verifier-accepted candidates by the deterministic objective.
    """

    ranked = rank_upba_v2_candidates(
        pool=pool,
        intents=intents,
        balances=balances,
        candidates=candidates,
        scorer=scorer,
    )
    ordered = [item.candidate for item in ranked]
    if top_k is not None:
        prefix = ordered[: max(0, top_k)]
        suffix = ordered[max(0, top_k) :]
        ordered = prefix + suffix
    permutation_ok = candidate_orders_are_hash_permutation(candidates, ordered)
    if not permutation_ok:
        raise ValueError("ranked candidate order is not a permutation of the input candidates")
    checked = verify_candidates_in_order(
        pool=pool,
        intents=intents,
        balances=balances,
        candidates=ordered,
    )
    return UpbaV2SearchReport(
        best=deterministic_best_verified_candidate(checked),
        verifier_calls=len(checked),
        invalid_accept_count=0,
        checked_hashes=tuple(result.certificate_hash for result in checked),
        permutation_ok=permutation_ok,
    )


def calls_until_winner(
    *,
    ordered_results: Sequence[VerifiedCandidateResult],
    winner_hash: str,
) -> int:
    """Count deterministic verifier calls until a known benchmark winner appears."""

    for index, result in enumerate(ordered_results, start=1):
        if result.certificate_hash == winner_hash:
            return index
    return len(ordered_results)


def advisory_candidate_hash(candidate: UniformBatchCertificateV1) -> str:
    """Return the verifier hash when available, or an advisory hash for invalid shapes."""

    try:
        return uniform_batch_certificate_hash(candidate)
    except (TypeError, ValueError):
        digest = sha256(
            domain_sep_bytes("advisory_upba_v2_candidate", version=1)
            + canonical_json_bytes(candidate.to_dict())
        ).hexdigest()
        return "0x" + digest


def candidate_hash_multiset(candidates: Sequence[UniformBatchCertificateV1]) -> tuple[str, ...]:
    """Return a deterministic hash multiset for candidate-order permutation checks."""

    return tuple(sorted(advisory_candidate_hash(candidate) for candidate in candidates))


def candidate_orders_are_hash_permutation(
    original: Sequence[UniformBatchCertificateV1],
    ordered: Sequence[UniformBatchCertificateV1],
) -> bool:
    """Return whether two candidate sequences have the same advisory hash multiset."""

    return candidate_hash_multiset(original) == candidate_hash_multiset(ordered)


def scorer_from_linear_model(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    model: object,
) -> EnergyScorer:
    """Wrap a model with an `energy(features)` method as a candidate scorer."""

    def score(candidate: UniformBatchCertificateV1) -> float:
        if tuple(getattr(model, "feature_names", ())) == SET_AWARE_FEATURE_NAMES:
            record = extract_upba_v2_set_aware_feature_record(
                pool=pool,
                intents=intents,
                balances=balances,
                candidate=candidate,
            )
        else:
            record = extract_upba_v2_feature_record(
                pool=pool,
                intents=intents,
                balances=balances,
                candidate=candidate,
                include_verifier_label=False,
            )
        return float(model.energy(record.values))  # type: ignore[attr-defined]

    return score


def _objective_for_candidate(
    candidate: UniformBatchCertificateV1 | Mapping[str, object],
    *,
    intents_by_id: Mapping[str, Intent],
) -> tuple[int, int]:
    parsed = candidate if isinstance(candidate, UniformBatchCertificateV1) else UniformBatchCertificateV1.from_obj(candidate)
    volume = 0
    surplus = 0
    for fill in parsed.fills:
        intent = intents_by_id[fill.intent_id]
        amount_in = int(intent.get_field("amount_in"))
        min_amount_out = int(intent.get_field("min_amount_out"))
        volume += int(fill.executed_out)
        required_min_out = (min_amount_out * int(fill.executed_in) + amount_in - 1) // amount_in
        surplus += int(fill.executed_out) - required_min_out
    return volume, surplus

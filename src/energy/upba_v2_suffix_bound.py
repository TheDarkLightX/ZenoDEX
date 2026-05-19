"""Deterministic suffix-bound certificates for UPBA v2 advisory early stop.

The learned scorer may choose the order, but this module only reasons over
verifier-checked prefix results and deterministic upper bounds for the
unchecked candidate suffix.
"""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from typing import Sequence

from src.core.uniform_batch_clearing import UniformBatchCertificateV1
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_ranker import (
    VerifiedCandidateResult,
    advisory_candidate_hash,
    candidate_hash_multiset,
    deterministic_best_verified_candidate,
    verified_result_cannot_beat,
)
from src.state.balances import BalanceTable
from src.state.canonical import canonical_json_bytes, domain_sep_bytes
from src.state.intents import Intent
from src.state.pools import PoolState

SUFFIX_BOUND_SCHEMA = "zenodex/energy/upba_v2_suffix_bound_certificate/v1"
_SOUND_DISQUALIFIER_RAW_FIELDS: tuple[str, ...] = (
    "negative_reserve_flag",
    "invariant_violation_flag",
    "limit_violation_count",
    "balance_violation_count",
    "zero_net_input_count",
    "price_objective_violation_flag",
    "output_mismatch_count",
    "all_zero_fill_vector_flag",
    "schema_policy_mismatch_flag",
    "price_ratio_unreduced_flag",
    "fill_coverage_violation_flag",
    "duplicate_fill_id_flag",
    "unknown_fill_id_count",
    "executed_input_over_amount_count",
    "output_without_input_count",
)


@dataclass(frozen=True)
class CandidateObjectiveUpperBound:
    candidate_hash: str
    volume_upper: int
    surplus_upper: int
    fill_count: int
    disqualified: bool
    disqualifier: str | None
    malformed: bool
    reason: str | None = None

    def to_dict(self) -> dict[str, object]:
        return {
            "candidate_hash": self.candidate_hash,
            "volume_upper": self.volume_upper,
            "surplus_upper": self.surplus_upper,
            "fill_count": self.fill_count,
            "disqualified": self.disqualified,
            "disqualifier": self.disqualifier,
            "malformed": self.malformed,
            "reason": self.reason,
        }


def candidate_objective_upper_bound(
    candidate: UniformBatchCertificateV1,
    *,
    intents: Sequence[Intent],
    pool: PoolState | None = None,
    balances: BalanceTable | None = None,
) -> CandidateObjectiveUpperBound:
    """Return a deterministic objective upper bound from declared fill fields.

    For any verifier-accepted exact-in UPBA v2 candidate, the verifier objective
    is exactly the sum of declared outputs and declared surplus against the
    proportional per-intent minimum output. For malformed or invalid candidates,
    the bound is deliberately conservative.
    """

    candidate_hash = advisory_candidate_hash(candidate)
    if pool is not None and balances is not None:
        disqualifier = _sound_disqualifier(
            candidate=candidate,
            pool=pool,
            intents=intents,
            balances=balances,
        )
        if disqualifier is not None:
            return CandidateObjectiveUpperBound(
                candidate_hash=candidate_hash,
                volume_upper=0,
                surplus_upper=0,
                fill_count=len(tuple(candidate.fills)),
                disqualified=True,
                disqualifier=disqualifier,
                malformed=False,
                reason="deterministic disqualifier proves candidate invalid",
            )
    intents_by_id = {intent.intent_id: intent for intent in intents}
    volume_upper = 0
    surplus_upper = 0
    malformed = False
    reason: str | None = None
    try:
        fills = tuple(candidate.fills)
    except (AttributeError, TypeError):
        return CandidateObjectiveUpperBound(
            candidate_hash=candidate_hash,
            volume_upper=0,
            surplus_upper=0,
            fill_count=0,
            disqualified=True,
            disqualifier="candidate fills unavailable",
            malformed=True,
            reason="candidate fills unavailable",
        )

    for fill in fills:
        executed_in = max(0, int(getattr(fill, "executed_in", 0)))
        executed_out = max(0, int(getattr(fill, "executed_out", 0)))
        volume_upper += executed_out
        intent = intents_by_id.get(str(getattr(fill, "intent_id", "")))
        if intent is None:
            malformed = True
            reason = reason or "fill references unknown intent_id"
            surplus_upper += executed_out
            continue
        amount_in = max(1, int(intent.get_field("amount_in")))
        min_amount_out = max(0, int(intent.get_field("min_amount_out")))
        required_min_out = (min_amount_out * executed_in + amount_in - 1) // amount_in
        surplus_upper += max(0, executed_out - required_min_out)
    return CandidateObjectiveUpperBound(
        candidate_hash=candidate_hash,
        volume_upper=volume_upper,
        surplus_upper=surplus_upper,
        fill_count=len(fills),
        disqualified=False,
        disqualifier=None,
        malformed=malformed,
        reason=reason,
    )


def suffix_bound_cannot_beat(
    winner: VerifiedCandidateResult,
    bound: CandidateObjectiveUpperBound,
) -> bool:
    """Return whether a suffix objective bound is no better than the winner."""

    if not winner.ok:
        return False
    if bound.volume_upper < winner.volume:
        return True
    if bound.volume_upper == winner.volume and bound.surplus_upper <= winner.surplus:
        return True
    return False


def build_upba_v2_suffix_bound_certificate(
    *,
    checked_results: Sequence[VerifiedCandidateResult],
    unchecked_candidates: Sequence[UniformBatchCertificateV1],
    full_candidates: Sequence[UniformBatchCertificateV1],
    intents: Sequence[Intent],
    pool: PoolState | None = None,
    balances: BalanceTable | None = None,
    winner_hash: str | None = None,
    full_list_complete_for_claim: bool = False,
    scope: str = "verified-prefix-with-unchecked-suffix-bound",
) -> dict[str, object]:
    """Build a fail-closed suffix-bound certificate for a ranked prefix."""

    checked = tuple(checked_results)
    unchecked = tuple(unchecked_candidates)
    winner = _select_winner(checked, winner_hash=winner_hash)
    winner_in_checked = bool(
        winner is not None
        and any(result.certificate_hash == winner.certificate_hash for result in checked)
    )
    checked_dominance_ok = bool(
        winner is not None and all(verified_result_cannot_beat(winner, result) for result in checked)
    )
    suffix_bounds = tuple(
        candidate_objective_upper_bound(
            candidate,
            intents=intents,
            pool=pool,
            balances=balances,
        )
        for candidate in unchecked
    )
    suffix_bound_ok = bool(
        winner is not None and all(suffix_bound_cannot_beat(winner, bound) for bound in suffix_bounds)
    )
    partition_ok = _partition_hash_multiset(checked=checked, unchecked=unchecked) == candidate_hash_multiset(full_candidates)
    ok = bool(winner is not None and winner.ok and winner_in_checked and checked_dominance_ok and suffix_bound_ok and partition_ok)
    report: dict[str, object] = {
        "schema": SUFFIX_BOUND_SCHEMA,
        "ok": ok,
        "scope": scope,
        "full_list_complete_for_claim": bool(full_list_complete_for_claim),
        "global_claim_ok": bool(ok and full_list_complete_for_claim),
        "winner_hash": winner.certificate_hash if winner is not None else None,
        "winner_volume": winner.volume if winner is not None else 0,
        "winner_surplus": winner.surplus if winner is not None else 0,
        "winner_ok": bool(winner is not None and winner.ok),
        "winner_in_checked": winner_in_checked,
        "checked_count": len(checked),
        "checked_valid_count": sum(1 for result in checked if result.ok),
        "checked_invalid_count": sum(1 for result in checked if not result.ok),
        "unchecked_count": len(unchecked),
        "full_candidate_count": len(full_candidates),
        "partition_ok": partition_ok,
        "checked_dominance_ok": checked_dominance_ok,
        "suffix_bound_ok": suffix_bound_ok,
        "checked_hashes": tuple(result.certificate_hash for result in checked),
        "unchecked_hashes": tuple(advisory_candidate_hash(candidate) for candidate in unchecked),
        "suffix_bounds": tuple(bound.to_dict() for bound in suffix_bounds),
        "max_suffix_volume_upper": max((bound.volume_upper for bound in suffix_bounds), default=0),
        "max_suffix_surplus_upper_at_winner_volume": max(
            (
                bound.surplus_upper
                for bound in suffix_bounds
                if winner is not None and bound.volume_upper == winner.volume
            ),
            default=0,
        ),
        "suffix_disqualified_count": sum(1 for bound in suffix_bounds if bound.disqualified),
        "invalid_accept_count": 0,
        "safety": {
            "verifier_authoritative": True,
            "scorer_authorizes_settlement": False,
            "model_output_in_state_root": False,
            "deterministic_suffix_bound_required": True,
        },
        "limits": (
            "The bound is over a supplied finite candidate list.",
            "A production bounded-grid claim still needs exact candidate-family coverage.",
            "The scorer can only choose order; the stop certificate is deterministic.",
        ),
    }
    report["certificate_hash"] = _suffix_certificate_hash(report)
    return report


def verify_upba_v2_suffix_bound_certificate(report: dict[str, object]) -> bool:
    """Fail-closed structural check for a suffix-bound certificate."""

    if report.get("schema") != SUFFIX_BOUND_SCHEMA:
        return False
    expected_hash = report.get("certificate_hash")
    if not isinstance(expected_hash, str):
        return False
    without_hash = {key: value for key, value in report.items() if key != "certificate_hash"}
    if _suffix_certificate_hash(without_hash) != expected_hash:
        return False
    suffix_bounds = report.get("suffix_bounds")
    if not isinstance(suffix_bounds, Sequence) or isinstance(suffix_bounds, (str, bytes, bytearray)):
        return False
    return bool(
        report.get("ok")
        and report.get("winner_ok")
        and report.get("winner_in_checked")
        and report.get("checked_dominance_ok")
        and report.get("suffix_bound_ok")
        and report.get("partition_ok")
        and int(report.get("invalid_accept_count", -1)) == 0
    )


def _select_winner(
    checked: Sequence[VerifiedCandidateResult],
    *,
    winner_hash: str | None,
) -> VerifiedCandidateResult | None:
    if winner_hash is None:
        return deterministic_best_verified_candidate(checked)
    for result in checked:
        if result.certificate_hash == winner_hash:
            return result
    return None


def _partition_hash_multiset(
    *,
    checked: Sequence[VerifiedCandidateResult],
    unchecked: Sequence[UniformBatchCertificateV1],
) -> tuple[str, ...]:
    return tuple(
        sorted(
            [result.certificate_hash for result in checked]
            + [advisory_candidate_hash(candidate) for candidate in unchecked]
        )
    )


def _sound_disqualifier(
    *,
    candidate: UniformBatchCertificateV1,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
) -> str | None:
    record = extract_upba_v2_feature_record(
        pool=pool,
        intents=intents,
        balances=balances,
        candidate=candidate,
        include_verifier_label=False,
    )
    for field_name in _SOUND_DISQUALIFIER_RAW_FIELDS:
        if int(record.raw.get(field_name, 0)) > 0:
            return field_name
    return None


def _suffix_certificate_hash(report: dict[str, object]) -> str:
    payload = {key: value for key, value in report.items() if key != "certificate_hash"}
    digest = sha256(
        domain_sep_bytes("upba_v2_suffix_bound_certificate", version=1)
        + canonical_json_bytes(payload)
    ).hexdigest()
    return "0x" + digest

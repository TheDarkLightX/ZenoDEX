"""Runtime dominance-cover checks for UPBA v2 advisory pruning.

These helpers are advisory research tools. They do not authorize settlement and
do not replace deterministic UPBA certificate verification.
"""

from __future__ import annotations

from collections import Counter
from hashlib import sha256
from typing import Sequence

from src.energy.upba_v2_ranker import (
    VerifiedCandidateResult,
    deterministic_best_verified_candidate,
    verified_result_cannot_beat,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes

DOMINANCE_COVER_SCHEMA = "zenodex/energy/upba_v2_dominance_cover_certificate/v1"


def weakly_dominates_verified(
    representative: VerifiedCandidateResult,
    candidate: VerifiedCandidateResult,
) -> bool:
    """Return whether a verifier-accepted representative weakly dominates one candidate."""

    if not representative.ok or not candidate.ok:
        return False
    if representative.volume > candidate.volume:
        return True
    return representative.volume == candidate.volume and representative.surplus >= candidate.surplus


def build_upba_v2_dominance_cover_certificate(
    *,
    full_results: Sequence[VerifiedCandidateResult],
    pruned_results: Sequence[VerifiedCandidateResult],
    winner_hash: str | None = None,
    full_list_complete_for_claim: bool = False,
    scope: str = "verified-accepted-full-list",
) -> dict[str, object]:
    """Build a deterministic dominance-cover receipt over verified results.

    The checker proves only the finite-list statement represented by its inputs:
    every verifier-accepted full-list candidate has a verifier-accepted pruned
    representative that weakly dominates it, and the declared pruned winner is
    weakly optimal over the pruned list. A bounded-grid or production claim still
    needs an external proof that the supplied full list is complete for that
    domain.
    """

    full = tuple(full_results)
    pruned = tuple(pruned_results)
    accepted_full = tuple(result for result in full if result.ok)
    accepted_pruned = tuple(result for result in pruned if result.ok)
    pruned_sound_ok = len(accepted_pruned) == len(pruned)
    winner = _select_winner(accepted_pruned, winner_hash=winner_hash)
    winner_in_pruned = winner is not None and any(
        result.certificate_hash == winner.certificate_hash for result in pruned
    )
    upper_bound_ok = bool(winner is not None) and all(
        verified_result_cannot_beat(winner, result) for result in accepted_pruned
    )

    representative_by_full_hash: dict[str, str] = {}
    uncovered_full_hashes: list[str] = []
    for candidate in accepted_full:
        representative = _dominance_representative(
            candidate=candidate,
            representatives=accepted_pruned,
        )
        if representative is None:
            uncovered_full_hashes.append(candidate.certificate_hash)
        else:
            representative_by_full_hash[candidate.certificate_hash] = representative.certificate_hash

    dominance_cover_ok = not uncovered_full_hashes
    ok = pruned_sound_ok and winner_in_pruned and upper_bound_ok and dominance_cover_ok
    report: dict[str, object] = {
        "schema": DOMINANCE_COVER_SCHEMA,
        "ok": ok,
        "scope": scope,
        "full_list_complete_for_claim": bool(full_list_complete_for_claim),
        "global_claim_ok": bool(ok and full_list_complete_for_claim),
        "full_candidate_count": len(full),
        "full_valid_count": len(accepted_full),
        "full_invalid_count": len(full) - len(accepted_full),
        "pruned_candidate_count": len(pruned),
        "pruned_valid_count": len(accepted_pruned),
        "pruned_invalid_count": len(pruned) - len(accepted_pruned),
        "pruned_sound_ok": pruned_sound_ok,
        "winner_hash": winner.certificate_hash if winner is not None else None,
        "winner_volume": winner.volume if winner is not None else None,
        "winner_surplus": winner.surplus if winner is not None else None,
        "winner_in_pruned": winner_in_pruned,
        "upper_bound_ok": upper_bound_ok,
        "dominance_cover_ok": dominance_cover_ok,
        "covered_full_count": len(representative_by_full_hash),
        "uncovered_full_count": len(uncovered_full_hashes),
        "uncovered_full_hashes": tuple(uncovered_full_hashes),
        "representative_by_full_hash": representative_by_full_hash,
        "full_hash_unique": _hashes_unique(full),
        "pruned_hash_unique": _hashes_unique(pruned),
        "invalid_accept_count": 0,
        "safety": {
            "verifier_authoritative": True,
            "scorer_authorizes_settlement": False,
            "model_output_in_state_root": False,
            "deterministic_verifier_required": True,
        },
        "limits": (
            "A passing certificate covers only the verified finite full list supplied to this checker.",
            "A bounded-grid or production claim still needs a separate proof that the full list is complete.",
            "The checker rejects invalid pruned candidates because pruned soundness is a theorem premise.",
        ),
    }
    report["certificate_hash"] = _certificate_hash(report)
    return report


def verify_upba_v2_dominance_cover_certificate(report: dict[str, object]) -> bool:
    """Fail-closed structural check for a dominance-cover report."""

    if report.get("schema") != DOMINANCE_COVER_SCHEMA:
        return False
    expected_hash = report.get("certificate_hash")
    if not isinstance(expected_hash, str):
        return False
    without_hash = {key: value for key, value in report.items() if key != "certificate_hash"}
    observed = _certificate_hash(without_hash)
    if observed != expected_hash:
        return False
    return bool(
        report.get("ok")
        and report.get("pruned_sound_ok")
        and report.get("winner_in_pruned")
        and report.get("upper_bound_ok")
        and report.get("dominance_cover_ok")
        and int(report.get("uncovered_full_count", -1)) == 0
        and int(report.get("invalid_accept_count", -1)) == 0
    )


def _select_winner(
    accepted_pruned: Sequence[VerifiedCandidateResult],
    *,
    winner_hash: str | None,
) -> VerifiedCandidateResult | None:
    if winner_hash is None:
        return deterministic_best_verified_candidate(accepted_pruned)
    for result in accepted_pruned:
        if result.certificate_hash == winner_hash:
            return result
    return None


def _dominance_representative(
    *,
    candidate: VerifiedCandidateResult,
    representatives: Sequence[VerifiedCandidateResult],
) -> VerifiedCandidateResult | None:
    dominating = [
        representative
        for representative in representatives
        if weakly_dominates_verified(representative, candidate)
    ]
    if not dominating:
        return None
    return max(
        dominating,
        key=lambda result: (result.volume, result.surplus, result.certificate_hash),
    )


def _hashes_unique(results: Sequence[VerifiedCandidateResult]) -> bool:
    counts = Counter(result.certificate_hash for result in results)
    return all(count == 1 for count in counts.values())


def _certificate_hash(report: dict[str, object]) -> str:
    payload = {key: value for key, value in report.items() if key != "certificate_hash"}
    digest = sha256(
        domain_sep_bytes("upba_v2_dominance_cover_certificate", version=1)
        + canonical_json_bytes(payload)
    ).hexdigest()
    return "0x" + digest

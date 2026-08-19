"""Build the canonical research packet for proof-market game theory V2."""

from __future__ import annotations

import dataclasses
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any, Final

from tools import proof_market_formal_evidence_v2 as formal
from tools import proof_market_game_theory_v2 as model
from tools.proof_market_game_theory_checks_v2 import evaluate_checks
from tools.proof_market_v1_refutation_v2 import v1_attack_evidence

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
SCHEMA: Final = "zenodex/proof-market-game-theory/v2"
REVIEWED_SOURCE_COMMIT: Final = "fa6d2012fb4ebbbb5893d8f218f0b61ccae93be5"


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{relative_path} must contain a JSON object")
    return value


def _fraction(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def _capacity_ticket_evidence() -> dict[str, Any]:
    split = (
        model.ProviderV2("A1", "OWNER_A", "DOMAIN_A", 100, 3),
        model.ProviderV2("Z1", "OWNER_A", "DOMAIN_A", 110, 2),
        model.ProviderV2("B1", "OWNER_B", "DOMAIN_B", 119, 5),
        model.ProviderV2("C1", "OWNER_C", "DOMAIN_C", 121, 100),
    )
    merged = (
        model.ProviderV2("A", "OWNER_A", "DOMAIN_A", 110, 5),
        model.ProviderV2("B1", "OWNER_B", "DOMAIN_B", 119, 5),
        model.ProviderV2("C1", "OWNER_C", "DOMAIN_C", 121, 100),
    )
    payment = 120

    def owner_wins(providers: tuple[model.ProviderV2, ...]) -> dict[str, int]:
        acceptors = model.posted_price_acceptors(providers, payment)
        total = sum(provider.measured_capacity_units for provider in acceptors)
        winners = Counter(
            model.select_capacity_ticket(providers, payment, seed).owner_id
            for seed in range(total)
        )
        return dict(sorted(winners.items()))

    return {
        "payment_atoms": payment,
        "split_owner_ticket_counts": model.owner_capacity_ticket_counts(split, payment),
        "merged_owner_ticket_counts": model.owner_capacity_ticket_counts(merged, payment),
        "split_owner_wins_over_full_ticket_cycle": owner_wins(split),
        "merged_owner_wins_over_full_ticket_cycle": owner_wins(merged),
        "fixed_seed_owner_split": model.select_capacity_ticket(
            split,
            payment,
            3,
        ).owner_id,
        "fixed_seed_owner_merged": model.select_capacity_ticket(
            merged,
            payment,
            3,
        ).owner_id,
        "rejection_sampling": {
            "three_unit_max_word_rejected": (
                model.rejection_sample_capacity_ticket(model.MAX_ATOMS, 3) is None
            ),
            "three_unit_zero_word_ticket": model.rejection_sample_capacity_ticket(
                0,
                3,
            ),
        },
    }


def _cartel_evidence() -> dict[str, Any]:
    below = model.stationary_equal_share_cartel(
        model.StationaryEqualShareCartelScenarioV2(3, 1, 2, 3, 0)
    )
    boundary = model.stationary_equal_share_cartel(
        model.StationaryEqualShareCartelScenarioV2(3, 2, 3, 3, 0)
    )
    return {
        "model": "STATIONARY_EQUAL_EXPECTED_SHARE_OR_ENFORCEABLE_TRANSFERS",
        "three_prover_zero_punishment_threshold": _fraction(
            model.stationary_equal_share_cartel_threshold(3)
        ),
        "discount_one_half": {
            "cooperate_pv": _fraction(below.cooperate_present_value),
            "deviate_pv": _fraction(below.deviate_present_value),
            "sustainable": below.sustainable,
        },
        "discount_two_thirds": {
            "cooperate_pv": _fraction(boundary.cooperate_present_value),
            "deviate_pv": _fraction(boundary.deviate_present_value),
            "sustainable": boundary.sustainable,
        },
    }


def _bond_evidence() -> dict[str, Any]:
    loss = model.DefaultLossV2(10, 20, 3, 5)
    bond = model.required_default_bond(
        model.DefaultBondRequestV2(loss, 20, 10, 5, 5_000)
    )
    disposition = model.dispose_prover_fault_bond(bond, loss)
    return {
        "named_restitution_atoms": loss.restitution_atoms,
        "required_bond_atoms": bond,
        "prover_fault_disposition": dataclasses.asdict(disposition),
        "prover_fault_disposition_total_atoms": disposition.total_atoms,
        "verifier_fault_return_atoms": model.verifier_fault_bond_return(bond),
    }


def _fallback_evidence() -> dict[str, Any]:
    scarcity = model.scarcity_or_direct_award(
        sealed_bids=(115, 130),
        posted_price_atoms=120,
        job_cap_atoms=120,
        direct_execution_cost_atoms=119,
    )
    direct = model.scarcity_or_direct_award(
        sealed_bids=(),
        posted_price_atoms=120,
        job_cap_atoms=120,
        direct_execution_cost_atoms=118,
    )
    direct_beats_scarcity = model.scarcity_or_direct_award(
        sealed_bids=(119,),
        posted_price_atoms=120,
        job_cap_atoms=120,
        direct_execution_cost_atoms=100,
    )
    unfunded = model.scarcity_or_direct_award(
        sealed_bids=(),
        posted_price_atoms=120,
        job_cap_atoms=120,
        direct_execution_cost_atoms=121,
    )
    withholding = model.enumerate_single_provider_stage_withholding(5)
    return {
        "scarcity_award": dataclasses.asdict(scarcity),
        "direct_award": dataclasses.asdict(direct),
        "direct_beats_costlier_scarcity": dataclasses.asdict(
            direct_beats_scarcity
        ),
        "unfunded_reject": dataclasses.asdict(unfunded),
        "single_provider_stage_withholding": dataclasses.asdict(withholding),
    }


def _reserve_evidence() -> dict[str, Any]:
    reserve = 30_000_000 * 100_000_000
    initial_state = model.ProofReserveClaimStateV2(
        reserve_remaining_atoms=100,
        owner_epoch_remaining_atoms=80,
        claimed_work_keys=frozenset(),
    )
    request_a = model.ProofReserveClaimRequestV2(
        economic_work_key="WORK_A",
        job_bonus_cap_atoms=60,
        eligibility=(
            model.ProofReserveEligibilityV2
            .INDEPENDENTLY_BASE_FUNDED_VERIFIED_UNCLAIMED_UNRELATED
        ),
    )
    first_claim = model.claim_proof_reserve_bonus(initial_state, request_a)
    if not isinstance(first_claim, model.ProofReserveClaimAcceptedV2):
        raise ValueError("bounded reserve claim evidence did not accept WORK_A")
    duplicate_claim = model.claim_proof_reserve_bonus(
        first_claim.state,
        request_a,
    )
    duplicate_rejection = (
        duplicate_claim.reason.value
        if isinstance(duplicate_claim, model.ProofReserveClaimRejectedV2)
        else None
    )
    return {
        "approved_reserve_zdex_atoms_e8": reserve,
        "funded_verified_unique_bonus_atoms_e8": model.proof_reserve_bonus(
            model.ProofReserveRequestV2(
                reserve,
                1_000 * 100_000_000,
                500 * 100_000_000,
                (
                    model.ProofReserveEligibilityV2
                    .INDEPENDENTLY_BASE_FUNDED_VERIFIED_UNCLAIMED_UNRELATED
                ),
            )
        ),
        "unfunded_base_bonus_atoms_e8": model.proof_reserve_bonus(
            model.ProofReserveRequestV2(
                reserve,
                1_000 * 100_000_000,
                500 * 100_000_000,
                model.ProofReserveEligibilityV2.BASE_PAYMENT_UNFUNDED,
            )
        ),
        "stateful_claim": {
            "initial_reserve_remaining_atoms": initial_state.reserve_remaining_atoms,
            "initial_owner_epoch_remaining_atoms": (
                initial_state.owner_epoch_remaining_atoms
            ),
            "first_bonus_atoms": first_claim.bonus_atoms,
            "reserve_remaining_after_first_atoms": (
                first_claim.state.reserve_remaining_atoms
            ),
            "owner_epoch_remaining_after_first_atoms": (
                first_claim.state.owner_epoch_remaining_atoms
            ),
            "claimed_work_keys_after_first": sorted(
                first_claim.state.claimed_work_keys
            ),
            "duplicate_rejection": duplicate_rejection,
            "duplicate_was_accepted": isinstance(
                duplicate_claim,
                model.ProofReserveClaimAcceptedV2,
            ),
        },
    }


def _bounded_game_evidence() -> dict[str, Any]:
    dominance = model.enumerate_critical_price_dominance(
        bidder_count=3,
        reserve_atoms=5,
    )
    posted_price = model.benchmark_indexed_posted_price(
        model.PostedPriceRequestV2(100, 2_000, 130, 125, 140)
    )
    return {
        "critical_price_dominance": dataclasses.asdict(dominance),
        "first_price_truthfulness_counterexample": (
            model.first_price_truthfulness_counterexample()
        ),
        "critical_price_coalition_counterexample": (
            model.critical_price_coalition_counterexample()
        ),
        "address_count_diversity_counterexample": (
            model.address_count_diversity_counterexample()
        ),
        "posted_price": {
            "computed_atoms": posted_price,
            "after_zero_acceptances_atoms": model.next_posted_price_after_round(
                current_price_atoms=posted_price,
                acceptance_count=0,
            ),
            "after_three_acceptances_atoms": model.next_posted_price_after_round(
                current_price_atoms=posted_price,
                acceptance_count=3,
            ),
            "current_round_acceptance_is_formula_input": False,
        },
        "capacity_ticket_split": _capacity_ticket_evidence(),
        "fallback": _fallback_evidence(),
        "repeated_cartel": _cartel_evidence(),
        "bond": _bond_evidence(),
        "proof_reserve": _reserve_evidence(),
    }


def _decision() -> dict[str, Any]:
    return {
        "normal_lane": "BENCHMARK_POSTED_PRICE_SEALED_ACCEPT_CAPACITY_TICKET",
        "scarcity_lane": "RESEARCH_ONLY_SAME_CAP_LATE_CAPACITY_PAY_AS_BID",
        "terminal_fallback": "FUNDED_DIRECT_EXECUTION",
        "critical_lane": "PAID_DISTINCT_MEASURED_DOMAIN_STANDBY",
        "entry_lane": "FINITE_30M_ZDEX_VERIFIED_USEFUL_WORK_BONUS",
        "reverse_dutch_default": "REJECTED",
        "critical_price_launch": "REJECTED_COALITION_MANIPULATION",
        "selected_for_production": False,
    }


def _game_surface() -> dict[str, Any]:
    return {
        "players": [
            "ZRPF_FEE_FUNDED_BUYER",
            "EXTERNAL_PREFUNDED_BUYER",
            "PROVER",
            "STANDBY_PROVER",
            "VERIFIER",
            "PROOF_RESERVE_CONTROLLER",
            "ZENOLEDGER",
        ],
        "authority": {
            "verifier": "creates an opaque claim-bound validity witness",
            "zenoledger": "sole proposed escrow, payment, slash, and occurrence-payment commit authority",
            "model": "no operational authority",
        },
        "funding": {
            "internal_zrpf": "DEX resource fees plus declared runway",
            "external_jobs": "buyer prefund",
            "bootstrap": "finite 30M ZDEX reserve bonus after funded base payment",
        },
        "identity_keys": {
            "economic_work_key": "exact canonical task encoding over computation, claim, inputs, verifier profile, and release; excludes buyer, deadline, access policy, and nonce",
            "occurrence_key": "economic work key plus buyer, prefund commitment, deadline, access policy, and nonce",
            "base_payment_nullifier": "occurrence_key",
            "reserve_bonus_nullifier": "economic_work_key",
            "semantic_equivalence": "open unless a closed task registry or independently verified equivalence certificate binds encodings",
        },
    }


def _primary_source_manifest() -> dict[str, Any]:
    return _load_json("docs/research/PROOF_MARKET_PRIMARY_SOURCE_MANIFEST_V2.json")


def _promotion_boundary() -> dict[str, Any]:
    return {
        "proved_or_refuted_in_exact_bounded_subject": [
            "V1 payment-floor defect",
            "V1 profitable unilateral clock waiting",
            "V1 calibration/ESSO bond mismatch",
            "fixed-identity critical-price unilateral truthfulness",
            "critical-price coalition counterexample and address-count identity-gate failure",
            "posted-price current-round action independence",
            "capacity-ticket aggregate weight equality over a complete uniform seed cycle",
            "single-provider same-occurrence withholding under a nonincreasing cap, certain normal assignment, and equal lane costs",
            "bounded lifecycle conservation and typed direct fallback",
            "bounded reserve and owner-epoch conservation with one-job work-key claim binding",
        ],
        "tested_in_reference_subject": [
            "immutable reserve claim consumes one exact EconomicWorkKey once",
        ],
        "requires_live_evidence": [
            "cost and latency distributions",
            "failure correlation",
            "capacity attestation and non-overcommitment",
            "beneficial ownership, related-party, and failure-domain evidence",
            "unpredictable unbiased randomness and frozen acceptor-root timing",
            "permissionless-floor, owner-cap, and failure-domain assignment policy",
            "entry, exit, concentration, boycott, and repeated-cartel behavior",
            "fee sufficiency and direct-execution runway",
            "semantic-equivalence admission for reserve-bonus deduplication",
            "mounted reserve-aware terminal settlement and atomic reserve/payment composition",
        ],
        "selected": False,
        "implemented": False,
        "mounted": False,
        "production_ready": False,
    }


def _theoremsearch_evidence() -> dict[str, Any]:
    return {
        "role": "RETRIEVAL_ONLY",
        "queries": [
            "single parameter procurement auction dominant strategy truthful critical payment private costs",
            "procurement auction collusion false name bids group strategyproof impossibility counterexample",
        ],
        "unpreserved_raw_output_sha256": {
            "truthfulness": "e6be65954d84ca557db7f434d159682a1d5f5931d344277f9f7a3e2d3de1fac2",
            "breakers": "5ab47ca82fe52cec0ebc320696ed5466d6b8457bbd8f0f3729ea6a53127232a9",
        },
        "raw_artifacts_preserved": False,
        "raw_hash_status": "ORPHAN_UNVERIFIABLE_HASHES",
        "hit_classification": {
            "truthfulness": "ADJACENT_AND_LOW_SIGNAL",
            "breakers": "ADJACENT_KARACA_SUPERMODULARITY_RESULT_NOT_TRANSFERRED",
        },
        "promoted_claims": [],
    }


def build_document(
    *,
    source_pins: list[dict[str, str]],
    checker_sha256: str,
) -> dict[str, Any]:
    v1_attacks = v1_attack_evidence()
    games = _bounded_game_evidence()
    formal_evidence = formal.build_formal_evidence()
    source_manifest = _primary_source_manifest()
    checks = evaluate_checks(v1_attacks, games, formal_evidence, source_manifest)
    return {
        "schema": SCHEMA,
        "status": "RESEARCH_ONLY_REFUTATION_BACKED_V2",
        "source_subject": {
            "reviewed_source_commit": REVIEWED_SOURCE_COMMIT,
            "source_pins": source_pins,
            "checker_bootstrap": {
                "path": "tools/check_proof_market_game_theory_v2.py",
                "sha256": checker_sha256,
                "externally_authenticated": False,
                "note": "an in-process checker cannot authenticate its own executed bytes",
            },
        },
        "decision": _decision(),
        "game_surface": _game_surface(),
        "attack_query": v1_attacks,
        "bounded_model": games,
        "formal_evidence": formal_evidence,
        "theoremsearch": _theoremsearch_evidence(),
        "primary_source_review": source_manifest,
        "checks": checks,
        "ok": all(checks.values()),
        "promotion_boundary": _promotion_boundary(),
        "nonclaims": [
            "No finite model proves that a live permissionless proof market will have adequate honest supply or competitive prices.",
            "The current leading experiment is not generally coalition-proof, false-name-proof, or equilibrium-efficient.",
            "Capacity tickets do not authenticate capacity, ownership, randomness, or independent failure domains.",
            "EconomicWorkKey deduplicates exact canonical encodings; semantic equivalence remains open.",
            "The bounded Python/ESSO reserve transition is not a mounted ZenoLedger transition and does not prove canonical key encoding or multi-job semantic-equivalence deduplication.",
            "External source pages were not content-snapshotted and remain advisory mutable evidence.",
            "Lean and ESSO replay receipts are source-pinned but are not externally signed or remotely attested.",
            "Direct execution availability, fee funding, cryptographic soundness, and ZenoLedger finality remain premises.",
            "This artifact grants no market, payment, proof, token, settlement, release, or production authority.",
        ],
    }

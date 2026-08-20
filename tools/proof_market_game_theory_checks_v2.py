"""Fail-closed predicates for the research-only proof-market packet V2."""

from __future__ import annotations

from typing import Any

EMPTY_SHA256 = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
ESSO_COMMIT = "7f80c6216be85c827e8d1cc2fa08ee3107a74588"
EXPECTED_RESERVE_WORK_KEY_V2 = (
    "ewk:v2:e87be2b5ecd2f1649f3f0da84726fdaca6e627c9e00004cce7ef5123c4ef0b48"
)

EXPECTED_LEAN_THEOREMS = [
    "truthful_weakly_dominates_threshold",
    "truthful_threshold_winner_nonnegative",
    "first_price_truthfulness_counterexample",
    "critical_price_coalition_counterexample",
    "capacity_ticket_split_preserves_owner_weight",
    "scarcity_payment_has_no_same_occurrence_uplift",
    "three_prover_stationary_equal_share_boundary",
    "full_default_bond_disposition_conserves",
]

EXPECTED_LEAN_TOOLCHAIN = {
    "lean": "4.27.0",
    "lean_commit": "db93fe1608548721853390a10cd40580fe7d22ae",
    "mathlib_commit": "a3a10db0e9d66acbebf76c5e6a135066525ac900",
}

EXPECTED_SOURCE_RECORDS = {
    "BOUNDLESS_AUCTION_CURRENT": (
        "https://docs.boundless.network/developers/tutorials/auction",
        "OFFICIAL_DOCUMENTATION_DESCRIPTION",
    ),
    "BOUNDLESS_LIFECYCLE_CURRENT": (
        "https://docs.boundless.network/developers/proof-lifecycle",
        "OFFICIAL_DOCUMENTATION_DESCRIPTION",
    ),
    "BOUNDLESS_PROVER_RELEASE_2_0": (
        "https://github.com/boundless-xyz/boundless/releases/tag/v2.0.0",
        "OFFICIAL_VERSIONED_RELEASE_NOTE",
    ),
    "PROO_PHI_V5": (
        "https://arxiv.org/html/2404.06495v5",
        "VERSIONED_RESEARCH_PAPER",
    ),
    "SUCCINCT_ARCHITECTURE_CURRENT": (
        "https://docs.succinct.xyz/docs/protocol/spn/architecture",
        "OFFICIAL_DOCUMENTATION_DESCRIPTION",
    ),
    "SUCCINCT_AUCTION_CURRENT": (
        "https://docs.succinct.xyz/docs/protocol/spn/auction",
        "OFFICIAL_DOCUMENTATION_DESCRIPTION",
    ),
    "SUCCINCT_LIFECYCLE_CURRENT": (
        "https://docs.succinct.xyz/docs/protocol/spn/lifecycle",
        "OFFICIAL_DOCUMENTATION_DESCRIPTION",
    ),
    "GEVULOT_FIRESTARTER_CURRENT": (
        "https://docs.gevulot.com/gevulot-docs/firestarter/overview",
        "OFFICIAL_DOCS_DESCRIBE_PERMISSIONED_SERVICE",
    ),
    "GEVULOT_ZKCLOUD_DESIGN": (
        "https://docs.gevulot.com/gevulot-docs/zkcloud-design/execution-guarantees",
        "OFFICIAL_DESIGN_DOCUMENTATION_NO_DEPLOYMENT_EVIDENCE",
    ),
    "BREVIS_AUCTION_CURRENT": (
        "https://provernet-docs.brevis.network/provernet-architecture/the-proof-marketplace/request-auction.html",
        "OFFICIAL_DOCUMENTATION_DESCRIPTION",
    ),
    "BREVIS_STAKING_CURRENT": (
        "https://provernet-docs.brevis.network/user-tutorial/staking-in-provernet.html",
        "OFFICIAL_SOURCE_STATUS_CONFLICT",
    ),
    "BREVIS_MAINNET_ANNOUNCEMENT": (
        "https://blog.brevis.network/2026/01/06/brevis-provernet-mainnet-and-brev-are-live/",
        "OFFICIAL_SOURCE_STATUS_CONFLICT",
    ),
    "KARACA_COALITION_PROOF_VCG": (
        "https://arxiv.org/abs/1711.06774v5",
        "ADJACENT_VERSIONED_PAPER_NOT_TRANSFERRED",
    ),
}

EXPECTED_SOURCE_OBSERVATIONS = {
    "BOUNDLESS_AUCTION_CURRENT": (
        "The documentation describes a rising requester price, first-prover "
        "lock, and a default disposition split between burn and a "
        "secondary-prover bounty."
    ),
    "BOUNDLESS_LIFECYCLE_CURRENT": (
        "The documentation describes requester prefunding, prover collateral, "
        "and payment after proof verification."
    ),
    "BOUNDLESS_PROVER_RELEASE_2_0": (
        "The release note reports removal of an approximately 30% cluster "
        "database penalty, approximately 99.6% predecessor lock fulfillment, "
        "and 25 ZKC slashed after two predecessor failures."
    ),
    "PROO_PHI_V5": (
        "Its homogeneous single-round core proves user-value DSIC, prover "
        "unit-cost DSIC, and budget balance under its assumptions; capacity "
        "reports, Sybils, repeated play, and all-prover monopoly remain outside "
        "that theorem."
    ),
    "SUCCINCT_ARCHITECTURE_CURRENT": (
        "The architecture page describes an off-chain auctioneer and ephemeral "
        "proof-request data."
    ),
    "SUCCINCT_AUCTION_CURRENT": (
        "The auction page describes reverse-auction selection and retry behavior."
    ),
    "SUCCINCT_LIFECYCLE_CURRENT": (
        "The lifecycle page permits multi-factor prover scoring, including "
        "price, stake, performance history, and other factors."
    ),
    "GEVULOT_FIRESTARTER_CURRENT": (
        "The official documentation describes Firestarter as a permissioned "
        "implementation of the broader ZkCloud design."
    ),
    "GEVULOT_ZKCLOUD_DESIGN": (
        "The design proposes qualified VRF assignment and configurable "
        "redundancy; the page does not establish deployed Firestarter behavior."
    ),
    "BREVIS_AUCTION_CURRENT": (
        "The request-auction page describes commit-reveal reverse procurement."
    ),
    "BREVIS_STAKING_CURRENT": (
        "The staking page says slashing is disabled, which conflicts with the "
        "mainnet announcement's statement that slashing rates are enforced."
    ),
    "BREVIS_MAINNET_ANNOUNCEMENT": (
        "The announcement says slashing rates are enforced, which conflicts "
        "with the staking page's statement that slashing is disabled."
    ),
    "KARACA_COALITION_PROOF_VCG": (
        "Coalition-resistance results require specialized supermodularity and "
        "market assumptions that have not been established for discrete "
        "ZenoProof jobs."
    ),
}


def _fallback_checks(fallback: dict[str, Any]) -> dict[str, bool]:
    direct_beats = fallback["direct_beats_costlier_scarcity"]
    withholding = fallback["single_provider_stage_withholding"]
    return {
        "FALLBACK_IS_SAME_CAP_AND_DIRECT_COST_AWARE": (
            fallback["scarcity_award"]["kind"] == "SCARCITY_PROVER"
            and fallback["scarcity_award"]["payment_atoms"] == 115
            and fallback["direct_award"]["kind"] == "DIRECT_EXECUTION"
            and direct_beats["kind"] == "DIRECT_EXECUTION"
            and direct_beats["payment_atoms"] == 100
            and fallback["unfunded_reject"]["kind"] == "UNFUNDED_REJECT"
        ),
        "SINGLE_PROVIDER_STAGE_WITHHOLDING_HAS_NO_STRICT_GAIN": (
            withholding["profitable_deviation"] is None
            and withholding["deviation_queries"] > 0
        ),
    }


def _formal_checks(formal: dict[str, Any]) -> dict[str, bool]:
    esso = formal["esso"]
    lean = formal["lean"]
    return {
        "ESSO_DUAL_SOLVER_VERIFIED": (
            esso["status"] == "VERIFIED_BOUNDED_DUAL_SOLVER"
            and esso["result"]["passed_queries"] == 14
            and esso["result"]["failed_queries"] == 0
            and esso["model_pin_matches"]
            and esso["verification_report_pin_matches"]
            and esso["raw_bundle_result_pin_matches"]
            and esso["preserved_report_replays_verified"]
            and esso["fault_race_mutant_pins_match"]
            and esso["fault_race_mutant_replays_sat"]
            and esso["toolchain"]["esso_commit"] == ESSO_COMMIT
            and esso["toolchain"]["z3"] == "4.15.4"
            and esso["toolchain"]["cvc5"] == "1.1.2"
            and esso["counterexample_ids"]
            == [
                "DIRECT_COMMIT_WITHOUT_DIRECT_LANE_BINDING",
                "PROVER_FAULT_SLASH_WITHOUT_VERIFIER_WITNESS",
                "PROVER_FAULT_WITNESS_VERIFICATION_RACE",
            ]
            and esso["counterexample_retention"]
            == {
                "DIRECT_COMMIT_WITHOUT_DIRECT_LANE_BINDING": (
                    "HASH_ONLY_MUTANT_SOURCE_AND_REPORT_NOT_PRESERVED"
                ),
                "PROVER_FAULT_SLASH_WITHOUT_VERIFIER_WITNESS": (
                    "HASH_ONLY_MUTANT_SOURCE_AND_REPORT_NOT_PRESERVED"
                ),
                "PROVER_FAULT_WITNESS_VERIFICATION_RACE": (
                    "SOURCE_REPORT_AND_BUNDLE_PRESERVED"
                ),
            }
        ),
        "LEAN_RESTRICTED_THEOREMS_COMPILED": (
            lean["status"] == "COMPILED_RESTRICTED_THEOREMS"
            and lean["exit_code"] == 0
            and lean["placeholder_hits"] == 0
            and lean["compiled_theorems"] == EXPECTED_LEAN_THEOREMS
            and lean["source_pin_matches"]
            and lean["root_import_pin_matches"]
            and lean["stdout_sha256"] == EMPTY_SHA256
            and lean["stderr_sha256"] == EMPTY_SHA256
            and lean["toolchain"] == EXPECTED_LEAN_TOOLCHAIN
        ),
    }


def _source_manifest_check(source_manifest: dict[str, Any]) -> bool:
    rows = source_manifest.get("sources")
    if not isinstance(rows, list):
        return False
    actual: dict[str, tuple[str, str]] = {}
    actual_observations: dict[str, str] = {}
    for row in rows:
        if not isinstance(row, dict):
            return False
        source_id = row.get("id")
        url = row.get("url")
        status = row.get("deployment_status")
        if not all(
            isinstance(value, str) and value
            for value in (
                source_id,
                url,
                status,
                row.get("publication_or_version"),
                row.get("exact_observation"),
                row.get("use_in_packet"),
            )
        ):
            return False
        if source_id in actual:
            return False
        actual[source_id] = (url, status)
        actual_observations[source_id] = row["exact_observation"]
    return bool(
        source_manifest.get("schema")
        == "zenodex/proof-market-primary-source-manifest/v2"
        and source_manifest.get("status")
        == "ADVISORY_OFFICIAL_SOURCE_SUMMARIES_AS_OF_ACCESS_DATE"
        and source_manifest.get("accessed_at") == "2026-08-18"
        and source_manifest.get("externally_authenticated") is False
        and source_manifest.get("content_snapshots_preserved") is False
        and actual == EXPECTED_SOURCE_RECORDS
        and actual_observations == EXPECTED_SOURCE_OBSERVATIONS
    )


def _v1_checks(v1_attacks: dict[str, Any]) -> dict[str, bool]:
    return {
        "V1_PAYMENT_FLOOR_DEFECT_REPRODUCED": (
            len(v1_attacks["floor_defects"]) == 2
        ),
        "V1_UNILATERAL_WAIT_PROFIT_REPRODUCED": all(
            row["success_adjusted_expected_gain_atoms"] > 0
            for row in v1_attacks["waiting_witnesses"]
        ),
        "V1_BOND_DISPOSITION_MISMATCH_REPRODUCED": (
            v1_attacks["v1_esso_half_restitution_atoms"]
            < v1_attacks["micro_required_bond_atoms"]
        ),
    }


def _auction_checks(games: dict[str, Any]) -> dict[str, bool]:
    dominance = games["critical_price_dominance"]
    address_count = games["address_count_diversity_counterexample"]
    posted = games["posted_price"]
    return {
        "CRITICAL_PRICE_BOUNDED_UNILATERAL_DOMINANCE": (
            dominance["profitable_deviation"] is None
            and dominance["truthful_ir_violation"] is None
        ),
        "FIRST_PRICE_TRUTHFULNESS_REFUTED": (
            games["first_price_truthfulness_counterexample"][
                "profitable_gain_atoms"
            ]
            > 0
        ),
        "CRITICAL_PRICE_COALITION_RESISTANCE_REFUTED": (
            games["critical_price_coalition_counterexample"][
                "profitable_gain_atoms"
            ]
            > 0
        ),
        "ADDRESS_COUNT_COMPETITION_REFUTED": (
            address_count["address_gate_passes"]
            and not address_count["distinct_owner_gate_passes"]
            and address_count["false_name_utility_gain_atoms"] == 0
        ),
        "POSTED_PRICE_HAS_NO_SAME_ROUND_RATCHET": len(
            {
                posted["computed_atoms"],
                posted["after_zero_acceptances_atoms"],
                posted["after_three_acceptances_atoms"],
            }
        )
        == 1,
    }


def _capacity_and_bond_checks(games: dict[str, Any]) -> dict[str, bool]:
    capacity = games["capacity_ticket_split"]
    bond = games["bond"]
    return {
        "CAPACITY_TICKET_SPLIT_INVARIANT_IN_DECLARED_EXAMPLE": (
            capacity["split_owner_ticket_counts"]
            == capacity["merged_owner_ticket_counts"]
            and capacity["split_owner_wins_over_full_ticket_cycle"]
            == capacity["merged_owner_wins_over_full_ticket_cycle"]
        ),
        "CAPACITY_TICKET_FIXED_SEED_SPLIT_INVARIANCE_REFUTED": (
            capacity["fixed_seed_owner_split"]
            != capacity["fixed_seed_owner_merged"]
        ),
        "CAPACITY_TICKET_REJECTION_SAMPLING_EXAMPLE": (
            capacity["rejection_sampling"]["three_unit_max_word_rejected"]
            and capacity["rejection_sampling"]["three_unit_zero_word_ticket"] == 0
        ),
        "FULL_PROVER_FAULT_BOND_DISPOSITION_CONSERVES": (
            bond["required_bond_atoms"]
            == bond["prover_fault_disposition_total_atoms"]
        ),
    }


def _reserve_checks(reserve: dict[str, Any]) -> dict[str, bool]:
    encoding = reserve["economic_work_key_encoding"]
    stateful = reserve["stateful_claim"]
    return {
        "PROOF_RESERVE_ECONOMIC_WORK_KEY_CANONICAL": (
            encoding["key"] == EXPECTED_RESERVE_WORK_KEY_V2
            and stateful["economic_work_key"] == EXPECTED_RESERVE_WORK_KEY_V2
            and encoding["changed_field_changes_key"] is True
        ),
        "PROOF_RESERVE_STATEFUL_CLAIM_CONSUMES_ONCE": (
            stateful["first_bonus_atoms"] > 0
            and stateful["reserve_remaining_after_first_atoms"]
            == stateful["initial_reserve_remaining_atoms"]
            - stateful["first_bonus_atoms"]
            and stateful["owner_epoch_remaining_after_first_atoms"]
            == stateful["initial_owner_epoch_remaining_atoms"]
            - stateful["first_bonus_atoms"]
            and stateful["claimed_work_keys_after_first"]
            == [EXPECTED_RESERVE_WORK_KEY_V2]
            and stateful["duplicate_rejection"] == "WORK_KEY_ALREADY_CLAIMED"
            and stateful["duplicate_was_accepted"] is False
        )
    }


def _key_parity_checks(key_parity: dict[str, Any]) -> dict[str, bool]:
    rust = key_parity.get("rust")
    receipt_checks = key_parity.get("receipt_checks")
    return {
        "PROOF_RESERVE_PYTHON_RUST_KEY_PARITY_GOLDEN_VECTOR": (
            key_parity.get("status") == "BOUNDED_CROSS_LANGUAGE_GOLDEN_VECTOR"
            and key_parity.get("ok") is True
            and isinstance(key_parity.get("python"), dict)
            and key_parity["python"].get("ok") is True
            and isinstance(receipt_checks, dict)
            and all(receipt_checks.values())
            and isinstance(rust, dict)
            and rust.get("status") == "PASSED"
            and rust.get("passed_tests") == 2
            and rust.get("failed_tests") == 0
        )
    }


def evaluate_checks(
    v1_attacks: dict[str, Any],
    games: dict[str, Any],
    formal: dict[str, Any],
    source_manifest: dict[str, Any],
    key_parity: dict[str, Any],
) -> dict[str, bool]:
    """Evaluate every named packet claim against exact generated evidence."""

    checks = _v1_checks(v1_attacks)
    checks.update(_auction_checks(games))
    checks.update(_capacity_and_bond_checks(games))
    checks.update(_fallback_checks(games["fallback"]))
    checks.update(_reserve_checks(games["proof_reserve"]))
    checks.update(_key_parity_checks(key_parity))
    checks.update(_formal_checks(formal))
    checks["PRIMARY_SOURCE_MANIFEST_IS_EXPLICITLY_ADVISORY"] = (
        _source_manifest_check(source_manifest)
    )
    return checks

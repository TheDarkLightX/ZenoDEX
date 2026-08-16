#!/usr/bin/env python3
"""Generate and check the research-only G1 service-procurement packet."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from collections.abc import Mapping
from functools import lru_cache
from itertools import permutations
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = (
    REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_CRITICAL_SERVICE_PROCUREMENT_V1.json"
)
SCHEMA = "zenodex/production-readiness-g1-critical-service-procurement/v1"
RESEARCH_SOURCE_SUBJECT = "0a385c782506bace99f890b5271200c0b3d68ab1"
CONTRACT_PATH = "tools/production_readiness_g1_critical_service_procurement_contract_v1.py"
CHECKER_PATH = "tools/check_production_readiness_g1_critical_service_procurement_v1.py"

sys.path.insert(0, str(REPO_ROOT))

from tools import (  # noqa: E402
    production_readiness_g1_critical_service_procurement_contract_v1 as contract,
)

EXPECTED_ROLE_IDS = frozenset(
    {
        "validator_finality_operator",
        "oracle_reporter_aggregator_disputer_and_watcher",
        "liquidator_and_keeper",
        "tau_relayer_and_destination_operator",
        "proof_prover_and_proof_miner",
    }
)


def _encoded(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _git_bytes(repo_root: Path, *args: str) -> bytes:
    return subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=True,
        capture_output=True,
    ).stdout


def _source_pins(repo_root: Path) -> list[dict[str, str]]:
    pins: list[dict[str, str]] = []
    for path in contract.RESEARCH_SOURCE_PATHS:
        frozen = _git_bytes(repo_root, "show", f"{RESEARCH_SOURCE_SUBJECT}:{path}")
        if (repo_root / path).read_bytes() != frozen:
            raise ValueError(f"critical-service procurement source drift: {path}")
        pins.append(
            {
                "path": path,
                "sha256": _sha256(frozen),
                "subject": RESEARCH_SOURCE_SUBJECT,
            }
        )
    return pins


def _validate_source_markers(repo_root: Path) -> None:
    markers = {
        "docs/research/PRODUCTION_READINESS_G1_CRITICAL_SERVICE_COSTS_V1.json": (
            '"proof_unit_price_atoms": null',
            '"qualified_benchmarks_complete": false',
            '"full_cost_quotes_complete": false',
        ),
        "docs/research/PRODUCTION_READINESS_G1_SERVICE_FUNDING_V1.json": (
            '"activation_allowed": false',
            '"future_revenue_rule": "Forecast revenue may support sensitivity analysis.',
            "the next period activates only with its complete cap prefunded",
        ),
        "tools/production_readiness_g1_critical_service_cost_contract_v1.py": (
            "FULL_ROLE_COST_CANDIDATE",
            "selection_eligible=complete and loaded_high > 0",
        ),
    }
    for path, required in markers.items():
        source = (repo_root / path).read_text(encoding="utf-8")
        missing = [marker for marker in required if marker not in source]
        if missing:
            raise ValueError(f"critical-service procurement marker drift: {path}: {missing}")


def _validate_contract() -> None:
    if contract.CRITICAL_SERVICE_ROLE_IDS != EXPECTED_ROLE_IDS:
        raise ValueError("critical service role registry differs from checker")
    registries = (
        (
            contract.SELECTED_PROCUREMENT_POLICIES,
            "procurement policies must remain unselected",
        ),
        (
            contract.SELECTED_QUALIFICATION_POLICIES,
            "qualification policies must remain unselected",
        ),
        (
            contract.SELECTED_COMPLETE_QUOTES,
            "complete quotes must remain unselected",
        ),
    )
    for registry, error in registries:
        if set(registry) != EXPECTED_ROLE_IDS or any(
            value is not None for value in registry.values()
        ):
            raise ValueError(error)
    if (
        contract.ACTIVATION_AUTHORIZED
        or contract.WORK_ADMISSION_AUTHORIZED
        or contract.PAYMENT_AUTHORIZED
    ):
        raise ValueError("research procurement contract gained runtime authority")
    if contract.MAX_RESEARCH_CANDIDATES != 16:
        raise ValueError("finite procurement candidate bound drifted")


def _fixture_bid(
    quote_id: str,
    *,
    period_cap_atoms: int,
    owner_id: str,
    cloud: str,
) -> contract.QualifiedServiceBidV1:
    return contract.QualifiedServiceBidV1(
        quote_id=quote_id,
        role_id="validator_finality_operator",
        provider_id=f"provider-{quote_id}",
        beneficial_owner_id=owner_id,
        payment_asset_id="USD_E6",
        valid_from_epoch=10,
        valid_through_epoch=20,
        service_spec_root="1" * 64,
        benchmark_profile_root="2" * 64,
        execution_subject_root="3" * 64,
        hardware_profile_root="4" * 64,
        failure_domains=(
            contract.FailureDomainV1("cloud_provider", cloud),
            contract.FailureDomainV1("jurisdiction", f"jurisdiction-{quote_id}"),
        ),
        quoted_period_cap_atoms=period_cap_atoms,
        one_time_onboarding_atoms=0,
        target_prefund_periods=18,
        target_prefund_atoms=18 * period_cap_atoms,
        bond_atoms=100,
        slash_atoms=100,
        quote_commitment_root="5" * 64,
        qualification_evidence_root="6" * 64,
    )


def _fixture_policy() -> contract.ProcurementPolicyV1:
    return contract.ProcurementPolicyV1(
        role_id="validator_finality_operator",
        payment_asset_id="USD_E6",
        selection_epoch=15,
        service_spec_root="1" * 64,
        benchmark_profile_root="2" * 64,
        execution_subject_root="3" * 64,
        hardware_profile_root="4" * 64,
        required_winners=2,
        period_budget_cap_atoms=1_000,
        onboarding_budget_cap_atoms=0,
        maximum_per_beneficial_owner=1,
        failure_domain_caps=(
            contract.FailureDomainCapV1("cloud_provider", 1),
            contract.FailureDomainCapV1("jurisdiction", 1),
        ),
        maximum_candidate_count=16,
    )


@lru_cache(maxsize=1)
def bounded_procurement_evidence() -> dict[str, Any]:
    bond_counterexample: dict[str, int] | None = None
    bond_cases = 0
    for defect_gain in range(9):
        for slash in range(9):
            for future_value_lost in range(9):
                for probability_bps in (0, 2_500, 5_000, 7_500, 10_000):
                    expected = (
                        probability_bps * slash + contract.BPS_SCALE * future_value_lost
                        >= contract.BPS_SCALE * defect_gain
                    )
                    bond_outcome = contract.assess_bond_adequacy_v1(
                        contract.BondTermsV1(
                            quote_id="bounded-quote",
                            payment_asset_id="USD_E6",
                            bond_atoms=slash,
                            slash_atoms=slash,
                            maximum_defect_gain_atoms=defect_gain,
                            future_value_lost_atoms=future_value_lost,
                            detection_probability_bps=probability_bps,
                        ),
                        expected_quote_id="bounded-quote",
                        expected_asset_id="USD_E6",
                    )
                    observed = isinstance(
                        bond_outcome,
                        contract.BondAdequacyAssessmentV1,
                    )
                    bond_cases += 1
                    if expected != observed:
                        bond_counterexample = {
                            "defect_gain_atoms": defect_gain,
                            "slash_atoms": slash,
                            "future_value_lost_atoms": future_value_lost,
                            "detection_probability_bps": probability_bps,
                        }
                        break

    bids = (
        _fixture_bid(
            "a",
            period_cap_atoms=100,
            owner_id="owner-x",
            cloud="cloud-1",
        ),
        _fixture_bid(
            "b",
            period_cap_atoms=101,
            owner_id="owner-y",
            cloud="cloud-1",
        ),
        _fixture_bid(
            "c",
            period_cap_atoms=102,
            owner_id="owner-x",
            cloud="cloud-2",
        ),
    )
    selector_counterexample: dict[str, object] | None = None
    selector_cases = 0
    for order in permutations(bids):
        selection_outcome = contract.select_service_bids_v1(
            order,
            _fixture_policy(),
        )
        selector_cases += 1
        if (
            not isinstance(selection_outcome, contract.ProcurementSelectionV1)
            or selection_outcome.selected_quote_ids != ("b", "c")
            or selection_outcome.total_period_cap_atoms != 203
        ):
            selector_counterexample = {
                "input_order": [bid.quote_id for bid in order],
                "observed": (
                    list(selection_outcome.selected_quote_ids)
                    if isinstance(
                        selection_outcome,
                        contract.ProcurementSelectionV1,
                    )
                    else selection_outcome.code.value
                ),
            }
            break

    return {
        "bond_boundary_search": {
            "domain": (
                "defect gain, slash, future value lost=0..8 atoms; "
                "detection probability in {0,2500,5000,7500,10000} bps"
            ),
            "cases": bond_cases,
            "counterexample": bond_counterexample,
            "predicate": ("p_bps*slash + 10000*future_value_lost >= 10000*maximum_defect_gain"),
        },
        "selector_permutation_search": {
            "domain": "all 6 permutations of the three-bid greedy-trap fixture",
            "cases": selector_cases,
            "counterexample": selector_counterexample,
            "expected_selection": ["b", "c"],
            "predicate": ("canonical exhaustive selection is invariant to candidate order"),
        },
        "named_mutant_witnesses": [
            {
                "id": "GREEDY_CHEAPEST_FIRST",
                "witness": ("A is cheapest but blocks B by cloud and C by owner; B+C is feasible"),
            },
            {
                "id": "LOW_CASE_PRICE_SELECTION",
                "witness": "selection objective uses the loaded high-case quote cap",
            },
            {
                "id": "COMMON_OWNER_SYBIL",
                "witness": "provider IDs differ while beneficial owner ID is equal",
            },
            {
                "id": "COMMON_FAILURE_DOMAIN",
                "witness": "providers share one capped cloud or jurisdiction value",
            },
            {
                "id": "BENCHMARK_PROFILE_SUBSTITUTION",
                "witness": "observation root tuple differs from quote and policy",
            },
            {
                "id": "QUOTE_REPLAY_AFTER_EXPIRY",
                "witness": "selection epoch exceeds valid_through_epoch",
            },
            {
                "id": "UNBONDED_SLASH",
                "witness": "slash atoms exceed bond atoms",
            },
            {
                "id": "PROOF_MARKET_CREATES_REWARD",
                "witness": "selection output cannot admit work or authorize payment",
            },
        ],
        "claim_ceiling": (
            "Exact only for the declared finite integer and three-candidate domains; "
            "this is not unbounded optimality or a production procurement receipt."
        ),
    }


def _role_qualification_packets() -> dict[str, dict[str, object]]:
    common = [
        "zero invalid-work accepts",
        "zero replay-or-duplicate accepts",
        "zero role-specific safety events",
        "zero recovery failures",
        "minimum successful trials and maximum failed trials",
        "bounded p95 latency, availability, and peak memory",
        "exact service, execution, hardware, and benchmark-profile roots",
    ]
    specific = {
        "validator_finality_operator": [
            "zero invalid-transition signs and double-sign events",
            "persistent last-sign-state recovery",
            "end-to-end finality and availability, independent of vendor SLA",
            "beneficial-owner, key-custody, geography, and failure-domain evidence",
        ],
        "oracle_reporter_aggregator_disputer_and_watcher": [
            "zero invalid or stale accepted reports",
            "occurrence-to-finality, freshness, and outage-recovery observations",
            "reporter owner, data-source, aggregator, and watcher diversity",
        ],
        "liquidator_and_keeper": [
            "zero bad-debt-worsening accepted actions",
            "eligible-action latency and deterministic failed-attempt treatment",
            "capital, external execution, and minimal-liquidation measurements",
        ],
        "tau_relayer_and_destination_operator": [
            "zero duplicate external-effect accepts",
            "authenticated acknowledgment, retry, idempotency, outage, and rejoin",
            "destination and relayer beneficial-owner and failure-domain diversity",
        ],
        "proof_prover_and_proof_miner": [
            "zero invalid-receipt accepts",
            "exact guest image, journal, verifier profile, cycles, latency, and memory",
            "failed-proof and deadline behavior with direct-execution fallback",
        ],
    }
    return {
        role_id: {
            "common_required_observations": common,
            "role_specific_required_observations": specific[role_id],
            "selected_qualification_policy": (contract.SELECTED_QUALIFICATION_POLICIES[role_id]),
            "selected_complete_quote": contract.SELECTED_COMPLETE_QUOTES[role_id],
            "selected_procurement_policy": (contract.SELECTED_PROCUREMENT_POLICIES[role_id]),
            "status": "OPEN_UNSELECTED",
        }
        for role_id in sorted(EXPECTED_ROLE_IDS)
    }


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    _validate_contract()
    _validate_source_markers(repo_root)
    return {
        "schema": SCHEMA,
        "status": "RESEARCH_ONLY_UNSELECTED",
        "production_promotion": False,
        "reviewed_subject": RESEARCH_SOURCE_SUBJECT,
        "research_source_pins": _source_pins(repo_root),
        "implementation_source_pins": [
            {
                "path": CONTRACT_PATH,
                "sha256": _sha256((repo_root / CONTRACT_PATH).read_bytes()),
            },
            {
                "path": CHECKER_PATH,
                "sha256": _sha256((repo_root / CHECKER_PATH).read_bytes()),
            },
        ],
        "external_qualification_context": [
            {
                "source": "CometBFT validator signing specification",
                "url": "https://docs.cometbft.com/v0.38/spec/consensus/signing",
                "checked_on": "2026-08-16",
                "observation": (
                    "A signer tracks its last signed height, round, and type to prevent "
                    "double signing; conflicting votes are evidence."
                ),
                "selection_effect": "NONE",
            },
            {
                "source": "CometBFT configuration reference",
                "url": "https://docs.cometbft.com/main/references/config/",
                "checked_on": "2026-08-16",
                "observation": (
                    "Validator key and last-sign-state custody are operator concerns; "
                    "the default filesystem key path is not a qualified ZenoDEX profile."
                ),
                "selection_effect": "NONE",
            },
            {
                "source": "DigitalOcean CPU Droplet SLA",
                "url": "https://www.digitalocean.com/sla/cpu-droplets",
                "checked_on": "2026-08-16",
                "observation": (
                    "The vendor publishes a per-Droplet monthly uptime SLA with exclusions; "
                    "it does not establish end-to-end validator service qualification."
                ),
                "selection_effect": "NONE",
            },
            {
                "source": "RISC Zero datasheet",
                "url": "https://dev.risczero.com/datasheet.pdf",
                "checked_on": "2026-08-16",
                "observation": (
                    "The published results are version- and hardware-specific and describe "
                    "cycle rounding; current ZRPF pricing needs an exact current replay."
                ),
                "selection_effect": "NONE",
            },
            {
                "source": "RISC Zero developer documentation",
                "url": "https://dev.risczero.com/",
                "checked_on": "2026-08-16",
                "observation": (
                    "A receipt verifies execution of a specific program, so prover "
                    "qualification must bind the exact image and journal profile."
                ),
                "selection_effect": "NONE",
            },
        ],
        "game_surface": {
            "players": sorted(EXPECTED_ROLE_IDS)
            + [
                "protocol treasury and procurement operator",
                "beneficial owners and affiliated bidders",
                "cloud, data, hardware, and destination vendors",
                "qualification and work verifiers",
                "governance, legal, and release operators",
            ],
            "actions": [
                "submit, withdraw, expire, replay, or understate a quote",
                "qualify or substitute a service, binary, image, hardware, or benchmark",
                "split identities, conceal common ownership, or share a failure domain",
                "bond, slash, select, onboard, admit work, invoice, or replace",
            ],
            "information_sets": [
                "private reservation cost, affiliation, and defect gain",
                "public quote caps, evidence roots, qualification results, and budgets",
                "external future revenue and correlated infrastructure failures",
            ],
            "payoff": (
                "verified capped payment minus complete operating, capital, failure, "
                "onboarding, and expected slash costs"
            ),
        },
        "attack_query": {
            "query": (
                "Can an unqualified, underpriced, affiliated, correlated, stale, or "
                "underbonded bidder win or cause an unfunded payment?"
            ),
            "disaster_states": [
                "LOWBALL_THEN_DEFAULT",
                "SHILL_OR_COMMON_OWNER_MULTIWIN",
                "CORRELATED_FAILURE_DOMAIN_MULTIWIN",
                "BENCHMARK_OR_IMAGE_SUBSTITUTION",
                "EXPIRED_QUOTE_REPLAY",
                "GREEDY_SELECTOR_MISSES_FEASIBLE_PORTFOLIO",
                "UNBONDED_OR_INADEQUATE_SLASH",
                "FUTURE_REVENUE_OR_MARKET_CREATES_PAYMENT",
            ],
        },
        "bounded_model": {
            "integer_domain": "all amounts are integer atoms in [0, 2^256 - 1]",
            "quote_cost_formula": {
                "fixed": (
                    "infrastructure + operator_on_call + security_monitoring + "
                    "data_license_external_io + risk_capital_insurance"
                ),
                "variable": ("maximum_jobs * (compute_execution_per_job + labor_external_per_job)"),
                "period_cap": ("ceil((fixed + variable) * (10000 + contingency_bps) / 10000)"),
                "onboarding": "separate one-time cap with a separate budget",
            },
            "qualification_rule": (
                "exact roots match; all invalid, replay, safety, and recovery counters "
                "equal zero; every selected integer threshold is met"
            ),
            "skin_in_the_game_rule": (
                "detection_probability_bps * slash_atoms + "
                "10000 * future_value_lost_atoms >= "
                "10000 * maximum_defect_gain_atoms; slash_atoms <= bond_atoms"
            ),
            "selection_rule": (
                "enumerate every required-winner combination for at most 16 candidates; "
                "enforce owner, failure-domain, recurring-budget, onboarding-budget, "
                "subject, asset, and epoch constraints; minimize recurring high-case "
                "cap, then onboarding cap, then sorted quote IDs"
            ),
            "selected_complete_quotes": contract.SELECTED_COMPLETE_QUOTES,
            "selected_qualification_policies": (contract.SELECTED_QUALIFICATION_POLICIES),
            "selected_procurement_policies": contract.SELECTED_PROCUREMENT_POLICIES,
        },
        "quote_component_contract": {
            "required_recurring_components": [
                "fixed infrastructure",
                "fixed operator and on-call labor",
                "fixed security, monitoring, and key custody",
                "fixed data-license and external-I/O costs",
                "fixed risk-capital and insurance costs",
                "variable compute and execution cost per job",
                "variable labor and external cost per job",
            ],
            "required_one_time_components": ["onboarding and replacement setup"],
            "zero_rule": (
                "zero is allowed only as an explicit value in a named component; "
                "the recurring cap must remain positive"
            ),
            "refinement": (
                "each complete quote must reproduce the existing FULL_ROLE_COST_CANDIDATE "
                "period cap and target prefund exactly"
            ),
        },
        "role_qualification_packets": _role_qualification_packets(),
        "procurement_flow": [
            "collect signed complete quote and beneficial-owner evidence",
            "run exact-subject role-specific qualification",
            "check bond and finite defect-gain inequality",
            "exhaustively select the lowest feasible high-case portfolio",
            "prefund selected recurring and onboarding caps in the payment asset",
            "external verifier may later construct an opaque work witness",
            "ZenoLedger must recheck current head, epoch, quote, job, period, and reserve caps",
            "atomic commit may pay no more than verified liability and remaining reserve",
        ],
        "payment_boundary": {
            "candidate_selection_creates_payment": False,
            "qualification_creates_payment": False,
            "proof_market_creates_reward": False,
            "future_revenue_counts_as_prefund": False,
            "required_future_production_path": (
                "release-selected verifier -> opaque work witness -> current-head and "
                "purpose-budget recheck -> atomic ZenoLedger commit"
            ),
        },
        "bounded_procurement_evidence": bounded_procurement_evidence(),
        "evidence_lane": {
            "current": [
                "typed complete-quote and qualification schema",
                "exact quote-to-cost-envelope refinement",
                "exact integer bond inequality with bonded-slash check",
                "bounded exhaustive multiwinner selector with canonical tie break",
                "beneficial-owner and named failure-domain concentration caps",
                "finite bond-boundary and candidate-permutation searches",
                "named mutants for greedy selection, substitution, replay, and Sybil bids",
            ],
            "required_before_selection": [
                "real competitive quotes with verified beneficial ownership",
                "selected role counts, service specs, benchmark profiles, and thresholds",
                "exact hardware, binary, guest-image, data-source, and destination evidence",
                "selected payment assets and purpose-bound recurring and onboarding reserves",
                "legal, tax, labor, procurement, sanctions, custody, and treasury review",
            ],
            "required_before_production": [
                "opaque verifier-created qualification and work witnesses",
                "Rust canonical quote, policy, qualification, selection, and payment codecs",
                "formal selector, concentration, budget, bond, and no-source-creation proofs",
                "mounted ZenoLedger admission and payment capability",
                "restart, replay, replacement, migration, and authority-epoch tests",
            ],
        },
        "promotion_boundary": {
            "claim": (
                "The research contract compares complete exact-subject quotes and returns "
                "a deterministic minimum-cost feasible set inside a bounded domain."
            ),
            "nonclaims": [
                "No real quote, qualification threshold, role count, or provider is selected.",
                "Beneficial-owner and failure-domain evidence remains externally supplied.",
                "The bond inequality depends on unselected defect-gain, detection, slash, and future-value inputs.",
                "The finite selector does not establish unbounded optimality or Byzantine procurement security.",
                "Vendor SLA and historical proof data do not qualify ZenoDEX end-to-end service.",
                "Caller-constructible Python values are not opaque authority witnesses.",
                "This artifact cannot admit work, move value, activate a role, or promote production.",
            ],
        },
        "activation_gate": {
            "critical_role_count": len(EXPECTED_ROLE_IDS),
            "selected_procurement_policy_count": 0,
            "selected_qualification_policy_count": 0,
            "qualified_production_quote_count": 0,
            "beneficial_ownership_verified": False,
            "failure_domain_independence_verified": False,
            "purpose_bound_reserves_custodied": False,
            "opaque_work_verifiers_implemented": False,
            "legal_activation_complete": False,
            "runtime_implemented": False,
            "mounted": False,
            "work_admission_allowed": False,
            "payment_allowed": False,
            "activation_allowed": False,
            "production_ready": False,
        },
    }


def _load_json_no_duplicates(path: Path) -> object:
    def pairs_hook(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        duplicates: list[str] = []
        for key, value in pairs:
            if key in result:
                duplicates.append(key)
            result[key] = value
        if duplicates:
            raise ValueError("duplicate JSON keys: " + ", ".join(sorted(set(duplicates))))
        return result

    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=pairs_hook)


def check_artifact(
    path: Path = DEFAULT_OUTPUT,
    repo_root: Path = REPO_ROOT,
) -> dict[str, Any]:
    errors: list[str] = []
    try:
        expected = build_document(repo_root)
        observed = _load_json_no_duplicates(path)
        if not isinstance(observed, dict):
            errors.append("artifact root must be an object")
        elif path.read_bytes() != _encoded(expected):
            errors.append("artifact bytes or semantics differ from generated procurement model")
    except (
        OSError,
        ValueError,
        json.JSONDecodeError,
        subprocess.SubprocessError,
    ) as exc:
        errors.append(str(exc))
    return {
        "ok": not errors,
        "artifact": str(path),
        "errors": errors,
        "selected_procurement_policy_count": 0,
        "qualified_production_quote_count": 0,
        "activation_allowed": False,
        "payment_allowed": False,
        "production_ready": False,
    }


def _write_atomic(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        dir=path.parent,
        prefix=f".{path.name}.",
        suffix=".tmp",
    )
    temporary_path = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary_path, path)
        directory_descriptor = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory_descriptor)
        finally:
            os.close(directory_descriptor)
    finally:
        if temporary_path.exists():
            temporary_path.unlink()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args(argv)

    if args.write:
        _write_atomic(args.output, _encoded(build_document()))
    report: dict[str, Any] = (
        check_artifact(args.output)
        if args.check
        else {
            "ok": True,
            "activation_allowed": False,
            "payment_allowed": False,
            "production_ready": False,
        }
    )
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif args.check:
        print("PASS" if report["ok"] else "FAIL")
        for error in report.get("errors", []):
            print(f"- {error}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

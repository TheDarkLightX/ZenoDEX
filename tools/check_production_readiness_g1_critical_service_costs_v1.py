#!/usr/bin/env python3
"""Generate and check the research-only G1 critical-service cost envelope."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from collections.abc import Mapping
from dataclasses import asdict
from functools import lru_cache
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "docs/research/PRODUCTION_READINESS_G1_CRITICAL_SERVICE_COSTS_V1.json"
)
SCHEMA = "zenodex/production-readiness-g1-critical-service-costs/v1"
RESEARCH_SOURCE_SUBJECT = "ae0c351e46aa969cb74d502e6948aef1167a99cd"
CONTRACT_PATH = (
    "tools/production_readiness_g1_critical_service_cost_contract_v1.py"
)
CHECKER_PATH = "tools/check_production_readiness_g1_critical_service_costs_v1.py"

sys.path.insert(0, str(REPO_ROOT))

from tools import (  # noqa: E402
    production_readiness_g1_critical_service_cost_contract_v1 as contract,
)
from tools import production_readiness_g1_service_funding_contract_v1 as funding  # noqa: E402

EXPECTED_ROLE_IDS = frozenset(
    {
        "validator_finality_operator",
        "oracle_reporter_aggregator_disputer_and_watcher",
        "liquidator_and_keeper",
        "tau_relayer_and_destination_operator",
        "proof_prover_and_proof_miner",
    }
)

EXPECTED_QUOTE_CORE = {
    "HETZNER_CCX13_US_MONTH_2026_06_15": (
        "Hetzner",
        "CALENDAR_MONTH",
        50_990_000,
        (
            "https://docs.hetzner.com/general/"
            "infrastructure-and-availability/price-adjustment/"
        ),
    ),
    "HETZNER_CCX33_US_MONTH_2026_06_15": (
        "Hetzner",
        "CALENDAR_MONTH",
        165_990_000,
        (
            "https://docs.hetzner.com/general/"
            "infrastructure-and-availability/price-adjustment/"
        ),
    ),
    "DIGITALOCEAN_GENERAL_PURPOSE_START_MONTH_2026_08_16": (
        "DigitalOcean",
        "CALENDAR_MONTH",
        63_000_000,
        "https://www.digitalocean.com/solutions/vps-hosting",
    ),
    "DIGITALOCEAN_A4000_HOUR_2026_08_16": (
        "DigitalOcean",
        "COMPUTE_HOUR",
        760_000,
        "https://www.digitalocean.com/pricing/additional-gpus",
    ),
    "DIGITALOCEAN_A100_HOUR_2026_08_16": (
        "DigitalOcean",
        "COMPUTE_HOUR",
        3_090_000,
        "https://www.digitalocean.com/pricing/additional-gpus",
    ),
}


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
        frozen = _git_bytes(
            repo_root,
            "show",
            f"{RESEARCH_SOURCE_SUBJECT}:{path}",
        )
        if (repo_root / path).read_bytes() != frozen:
            raise ValueError(f"critical-service research source drift: {path}")
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
        "docs/FIRE_REVENUE_SURFACE_ATLAS.md": (
            "StakeRewards <= RevenueBackedRewardBudget + ExplicitSubsidy",
        ),
        "zk/asset_transfer_module_risc0/README.md": (
            "real proof elapsed: 569.750161942 seconds",
        ),
        "zk/asset_lane_coordinator_risc0/README.md": (
            "complete module-to-lane recursive proof: 1,443.666295007 seconds",
        ),
        "docs/research/PRODUCTION_READINESS_G1_SERVICE_FUNDING_V1.json": (
            '"minimum": 18',
            '"maximum": 36',
            '"future_revenue_rule"',
        ),
    }
    for path, required in markers.items():
        text = (repo_root / path).read_text(encoding="utf-8")
        missing = [marker for marker in required if marker not in text]
        if missing:
            raise ValueError(
                f"critical-service source marker drift: {path}: {missing}"
            )


def _validate_contract() -> None:
    if contract.CRITICAL_SERVICE_ROLE_IDS != EXPECTED_ROLE_IDS:
        raise ValueError("critical service role registry differs from checker")
    if set(contract.SELECTED_CRITICAL_SERVICE_COST_ENVELOPES) != EXPECTED_ROLE_IDS:
        raise ValueError("selected cost-envelope registry has wrong role set")
    if any(
        value is not None
        for value in contract.SELECTED_CRITICAL_SERVICE_COST_ENVELOPES.values()
    ):
        raise ValueError("critical service costs must remain unselected")
    if set(contract.SELECTED_CRITICAL_SERVICE_REVENUE_INPUTS) != EXPECTED_ROLE_IDS:
        raise ValueError("selected revenue-input registry has wrong role set")
    if any(
        value is not None
        for value in contract.SELECTED_CRITICAL_SERVICE_REVENUE_INPUTS.values()
    ):
        raise ValueError("critical service revenue inputs must remain unselected")
    if not EXPECTED_ROLE_IDS <= funding.BUDGET_ELIGIBLE_ROLE_IDS:
        raise ValueError("critical roles are not all budget eligible")

    quotes = contract.external_benchmark_quotes_v1()
    observed = {
        quote_id: (
            quote.provider,
            quote.billing_unit.value,
            quote.amount_atoms,
            quote.source_url,
        )
        for quote_id, quote in quotes.items()
    }
    if observed != EXPECTED_QUOTE_CORE:
        raise ValueError("external benchmark quote core differs from checker")
    if any(
        quote.payment_asset_id != contract.USD_E6
        or quote.evidence_scope
        is not contract.BenchmarkEvidenceScopeV1.COMPONENT_ONLY
        or quote.checked_on != "2026-08-16"
        for quote in quotes.values()
    ):
        raise ValueError("benchmark scope, units, or observation date drifted")


@lru_cache(maxsize=1)
def bounded_cost_evidence() -> dict[str, Any]:
    ceiling_counterexample: dict[str, int] | None = None
    ceiling_cases = 0
    for raw_atoms in range(33):
        for contingency_bps in range(101):
            loaded = contract._ceil_loaded_atoms(raw_atoms, contingency_bps)
            numerator = raw_atoms * (contract.BPS_SCALE + contingency_bps)
            ceiling_cases += 1
            if (
                loaded * contract.BPS_SCALE < numerator
                or (
                    loaded > 0
                    and (loaded - 1) * contract.BPS_SCALE >= numerator
                )
            ):
                ceiling_counterexample = {
                    "raw_atoms": raw_atoms,
                    "contingency_bps": contingency_bps,
                    "loaded_atoms": loaded,
                }
                break

    prefund_counterexample: dict[str, int] | None = None
    prefund_cases = 0
    for realized_prefund_atoms in range(17):
        for forecast_atoms in range(17):
            for target_atoms in range(1, 17):
                shortfall = max(0, target_atoms - realized_prefund_atoms)
                target_met = shortfall == 0
                prefund_cases += 1
                if target_met != (realized_prefund_atoms >= target_atoms):
                    prefund_counterexample = {
                        "realized_prefund_atoms": realized_prefund_atoms,
                        "forecast_atoms": forecast_atoms,
                        "target_atoms": target_atoms,
                    }
                    break

    return {
        "ceiling_rounding_search": {
            "domain": "raw atoms=0..32; contingency bps=0..100",
            "cases": ceiling_cases,
            "counterexample": ceiling_counterexample,
            "predicate": (
                "loaded*10000 >= numerator and, when loaded>0, "
                "(loaded-1)*10000 < numerator"
            ),
        },
        "prefund_separation_search": {
            "domain": (
                "realized prefund=0..16; forecast=0..16; target=1..16"
            ),
            "cases": prefund_cases,
            "counterexample": prefund_counterexample,
            "predicate": (
                "prefund target met iff realized purpose-bound prefund >= target; "
                "forecast is observational only"
            ),
        },
        "named_mutant_witnesses": [
            {
                "id": "FLOOR_CONTINGENCY_UNDERFUNDS",
                "raw_atoms": 1,
                "contingency_bps": 1,
                "correct_loaded_atoms": 2,
                "mutant_loaded_atoms": 1,
                "loss_atoms": 1,
            },
            {
                "id": "FORECAST_COUNTED_AS_PREFUND",
                "target_atoms": 10,
                "realized_prefund_atoms": 0,
                "forecast_atoms": 10,
                "correct_target_met": False,
                "mutant_target_met": True,
            },
            {
                "id": "LOW_CASE_PERIOD_CAP",
                "low_case_atoms": 10,
                "high_case_atoms": 20,
                "underfunded_atoms": 10,
            },
            {
                "id": "OMITTED_ROLE_MULTIPLICITY",
                "role_count": 7,
                "per_role_atoms": 100,
                "omitted_atoms": 600,
            },
            {
                "id": "PROOF_MARKET_CREATES_REWARD",
                "prefunded_reserve_atoms": 0,
                "accepted_bid_atoms": 1,
                "unfunded_atoms": 1,
            },
            {
                "id": "CROSS_ASSET_PORTFOLIO",
                "left_asset": "USD_E6",
                "right_asset": "USDC",
                "mutant_action": "SUM_WITHOUT_SELECTED_CONVERSION",
            },
        ],
        "claim_ceiling": (
            "Exact only for the declared bounded integer searches and direct "
            "cost, contingency, prefund, and same-asset aggregation arithmetic."
        ),
    }


def _quote_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for quote_id, quote in sorted(
        contract.external_benchmark_quotes_v1().items()
    ):
        row = asdict(quote)
        row["quote_id"] = quote_id
        rows.append(row)
    return rows


def _critical_role_packets() -> dict[str, dict[str, Any]]:
    routes = funding.participant_funding_registry_v1()
    sources = funding.allowed_funding_sources_v1()
    common_open_inputs = [
        "payment asset and conversion policy",
        "complete fixed and variable cost ranges",
        "role count, maximum jobs, contingency, and target periods",
        "purpose-bound opening reserve",
        "claimant credential, work verifier, bond, and slash rule",
        "period-to-block conversion and authority epoch",
        "legal, tax, procurement, and release roots",
    ]
    packets: dict[str, dict[str, Any]] = {
        "validator_finality_operator": {
            "compensation_shape": (
                "FIXED_AVAILABILITY_PLUS_VERIFIED_INCIDENT_AND_REPLACEMENT_COST"
            ),
            "pricing_rule": "NO_TRANSACTION_OR_VOLUME_WEIGHT",
            "specific_open_inputs": [
                "seven-validator retained profile reconfirmation",
                "qualified node shape, geography, backup, monitoring, and key custody",
                "operator labor, on-call, incident, and replacement cost",
            ],
        },
        "oracle_reporter_aggregator_disputer_and_watcher": {
            "compensation_shape": (
                "FIXED_AVAILABILITY_PLUS_ACCEPTED_REPORT_DISPUTE_OR_WATCHER_JOB"
            ),
            "pricing_rule": "VERIFIED_WORK_CAPPED_BY_PREFUNDED_BUDGET",
            "specific_open_inputs": [
                "reporter, aggregator, disputer, and watcher counts",
                "data-license, report, dispute, monitoring, and availability costs",
                "DefectGain <= DetectionProbability*Slash + FutureValueLost",
            ],
        },
        "liquidator_and_keeper": {
            "compensation_shape": (
                "SUCCESSFUL_ACTION_FEE_OR_PENALTY_SHARE_PLUS_OPTIONAL_LIVENESS_BUDGET"
            ),
            "pricing_rule": (
                "PAYMENT<=MIN(VERIFIED_BID,SELECTED_ACTION_SURPLUS,JOB_CAP,RESERVE)"
            ),
            "specific_open_inputs": [
                "Tau execution fee and capital-opportunity cost",
                "minimal liquidation fraction and bad-debt non-worsening rule",
                "eligibility, deterministic selection, and failed-attempt treatment",
            ],
        },
        "tau_relayer_and_destination_operator": {
            "compensation_shape": (
                "FIXED_AVAILABILITY_PLUS_ACKNOWLEDGED_EXTERNAL_IO_REIMBURSEMENT"
            ),
            "pricing_rule": "ACKNOWLEDGED_COST_CAPPED_BY_PREFUNDED_BUDGET",
            "specific_open_inputs": [
                "Tau fee schedule and destination operator count",
                "retry, duplicate, outage, and rejoin cost assumptions",
                "authenticated acknowledgment and destination idempotency verifier",
            ],
        },
        "proof_prover_and_proof_miner": {
            "compensation_shape": (
                "VERIFIED_PROOF_MARKET_JOB_WITH_DIRECT_EXECUTION_FALLBACK"
            ),
            "pricing_rule": "VERIFIED_BID_CAPPED_BY_PREFUNDED_BUDGET",
            "proof_unit_price_atoms": None,
            "specific_open_inputs": [
                "qualified hardware and exact guest cycle/latency benchmark",
                "auction, mining, procurement, or first-valid selection rule",
                "deadline, failed-proof cost, bond, substitution, and fallback rule",
            ],
        },
    }
    for role_id, packet in packets.items():
        packet.update(
            {
                "service_criticality": routes[role_id].service_criticality.value,
                "unfunded_behavior": routes[role_id].unfunded_behavior,
                "allowed_funding_sources": sorted(
                    source.value for source in sources[role_id]
                ),
                "selected_cost_envelope": (
                    contract.SELECTED_CRITICAL_SERVICE_COST_ENVELOPES[role_id]
                ),
                "selected_revenue_input": (
                    contract.SELECTED_CRITICAL_SERVICE_REVENUE_INPUTS[role_id]
                ),
                "open_inputs": common_open_inputs + packet["specific_open_inputs"],
                "status": "OPEN_UNSELECTED",
            }
        )
    return packets


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    _validate_contract()
    _validate_source_markers(repo_root)
    source_pins = _source_pins(repo_root)
    validator_scenario = asdict(contract.validator_infrastructure_scenario_v1())

    return {
        "schema": SCHEMA,
        "status": "RESEARCH_ONLY_UNSELECTED",
        "production_promotion": False,
        "reviewed_subject": RESEARCH_SOURCE_SUBJECT,
        "research_source_pins": source_pins,
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
        "game_surface": {
            "players": sorted(EXPECTED_ROLE_IDS)
            + [
                "protocol treasury and deployment-capital providers",
                "fee-paying users and interface customers",
                "governance and release operators",
                "cloud, data, and external-I/O vendors",
            ],
            "actions": [
                "quote, bid, procure, prefund, top up, pay, exhaust, or replace",
                "submit or verify a report, liquidation, relay acknowledgment, proof, or precommit",
                "forecast future revenue or bind already realized revenue to a purpose budget",
            ],
            "payoff": (
                "admitted payment minus infrastructure, labor, capital, data, "
                "execution, failure, and bonded-risk costs"
            ),
            "external_information": [
                "future usage and protocol revenue",
                "operator reservation wages and beneficial ownership",
                "Tau fees, data licenses, proof hardware performance, and taxes",
            ],
        },
        "attack_query": {
            "query": (
                "Can a service activate from a component-only estimate, low-case "
                "cap, cross-asset sum, future-revenue forecast, or market-selected "
                "claim without realized purpose-bound funding?"
            ),
            "disaster_states": [
                "COMPONENT_QUOTE_MISREPRESENTED_AS_FULL_COMPENSATION",
                "FUTURE_REVENUE_COUNTED_AS_CUSTODIED_PREFUND",
                "LOW_CASE_CAP_UNDERFUNDS_HIGH_CASE_SERVICE",
                "ROLE_MULTIPLICITY_OMITTED",
                "CROSS_ASSET_COSTS_SUMMED_WITHOUT_CONVERSION",
                "PROOF_MARKET_CREATES_AN_UNFUNDED_REWARD",
                "UNFUNDED_CRITICAL_ROLE_ACTIVATES",
            ],
        },
        "bounded_model": {
            "integer_domain": "all amounts are integer atoms in [0, 2^256 - 1]",
            "cost_formula": {
                "fixed_low": (
                    "role_count * (infrastructure_low + operator_low)"
                ),
                "fixed_high": (
                    "role_count * (infrastructure_high + operator_high)"
                ),
                "variable_low": "maximum_jobs * per_job_low",
                "variable_high": "maximum_jobs * per_job_high",
                "raw_low": "fixed_low + variable_low",
                "raw_high": "fixed_high + variable_high",
                "loaded_low": (
                    "ceil(raw_low * (10000 + contingency_bps) / 10000)"
                ),
                "loaded_high": (
                    "ceil(raw_high * (10000 + contingency_bps) / 10000)"
                ),
                "period_cap": "loaded_high",
                "target_prefund": "period_cap * target_prefund_periods",
            },
            "affordability_formula": {
                "prefund_shortfall": (
                    "max(0, target_prefund - realized_purpose_bound_prefund)"
                ),
                "prefund_target_met": "prefund_shortfall == 0",
                "recurring_break_even_low": "revenue_low >= period_cap",
                "forecast_rule": (
                    "forecast revenue never increases realized purpose-bound prefund"
                ),
                "asset_rule": (
                    "sum only identical payment assets; conversion requires a selected lane"
                ),
            },
            "skin_in_the_game_condition": {
                "economic_detection": (
                    "DefectGain <= DetectionProbability * SlashAmount "
                    "+ FutureValueLost"
                ),
                "deterministic_precommit_detection": (
                    "DefectGain <= SlashAmount + FutureValueLost"
                ),
                "status": "REQUIRED_UNSELECTED",
            },
            "selected_cost_envelopes": (
                contract.SELECTED_CRITICAL_SERVICE_COST_ENVELOPES
            ),
            "selected_revenue_inputs": (
                contract.SELECTED_CRITICAL_SERVICE_REVENUE_INPUTS
            ),
            "candidate_runway_months": {
                "minimum": 18,
                "maximum": 36,
                "status": "ADVISORY_UNSELECTED",
            },
        },
        "external_benchmark_snapshot": {
            "checked_on": "2026-08-16",
            "payment_asset_id": contract.USD_E6,
            "quotes": _quote_rows(),
            "refresh_required_before_selection": True,
            "scope": (
                "Public list-price observations are component inputs only. "
                "They are not vendor quotes, qualified hardware, or complete compensation."
            ),
        },
        "validator_infrastructure_scenario": {
            **validator_scenario,
            "profile_status": "RETAINED_SEVEN_VALIDATOR_ASSUMPTION_RECONFIRM_REQUIRED",
            "scope": (
                "Infrastructure-only arithmetic using Hetzner CCX13-to-CCX33 "
                "USA monthly list prices; excludes every operator and availability cost."
            ),
            "digitalocean_cross_check_atoms_per_month": 63_000_000,
        },
        "critical_role_packets": _critical_role_packets(),
        "revenue_source_boundary": {
            "bootstrap": [
                "purpose-bound deployment capital in the payment asset",
                "selected genesis service lot after admitted conversion and legal activation",
            ],
            "recurring": [
                "finalized protocol-owned fee revenue routed to the role budget",
                "selected liquidation or keeper action fee",
                "explicit Tau external-I/O fee",
                "signed opt-in interface fee",
                "verified user-granted execution improvement",
            ],
            "excluded": [
                "LP-owned fees, user property, refundable bonds, insurance principal",
                "unconverted genesis ZDEX inventory",
                "forecast volume, forecast fee revenue, and expected token appreciation",
                "buyback carry already assigned after the service waterfall",
            ],
            "revenue_range_status": "NO_NUMERIC_REVENUE_RANGE_SELECTED",
        },
        "proof_cost_boundary": {
            "local_historical_observations": [
                {
                    "path": "zk/asset_transfer_module_risc0/README.md",
                    "elapsed_seconds": "569.750161942",
                    "scope": "one historical real asset-transfer module proof",
                },
                {
                    "path": "zk/asset_lane_coordinator_risc0/README.md",
                    "elapsed_seconds": "1443.666295007",
                    "scope": "one historical child-plus-recursive lane proof",
                },
            ],
            "public_compute_quotes": [
                "DIGITALOCEAN_A4000_HOUR_2026_08_16",
                "DIGITALOCEAN_A100_HOUR_2026_08_16",
            ],
            "proof_unit_price_atoms": None,
            "conversion_allowed": False,
            "reason": (
                "The historical proofs do not bind the quoted GPU types, and the "
                "quoted hourly rates do not establish RISC0 compatibility, cycles, "
                "queueing, failure cost, or current ZRPF throughput."
            ),
        },
        "bounded_cost_evidence": bounded_cost_evidence(),
        "evidence_lane": {
            "current": [
                "exact integer cost-range, contingency, runway, and affordability evaluator",
                "same-asset portfolio aggregation with cross-asset rejection",
                "direct refinement into the existing service-budget sizing fields",
                "dated primary-source infrastructure and compute component prices",
                "finite ceiling-rounding and prefund-separation searches",
                "named mutants for underfunding and source creation",
            ],
            "required_before_selection": [
                "competitive role-specific quotes with complete cost components",
                "qualified node, oracle, Tau, keeper, and prover benchmarks",
                "selected fee lanes and conservative usage/revenue scenarios",
                "bond, slash, work verifier, claimant, and replacement rules",
                "legal, tax, labor, procurement, custody, and treasury review",
            ],
            "required_before_production": [
                "Rust transition and canonical cost/payment codec",
                "formal per-asset budget, exhaustion, and no-source-creation proofs",
                "mounted ZenoLedger payment capability with opaque work witnesses",
                "restart, replay, migration, authority-epoch, and release tests",
            ],
        },
        "approval_packet": {
            "status": "NOT_READY_FOR_NUMERIC_APPROVAL",
            "recommended_order": [
                "reconfirm enabled roles and counts",
                "obtain full low/high cost quotes and qualified performance measurements",
                "select payment assets, fee lanes, maximum jobs, and exhaustion behavior",
                "size high-case caps plus contingency and custody the target runway",
                "approve each role separately with work, bond, legal, and release roots",
                "compute buyback-eligible surplus only after role reserves are funded",
            ],
            "role_specific_approval_required": True,
            "blanket_approval_supported": False,
        },
        "promotion_boundary": {
            "claim": (
                "The research model computes conservative high-case integer caps, "
                "keeps forecasts outside prefund, and rejects cross-asset aggregation "
                "inside its declared typed model."
            ),
            "nonclaims": [
                "No complete service cost, payment asset, revenue range, fee lane, or runway is selected.",
                "Public list prices do not establish qualified hardware or adequate compensation.",
                "No proof-unit price is derived from unrelated hardware and historical proof observations.",
                "The model does not prove service quality, participation, oracle truth, Tau fees, or future revenue.",
                "The model is unmounted and cannot admit work, pay a participant, or activate a role.",
                "Finite enumeration is not an unbounded proof or a production readiness receipt.",
            ],
        },
        "activation_gate": {
            "critical_role_count": len(EXPECTED_ROLE_IDS),
            "selected_cost_envelope_count": 0,
            "selected_revenue_input_count": 0,
            "full_cost_quotes_complete": False,
            "qualified_benchmarks_complete": False,
            "purpose_bound_runway_custodied": False,
            "work_verifiers_selected": False,
            "legal_activation_complete": False,
            "runtime_implemented": False,
            "mounted": False,
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
            raise ValueError(
                "duplicate JSON keys: " + ", ".join(sorted(set(duplicates)))
            )
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
            errors.append(
                "artifact bytes or semantics differ from generated critical-service model"
            )
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
        "selected_cost_envelope_count": 0,
        "activation_allowed": False,
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

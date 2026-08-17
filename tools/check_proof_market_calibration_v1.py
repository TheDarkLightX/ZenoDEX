#!/usr/bin/env python3
"""Generate or verify the research-only proof-market calibration packet."""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT: Final = REPO_ROOT / "docs/research/PROOF_MARKET_CALIBRATION_V1.json"
SCHEMA: Final = "zenodex/proof-market-calibration/v1"
REVIEWED_SOURCE_COMMIT: Final = "966e81acc8c40a9aa776eb645972fb8a466b75c9"
SOURCE_PATHS: Final = (
    "tools/check_proof_market_calibration_v1.py",
    "tools/proof_market_calibration_v1.py",
    "docs/research/PROOF_MARKET_CALIBRATION_V1.md",
)

sys.path.insert(0, str(REPO_ROOT))

from tools import proof_market_calibration_v1 as model  # noqa: E402


def _canonical_bytes(document: dict[str, Any]) -> bytes:
    return json.dumps(document, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _source_pins() -> list[dict[str, str]]:
    result: list[dict[str, str]] = []
    for relative_path in SOURCE_PATHS:
        path = REPO_ROOT / relative_path
        if not path.is_file():
            raise ValueError(f"missing calibration source: {relative_path}")
        result.append({"path": relative_path, "sha256": _sha256(path.read_bytes())})
    return result


def _asdict(value: Any) -> dict[str, Any]:
    return dataclasses.asdict(value)


def _workloads() -> tuple[model.WorkloadClassV1, ...]:
    return (
        model.WorkloadClassV1("MICRO_64_MCYCLE", 2_000, 64, 1_000_000, 12_500),
        model.WorkloadClassV1("STANDARD_1024_MCYCLE", 4_500, 1_024, 5_000_000, 12_500),
        model.WorkloadClassV1("LARGE_5_GCYCLE", 3_000, 5_000, 25_000_000, 12_500),
        model.WorkloadClassV1("VERY_LARGE_50_GCYCLE", 500, 50_000, 250_000_000, 12_500),
    )


def _shocks() -> tuple[model.CostShockV1, ...]:
    return (
        model.CostShockV1("EFFICIENT", 2_500, 7_000, 12_000, 0),
        model.CostShockV1("BASE", 5_000, 10_000, 10_000, 100),
        model.CostShockV1("STRESSED", 2_500, 16_000, 7_000, 500),
    )


def _provers() -> tuple[model.ProverProfileV1, ...]:
    return (
        model.ProverProfileV1(
            "COMMUNITY_L4_EQUIVALENT",
            "OWNER_COMMUNITY",
            264,
            1_000_000,
            250_000,
            100_000_000,
            400,
            2_000,
        ),
        model.ProverProfileV1(
            "TEN_GPU_CLUSTER",
            "OWNER_SMALL_CLUSTER",
            2_640,
            8_000_000,
            500_000,
            2_000_000_000,
            200,
            1_500,
        ),
        model.ProverProfileV1(
            "LARGE_CLUSTER",
            "OWNER_LARGE_CLUSTER",
            10_000,
            25_000_000,
            1_000_000,
            20_000_000_000,
            100,
            1_000,
        ),
    )


def _capacity_scenarios() -> tuple[model.CapacityDemandScenarioV1, ...]:
    def request(requestor: str, owner: str, slots: int) -> model.RequestorDemandV1:
        return model.RequestorDemandV1(requestor, owner, slots)

    return (
        model.CapacityDemandScenarioV1(
            "LOW_DEMAND",
            2_500,
            (
                request("A1", "OWNER_A", 10),
                request("B1", "OWNER_B", 5),
                request("C1", "OWNER_C", 5),
            ),
            20,
        ),
        model.CapacityDemandScenarioV1(
            "BASE_DEMAND",
            5_000,
            (
                request("A2", "OWNER_A", 30),
                request("B2", "OWNER_B", 20),
                request("C2", "OWNER_C", 15),
            ),
            40,
        ),
        model.CapacityDemandScenarioV1(
            "SURGE_DEMAND",
            2_500,
            (
                request("A3", "OWNER_A", 35),
                request("A4", "OWNER_A", 35),
                request("B3", "OWNER_B", 20),
                request("C3", "OWNER_C", 20),
            ),
            80,
        ),
    )


def _policy_grid() -> tuple[tuple[model.AuctionPolicyV1, model.CapacityPolicyV1], ...]:
    bonds = (
        ("LOSS", model.BondRuleV1.LOSS_BASED, 0),
        ("STATIC_5X", model.BondRuleV1.STATIC_MULTIPLE, 50_000),
        ("STATIC_10X", model.BondRuleV1.STATIC_MULTIPLE, 100_000),
    )
    result: list[tuple[model.AuctionPolicyV1, model.CapacityPolicyV1]] = []
    for bond_name, bond_rule, bond_multiple_bps in bonds:
        for maximum_price_cost_bps in (12_500, 25_000, 40_000):
            for primary_window_factor_bps in (12_500, 17_500, 25_000):
                for permissionless_floor_bps in (1_000, 2_000, 3_000):
                    for priority_owner_cap_bps in (2_000, 3_000, 4_000):
                        policy_id = (
                            f"{bond_name}_P{maximum_price_cost_bps}_"
                            f"W{primary_window_factor_bps}_"
                            f"F{permissionless_floor_bps}_"
                            f"C{priority_owner_cap_bps}"
                        )
                        result.append(
                            (
                                model.AuctionPolicyV1(
                                    policy_id,
                                    8_000,
                                    maximum_price_cost_bps,
                                    primary_window_factor_bps,
                                    5_000,
                                    120,
                                    bond_rule,
                                    bond_multiple_bps,
                                ),
                                model.CapacityPolicyV1(
                                    100,
                                    permissionless_floor_bps,
                                    priority_owner_cap_bps,
                                ),
                            )
                        )
    return tuple(result)


def _hard_constraints(
    auction: model.AuctionPolicyEvaluationV1,
    capacity: model.CapacityPolicyEvaluationV1,
    auction_policy: model.AuctionPolicyV1,
    capacity_policy: model.CapacityPolicyV1,
) -> dict[str, bool]:
    return {
        "LOSS_BASED_BOND": auction_policy.bond_rule is model.BondRuleV1.LOSS_BASED,
        "FULFILLMENT_AT_LEAST_9500_BPS": auction.fulfillment_bps >= 9_500,
        "NO_ADMITTED_LATE_LOCK": auction.admitted_late_count == 0,
        "ELIGIBLE_OWNER_FRACTION_AT_LEAST_5000_BPS": (
            auction.average_eligible_owner_fraction_bps >= 5_000
        ),
        "BOND_EXCLUSION_AT_MOST_4000_BPS": auction.bond_exclusion_bps <= 4_000,
        "PERMISSIONLESS_FLOOR_AT_LEAST_2000_BPS": (
            capacity_policy.permissionless_floor_bps >= 2_000
        ),
        "PRIORITY_OWNER_CAP_AT_MOST_3000_BPS": (
            capacity_policy.priority_owner_cap_bps <= 3_000
        ),
        "PERMISSIONLESS_SERVICE_AT_LEAST_8000_BPS": (
            capacity.permissionless_service_bps >= 8_000
        ),
        "PRIORITY_SERVICE_AT_LEAST_6500_BPS": capacity.priority_service_bps >= 6_500,
        "UTILIZATION_AT_LEAST_7500_BPS": capacity.utilization_bps >= 7_500,
    }


def _candidate_rows() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    workloads = _workloads()
    shocks = _shocks()
    provers = _provers()
    reference_prover = provers[1]
    capacity_scenarios = _capacity_scenarios()
    rows: list[dict[str, Any]] = []
    detailed: dict[str, tuple[model.AuctionPolicyEvaluationV1, model.CapacityPolicyEvaluationV1]] = {}
    for auction_policy, capacity_policy in _policy_grid():
        auction = model.evaluate_auction_policy(
            workloads,
            shocks,
            provers,
            auction_policy,
            reference_prover,
        )
        capacity = model.evaluate_capacity_policy(capacity_scenarios, capacity_policy)
        constraints = _hard_constraints(
            auction,
            capacity,
            auction_policy,
            capacity_policy,
        )
        hard_ok = all(constraints.values())
        row = {
            "policy_id": auction_policy.policy_id,
            "auction_policy": _asdict(auction_policy),
            "capacity_policy": _asdict(capacity_policy),
            "auction_metrics": {
                key: value
                for key, value in _asdict(auction).items()
                if key != "outcomes"
            },
            "capacity_metrics": {
                key: value
                for key, value in _asdict(capacity).items()
                if key != "outcomes"
            },
            "hard_constraints": constraints,
            "hard_ok": hard_ok,
        }
        rows.append(row)
        detailed[auction_policy.policy_id] = (auction, capacity)
    qualifying = [row for row in rows if row["hard_ok"]]
    if not qualifying:
        raise AssertionError("calibration grid has no hard-eligible policy")
    qualifying.sort(
        key=lambda row: (
            int(row["auction_metrics"]["average_competitive_payment_atoms"]),
            int(row["auction_metrics"]["collusive_uplift_bps"]),
            int(row["auction_metrics"]["bond_exclusion_bps"]),
            -int(row["capacity_metrics"]["permissionless_service_bps"]),
            -int(row["capacity_metrics"]["priority_service_bps"]),
            -int(row["capacity_metrics"]["utilization_bps"]),
            str(row["policy_id"]),
        )
    )
    recommended = qualifying[0]
    recommended_auction, recommended_capacity = detailed[str(recommended["policy_id"])]

    paired_policy_ids = {
        "loss_based": str(recommended["policy_id"]),
        "static_5x": str(recommended["policy_id"]).replace("LOSS_", "STATIC_5X_", 1),
        "static_10x": str(recommended["policy_id"]).replace("LOSS_", "STATIC_10X_", 1),
    }
    paired_rows = {
        label: next(row for row in rows if row["policy_id"] == policy_id)
        for label, policy_id in paired_policy_ids.items()
    }
    if not (
        int(paired_rows["loss_based"]["auction_metrics"]["bond_exclusion_bps"])
        <= int(paired_rows["static_5x"]["auction_metrics"]["bond_exclusion_bps"])
        <= int(paired_rows["static_10x"]["auction_metrics"]["bond_exclusion_bps"])
    ):
        raise AssertionError("static bond multiples unexpectedly reduce capital exclusion")
    return rows, {
        "candidate": recommended,
        "auction_outcomes": [_asdict(row) for row in recommended_auction.outcomes],
        "capacity_outcomes": [_asdict(row) for row in recommended_capacity.outcomes],
        "paired_bond_rule_comparison": paired_rows,
    }


def _boundary_refutations() -> dict[str, Any]:
    wallet_split = model.aggregate_requestor_demands_by_owner(
        (
            model.RequestorDemandV1("WALLET_A", "SAME_OWNER", 35),
            model.RequestorDemandV1("WALLET_B", "SAME_OWNER", 35),
            model.RequestorDemandV1("WALLET_C", "OTHER_OWNER", 20),
        )
    )
    zero_floor_reject = None
    try:
        model.simulate_capacity_scenario(
            _capacity_scenarios()[0],
            model.CapacityPolicyV1(100, 0, 2_000),
        )
    except ValueError as exc:
        zero_floor_reject = str(exc)
    if zero_floor_reject != "permissionless floor must be nonzero":
        raise AssertionError("zero permissionless floor did not fail closed")
    if wallet_split != (("OTHER_OWNER", 20), ("SAME_OWNER", 70)):
        raise AssertionError("wallet splitting bypassed beneficial-owner aggregation")
    return {
        "wallet_split_aggregation": wallet_split,
        "zero_permissionless_floor_reject": zero_floor_reject,
        "mutants": [
            {
                "id": "MUTANT_LOCK_USES_HEADLINE_WINDOW",
                "killed_by": "each bid recomputes remaining work after auction delay",
            },
            {
                "id": "MUTANT_STATIC_10X_IS_ALWAYS_SAFE",
                "killed_by": "paired capital-exclusion comparison at identical price, window, and capacity parameters",
            },
            {
                "id": "MUTANT_WALLET_SPLIT_BYPASSES_PRIORITY_CAP",
                "killed_by": "requestor demand aggregates by beneficial owner before the cap",
            },
            {
                "id": "MUTANT_ZERO_PERMISSIONLESS_FLOOR",
                "killed_by": "typed capacity policy rejects the zero floor",
            },
        ],
    }


def _source_review() -> dict[str, Any]:
    return {
        "checked_on": "2026-08-17",
        "primary_sources": [
            {
                "id": "BOUNDLESS_PERFORMANCE_OPTIMIZATION",
                "url": "https://docs.boundless.network/provers/performance-optimization",
                "observations": [
                    "official example reports approximately 400 kHz system throughput",
                    "official single-GPU example reports approximately 264 kHz",
                    "guidance says to benchmark representative workloads",
                ],
            },
            {
                "id": "BOUNDLESS_PROVER_QUICK_START",
                "url": "https://docs.boundless.network/provers/quick-start",
                "observations": [
                    "4090 and L4 are named as strong tested GPUs",
                    "at least ten GPUs are recommended for a competitive prover",
                ],
            },
            {
                "id": "BOUNDLESS_AUCTION_GUIDE",
                "url": "https://docs.boundless.network/developers/tutorials/auction",
                "observations": [
                    "example lock timeout is 1.25 times estimated proving time",
                    "testing guidance discusses five-to-ten-times maximum-price collateral",
                    "the guide warns large 50-GCycle requests may not lock under high collateral",
                ],
            },
            {
                "id": "BOUNDLESS_BROKER_CONFIGURATION",
                "url": "https://docs.boundless.network/provers/broker",
                "observations": [
                    "broker admission uses measured peak proving kHz, minimum deadline, maximum collateral, and minimum price per MCycle",
                    "illustrative minimum price configuration is 0.02 USD per MCycle",
                ],
            },
            {
                "id": "GOOGLE_CLOUD_GPU_PRICING",
                "url": "https://cloud.google.com/products/compute/gpus-pricing",
                "observations": [
                    "listed L4 GPU-only on-demand price observed as 0.56004024 USD per GPU-hour",
                ],
            },
            {
                "id": "LAMBDA_GPU_PRICING",
                "url": "https://lambda.ai/instances",
                "observations": [
                    "listed A6000 price observed as 1.09 USD per GPU-hour",
                    "listed H100 PCIe and SXM prices observed as 3.29 and 4.29 USD per GPU-hour",
                ],
            },
        ],
        "interpretation": (
            "The cited values bound source-informed scenarios. They are examples and listed prices, "
            "not measurements of ZenoProof demand, ZRPF guests, or current Boundless clearing prices."
        ),
    }


def _document() -> dict[str, Any]:
    rows, recommendation = _candidate_rows()
    workloads = _workloads()
    shocks = _shocks()
    provers = _provers()
    capacity_scenarios = _capacity_scenarios()
    return {
        "schema": SCHEMA,
        "status": "RESEARCH_ONLY_UNMOUNTED_UNSELECTED",
        "source_subject": {
            "reviewed_source_commit": REVIEWED_SOURCE_COMMIT,
            "source_pins": _source_pins(),
            "checker_bootstrap_verified": False,
        },
        "game_surface": {
            "players": [
                "proof buyer",
                "independent prover",
                "small proving cluster",
                "large proving cluster",
                "paid-priority capacity buyer",
                "permissionless proof miner",
                "beneficial-owner coalition",
                "ZenoLedger settlement authority",
            ],
            "actions": [
                "post a prefunded rising-price request",
                "bid now, wait, lock, prove, default, or decline",
                "reserve capacity or split requestor wallets",
                "reprocure after failure or use direct execution",
            ],
            "information": [
                "cycle estimate, price band, deadline, bond, verifier profile, and policy are public",
                "actual prover cost, congestion, failure correlation, and beneficial ownership require authenticated observations",
            ],
            "timing": "preflight, rising-price ramp, lock admission, proving, verification, durable publication, payment",
            "payoff": (
                "successful payment minus compute, capital, and failure downside for the prover; "
                "verified delivery value minus price and delay loss for the buyer"
            ),
        },
        "attack_query": [
            "a prover locks after too much of the headline window has elapsed",
            "a static collateral multiple excludes smaller honest provers without covering a named additional loss",
            "colluding provers wait to the maximum price",
            "one buyer exhausts priority capacity through many wallets",
            "paid priority consumes every slot and starves permissionless proof mining",
            "an illustrative benchmark is promoted as a live clearing-price forecast",
        ],
        "bounded_model": {
            "units": {
                "money": "MICRO_USD_ATOMS; 1 USD = 1,000,000 atoms",
                "throughput": "KILOCYCLES_PER_SECOND",
                "work": "MILLION_RISC_V_CYCLES",
                "probability_and_ratios": "BASIS_POINTS",
                "capacity": "ABSTRACT_CONCURRENT_SLOTS",
            },
            "formulas": [
                "proving_seconds = ceil(mcycles * 1000 / shocked_throughput_khz)",
                "reservation_price = ceil((cost_plus_margin * 10000 + failure_bps * bond) / success_bps)",
                "required_bond = max(maximum_payment, 1.25 * maximum_payment + named_delay_damage)",
                "lock_admitted only if remaining_window >= proving_seconds + publication_buffer",
                "owner demand aggregates before priority caps; unused priority capacity spills to permissionless demand",
            ],
            "workloads": [_asdict(row) for row in workloads],
            "cost_shocks": [_asdict(row) for row in shocks],
            "prover_profiles": [_asdict(row) for row in provers],
            "capacity_demand_scenarios": [_asdict(row) for row in capacity_scenarios],
            "policy_grid_count": len(rows),
            "policy_rows": rows,
            "boundary_refutations": _boundary_refutations(),
        },
        "evidence_lane": {
            "kind": "exact deterministic Python enumeration",
            "scenario_count_per_auction_policy": len(workloads) * len(shocks),
            "policy_count": len(rows),
            "auction_scenario_evaluations": len(rows) * len(workloads) * len(shocks),
            "capacity_scenario_evaluations": len(rows) * len(capacity_scenarios),
            "source_review": _source_review(),
        },
        "recommendation": {
            "status": "RESEARCH_ENVELOPE_UNSELECTED",
            **recommendation,
            "interpretation": [
                "derive collateral from named reprocurement and delay losses; never truncate a required bond to fit a prover",
                "recompute the effective remaining window when the lock is attempted",
                "bound collusive waiting through an independently benchmarked maximum price and direct-execution fallback",
                "reserve a nonzero permissionless floor and aggregate caps by beneficial owner",
                "replace source-informed priors with signed live workload, bid, latency, default, and capacity telemetry before selection",
            ],
        },
        "promotion_boundary": {
            "claim": "The exact grid identifies a falsifiable launch envelope under the declared source-informed scenarios.",
            "nonclaims": [
                "The recommended row is not a selected fee, price, deadline, collateral, or capacity profile.",
                "The scenario weights do not forecast demand, proving cost, failure, utilization, or market price.",
                "Cloud list prices omit some host, storage, bandwidth, tax, capital, and operational costs.",
                "Beneficial-owner aggregation, workload-cycle estimates, and live telemetry remain external authenticated premises.",
                "No simulation output can admit a proof, reserve capacity, pay a prover, slash a bond, or commit ZenoLedger state.",
            ],
            "selected": False,
            "mounted": False,
            "production_ready": False,
        },
    }


def _write_or_check(output_path: Path, write: bool) -> tuple[bool, dict[str, Any]]:
    document = _document()
    expected = _canonical_bytes(document)
    if write:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_bytes(expected)
    actual = output_path.read_bytes() if output_path.is_file() else b""
    ok = actual == expected
    return ok, {
        "schema": SCHEMA,
        "ok": ok,
        "output": str(output_path),
        "sha256": _sha256(expected),
        "bytes": len(expected),
        "status": document["status"],
        "selected": False,
        "mounted": False,
        "production_ready": False,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    try:
        ok, report = _write_or_check(Path(args.output).resolve(), args.write)
    except Exception as exc:
        ok = False
        report = {"schema": SCHEMA, "ok": False, "error": str(exc)}
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("PASS" if ok else "FAIL")
    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())

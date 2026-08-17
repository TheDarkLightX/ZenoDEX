from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools import check_zrpf_business_model_v1 as checker
from tools import zrpf_business_model_v1 as model

REPO_ROOT = Path(__file__).resolve().parents[1]


def _profile() -> model.ProofCostProfileV1:
    return model.ProofCostProfileV1(1_000, 200, 1, 10)


@pytest.mark.parametrize(
    ("multiplier_bps", "expected_threshold"),
    [(10_000, 172), (15_000, 277), (20_000, 400)],
)
def test_proof_batch_threshold_is_exact_at_cost_shock_boundary(
    multiplier_bps: int, expected_threshold: int
) -> None:
    assert (
        model.minimum_economic_batch_units(_profile(), multiplier_bps, 2_500)
        == expected_threshold
    )
    below = model.assess_proof_batch(
        _profile(), expected_threshold - 1, multiplier_bps, 2_500
    )
    at = model.assess_proof_batch(
        _profile(), expected_threshold, multiplier_bps, 2_500
    )
    assert below.zrpf_economic is False
    assert at.zrpf_economic is True


def test_proof_batch_rounding_excess_is_refundable_not_surplus() -> None:
    outcome = model.assess_proof_batch(_profile(), 256, 10_000, 2_500)
    assert outcome.refundable_rounding_atoms == (
        outcome.collected_resource_fee_atoms - outcome.maximum_proof_liability_atoms
    )
    assert outcome.refundable_rounding_atoms == 228


def test_first_valid_race_wastes_compute_that_a_lock_avoids() -> None:
    provers = (
        model.ProverV1("A", 70, 1, "owner-a", "gpu-a"),
        model.ProverV1("B", 80, 2, "owner-b", "gpu-b"),
        model.ProverV1("C", 95, 3, "owner-c", "gpu-c"),
        model.ProverV1("D", 110, 4, "owner-d", "gpu-d"),
    )
    race = model.first_valid_race(provers, 100)
    locked = model.reverse_dutch_lock(provers, 60, 100, 5)
    assert race.duplicate_compute_waste_atoms == 285
    assert locked.duplicate_compute_waste_atoms == 0
    assert locked.total_compute_cost_atoms == locked.useful_compute_cost_atoms == 70


def test_reverse_dutch_cartel_extraction_is_bounded_by_direct_cost_cap() -> None:
    provers = (
        model.ProverV1("A", 70, 1, "owner-a", "gpu-a"),
        model.ProverV1("B", 80, 2, "owner-b", "gpu-b"),
    )
    cartel = model.reverse_dutch_lock(
        provers, 60, 100, 5, collusive_wait=True
    )
    assert cartel.payment_atoms == 100
    assert cartel.fallback_required is False


def test_second_price_common_owner_can_raise_payment() -> None:
    provers = (
        model.ProverV1("A1", 70, 1, "owner-a", "gpu-a"),
        model.ProverV1("A2", 75, 2, "owner-a", "gpu-a2"),
        model.ProverV1("B", 120, 3, "owner-b", "gpu-b"),
    )
    outcome = model.sealed_bid_procurement(
        provers,
        {"A1": 70, "A2": 100, "B": 120},
        120,
        model.ProcurementKindV1.SECOND_PRICE,
    )
    assert outcome.winner_id == "A1"
    assert outcome.payment_atoms == 100


def test_default_bond_boundary_uses_cross_multiplied_expected_downside() -> None:
    assert model.bond_covers_default(10, 10, 0, 10_000) is True
    assert model.bond_covers_default(10, 19, 0, 5_000) is False
    assert model.bond_covers_default(10, 18, 1, 5_000) is True


def test_fee_waterfall_blocks_burn_until_every_required_gap_is_funded() -> None:
    outcome = model.allocate_fee_waterfall(
        model.FeeWaterfallInputV1(10, 0, 2, 4, 5, 1, True)
    )
    assert outcome.all_required_prefunded is False
    assert outcome.burn_atoms == 0
    assert (
        outcome.safety_atoms
        + outcome.critical_service_atoms
        + outcome.operations_atoms
        + outcome.carry_atoms
        == outcome.available_atoms
    )


def test_true_residual_burn_dominates_fixed_gross_burn_for_solvency() -> None:
    safe = model.allocate_fee_waterfall(
        model.FeeWaterfallInputV1(10, 0, 2, 4, 3, 0, True)
    )
    mutant_burn, mutant_remaining = model.gross_revenue_burn_mutant(10, 9_000)
    assert safe.burn_atoms == 1
    assert safe.all_required_prefunded is True
    assert mutant_burn == 9
    assert mutant_remaining == 1


@pytest.mark.parametrize("excess_atoms", [0, 1, 2, 3, 10, 10_001])
def test_zeno_burn_cap_never_eliminates_active_floor_excess(
    excess_atoms: int,
) -> None:
    before = model.ZDEX_ACTIVE_FLOOR_ATOMS + excess_atoms
    after = before - model.maximum_zdex_burn_atoms(before)
    assert after >= model.ZDEX_ACTIVE_FLOOR_ATOMS
    if excess_atoms:
        assert after > model.ZDEX_ACTIVE_FLOOR_ATOMS


def test_fee_credit_is_directly_wash_loss_making_below_full_fee() -> None:
    assert model.wash_round_trip_profit_atoms(100, 9_999) == -1
    assert model.wash_round_trip_profit_atoms(100, 10_000) == 0
    assert model.required_fee_credit_volume_lift_bps(500) == 527
    assert model.required_fee_credit_volume_lift_bps(1_000) == 1_112


def test_geometric_proof_bonus_never_crosses_reserve_floor() -> None:
    policy = model.ProofBonusScheduleV1(
        model.PROOF_RESERVE_INITIAL_ATOMS,
        model.PROOF_RESERVE_FLOOR_ATOMS,
        5,
    )
    outcome = model.simulate_proof_bonus(policy, 3_650)
    assert outcome.closing_reserve_atoms > policy.reserve_floor_atoms
    assert outcome.released_atoms + outcome.closing_reserve_atoms == (
        policy.opening_reserve_atoms
    )
    assert outcome.released_atoms // model.ZDEX_SCALE == 25_165_677


def test_zero_structural_shortfall_has_unbounded_subsidy_runway() -> None:
    assert model.subsidy_runway_days(30_000_000, 50_000, 0) is None


def test_esso_receipt_binds_repaired_model_and_preserved_counterexample() -> None:
    receipt = json.loads(
        (REPO_ROOT / "docs/research/ZRPF_FEE_WATERFALL_ESSO_V1.json").read_text()
    )
    model_bytes = (REPO_ROOT / receipt["model"]["path"]).read_bytes()
    assert hashlib.sha256(model_bytes).hexdigest() == receipt["model"]["sha256"]
    assert receipt["result"]["verdict"] == "VERIFIED"
    assert receipt["result"]["passed_queries"] == 12
    assert receipt["preserved_counterexample"]["id"] == (
        "PAID_PHASE_WITHOUT_PAYMENT_WITNESS"
    )


def test_business_model_artifact_is_exact_and_research_only() -> None:
    document = checker.build_document()
    observed = json.loads(
        (REPO_ROOT / "docs/research/ZRPF_BUSINESS_MODEL_V1.json").read_text()
    )
    assert observed == document
    assert observed["status"] == "RESEARCH_ONLY_ADVISORY"
    assert observed["promotion_boundary"]["production_ready"] is False


def test_business_model_cli_rejects_tampered_artifact() -> None:
    tampered_path = REPO_ROOT / "docs/research/.zrpf_business_model_tampered.json"
    document = checker.build_document()
    document["promotion_boundary"]["production_ready"] = True
    tampered_path.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")
    try:
        completed = subprocess.run(
            [
                sys.executable,
                str(REPO_ROOT / "tools/check_zrpf_business_model_v1.py"),
                "--json",
                "--output",
                str(tampered_path),
            ],
            cwd=REPO_ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
        assert completed.returncode == 1
        assert "differ" in completed.stdout
    finally:
        tampered_path.unlink(missing_ok=True)

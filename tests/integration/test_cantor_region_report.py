from __future__ import annotations

from src.integration.cantor_region_report import build_cantor_region_report, depth_cube_count
from src.integration.cantor_prefix_algebra import CantorPrefixRegion
from src.integration.resource_load_shedding_regret_guard_regions import build_resource_load_shedding_regret_guard_regions
from src.integration.zusd_recovery_mode_gate_regions import build_zusd_recovery_mode_gate_regions


def test_depth_cube_count_matches_basic_cylinders() -> None:
    assert depth_cube_count(CantorPrefixRegion.top(), 3) == 8
    assert depth_cube_count(CantorPrefixRegion.from_strings(["0*"]), 3) == 4
    assert depth_cube_count(CantorPrefixRegion.from_strings(["00*", "11*"]), 3) == 4


def test_cantor_region_report_zusd_recovery_partition_and_refinements() -> None:
    regions = build_zusd_recovery_mode_gate_regions()
    report = build_cantor_region_report(
        depth=6,
        regions={
            "risky_action_allowed": regions.risky_action_allowed,
            "safe_non_risky_action_allowed": regions.safe_non_risky_action_allowed,
            "denied": regions.denied,
            "action_allowed": regions.action_allowed,
            "blocked_by_recovery": regions.blocked_by_recovery,
        },
        partition=("risky_action_allowed", "safe_non_risky_action_allowed", "denied"),
        refinements=(("risky_action_allowed", "action_allowed"), ("blocked_by_recovery", "denied")),
        disjoint_pairs=(("risky_action_allowed", "denied"), ("safe_non_risky_action_allowed", "denied")),
    )

    assert report.partition_total is True
    assert sum(stat.depth_cube_count for stat in report.regions[:3]) == 64
    assert all(rel.holds for rel in report.disjoint_pairs)
    assert report.refinements[0].holds is True


def test_cantor_region_report_resource_load_shedding_partition_and_refinements() -> None:
    regions = build_resource_load_shedding_regret_guard_regions()
    report = build_cantor_region_report(
        depth=12,
        regions={
            "proof_gated": regions.proof_gated_final_admission_ok,
            "admitted_without_proof": regions.admitted_without_proof,
            "denied": regions.denied,
            "final": regions.final_admission_ok,
            "normal_only": regions.normal_only,
            "shed_only": regions.shed_only,
        },
        partition=("proof_gated", "admitted_without_proof", "denied"),
        refinements=(("proof_gated", "final"),),
        disjoint_pairs=(("normal_only", "shed_only"),),
    )

    counts = {stat.name: stat.depth_cube_count for stat in report.regions}
    assert report.partition_total is True
    assert counts["proof_gated"] + counts["admitted_without_proof"] + counts["denied"] == 4096
    assert report.refinements[0].holds is True
    assert report.disjoint_pairs[0].holds is True

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .cantor_region_morphism_receipts import (
    CantorRegionProductProjectionReceipt,
    build_cantor_region_product_projection_receipt,
)
from .cantor_region_report import CantorRegionRelation, CantorRegionReport, CantorRegionStats, build_cantor_region_report
from .exact_out_many_pool_adaptive_liveness_regions import build_exact_out_many_pool_adaptive_liveness_regions
from .resource_load_shedding_regret_guard_regions import build_resource_load_shedding_regret_guard_regions
from .settlement_witness_lifecycle_regions import build_settlement_witness_lifecycle_regions
from .zusd_recovery_mode_gate_regions import build_zusd_recovery_mode_gate_regions


CANTOR_REGION_ASSURANCE_BUNDLE_SCHEMA = "zenodex/cantor-region-assurance-bundle/v1"


@dataclass(frozen=True)
class CantorRegionAssuranceSurface:
    name: str
    depth: int
    report: CantorRegionReport

    def to_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "depth": self.depth,
            "report": _report_payload(self.report),
        }


@dataclass(frozen=True)
class CantorRegionAssuranceBundle:
    surfaces: tuple[CantorRegionAssuranceSurface, ...]
    product_receipts: tuple[CantorRegionProductProjectionReceipt, ...]
    schema: str = CANTOR_REGION_ASSURANCE_BUNDLE_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != CANTOR_REGION_ASSURANCE_BUNDLE_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if not self.surfaces:
            raise ValueError("surfaces must be non-empty")

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "surface_count": len(self.surfaces),
            "product_receipt_count": len(self.product_receipts),
            "surfaces": [surface.to_dict() for surface in self.surfaces],
            "product_receipts": [receipt.to_dict() for receipt in self.product_receipts],
        }


def _stats_payload(stats: CantorRegionStats) -> dict[str, object]:
    return {
        "name": stats.name,
        "prefix_count": stats.prefix_count,
        "depth": stats.depth,
        "depth_cube_count": stats.depth_cube_count,
        "prefixes": list(stats.prefixes),
    }


def _relation_payload(relation: CantorRegionRelation) -> dict[str, object]:
    return {
        "left": relation.left,
        "right": relation.right,
        "holds": relation.holds,
        "kind": relation.kind,
    }


def _report_payload(report: CantorRegionReport) -> dict[str, object]:
    return {
        "depth": report.depth,
        "regions": [_stats_payload(stats) for stats in report.regions],
        "partition_names": list(report.partition_names),
        "partition_total": report.partition_total,
        "refinements": [_relation_payload(relation) for relation in report.refinements],
        "disjoint_pairs": [_relation_payload(relation) for relation in report.disjoint_pairs],
    }


def build_default_cantor_region_assurance_bundle() -> CantorRegionAssuranceBundle:
    settlement = build_settlement_witness_lifecycle_regions()
    exact_out = build_exact_out_many_pool_adaptive_liveness_regions()
    resource = build_resource_load_shedding_regret_guard_regions()
    zusd = build_zusd_recovery_mode_gate_regions()

    surfaces = (
        CantorRegionAssuranceSurface(
            name="settlement_witness_lifecycle",
            depth=7,
            report=build_cantor_region_report(
                depth=7,
                regions={
                    "accepted": settlement.accepted,
                    "rejected": settlement.rejected,
                    "invalid": settlement.invalid,
                    "lifecycle_ok": settlement.lifecycle_ok,
                    "witness_coherent": settlement.witness_coherent,
                },
                partition=("accepted", "rejected", "invalid"),
                refinements=(("accepted", "lifecycle_ok"), ("rejected", "lifecycle_ok")),
                disjoint_pairs=(("accepted", "rejected"), ("accepted", "invalid"), ("rejected", "invalid")),
            ),
        ),
        CantorRegionAssuranceSurface(
            name="exact_out_adaptive_liveness",
            depth=14,
            report=build_cantor_region_report(
                depth=14,
                regions={
                    "liveness_ok": exact_out.liveness_ok,
                    "budget_blocked": exact_out.budget_blocked,
                    "invalid": exact_out.invalid,
                    "coherent_surface": exact_out.coherent_surface,
                    "returned_success": exact_out.returned_success,
                    "explicit_failure": exact_out.explicit_failure,
                },
                partition=("liveness_ok", "budget_blocked", "invalid"),
                refinements=(("liveness_ok", "coherent_surface"), ("budget_blocked", "coherent_surface")),
                disjoint_pairs=(("liveness_ok", "budget_blocked"),),
            ),
        ),
        CantorRegionAssuranceSurface(
            name="resource_load_shedding_regret_guard",
            depth=12,
            report=build_cantor_region_report(
                depth=12,
                regions={
                    "proof_gated": resource.proof_gated_final_admission_ok,
                    "admitted_without_proof": resource.admitted_without_proof,
                    "denied": resource.denied,
                    "final": resource.final_admission_ok,
                    "normal_only": resource.normal_only,
                    "shed_only": resource.shed_only,
                },
                partition=("proof_gated", "admitted_without_proof", "denied"),
                refinements=(("proof_gated", "final"),),
                disjoint_pairs=(("normal_only", "shed_only"),),
            ),
        ),
        CantorRegionAssuranceSurface(
            name="zusd_recovery_mode_gate",
            depth=6,
            report=build_cantor_region_report(
                depth=6,
                regions={
                    "risky_action_allowed": zusd.risky_action_allowed,
                    "safe_non_risky_action_allowed": zusd.safe_non_risky_action_allowed,
                    "denied": zusd.denied,
                    "action_allowed": zusd.action_allowed,
                    "recovery_blocked_request": zusd.recovery_blocked_request,
                },
                partition=("risky_action_allowed", "safe_non_risky_action_allowed", "denied"),
                refinements=(("risky_action_allowed", "action_allowed"), ("recovery_blocked_request", "denied")),
                disjoint_pairs=(("risky_action_allowed", "denied"), ("safe_non_risky_action_allowed", "denied")),
            ),
        ),
    )

    product_receipts = (
        build_cantor_region_product_projection_receipt(
            product_name="zusd_action_allowed_x_resource_final_admission",
            left_name="zusd_action_allowed",
            left_region=zusd.action_allowed,
            left_depth=6,
            right_name="resource_final_admission",
            right_region=resource.final_admission_ok,
            right_depth=12,
        ),
    )

    return CantorRegionAssuranceBundle(surfaces=surfaces, product_receipts=product_receipts)

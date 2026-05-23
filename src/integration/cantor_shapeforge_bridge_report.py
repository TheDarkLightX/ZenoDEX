from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any

from .cantor_region_assurance_bundle import CantorRegionAssuranceBundle, build_default_cantor_region_assurance_bundle
from .cantor_region_backend_invariance_receipt import build_cantor_region_backend_invariance_receipt


SHAPEFORGE_CANTOR_BRIDGE_REPORT_SCHEMA = "zenodex/shapeforge-cantor-bridge-report/v1"
DEFAULT_SHAPEFORGE_WORLD_MODEL_PATH = Path("docs/zenodex/world_model_promoted/zenodex_world_model.seed.json")


_SURFACE_BRIDGE_CONFIG: dict[str, dict[str, object]] = {
    "settlement_witness_lifecycle": {
        "primary_slice_id": "settlement_strong_validation",
        "related_slice_ids": (),
        "sources": (
            "src/integration/settlement_witness_lifecycle_regions.py",
            "src/integration/cantor_region_assurance_bundle.py",
        ),
    },
    "exact_out_adaptive_liveness": {
        "primary_slice_id": "exact_out_audited_bounds_contract",
        "related_slice_ids": ("exact_out_adaptive_gate",),
        "sources": (
            "src/integration/exact_out_many_pool_adaptive_liveness_regions.py",
            "src/integration/cantor_region_assurance_bundle.py",
        ),
    },
    "zusd_recovery_mode_gate": {
        "primary_slice_id": "zusd_oracle_pending_gate",
        "related_slice_ids": (),
        "sources": (
            "src/integration/zusd_recovery_mode_gate_regions.py",
            "src/integration/cantor_region_assurance_bundle.py",
        ),
    },
    "resource_load_shedding_regret_guard": {
        "primary_slice_id": "resource_load_shedding_regret_guard",
        "related_slice_ids": (),
        "sources": (
            "src/integration/resource_load_shedding_regret_guard_regions.py",
            "src/integration/cantor_region_assurance_bundle.py",
        ),
    },
}


@dataclass(frozen=True)
class CantorShapeForgeCandidateEvidence:
    claim: str
    evidence_class: str
    source: str

    def to_dict(self) -> dict[str, object]:
        return {
            "claim": self.claim,
            "evidence_class": self.evidence_class,
            "source": self.source,
        }


@dataclass(frozen=True)
class CantorShapeForgeMappedSurface:
    surface_name: str
    primary_slice_id: str
    current_slice_status: str
    related_slice_ids: tuple[str, ...]
    partition_total: bool
    region_names: tuple[str, ...]
    refinement_pairs: tuple[tuple[str, str], ...]
    disjoint_pairs: tuple[tuple[str, str], ...]
    suggested_sources: tuple[str, ...]
    suggested_evidence: tuple[CantorShapeForgeCandidateEvidence, ...]

    def to_dict(self) -> dict[str, object]:
        return {
            "surface_name": self.surface_name,
            "primary_slice_id": self.primary_slice_id,
            "current_slice_status": self.current_slice_status,
            "related_slice_ids": list(self.related_slice_ids),
            "partition_total": self.partition_total,
            "region_names": list(self.region_names),
            "refinement_pairs": [[left, right] for left, right in self.refinement_pairs],
            "disjoint_pairs": [[left, right] for left, right in self.disjoint_pairs],
            "suggested_sources": list(self.suggested_sources),
            "suggested_evidence": [item.to_dict() for item in self.suggested_evidence],
        }


@dataclass(frozen=True)
class CantorShapeForgeUnmappedSurface:
    surface_name: str
    reason: str
    suggested_improvement_target: str
    suggested_sources: tuple[str, ...]

    def to_dict(self) -> dict[str, object]:
        return {
            "surface_name": self.surface_name,
            "reason": self.reason,
            "suggested_improvement_target": self.suggested_improvement_target,
            "suggested_sources": list(self.suggested_sources),
        }


@dataclass(frozen=True)
class CantorShapeForgeBridgeReport:
    world_model_id: str
    world_model_path: str
    bundle_schema: str
    backend_invariance: dict[str, object]
    mapped_surfaces: tuple[CantorShapeForgeMappedSurface, ...]
    unmapped_surfaces: tuple[CantorShapeForgeUnmappedSurface, ...]
    schema: str = SHAPEFORGE_CANTOR_BRIDGE_REPORT_SCHEMA

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "world_model_id": self.world_model_id,
            "world_model_path": self.world_model_path,
            "bundle_schema": self.bundle_schema,
            "backend_invariance": dict(self.backend_invariance),
            "mapped_surface_count": len(self.mapped_surfaces),
            "unmapped_surface_count": len(self.unmapped_surfaces),
            "mapped_surfaces": [surface.to_dict() for surface in self.mapped_surfaces],
            "unmapped_surfaces": [surface.to_dict() for surface in self.unmapped_surfaces],
        }


def _load_world_model(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"world model must be a JSON object: {path}")
    return data


def _slice_status_map(world_model: dict[str, Any]) -> dict[str, str]:
    out: dict[str, str] = {}
    for slice_obj in world_model.get("slices", []):
        if not isinstance(slice_obj, dict):
            continue
        slice_id = slice_obj.get("slice_id")
        status = slice_obj.get("status")
        if isinstance(slice_id, str) and isinstance(status, str):
            out[slice_id] = status
    return out


def _default_region_source(surface_name: str) -> str:
    candidate = Path("src/integration") / f"{surface_name}_regions.py"
    return str(candidate) if candidate.exists() else "src/integration"


def _candidate_evidence_for_surface(surface_name: str) -> tuple[CantorShapeForgeCandidateEvidence, ...]:
    if surface_name == "settlement_witness_lifecycle":
        return (
            CantorShapeForgeCandidateEvidence(
                claim="A replayable Cantor-region assurance bundle shows that the bounded settlement witness lifecycle shell partitions exactly into accepted, rejected, and invalid regions, and that accepted and rejected each refine lifecycle_ok.",
                evidence_class="contract",
                source="src/integration/cantor_region_assurance_bundle.py",
            ),
        )
    if surface_name == "exact_out_adaptive_liveness":
        return (
            CantorShapeForgeCandidateEvidence(
                claim="A replayable Cantor-region assurance bundle shows that the bounded exact-out adaptive-liveness shell partitions exactly into liveness_ok, budget_blocked, and invalid regions, and that the first two regions each refine coherent_surface.",
                evidence_class="contract",
                source="src/integration/cantor_region_assurance_bundle.py",
            ),
        )
    if surface_name == "zusd_recovery_mode_gate":
        return (
            CantorShapeForgeCandidateEvidence(
                claim="A replayable Cantor-region assurance bundle shows that the bounded zUSD recovery-mode gate shell partitions exactly into risky_action_allowed, safe_non_risky_action_allowed, and denied regions, with risky_action_allowed refining action_allowed and recovery_blocked_request refining denied.",
                evidence_class="contract",
                source="src/integration/cantor_region_assurance_bundle.py",
            ),
        )
    if surface_name == "resource_load_shedding_regret_guard":
        return (
            CantorShapeForgeCandidateEvidence(
                claim="A replayable Cantor-region assurance bundle shows that the bounded resource load-shedding shell partitions exactly into proof_gated, admitted_without_proof, and denied regions.",
                evidence_class="contract",
                source="src/integration/cantor_region_assurance_bundle.py",
            ),
            CantorShapeForgeCandidateEvidence(
                claim="Within the same bounded shell, proof_gated admission refines final admission, and the normal-only and shed-only path regions are disjoint while their union recovers final admission.",
                evidence_class="contract",
                source="src/integration/resource_load_shedding_regret_guard_regions.py",
            ),
        )
    return ()


def build_cantor_shapeforge_bridge_report(
    *,
    world_model_path: Path = DEFAULT_SHAPEFORGE_WORLD_MODEL_PATH,
    bundle: CantorRegionAssuranceBundle | None = None,
) -> CantorShapeForgeBridgeReport:
    world_model = _load_world_model(world_model_path)
    world_model_id = world_model.get("world_model_id")
    if not isinstance(world_model_id, str) or not world_model_id:
        raise ValueError(f"world model id missing in {world_model_path}")

    slice_status = _slice_status_map(world_model)
    assurance_bundle = bundle or build_default_cantor_region_assurance_bundle()
    backend_invariance = build_cantor_region_backend_invariance_receipt().to_dict()

    mapped_surfaces: list[CantorShapeForgeMappedSurface] = []
    unmapped_surfaces: list[CantorShapeForgeUnmappedSurface] = []

    for surface in assurance_bundle.surfaces:
        config = _SURFACE_BRIDGE_CONFIG.get(surface.name)
        if config is None:
            unmapped_surfaces.append(
                CantorShapeForgeUnmappedSurface(
                    surface_name=surface.name,
                    reason="no promoted ShapeForge slice currently names this bounded shell",
                    suggested_improvement_target="world-model promotion",
                    suggested_sources=(
                        "src/integration/cantor_region_assurance_bundle.py",
                        _default_region_source(surface.name),
                    ),
                )
            )
            continue

        primary_slice_id = str(config["primary_slice_id"])
        if primary_slice_id not in slice_status:
            raise ValueError(
                f"configured ShapeForge slice {primary_slice_id!r} missing from {world_model_path}"
            )
        related_slice_ids = tuple(str(item) for item in config["related_slice_ids"])
        missing_related = [sid for sid in related_slice_ids if sid not in slice_status]
        if missing_related:
            raise ValueError(
                f"configured related ShapeForge slices missing from {world_model_path}: {missing_related}"
            )

        mapped_surfaces.append(
            CantorShapeForgeMappedSurface(
                surface_name=surface.name,
                primary_slice_id=primary_slice_id,
                current_slice_status=slice_status[primary_slice_id],
                related_slice_ids=related_slice_ids,
                partition_total=bool(surface.report.partition_total),
                region_names=tuple(region.name for region in surface.report.regions),
                refinement_pairs=tuple((rel.left, rel.right) for rel in surface.report.refinements),
                disjoint_pairs=tuple((rel.left, rel.right) for rel in surface.report.disjoint_pairs),
                suggested_sources=tuple(str(item) for item in config["sources"]),
                suggested_evidence=_candidate_evidence_for_surface(surface.name),
            )
        )

    return CantorShapeForgeBridgeReport(
        world_model_id=world_model_id,
        world_model_path=str(world_model_path),
        bundle_schema=assurance_bundle.schema,
        backend_invariance=backend_invariance,
        mapped_surfaces=tuple(mapped_surfaces),
        unmapped_surfaces=tuple(unmapped_surfaces),
    )

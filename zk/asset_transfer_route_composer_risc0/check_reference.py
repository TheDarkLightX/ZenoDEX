"""Replay exported Rust route roots through the independent Python core.

This bounded fixture checker authenticates no input and grants no authority.
Run from the repository root with the exported reference JSON path.
"""

from __future__ import annotations

import dataclasses
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from src.core import global_economic_proof_v1 as proof
from src.core import global_settlement_types_v1 as abi
from src.core.global_economic_state_decoder_v1 import decode_global_economic_state_v1
from src.core.global_economic_state_effect_refinement_v1 import (
    GlobalEconomicStateEffectRefinementCandidateV1,
    refine_route_global_economic_state_effects_v1,
)
from src.core.route_global_state_projection_v1 import (
    RouteGlobalStateProjectionCandidateV1,
    project_route_global_state_v1,
)


def record(cls, raw, *, enums=None):
    """Explicit flat ABI record decoding for this test artifact only."""
    data = dict(raw)
    if data.pop("schema", None) != abi.GLOBAL_SETTLEMENT_ABI_V1 and "schema" in raw:
        raise ValueError("reference schema")
    if set(data) != {field.name for field in dataclasses.fields(cls)}:
        raise ValueError(f"reference fields: {cls.__name__}")
    for key, value in data.items():
        if isinstance(value, list):
            data[key] = tuple(value)
    for key, kind in (enums or {}).items():
        value = data[key]
        data[key] = tuple(kind(item) for item in value) if isinstance(value, tuple) else kind(value)
    return cls(**data)


def profile(input_value):
    common = {"status": abi.ReleaseStatusV1, "evidence_statuses": abi.EvidenceStatusV1}
    lanes = abi.LaneRegistryV1(
        tuple(
            record(abi.LaneModuleReleaseV1, row, enums={**common, "lane_id": abi.LaneIdV1})
            for row in input_value["lanes"]["releases"]
        )
    )
    coordinators = abi.LaneCoordinatorRegistryV1(
        tuple(
            record(abi.LaneCoordinatorReleaseV1, row, enums={**common, "lane_id": abi.LaneIdV1})
            for row in input_value["coordinators"]["releases"]
        )
    )
    routes = abi.RouteRegistryV1(
        tuple(
            record(abi.RouteReleaseV1, row, enums={**common, "ordered_lanes": abi.LaneIdV1})
            for row in input_value["routes"]["routes"]
        )
    )
    value = dict(input_value["profile"])
    for key, registry in [
        ("lane_registry_root", lanes),
        ("lane_coordinator_registry_root", coordinators),
        ("route_registry_root", routes),
    ]:
        if value.pop(key) != registry.registry_root:
            raise ValueError("reference registry root")
    value.update(lane_registry=lanes, lane_coordinator_registry=coordinators, route_registry=routes)
    return record(abi.EconomicProfileSnapshotV1, value, enums={"status": abi.ProfileStatusV1})


def check(path: Path):
    if path.stat().st_size > 8 * 1024 * 1024:
        raise ValueError("reference size")

    def closed_pairs(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate reference field")
            result[key] = value
        return result

    data = json.loads(path.read_bytes(), object_pairs_hook=closed_pairs)
    value = data["input"]
    selected = profile(value)
    pre = decode_global_economic_state_v1(value["pre_state"])
    post = decode_global_economic_state_v1(value["post_state"])
    route = record(proof.RouteCompositionJournalV1, data["route_journal"])
    lane = record(
        proof.LaneCompositionJournalV1, data["lane_journal"], enums={"lane_id": abi.LaneIdV1}
    )
    occurrence = record(proof.EconomicCommandOccurrenceV1, value["occurrence"])
    effects = dict(data["effect_plan"])
    effects.pop("schema")
    for key, cls, enums in [
        ("rows", abi.EconomicEffectRowV1, {"kind": abi.EconomicEffectKindV1}),
        ("asset_conservation", abi.AssetConservationRowV1, {}),
        ("fee_conservation", abi.FeeConservationRowV1, {}),
        ("lane_writes", abi.LaneWriteV1, {"lane_id": abi.LaneIdV1}),
        ("external_outbox_enqueue", abi.ExternalOutboxEnqueueV1, {}),
    ]:
        effects[key] = tuple(record(cls, row, enums=enums) for row in effects[key])
    effects["occurrence_consumptions"] = tuple(effects["occurrence_consumptions"])
    plan = abi.GlobalEconomicEffectPlanV1(**effects)
    projected = project_route_global_state_v1(
        RouteGlobalStateProjectionCandidateV1(
            selected, selected.route_registry.routes[0], (lane,), route, pre, post
        )
    )
    candidate = GlobalEconomicStateEffectRefinementCandidateV1(
        pre, post, plan, (occurrence,), (route,)
    )
    refined = refine_route_global_economic_state_effects_v1(candidate)
    if (
        projected.projection_root != data["projection_root"]
        or refined.refinement_root != data["refinement_root"]
    ):
        raise ValueError("Python/Rust semantic root mismatch")
    if {row.owner: row.amount_atoms for row in post.balances} != {
        "alice": 68,
        "bob": 40,
        "treasury": 7,
    }:
        raise ValueError("independent transfer arithmetic")
    altered_rows = list(post.balances)
    altered_rows[0] = dataclasses.replace(
        altered_rows[0], amount_atoms=altered_rows[0].amount_atoms + 1
    )
    altered_rows[1] = dataclasses.replace(
        altered_rows[1], amount_atoms=altered_rows[1].amount_atoms - 1
    )
    try:
        refine_route_global_economic_state_effects_v1(
            dataclasses.replace(
                candidate, post_state=dataclasses.replace(post, balances=tuple(altered_rows))
            )
        )
    except ValueError:
        pass
    else:
        raise ValueError("conserved unauthorized allocation mutant survived")
    print(
        "PASS: exact Python/Rust projection and refinement, independent amounts, conserved misattribution rejection"
    )


if __name__ == "__main__":
    check(Path(sys.argv[1]))

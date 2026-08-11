#!/usr/bin/env python3
"""Fail-closed checker for the ZRPF ShapeForge receipt and lane-output slices.

This checker validates the evidence-axis authority refinement with exact opaque
route-witness and public assumption-root pairing, two operator-axis
module-output increments, one guard-axis release-route increment, one
evidence-axis module-receipt increment, one evidence-axis receipt-backed lane
composition increment, one evidence-axis governed route-receipt increment, and
exact source pins. A sibling research crate emits a direct one-through-eight
route recursive receipt for structural plumbing evidence. This checker does not
mount a writer, prove the structural test leaf's economics, or grant publication
authority.
"""

from __future__ import annotations

import argparse
import json
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

if __package__:
    from . import zrpf_shapeforge_contract_support_v1 as _support
else:
    import zrpf_shapeforge_contract_support_v1 as _support  # type: ignore[no-redef]

ContractError = _support.ContractError
_exact_keys = _support.exact_keys
_ids = _support.ids
load_artifacts = _support.load_artifacts
load_json = _support.load_json
_nonempty_string = _support.nonempty_string
_nonempty_unique_strings = _support.nonempty_unique_strings
_objects_with = _support.objects_with
_validate_source_pins = _support.validate_source_pins

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONTRACT = REPO_ROOT / "docs/research/zrpf_shapeforge_global_epoch_admission_v1.json"

CONTRACT_SCHEMA = "zenodex/zrpf-shapeforge-global-epoch-admission/v1"
CHECK_SCHEMA = "zenodex/zrpf-shapeforge-global-epoch-admission-check/v1"
STATUS = "RESEARCH_ONLY_UNMOUNTED"
WORLD_MODEL_ID = "zenodex_shape_reference_v3"
SLICE_ID = "global_epoch_receipt_admission"
SLICE_STATUS = "contract"
AXIS = "evidence"
TARGET_EVIDENCE_CLASS = "contract"
SCENARIO_ID = "scenario_global_epoch_structural_journal_without_receipt_verifier"
CORPUS_SCENARIO_ID = SCENARIO_ID
TACTIC_ID = "refine_economic_evidence_into_publication_authority"
HYPOTHESIS_ID = "synthetic_structural_journal_authorizes_global_epoch_v1"
INVARIANT_ID = "global_publication_requires_release_selected_receipt_and_full_binding"
ASSET_MODULE_SLICE_ID = "asset_transfer_lane_module_output"
ASSET_MODULE_SLICE_STATUS = "contract"
ASSET_MODULE_AXIS = "operator"
ASSET_MODULE_SCENARIO_ID = "scenario_asset_transfer_host_fixture_rebinding"
ASSET_MODULE_HYPOTHESIS_ID = "host_fixture_private_port_equivalent_to_module_owned_output_v1"
MANAGED_LIFECYCLE_SLICE_ID = "managed_asset_lifecycle_lane_module_output"
MANAGED_LIFECYCLE_SCENARIO_ID = "scenario_managed_asset_lifecycle_host_fixture_rebinding"
MANAGED_LIFECYCLE_HYPOTHESIS_ID = "managed_lifecycle_host_fixture_private_port_equivalent_v1"
RELEASE_ROUTE_SLICE_ID = "lane_module_release_route_binding"
RELEASE_ROUTE_AXIS = "guard"
RELEASE_ROUTE_SCENARIO_ID = "scenario_managed_issue_occurrence_relabels_burn_output"
RELEASE_ROUTE_HYPOTHESIS_ID = "occurrence_id_alone_binds_managed_command_semantics_v1"
RELEASE_ROUTE_INVARIANT_ID = (
    "lane_module_release_route_binding_requires_exact_input_output_and_occurrence_semantics"
)
MODULE_RECEIPT_SLICE_ID = "lane_module_receipt_verification"
MODULE_RECEIPT_AXIS = "evidence"
MODULE_RECEIPT_SCENARIO_ID = "scenario_structural_lane_binding_without_module_receipt_verification"
MODULE_RECEIPT_HYPOTHESIS_ID = "structural_lane_binding_authorizes_verified_module_v1"
MODULE_RECEIPT_INVARIANT_ID = (
    "verified_lane_module_transition_requires_release_image_exact_journal_and_receipt"
)
RECEIPT_BACKED_LANE_SLICE_ID = "receipt_backed_asset_lane_composition"
RECEIPT_BACKED_LANE_AXIS = "evidence"
RECEIPT_BACKED_LANE_SCENARIO_ID = "scenario_valid_module_receipt_substitutes_different_lane_journal"
RECEIPT_BACKED_LANE_HYPOTHESIS_ID = "valid_module_receipt_authorizes_different_lane_journal_v1"
RECEIPT_BACKED_LANE_INVARIANT_ID = (
    "receipt_backed_lane_composition_requires_exact_verified_module_journal"
)
ROUTE_COMPOSITION_SLICE_ID = "route_composition_receipt_verification"
ROUTE_COMPOSITION_AXIS = "evidence"
ROUTE_COMPOSITION_SCENARIO_ID = "scenario_verified_lane_witness_substitutes_different_route_journal"
ROUTE_COMPOSITION_HYPOTHESIS_ID = (
    "valid_verified_lane_witness_authorizes_different_route_journal_v1"
)
ROUTE_COMPOSITION_INVARIANT_ID = (
    "verified_route_composition_requires_governed_image_exact_ordered_lane_witnesses_and_receipt"
)
NONCLAIM = (
    "the ShapeForge refinement contract does not authenticate or mount a cryptographic "
    "verifier implementation, durable publisher, route, migration, or production authority"
)

ROOT_KEYS = {
    "schema",
    "status",
    "production_authority",
    "world_model_id",
    "phi",
    "implemented_deltas",
    "required_artifacts",
    "source_pins",
    "nonclaims",
}
PHI_KEYS = {
    "slice_id",
    "axis",
    "improvement_target",
    "claim",
    "target_evidence_class",
    "state_variables",
    "operators",
    "guards",
    "observables",
    "canonical_keys",
    "evidence",
    "gaps",
    "negative_knowledge",
    "shape_delta",
}
ARTIFACT_KEYS = {"name", "path"}
EVIDENCE_KEYS = {"claim", "class", "source"}
DELTA_KEYS = {"slice_id", "axis", "improvement_target", "status", "claim"}
EVIDENCE_CLASSES = {"proved", "contract", "implemented", "tested_discovery", "hypothesis"}
MODULE_SPECS = (
    {
        "label": "asset-module",
        "slice_id": ASSET_MODULE_SLICE_ID,
        "scenario_id": ASSET_MODULE_SCENARIO_ID,
        "hypothesis_id": ASSET_MODULE_HYPOTHESIS_ID,
        "axis": ASSET_MODULE_AXIS,
        "invariant_id": INVARIANT_ID,
    },
    {
        "label": "managed-lifecycle",
        "slice_id": MANAGED_LIFECYCLE_SLICE_ID,
        "scenario_id": MANAGED_LIFECYCLE_SCENARIO_ID,
        "hypothesis_id": MANAGED_LIFECYCLE_HYPOTHESIS_ID,
        "axis": ASSET_MODULE_AXIS,
        "invariant_id": INVARIANT_ID,
    },
    {
        "label": "release-route",
        "slice_id": RELEASE_ROUTE_SLICE_ID,
        "scenario_id": RELEASE_ROUTE_SCENARIO_ID,
        "hypothesis_id": RELEASE_ROUTE_HYPOTHESIS_ID,
        "axis": RELEASE_ROUTE_AXIS,
        "invariant_id": RELEASE_ROUTE_INVARIANT_ID,
    },
    {
        "label": "module-receipt",
        "slice_id": MODULE_RECEIPT_SLICE_ID,
        "scenario_id": MODULE_RECEIPT_SCENARIO_ID,
        "hypothesis_id": MODULE_RECEIPT_HYPOTHESIS_ID,
        "axis": MODULE_RECEIPT_AXIS,
        "invariant_id": MODULE_RECEIPT_INVARIANT_ID,
    },
    {
        "label": "receipt-backed-lane",
        "slice_id": RECEIPT_BACKED_LANE_SLICE_ID,
        "scenario_id": RECEIPT_BACKED_LANE_SCENARIO_ID,
        "hypothesis_id": RECEIPT_BACKED_LANE_HYPOTHESIS_ID,
        "axis": RECEIPT_BACKED_LANE_AXIS,
        "invariant_id": RECEIPT_BACKED_LANE_INVARIANT_ID,
    },
    {
        "label": "route-composition",
        "slice_id": ROUTE_COMPOSITION_SLICE_ID,
        "scenario_id": ROUTE_COMPOSITION_SCENARIO_ID,
        "hypothesis_id": ROUTE_COMPOSITION_HYPOTHESIS_ID,
        "axis": ROUTE_COMPOSITION_AXIS,
        "invariant_id": ROUTE_COMPOSITION_INVARIANT_ID,
    },
)

EXPECTED_ARTIFACTS = {
    "world_model": "docs/zenodex/shapeforge_promoted/zenodex_world_model.seed.json",
    "tactic_bank": "docs/zenodex/shapeforge_promoted/tactic_bank.seed.json",
    "scenario_corpus": "docs/zenodex/shapeforge_promoted/scenario_corpus.seed.json",
    "development_import": "docs/zenodex/shapeforge_promoted/development_import_bundle.json",
    "negative_knowledge": "docs/zenodex/shapeforge_promoted/zenodex_negative_knowledge.seed.json",
}
EXPECTED_PHI_LISTS = {
    "state_variables": [
        "economic_profile",
        "epoch_certificate",
        "ordered_route_journals",
        "ordered_route_assumption_roots",
        "ordered_verified_routes",
        "ordered_route_effect_plans",
        "effect_plan",
        "receipt_bytes",
        "release_selected_receipt_verifier",
        "body_and_state",
        "ledger_head",
    ],
    "operators": ["verify_economic_epoch", "commit_verified_economic_epoch"],
    "guards": [
        "active_governed_profile_route",
        "exact_epoch_binding",
        "exact_verified_route_witnesses",
        "exact_route_assumption_roots",
        "exact_route_effect_plan_aggregation",
        "release_selected_succinct_receipt",
        "opaque_verified_epoch_only",
        "atomic_head_profile_body_binding",
    ],
    "observables": ["verification_outcome", "commit_outcome", "published_epoch_record"],
    "canonical_keys": ["economic_occurrence_position"],
    "negative_knowledge": [HYPOTHESIS_ID],
}


def _validate_phi(phi: Any, errors: list[str]) -> Mapping[str, Any] | None:
    if not _exact_keys(phi, PHI_KEYS, "phi", errors):
        return None
    assert isinstance(phi, Mapping)
    expected_scalars = {
        "slice_id": SLICE_ID,
        "axis": AXIS,
        "improvement_target": "contract strengthening",
        "target_evidence_class": TARGET_EVIDENCE_CLASS,
    }
    for key, scalar_expected in expected_scalars.items():
        if phi.get(key) != scalar_expected:
            errors.append(f"phi.{key} must equal {scalar_expected}")
    _nonempty_string(phi.get("claim"), "phi.claim", errors)
    for key, expected_list in EXPECTED_PHI_LISTS.items():
        if phi.get(key) != expected_list:
            errors.append(f"phi.{key} must equal the closed required list")
    for key in ("gaps", "shape_delta"):
        _nonempty_unique_strings(phi.get(key), f"phi.{key}", errors)
    evidence = phi.get("evidence")
    if not isinstance(evidence, list) or not evidence:
        errors.append("phi.evidence must be a nonempty list")
    else:
        for index, item in enumerate(evidence):
            label = f"phi.evidence[{index}]"
            if not _exact_keys(item, EVIDENCE_KEYS, label, errors):
                continue
            assert isinstance(item, Mapping)
            _nonempty_string(item.get("claim"), f"{label}.claim", errors)
            _nonempty_string(item.get("source"), f"{label}.source", errors)
            if item.get("class") not in EVIDENCE_CLASSES:
                errors.append(f"{label}.class is not closed")
    return phi


def _validate_artifact_manifest(contract: Mapping[str, Any], errors: list[str]) -> None:
    rows = contract.get("required_artifacts")
    if not isinstance(rows, list):
        errors.append("required_artifacts must be a list")
        return
    actual: dict[str, str] = {}
    for index, row in enumerate(rows):
        if not _exact_keys(row, ARTIFACT_KEYS, f"required_artifacts[{index}]", errors):
            continue
        assert isinstance(row, Mapping)
        name = row.get("name")
        path = row.get("path")
        if not isinstance(name, str) or not isinstance(path, str):
            errors.append(f"required_artifacts[{index}] fields must be strings")
            continue
        if name in actual:
            errors.append(f"required_artifacts contains duplicate name {name}")
        actual[name] = path
    if actual != EXPECTED_ARTIFACTS:
        errors.append("required_artifacts must equal the closed ShapeForge artifact map")


def _validate_implemented_deltas(
    contract: Mapping[str, Any], world: Mapping[str, Any], errors: list[str]
) -> dict[str, str | None]:
    rows = contract.get("implemented_deltas")
    if not isinstance(rows, list) or len(rows) != len(MODULE_SPECS):
        errors.append("implemented_deltas must equal the closed implemented deltas")
        return {spec["slice_id"]: None for spec in MODULE_SPECS}
    statuses: dict[str, str | None] = {}
    for index, (row, spec) in enumerate(zip(rows, MODULE_SPECS, strict=True)):
        label = spec["label"]
        slice_id = spec["slice_id"]
        if not _exact_keys(row, DELTA_KEYS, f"implemented_deltas[{index}]", errors):
            statuses[slice_id] = None
            continue
        assert isinstance(row, Mapping)
        expected = {
            "slice_id": slice_id,
            "axis": spec["axis"],
            "improvement_target": "contract strengthening",
            "status": ASSET_MODULE_SLICE_STATUS,
        }
        for key, value in expected.items():
            if row.get(key) != value:
                errors.append(f"implemented_deltas[{index}].{key} must equal {value}")
        _nonempty_string(row.get("claim"), f"implemented_deltas[{index}].claim", errors)
        slices = _objects_with(world.get("slices"), "slice_id", slice_id)
        statuses[slice_id] = str(slices[0].get("status")) if len(slices) == 1 else None
        if len(slices) != 1:
            errors.append(f"world model must contain exactly one {label} output slice")
            continue
        if slices[0].get("status") != ASSET_MODULE_SLICE_STATUS:
            errors.append(f"{label} world-model slice status must equal contract")
        scenarios = _objects_with(
            world.get("scenario_transforms"), "scenario_id", spec["scenario_id"]
        )
        if len(scenarios) != 1:
            errors.append(f"world model must contain exactly one {label} operator scenario")
        elif scenarios[0].get("axis") != spec["axis"]:
            errors.append(f"{label} world-model scenario axis must equal {spec['axis']}")
        elif scenarios[0].get("slice_id") != slice_id:
            errors.append(f"{label} world-model scenario must reference its output slice")
    return statuses


def _validate_world_model(
    world: Mapping[str, Any], phi: Mapping[str, Any] | None, errors: list[str]
) -> str | None:
    if world.get("world_model_id") != WORLD_MODEL_ID:
        errors.append("world model id mismatch")
    slices = _objects_with(world.get("slices"), "slice_id", SLICE_ID)
    if len(slices) != 1:
        errors.append("world model must contain exactly one required slice")
        return None
    target = slices[0]
    if target.get("status") != SLICE_STATUS:
        errors.append("world-model slice status must equal contract")
    if phi is not None:
        field_map = {
            "state_vars": "state_variables",
            "operators": "operators",
            "guards": "guards",
            "observables": "observables",
            "canonical_keys": "canonical_keys",
        }
        for world_key, phi_key in field_map.items():
            if _ids(target.get(world_key)) != phi.get(phi_key):
                errors.append(f"world-model slice {world_key} must match phi.{phi_key}")
    scenarios = _objects_with(world.get("scenario_transforms"), "scenario_id", SCENARIO_ID)
    if len(scenarios) != 1:
        errors.append("world model must contain exactly one required evidence scenario")
    elif scenarios[0].get("axis") != AXIS:
        errors.append("world-model scenario axis must equal evidence")
    elif scenarios[0].get("slice_id") != SLICE_ID:
        errors.append("world-model scenario must reference the required slice")
    invariants = _objects_with(world.get("cross_slice_invariants"), "id", INVARIANT_ID)
    if len(invariants) != 1:
        errors.append("world model must contain exactly one publication-authority invariant")
    return str(target.get("status"))


def _validate_authority_mirrors(
    artifacts: Mapping[str, Mapping[str, Any]],
    errors: list[str],
) -> None:
    tactic_bank = artifacts.get("tactic_bank", {})
    scenario_corpus = artifacts.get("scenario_corpus", {})
    development = artifacts.get("development_import", {})
    negative = artifacts.get("negative_knowledge", {})
    tactics = _objects_with(tactic_bank.get("tactics"), "tactic_id", TACTIC_ID)
    if len(tactics) != 1:
        errors.append("tactic bank must contain exactly one authority-refinement tactic")
    mirrored_tactics = _objects_with(development.get("tactics"), "tactic_id", TACTIC_ID)
    if len(tactics) == 1 and mirrored_tactics != tactics:
        errors.append("development import must mirror the required tactic exactly")

    scenarios = _objects_with(
        scenario_corpus.get("scenario_seeds"), "scenario_id", CORPUS_SCENARIO_ID
    )
    if len(scenarios) != 1:
        errors.append("scenario corpus must contain exactly one structural-journal scenario")
    elif scenarios[0].get("status") != "TESTED_ONLY":
        errors.append("structural-journal scenario must remain TESTED_ONLY")
    mirrored_scenarios = _objects_with(
        development.get("scenario_seeds"), "scenario_id", CORPUS_SCENARIO_ID
    )
    if len(scenarios) == 1 and mirrored_scenarios != scenarios:
        errors.append("development import must mirror the required scenario exactly")

    records = _objects_with(negative.get("records"), "hypothesis_id", HYPOTHESIS_ID)
    if len(records) != 1:
        errors.append("negative knowledge must contain exactly one required hypothesis")
    else:
        record = records[0]
        expected = {
            "axis": AXIS,
            "slice_id": SLICE_ID,
            "scenario_id": SCENARIO_ID,
            "negative_kind": "blocked_promotion",
            "status": "blocked",
            "current_evidence_class": "hypothesis",
            "target_evidence_class": TARGET_EVIDENCE_CLASS,
            "world_model_id": WORLD_MODEL_ID,
        }
        for key, value in expected.items():
            if record.get(key) != value:
                errors.append(f"negative knowledge {key} must equal {value}")
        if INVARIANT_ID not in record.get("related_invariants", []):
            errors.append("negative knowledge must bind the publication-authority invariant")


def _validate_module_mirrors(
    scenario_corpus: Mapping[str, Any],
    development: Mapping[str, Any],
    negative: Mapping[str, Any],
    errors: list[str],
) -> None:
    for spec in MODULE_SPECS:
        label = spec["label"]
        scenarios = _objects_with(
            scenario_corpus.get("scenario_seeds"), "scenario_id", spec["scenario_id"]
        )
        if len(scenarios) != 1:
            errors.append(f"scenario corpus must contain exactly one {label} operator scenario")
        elif scenarios[0].get("status") != "TESTED_ONLY":
            errors.append(f"{label} operator scenario must remain TESTED_ONLY")
        mirrored = _objects_with(
            development.get("scenario_seeds"), "scenario_id", spec["scenario_id"]
        )
        if len(scenarios) == 1 and mirrored != scenarios:
            errors.append(f"development import must mirror the {label} scenario exactly")
        records = _objects_with(negative.get("records"), "hypothesis_id", spec["hypothesis_id"])
        if len(records) != 1:
            errors.append(f"negative knowledge must contain exactly one {label} hypothesis")
            continue
        expected = {
            "axis": spec["axis"],
            "slice_id": spec["slice_id"],
            "scenario_id": spec["scenario_id"],
            "negative_kind": "blocked_promotion",
            "status": "blocked",
            "current_evidence_class": "hypothesis",
            "target_evidence_class": "contract",
            "world_model_id": WORLD_MODEL_ID,
        }
        for key, value in expected.items():
            if records[0].get(key) != value:
                errors.append(f"{label} negative knowledge {key} must equal {value}")
        if spec["invariant_id"] not in records[0].get("related_invariants", []):
            errors.append(f"{label} negative knowledge must bind the authority invariant")


def _validate_mirrors(artifacts: Mapping[str, Mapping[str, Any]], errors: list[str]) -> None:
    scenario_corpus = artifacts.get("scenario_corpus", {})
    development = artifacts.get("development_import", {})
    negative = artifacts.get("negative_knowledge", {})
    _validate_authority_mirrors(artifacts, errors)
    _validate_module_mirrors(scenario_corpus, development, negative, errors)


def validate_contract(
    contract: Mapping[str, Any],
    artifacts: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    errors: list[str] = []
    _exact_keys(contract, ROOT_KEYS, "contract", errors)
    if contract.get("schema") != CONTRACT_SCHEMA:
        errors.append(f"schema must equal {CONTRACT_SCHEMA}")
    if contract.get("status") != STATUS:
        errors.append(f"status must equal {STATUS}")
    if contract.get("production_authority") is not False:
        errors.append("production_authority must be the JSON boolean false")
    if contract.get("world_model_id") != WORLD_MODEL_ID:
        errors.append(f"world_model_id must equal {WORLD_MODEL_ID}")

    phi = _validate_phi(contract.get("phi"), errors)
    _validate_artifact_manifest(contract, errors)
    source_pin_count = _validate_source_pins(contract, errors)
    nonclaims = _nonempty_unique_strings(contract.get("nonclaims"), "nonclaims", errors)
    if nonclaims is not None and not any(
        "production authority" in item.lower() for item in nonclaims
    ):
        errors.append("nonclaims must explicitly deny production authority")

    if set(artifacts) != set(EXPECTED_ARTIFACTS):
        errors.append("loaded artifacts must equal the closed ShapeForge artifact set")
    world = artifacts.get("world_model", {})
    slice_status = _validate_world_model(world, phi, errors)
    implemented_statuses = _validate_implemented_deltas(contract, world, errors)
    _validate_mirrors(artifacts, errors)

    return {
        "schema": CHECK_SCHEMA,
        "ok": not errors,
        "contract_status": contract.get("status"),
        "production_authority": contract.get("production_authority"),
        "world_model_id": contract.get("world_model_id"),
        "slice_id": phi.get("slice_id") if phi is not None else None,
        "slice_status": slice_status,
        "implemented_slice_id": ASSET_MODULE_SLICE_ID,
        "implemented_slice_status": implemented_statuses.get(ASSET_MODULE_SLICE_ID),
        "implemented_delta_axis": ASSET_MODULE_AXIS,
        "managed_lifecycle_slice_id": MANAGED_LIFECYCLE_SLICE_ID,
        "managed_lifecycle_slice_status": implemented_statuses.get(MANAGED_LIFECYCLE_SLICE_ID),
        "release_route_slice_id": RELEASE_ROUTE_SLICE_ID,
        "release_route_slice_status": implemented_statuses.get(RELEASE_ROUTE_SLICE_ID),
        "release_route_delta_axis": RELEASE_ROUTE_AXIS,
        "module_receipt_slice_id": MODULE_RECEIPT_SLICE_ID,
        "module_receipt_slice_status": implemented_statuses.get(MODULE_RECEIPT_SLICE_ID),
        "module_receipt_delta_axis": MODULE_RECEIPT_AXIS,
        "receipt_backed_lane_slice_id": RECEIPT_BACKED_LANE_SLICE_ID,
        "receipt_backed_lane_slice_status": implemented_statuses.get(RECEIPT_BACKED_LANE_SLICE_ID),
        "receipt_backed_lane_delta_axis": RECEIPT_BACKED_LANE_AXIS,
        "route_composition_slice_id": ROUTE_COMPOSITION_SLICE_ID,
        "route_composition_slice_status": implemented_statuses.get(ROUTE_COMPOSITION_SLICE_ID),
        "route_composition_delta_axis": ROUTE_COMPOSITION_AXIS,
        "axis": phi.get("axis") if phi is not None else None,
        "target_evidence_class": phi.get("target_evidence_class") if phi is not None else None,
        "artifact_count": len(artifacts),
        "source_pin_count": source_pin_count,
        "errors": errors,
        "nonclaim": NONCLAIM,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check the fail-closed ZRPF ShapeForge global epoch admission slice."
    )
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    args = parser.parse_args(argv)
    try:
        contract = load_json(args.contract)
        artifacts = load_artifacts(contract)
        report = validate_contract(contract, artifacts)
    except ContractError as exc:
        report = {
            "schema": CHECK_SCHEMA,
            "ok": False,
            "errors": [str(exc)],
            "nonclaim": NONCLAIM,
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
